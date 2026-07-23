#!/usr/bin/env python3
"""Refine a blueprint by using Lean as the critic.

This is the author/critic loop:

1. validate the current blueprint;
2. before chunking, optionally ask the model to decompose a bounded set of
   structurally suspicious blueprint nodes into smaller helper nodes;
3. choose the next dependency-closed chunk from the blueprint ``\\uses`` graph;
4. ask a read-only model call to generate disposable Lean for that chunk only,
   while still showing the whole blueprint as context;
5. run Lean on accepted chunk context plus the new chunk;
6. audit that the compiled Lean statements actually align with the target nodes;
7. if Lean/audit fails because the generated Lean is malformed or mistranslated,
   retry Lean generation for the same chunk;
8. if Lean/audit fails because the blueprint is missing mathematical content, ask
   a second model call to fix the blueprint, not the Lean file;
9. after a blueprint repair, revalidate and replan chunks from the repaired
   blueprint;
10. publish only when every chunk has passed.

Lean code is not the source of truth here. The generated files under
``.auto-blueprint/formalization/`` are test artifacts and are overwritten across
trials. A failed proof should cause better blueprint statements, hypotheses,
dependencies, or intermediate lemmas. Errors from trial N are used to repair the
blueprint before the next chunk pass generates fresh Lean.
"""
from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from generate_blueprint import _extract_json, read_paper
from lean_preflight import check_lean_environment, default_lean_command
from model_runners import RunnerError, get_runner
from model_runners.base import is_environment_error
from telemetry import TelemetryRun, node_structural_features
from validate_blueprint import Node, print_result, validate_blueprint

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
SKILL_PATH = REPO_ROOT / ".claude" / "skills" / "paper-to-blueprint" / "SKILL.md"
SCRATCH_DIR = REPO_ROOT / ".auto-blueprint" / "formalization"
PUBLISHED_LEAN_NAME = "formalization.lean"
LEAN_GENERATION_RETRIES = 5
AUTO_CHUNK_SIZE = 0
DEFAULT_AUTO_CHUNK_LIMIT = 8
MEDIUM_NODES_PER_CHUNK = 3
DEFAULT_MODEL_TIMEOUT = 300
DEFAULT_HARD_MODEL_TIMEOUT = 600
CURRENT_LOG_PATH: Path | None = None
MAX_LIBRARY_CANDIDATES = 40
MIN_LIBRARY_CANDIDATES_BEFORE_MODEL_TERMS = 8
LEAN_IDIOM_CHEATSHEET = """\
- Finite sums use `open scoped BigOperators`; common rewrites include
  `Finset.sum_mul`, `Finset.mul_sum`, `Finset.sum_add_distrib`, and
  `Finset.sum_congr`.
- For finite functions `I -> R`, prefer explicit definitions like
  `∑ i : I, v i * w i` when inner-product notation is not essential.
- Continuity proofs often compose existing continuous maps; useful lemmas and
  tactics include `continuous_const`, `continuous_id`, `.add`, `.sub`, `.mul`,
  `.div_const`, `.const_mul`, `.min`, `.max`, and `continuity`.
- Real square/root goals often use `sq_nonneg`, `sq`, `Real.sq_sqrt`, and
  `Real.sqrt_sq_eq_abs`; check hypotheses before using nonneg-specific lemmas.
- `EuclideanSpace R (Fin n)` is a function type indexed by `Fin n`; avoid
  searching for bespoke vector APIs when pointwise functions or finite sums are
  enough for the blueprint statement.
- Avoid blanket imports. If a candidate snippet names the needed theorem, import
  the candidate's listed module directly.
"""
FORBIDDEN_LEAN_PLACEHOLDERS = re.compile(r"\b(sorry|admit)\b|by\s*\?")
FORBIDDEN_ASSUMPTIONS = re.compile(r"^\s*(axiom|constant|opaque)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.MULTILINE)
FORBIDDEN_BLUEPRINT_STUBS = re.compile(
    r"\b(?:"
    r"[A-Za-z_][A-Za-z0-9_'.]*(?:_from_blueprint|_from_paper|_from_the_paper|FromBlueprint|FromPaper)"
    r"|[A-Z][A-Za-z0-9_'.]*_\d{4}_[A-Za-z0-9_'.]*"
    r")\b"
)
LEAN_DECL_START_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:noncomputable|private|protected|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b"
)
VACUOUS_TRUE_EXAMPLES = re.compile(r"^\s*example[\s\S]*?:\s*True\s*:=", re.MULTILINE)
PLACEHOLDER_NAME_RE = re.compile(r"(?:^|_)(?:stub|gap|todo|sorry|trivial)(?:_|$)", re.IGNORECASE)

LEAN_GENERATION_ERROR_PATTERNS = (
    "unexpected token",
    "unknown constant",
    "unknown identifier",
    "unknown module",
    "unknown namespace",
    "function expected",
    "type mismatch",
    "application type mismatch",
    "invalid projection",
    "failed to synthesize",
    "invalid field notation",
    "ambiguous",
    "object file",
    ".olean",
)


@dataclass
class LeanAttempt:
    ok: bool
    command: list[str]
    stdout: str = ""
    stderr: str = ""
    reason: str = ""
    kind: str = "lean"
    rejected_labels: set[str] | None = None

    @property
    def output(self) -> str:
        return "\n".join(part for part in (self.reason, self.stdout, self.stderr) if part).strip()


@dataclass
class LeanDecl:
    kind: str
    name: str
    line: int
    text: str


@dataclass
class LibraryCandidate:
    library: str
    module: str
    declaration: str
    file: Path
    line: int
    matched: str
    snippet: str = ""


@dataclass
class AcceptedChunk:
    labels: list[str]
    imports: list[str]
    body: str
    fingerprints: dict[str, str]
    module: str
    path: Path
    signatures: str


@dataclass
class PrunedChunk:
    labels: list[str]
    lean_code: str
    imports: list[str]
    body: str
    signatures: str


class TeeStream:
    """Mirror script output to the terminal and a persistent run log."""

    def __init__(self, terminal, log_file, *, started_at: float):
        self.terminal = terminal
        self.log_file = log_file
        self.started_at = started_at
        self.at_line_start = True

    def write(self, text: str) -> int:
        for chunk in text.splitlines(keepends=True):
            if self.at_line_start and chunk:
                prefix = f"[+{int(time.monotonic() - self.started_at):06d}s] "
                self.terminal.write(prefix)
                self.log_file.write(prefix)
            self.terminal.write(chunk)
            self.log_file.write(chunk)
            self.at_line_start = chunk.endswith("\n")
        return len(text)

    def flush(self) -> None:
        self.terminal.flush()
        self.log_file.flush()


def _run_log_path(name: str) -> Path:
    out_dir = SCRATCH_DIR / name
    out_dir.mkdir(parents=True, exist_ok=True)
    stamp = time.strftime("%Y%m%d-%H%M%S")
    return out_dir / f"run-{stamp}.log"


def _clear_stale_attempt_artifacts(name: str) -> int:
    """Remove old model-generated Lean attempts before a fresh refinement run.

    Timestamped run logs are intentionally kept for human debugging, but stale
    Lean attempts and reports are deleted so a new agent run does not have
    previous failed implementations sitting in the obvious scratch location.
    """
    out_dir = SCRATCH_DIR / name
    if not out_dir.exists():
        return 0
    patterns = (
        "chunk_*_attempt_*.lean",
        "trial_*.lean",
        "partial_formalization.lean",
        "assembled_formalization.lean",
        "report.md",
    )
    removed = 0
    for pattern in patterns:
        for path in out_dir.glob(pattern):
            if not path.is_file():
                continue
            path.unlink()
            removed += 1
    return removed


def _read_blueprint_source(name: str) -> str:
    src = REPO_ROOT / "blueprints" / name / "blueprint" / "src"
    content = src / "content.tex"
    if not content.is_file():
        raise FileNotFoundError(f"{content.relative_to(REPO_ROOT)} does not exist")
    parts = [f"% FILE: {content.relative_to(REPO_ROOT)}\n{content.read_text(encoding='utf-8')}"]
    common = src / "macros" / "common.tex"
    if common.is_file():
        parts.append(f"% FILE: {common.relative_to(REPO_ROOT)}\n{common.read_text(encoding='utf-8')}")
    return "\n\n".join(parts)


def _lean_name(label: str) -> str:
    name = re.sub(r"[^A-Za-z0-9_]+", "_", label).strip("_")
    if not name or name[0].isdigit():
        name = f"node_{name}"
    return name


def _node_summary(nodes: dict[str, Node]) -> str:
    lines: list[str] = []
    for label, node in sorted(nodes.items(), key=lambda item: (item[1].file, item[1].line, item[0])):
        uses = ", ".join(sorted(node.uses)) or "(none)"
        lean_decl = node.lean_decl or ""
        lines.append(
            f"- {label}: {node.kind}, Lean name `{_lean_name(label)}`, "
            f"uses [{uses}], settled decl `{lean_decl}`"
        )
    return "\n".join(lines)


def _node_order(nodes: dict[str, Node]) -> list[str]:
    return [
        label
        for label, _node in sorted(
            nodes.items(),
            key=lambda item: (str(item[1].file), item[1].line, item[0]),
        )
    ]


HARD_NODE_KEYWORDS = (
    "approximation",
    "bichromatic",
    "correctness",
    "hardness",
    "lower bound",
    "ovc",
    "reconstruction",
    "reduction",
    "runtime",
    "seth",
    "tensor",
    "transfer",
)


def _node_difficulty(label: str, node: Node, block: str) -> str:
    """Classify a blueprint node for scheduling, not for mathematical meaning."""
    text = f"{label}\n{node.kind}\n{block}".lower()
    score = 0
    if node.kind in {"theorem", "corollary"}:
        score += 5
    elif node.kind in {"lemma", "proposition"}:
        score += 2
    score += min(len(node.uses), 6) // 2
    if len(block) > 3500:
        score += 3
    elif len(block) > 1800:
        score += 1
    score += sum(1 for keyword in HARD_NODE_KEYWORDS if keyword in text)

    if score >= 6:
        return "hard"
    if score >= 3:
        return "medium"
    return "easy"


def _decomposition_candidate_reasons(label: str, node: Node, block: str) -> list[str]:
    """Explain why a node should be decomposed before expensive Lean attempts.

    This is deliberately a prepass heuristic, not a correctness judgment. The
    model still has to edit the blueprint, validation has to pass, and generated
    Lean must later align with the resulting blueprint nodes one-to-one.
    """
    features = node_structural_features(label, node.kind, block, len(node.uses))
    reasons: list[str] = []
    if features["proof_chars"] > 1200 and features["display_math_count"] >= 2:
        reasons.append("long proof with multiple displayed equations")
    if features["sum_token_count"] + features["product_token_count"] >= 3:
        reasons.append("multiple finite sum/product operators")
    if features["reindex_token_count"] > 0:
        reasons.append("reindexing or bijection language")
    if features["equation_like_count"] >= 8 and features["proof_chars"] > 700:
        reasons.append("many equation/inequality steps in one node")
    if node.kind in {"theorem", "corollary"} and len(node.uses) >= 5:
        reasons.append("high-level result with many dependencies")
    if (
        _node_difficulty(label, node, block) == "hard"
        and features["proof_chars"] > 500
        and features["display_math_count"] > 0
    ):
        reasons.append("scheduler-hard node with nontrivial proof text")
    return reasons


def _pre_decomposition_candidates(
    nodes: dict[str, Node],
    *,
    accepted_labels: set[str],
    limit: int,
) -> list[tuple[str, list[str]]]:
    """Return suspicious unresolved nodes for the pre-refinement decomposition pass."""
    if limit <= 0:
        return []
    blocks = _node_tex_blocks(nodes)
    candidates: list[tuple[int, str, list[str]]] = []
    for label in _node_order(nodes):
        node = nodes[label]
        if label in accepted_labels or node.mathlibok:
            continue
        reasons = _decomposition_candidate_reasons(label, node, blocks.get(label, ""))
        if not reasons:
            continue
        features = node_structural_features(label, node.kind, blocks.get(label, ""), len(node.uses))
        score = (
            len(reasons) * 10
            + min(int(features["proof_chars"] or 0) // 250, 8)
            + min(int(features["equation_like_count"] or 0), 12)
            + min(len(node.uses), 8)
        )
        candidates.append((score, label, reasons))
    candidates.sort(key=lambda item: (-item[0], _node_order(nodes).index(item[1])))
    return [(label, reasons) for _score, label, reasons in candidates[:limit]]


def _parse_decomposition_refusal(text: str) -> dict | None:
    """Detect a structured generation refusal (node needs blueprint helpers).

    The generation prompt allows the model to reply with a single
    ``NEEDS-DECOMPOSITION: {...json...}`` line instead of emitting weakened
    Lean it knows cannot match the blueprint node 1-1.
    """
    match = re.search(r"NEEDS-DECOMPOSITION:\s*(\{.*\})", text, re.DOTALL)
    if not match:
        return None
    payload: dict = {"label": "", "missing_helpers": [], "reason": ""}
    try:
        parsed = json.loads(match.group(1))
        if isinstance(parsed, dict):
            payload["label"] = str(parsed.get("label") or "")
            payload["missing_helpers"] = [
                str(h) for h in (parsed.get("missing_helpers") or []) if str(h).strip()
            ]
            payload["reason"] = str(parsed.get("reason") or "")
    except json.JSONDecodeError:
        payload["reason"] = match.group(1)[:2000]
    return payload


def _decomposition_note(labels: list[str], helpers: list[str] | None = None) -> str:
    helper_text = ""
    if helpers:
        helper_text = (
            " The generator identified these missing helper statements; add each as its "
            "own blueprint node (definition/lemma) with correct \\uses edges: "
            + " | ".join(helpers[:8])
        )
    return (
        "Repair by DECOMPOSITION. Split the node(s) "
        + ", ".join(labels)
        + " into 2-4 smaller blueprint nodes (statement-level helper definitions/"
        "lemmas), each individually formalizable as a single Lean declaration with "
        "1-1 structural correspondence, and rewire \\uses so the original node "
        "depends on the new helpers. Keep the mathematics identical; only the "
        "packaging changes. Do NOT merely rephrase the existing node text."
        + helper_text
    )


def _next_chunk(
    nodes: dict[str, Node],
    accepted: set[str],
    *,
    chunk_size: int,
    force_singletons: set[str] | None = None,
) -> list[str]:
    """Pick a dependency-closed chunk, batching easy nodes and isolating hard ones."""
    force_singletons = force_singletons or set()
    available = set(accepted) | {label for label, node in nodes.items() if node.mathlibok}
    remaining = [label for label in _node_order(nodes) if label not in available]
    blocks = _node_tex_blocks(nodes)
    difficulties = {
        label: _node_difficulty(label, node, blocks.get(label, ""))
        for label, node in nodes.items()
    }
    chunk: list[str] = []
    progressed = True
    while progressed and len(chunk) < chunk_size:
        progressed = False
        for label in remaining:
            if label in chunk:
                continue
            node = nodes[label]
            if not node.uses <= (available | set(chunk)):
                continue

            difficulty = difficulties[label]
            if label in force_singletons:
                if not chunk:
                    chunk.append(label)
                return chunk

            if difficulty == "hard":
                # If a hard node is the first ready obligation, isolate it.
                # If easy/medium nodes are already in this chunk, leave the
                # hard node for the next pass instead of mixing obligations.
                if not chunk:
                    chunk.append(label)
                return chunk

            medium_count = sum(1 for item in chunk if difficulties[item] == "medium")
            if difficulty == "medium" and medium_count >= MEDIUM_NODES_PER_CHUNK:
                return chunk

            chunk.append(label)
            progressed = True
            if len(chunk) >= chunk_size:
                break
    return chunk


def _is_timeout_error(exc: Exception) -> bool:
    text = str(exc).lower()
    return "timed out" in text or "timeout" in text


def _chunk_summary(nodes: dict[str, Node], labels: list[str]) -> str:
    return _node_summary({label: nodes[label] for label in labels})


def _dependency_checklist(nodes: dict[str, Node], labels: list[str]) -> str:
    """Per-target list of non-Mathlib dependency Lean names the decl must mention.

    Mirrors the deterministic audit (`_nonmathlib_uses_missing_from_decl`) so
    the requirement is stated up front instead of discovered after a full
    generation."""
    lines: list[str] = []
    for label in labels:
        node = nodes.get(label)
        if node is None:
            continue
        required = [
            _lean_name(dep)
            for dep in sorted(node.uses)
            if dep in nodes and not nodes[dep].mathlibok
        ]
        if required:
            lines.append(f"- {label}: {', '.join(required)}")
    return "\n".join(lines) if lines else "- (no required dependency mentions)"


def _chunk_difficulty_summary(nodes: dict[str, Node], labels: list[str]) -> str:
    blocks = _node_tex_blocks({label: nodes[label] for label in labels})
    return ", ".join(
        f"{label}={_node_difficulty(label, nodes[label], blocks.get(label, ''))}"
        for label in labels
    )


def _chunk_has_hard_node(nodes: dict[str, Node], labels: list[str]) -> bool:
    blocks = _node_tex_blocks({label: nodes[label] for label in labels})
    return any(
        _node_difficulty(label, nodes[label], blocks.get(label, "")) == "hard"
        for label in labels
    )


@contextlib.contextmanager
def _runner_timeout(runner, timeout: int):
    """Temporarily adjust a runner's per-call timeout for one model call."""
    previous = runner.timeout
    runner.timeout = timeout
    try:
        yield
    finally:
        runner.timeout = previous


def _node_fingerprints(nodes: dict[str, Node]) -> dict[str, str]:
    blocks = _node_tex_blocks(nodes)
    return {
        label: hashlib.sha256(blocks.get(label, "").encode("utf-8")).hexdigest()
        for label in nodes
    }


def _dependency_descendants(nodes: dict[str, Node], changed: set[str]) -> set[str]:
    """Return labels whose transitive dependencies include any changed label."""
    affected = set(changed)
    progressed = True
    while progressed:
        progressed = False
        for label, node in nodes.items():
            if label in affected:
                continue
            if node.uses & affected:
                affected.add(label)
                progressed = True
    return affected


def _dependency_descendants_within(nodes: dict[str, Node], changed: set[str], universe: set[str]) -> set[str]:
    """Return changed labels plus their blueprint descendants inside ``universe``."""
    return _dependency_descendants(nodes, changed) & universe


def _dependency_closure(nodes: dict[str, Node], labels: list[str]) -> set[str]:
    """Return all transitive blueprint dependencies of the supplied labels."""
    seen: set[str] = set()
    stack = list(labels)
    while stack:
        label = stack.pop()
        node = nodes.get(label)
        if node is None:
            continue
        for dep in node.uses:
            if dep not in nodes or dep in seen:
                continue
            seen.add(dep)
            stack.append(dep)
    return seen


def _nonmathlib_uses_missing_from_decl(
    label: str,
    node: Node,
    decl: LeanDecl,
    nodes: dict[str, Node],
    decls: dict[str, LeanDecl],
) -> list[str]:
    """Find explicit blueprint dependencies not visible in this Lean declaration.

    ``\\uses`` is the blueprint's public dependency contract. For generated
    declarations corresponding to blueprint nodes, the Lean statement/body
    should mention each non-Mathlib dependency's generated declaration name,
    either directly or through a same-module helper structure/result type used
    by that declaration. This catches ignored dependencies without rejecting
    patterns like ``def def_msd : MSDData := ...`` where ``MSDData`` carries the
    dependency field type.
    """
    visible_text = _decl_text_with_local_helpers(decl, decls)
    missing: list[str] = []
    for dep in sorted(node.uses):
        dep_node = nodes.get(dep)
        if dep_node is None or dep_node.mathlibok:
            continue
        dep_name = _lean_name(dep)
        if not re.search(rf"\b{re.escape(dep_name)}\b", visible_text):
            missing.append(dep)
    return missing


def _decl_text_with_local_helpers(decl: LeanDecl, decls: dict[str, LeanDecl], *, max_depth: int = 2) -> str:
    """Return declaration text plus nearby helper declarations it references.

    This is a conservative local approximation of the Lean dependency graph.
    It is only used for deterministic statement-audit coverage; Lean itself
    remains the authority for compilation.
    """
    seen = {decl.name}
    parts = [decl.text]
    frontier = [decl]
    for _depth in range(max_depth):
        next_frontier: list[LeanDecl] = []
        haystack = "\n".join(item.text for item in frontier)
        for name, candidate in decls.items():
            if name in seen:
                continue
            if re.search(rf"\b{re.escape(name)}\b", haystack):
                seen.add(name)
                parts.append(candidate.text)
                next_frontier.append(candidate)
        if not next_frontier:
            break
        frontier = next_frontier
    return "\n\n".join(parts)


def _accepted_state(chunks: list[AcceptedChunk]) -> tuple[set[str], list[str], list[str]]:
    labels: set[str] = set()
    imports: list[str] = []
    signatures: list[str] = []
    for chunk in chunks:
        labels.update(chunk.labels)
        module_import = f"import {chunk.module}"
        for item in [module_import]:
            if item not in imports:
                imports.append(item)
        signatures.append(chunk.signatures)
    return labels, imports, signatures


def _standalone_accepted_code(chunks: list[AcceptedChunk]) -> str:
    imports: list[str] = []
    bodies: list[str] = []
    for chunk in chunks:
        for item in chunk.imports:
            if item not in imports:
                imports.append(item)
        bodies.append(chunk.body)
    return _compose_lean_file(imports, bodies)


def _node_tex_blocks(nodes: dict[str, Node]) -> dict[str, str]:
    """Extract the rendered-source contract for each blueprint node."""
    by_file: dict[Path, str] = {}
    blocks: dict[str, str] = {}
    for label, node in nodes.items():
        if node.file not in by_file:
            by_file[node.file] = node.file.read_text(encoding="utf-8")
        text = by_file[node.file]
        label_pos = text.find(rf"\label{{{label}}}")
        if label_pos == -1:
            blocks[label] = ""
            continue
        begin = text.rfind(r"\begin{", 0, label_pos)
        env_end = text.find(r"\end{", label_pos)
        if begin == -1 or env_end == -1:
            blocks[label] = text[label_pos : label_pos + 1200]
            continue
        env_close = text.find("}", env_end)
        if env_close == -1:
            blocks[label] = text[begin : env_end + 80]
            continue
        block_end = env_close + 1
        proof = re.match(r"\s*\\begin\{proof\}[\s\S]*?\\end\{proof\}", text[block_end:])
        if proof:
            block_end += proof.end()
        blocks[label] = text[begin:block_end].strip()
    return blocks


def _lean_module_for(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def _library_roots() -> list[tuple[str, Path]]:
    """Return local Lean library roots; CS Lib is included when installed."""
    roots: list[tuple[str, Path]] = []
    mathlib = REPO_ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
    if mathlib.is_dir():
        roots.append(("Mathlib", mathlib))
    packages = REPO_ROOT / ".lake" / "packages"
    if packages.is_dir():
        for child in sorted(packages.iterdir()):
            low = child.name.lower().replace("-", "").replace("_", "")
            if "cslib" not in low:
                continue
            for candidate in (child / "CSLib", child / "Cslib", child / "CsLib", child):
                if candidate.is_dir():
                    roots.append(("CSLib", candidate))
                    break
    return roots


def _search_terms_from_blueprint(nodes: dict[str, Node], blueprint_blocks: dict[str, str]) -> list[str]:
    """Build lexical search terms for local Mathlib/CS Lib lookup."""
    stopwords = {
        "about",
        "after",
        "also",
        "apply",
        "argument",
        "because",
        "before",
        "begin",
        "between",
        "blueprint",
        "claim",
        "commute",
        "concrete",
        "condition",
        "definition",
        "different",
        "displayed",
        "double",
        "equivalently",
        "exists",
        "factor",
        "fin",
        "finite",
        "fintype",
        "formal",
        "function",
        "given",
        "have",
        "hypothesis",
        "label",
        "later",
        "lemma",
        "mathsf",
        "number",
        "only",
        "paper",
        "proof",
        "proposition",
        "real",
        "result",
        "reverse",
        "should",
        "statement",
        "sum",
        "there",
        "theorem",
        "these",
        "this",
        "threshold",
        "type",
        "uses",
        "used",
        "vector",
        "where",
        "which",
        "with",
    }
    aliases = {
        "inner product": ["inner", "innerProduct", "dotProduct"],
        "tensor": ["TensorProduct", "kron"],
        "kronecker": ["TensorProduct", "tmul"],
        "hamming": ["hamming", "Hamming"],
        "edit distance": ["levenshtein", "editDistance"],
        "levenshtein": ["levenshtein"],
        "entropy": ["entropy", "binEntropy"],
        "orthogonal": ["orthogonal", "Orthogonal"],
        "continuous": ["Continuous", "continuous"],
        "finite sum": ["Finset.sum"],
        "softmax": ["softmax", "Real.exp"],
        "simple graph": ["SimpleGraph"],
        "variance": ["variance"],
        "probability": ["ProbabilityTheory", "MeasureTheory"],
    }
    terms: list[str] = []
    seen: set[str] = set()

    def add(term: str) -> None:
        term = term.strip()
        if len(term) < 3 or term.lower() in seen:
            return
        seen.add(term.lower())
        terms.append(term)

    for label, node in nodes.items():
        add(_lean_name(label))
        if node.lean_decl:
            add(node.lean_decl)
        text = blueprint_blocks.get(label, "")
        low = text.lower()
        for phrase, phrase_terms in aliases.items():
            if phrase in low:
                for term in phrase_terms:
                    add(term)
    return terms


def _parse_declaration_from_line(line: str) -> str | None:
    match = LEAN_DECL_START_RE.match(line)
    if match:
        return match.group(2)
    return None


def _lean_decl_snippet(path: Path, line_no: int, *, max_lines: int = 8, max_chars: int = 900) -> str:
    """Return the declaration header near file:line so the model need not open it."""
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return ""
    start = max(0, line_no - 1)
    out: list[str] = []
    for line in lines[start : start + max_lines]:
        stripped = line.rstrip()
        if stripped.lstrip().startswith("--"):
            continue
        out.append(stripped)
        joined = "\n".join(out).strip()
        if ":=" in stripped or " where" in stripped or len(joined) >= max_chars:
            break
    return "\n".join(out).strip()[:max_chars]


def _candidate_from_decl_line(
    roots: list[tuple[str, Path]],
    path: Path,
    line_no: int,
    line: str,
    terms: list[str],
) -> LibraryCandidate | None:
    decl = _parse_declaration_from_line(line.strip())
    if decl is None:
        return None

    resolved = path.resolve()
    lib_name = "Lean"
    module = path.stem
    for name, root in [(name, root.resolve()) for name, root in roots]:
        if resolved == root or root in resolved.parents:
            lib_name = name
            module = _lean_module_for(root, resolved)
            break

    matched = next(
        (
            term
            for term in terms
            if term.lower() in line.lower()
            or term.lower() in decl.lower()
            or term.lower() in module.lower()
        ),
        terms[0],
    )
    return LibraryCandidate(
        lib_name,
        module,
        decl,
        resolved,
        line_no,
        matched,
        _lean_decl_snippet(resolved, line_no),
    )


def _python_library_candidates(
    roots: list[tuple[str, Path]],
    terms: list[str],
    *,
    max_candidates: int,
) -> list[LibraryCandidate]:
    if not roots or not terms:
        return []
    lowered = [term.lower() for term in terms[:80]]
    candidates: list[LibraryCandidate] = []
    seen: set[tuple[str, str]] = set()
    for _name, root in roots:
        for path in root.rglob("*.lean"):
            try:
                with path.open(encoding="utf-8") as fh:
                    for line_no, line in enumerate(fh, start=1):
                        low = line.lower()
                        if not any(term in low for term in lowered):
                            continue
                        candidate = _candidate_from_decl_line(roots, path, line_no, line, terms)
                        if candidate is None:
                            continue
                        key = (candidate.module, candidate.declaration)
                        if key in seen:
                            continue
                        seen.add(key)
                        candidates.append(candidate)
                        if len(candidates) >= max_candidates:
                            return candidates
            except OSError:
                continue
    return candidates


def _rg_library_candidates(
    roots: list[tuple[str, Path]],
    terms: list[str],
    *,
    max_candidates: int,
) -> list[LibraryCandidate]:
    rg = shutil.which("rg")
    if not rg or not roots or not terms:
        return _python_library_candidates(roots, terms, max_candidates=max_candidates)
    pattern = "|".join(re.escape(term) for term in terms[:80])
    cmd = [
        rg,
        "--no-heading",
        "--line-number",
        "--glob",
        "*.lean",
        pattern,
        *[str(root) for _name, root in roots],
    ]
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), capture_output=True, text=True)
    if proc.returncode not in {0, 1}:
        return _python_library_candidates(roots, terms, max_candidates=max_candidates)

    candidates: list[LibraryCandidate] = []
    seen: set[tuple[str, str]] = set()
    for raw in proc.stdout.splitlines():
        parts = raw.split(":", 2)
        if len(parts) != 3:
            continue
        path = Path(parts[0])
        try:
            line_no = int(parts[1])
        except ValueError:
            continue
        line = parts[2].strip()
        candidate = _candidate_from_decl_line(roots, path, line_no, line, terms)
        if candidate is None:
            continue

        key = (candidate.module, candidate.declaration)
        if key in seen:
            continue
        seen.add(key)
        candidates.append(candidate)
        if len(candidates) >= max_candidates:
            break
    return candidates or _python_library_candidates(roots, terms, max_candidates=max_candidates)


def _library_search_terms_prompt(name: str, blueprint_source: str, existing_terms: list[str]) -> str:
    return f"""TASK: PROPOSE-LEAN-LIBRARY-SEARCH-TERMS

The deterministic local Mathlib/CS Lib search found too few useful candidates.
Propose better Lean library search terms for the blueprint below.

Return exactly one JSON object:
{{
  "terms": ["short Lean/library search term", "..."]
}}

Rules:
- Return terms only; do not generate Lean.
- Prefer likely declaration names, module words, and common theorem names.
- Include synonyms when paper terminology may differ from Lean terminology.
- Keep the list under 40 terms.

Blueprint name: {name}

Existing terms already tried:
{", ".join(existing_terms[:80])}

Blueprint source:
```tex
{blueprint_source[:20000]}
```
"""


def _search_local_lean_libraries(
    name: str,
    nodes: dict[str, Node],
    blueprint_source: str,
    *,
    term_runner=None,
) -> tuple[str, list[LibraryCandidate]]:
    """Search local Mathlib/CS Lib once for the current blueprint version."""
    roots = _library_roots()
    root_names = ", ".join(name for name, _root in roots) or "(none)"
    print(f"==> Searching local Lean libraries for candidate declarations ({root_names})", flush=True)
    blueprint_blocks = _node_tex_blocks(nodes)
    terms = _search_terms_from_blueprint(nodes, blueprint_blocks)
    candidates = _rg_library_candidates(roots, terms, max_candidates=MAX_LIBRARY_CANDIDATES)

    if len(candidates) < MIN_LIBRARY_CANDIDATES_BEFORE_MODEL_TERMS and term_runner is not None:
        print("  deterministic search was sparse; asking model for extra search terms", flush=True)
        result = term_runner.run(_library_search_terms_prompt(name, blueprint_source, terms), cwd=REPO_ROOT, retries=0)
        try:
            payload = _extract_json(result.text)
            extra_terms = [str(term) for term in payload.get("terms", []) if str(term).strip()]
        except ValueError:
            extra_terms = []
        if extra_terms:
            terms.extend(extra_terms)
            candidates = _rg_library_candidates(roots, terms, max_candidates=MAX_LIBRARY_CANDIDATES)

    lines = []
    lines.append(
        "- Candidate modules below were found by deterministic local search; "
        "treat module paths as already verified."
    )
    if not any(lib == "CSLib" for lib, _root in roots):
        lines.append("- CS Lib: not installed locally under `.lake/packages/`; search used available local libraries only.")
    for cand in candidates:
        rel = cand.file
        try:
            rel = cand.file.relative_to(REPO_ROOT)
        except ValueError:
            pass
        lines.append(
            f"- {cand.library}: `{cand.declaration}` in `{cand.module}` "
            f"({rel}:{cand.line}, matched `{cand.matched}`)"
        )
        if cand.snippet:
            lines.append("  ```lean")
            lines.extend(f"  {line}" for line in cand.snippet.splitlines())
            lines.append("  ```")

    print(f"  found {len(candidates)} candidate declaration(s)", flush=True)
    summary = "\n".join(lines) if lines else "- No local Lean library candidates found."
    return summary, candidates


def _lean_declarations(code: str) -> dict[str, LeanDecl]:
    lines = code.splitlines()
    starts: list[tuple[int, re.Match[str]]] = []
    for idx, line in enumerate(lines):
        match = LEAN_DECL_START_RE.match(line)
        if match:
            starts.append((idx, match))

    decls: dict[str, LeanDecl] = {}
    for pos, (start_idx, match) in enumerate(starts):
        end_idx = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        name = match.group(2)
        decls[name] = LeanDecl(
            kind=match.group(1),
            name=name,
            line=start_idx + 1,
            text="\n".join(lines[start_idx:end_idx]).strip(),
        )
    return decls


def _module_safe_name(name: str) -> str:
    parts = re.split(r"[^A-Za-z0-9]+", name)
    safe = "".join(part[:1].upper() + part[1:] for part in parts if part)
    return safe or "Blueprint"


def _generated_module_dir(name: str) -> Path:
    return REPO_ROOT / "AutoBlueprint" / "Generated" / _module_safe_name(name)


def _chunk_module(name: str, chunk_number: int) -> tuple[str, Path]:
    base = _module_safe_name(name)
    module = f"AutoBlueprint.Generated.{base}.Chunk{chunk_number:02d}"
    path = REPO_ROOT / "AutoBlueprint" / "Generated" / base / f"Chunk{chunk_number:02d}.lean"
    return module, path


def _chunk_manifest_path(name: str) -> Path:
    return _generated_module_dir(name) / "manifest.json"


def _routing_hints_path(name: str) -> Path:
    return SCRATCH_DIR / name / "routing_hints.json"


def _load_routing_hints(name: str) -> dict[str, set[str]]:
    path = _routing_hints_path(name)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return {"forced_singletons": set(), "timeout_hard_overrides": set()}
    return {
        "forced_singletons": {
            str(label) for label in payload.get("forced_singletons", []) if str(label).strip()
        },
        "timeout_hard_overrides": {
            str(label) for label in payload.get("timeout_hard_overrides", []) if str(label).strip()
        },
    }


def _write_routing_hints(
    name: str,
    *,
    forced_singletons: set[str],
    timeout_hard_overrides: set[str],
) -> None:
    path = _routing_hints_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "forced_singletons": sorted(forced_singletons),
                "timeout_hard_overrides": sorted(timeout_hard_overrides),
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_chunk_manifest(name: str, accepted_chunks: list[AcceptedChunk]) -> None:
    """Record accepted chunks so --continue can skip re-verifying unchanged ones.

    Each entry stores enough to prove nothing relevant changed: the chunk file
    hash (the Lean code) and the per-label blueprint fingerprints (the TeX the
    audit judged it against). If both still match at resume time, the previous
    Lean check and alignment audit verdicts still hold.
    """
    entries = []
    for chunk in accepted_chunks:
        try:
            sha = _file_sha256(chunk.path)
        except OSError:
            continue
        entries.append(
            {
                "file": chunk.path.name,
                "sha256": sha,
                "labels": list(chunk.labels),
                "fingerprints": dict(chunk.fingerprints),
            }
        )
    path = _chunk_manifest_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"chunks": entries}, indent=2) + "\n", encoding="utf-8")


def _read_chunk_manifest(name: str) -> dict[str, dict]:
    try:
        data = json.loads(_chunk_manifest_path(name).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    entries = data.get("chunks") if isinstance(data, dict) else None
    if not isinstance(entries, list):
        return {}
    return {entry["file"]: entry for entry in entries if isinstance(entry, dict) and "file" in entry}


def _manifest_current_accepted_labels(name: str, validation_nodes: dict[str, Node]) -> set[str]:
    """Return manifest labels whose code and blueprint fingerprints still match.

    This is only a cheap prepass filter; the real ``--continue`` path still owns
    accepting generated Lean as usable context.
    """
    manifest = _read_chunk_manifest(name)
    if not manifest:
        return set()
    current_fingerprints = _node_fingerprints(validation_nodes)
    generated_dir = _generated_module_dir(name)
    labels: set[str] = set()
    for entry in manifest.values():
        file_name = str(entry.get("file") or "")
        path = generated_dir / file_name
        fingerprints = entry.get("fingerprints") or {}
        entry_labels = entry.get("labels") or []
        if (
            file_name
            and path.is_file()
            and path.with_suffix(".olean").is_file()
            and entry.get("sha256") == _file_sha256(path)
            and set(fingerprints) == set(entry_labels)
            and all(
                label in validation_nodes
                and current_fingerprints.get(label) == fingerprint
                for label, fingerprint in fingerprints.items()
            )
        ):
            labels.update(str(label) for label in entry_labels)
    return labels


def _olean_roots() -> list[Path]:
    """Directories holding compiled .olean trees for local packages."""
    roots = [REPO_ROOT / ".lake" / "build" / "lib" / "lean"]
    packages = REPO_ROOT / ".lake" / "packages"
    if packages.is_dir():
        roots.extend(sorted(packages.glob("*/.lake/build/lib/lean")))
    return [root for root in roots if root.is_dir()]


def _missing_olean_imports(import_lines: list[str]) -> list[str]:
    """Return import lines whose module has no compiled .olean locally.

    Only flags modules whose top-level namespace is owned by a local package
    root (e.g. Mathlib, Batteries); core namespaces like Init/Lean/Std live in
    the toolchain and are never flagged. Generated AutoBlueprint modules are
    compiled by this script itself and are skipped too.
    """
    roots = _olean_roots()
    missing: list[str] = []
    for line in import_lines:
        module = line.strip()
        if not module.startswith("import "):
            continue
        module = module[len("import "):].strip()
        if not module or module.startswith("AutoBlueprint"):
            continue
        top = module.split(".", 1)[0]
        rel = Path(*module.split("."))
        owned = False
        found = False
        for root in roots:
            if (root / top).is_dir() or (root / f"{top}.olean").is_file():
                owned = True
                if (root / rel.parent / f"{rel.name}.olean").is_file():
                    found = True
                    break
        if owned and not found:
            missing.append(line.strip())
    return missing


def _decl_signatures(code: str) -> str:
    signatures: list[str] = []
    for decl in _lean_declarations(code).values():
        lines = decl.text.splitlines()
        head_lines: list[str] = []
        for line in lines:
            head_lines.append(line)
            if ":=" in line or line.strip().endswith("where"):
                break
            if len(head_lines) >= 8:
                break
        head = "\n".join(head_lines)
        head = head.split(":=", 1)[0].rstrip()
        signatures.append(head)
    return "\n\n".join(signatures)


def _deterministic_statement_audit(
    code: str,
    nodes: dict[str, Node],
    all_nodes: dict[str, Node] | None = None,
) -> list[str]:
    """Catch obvious coverage and weakening failures before using model judgment."""
    issues: list[str] = []
    decls = _lean_declarations(code)
    all_nodes = all_nodes or nodes
    required = {label: node for label, node in nodes.items() if not node.mathlibok}

    missing = [f"{label} -> `{_lean_name(label)}`" for label in sorted(required) if _lean_name(label) not in decls]
    if missing:
        shown = ", ".join(missing[:20])
        more = "" if len(missing) <= 20 else f", ... ({len(missing)} total)"
        issues.append(f"missing generated declarations for blueprint nodes: {shown}{more}")

    prop_true = [
        f"{decl.kind} {decl.name}"
        for decl in decls.values()
        if decl.kind in {"def", "abbrev"} and re.search(r":\s*Prop\s*:=\s*True\b", decl.text)
    ]
    if prop_true:
        shown = ", ".join(prop_true[:20])
        more = "" if len(prop_true) <= 20 else f", ... ({len(prop_true)} total)"
        issues.append(f"defines propositions as `True`: {shown}{more}")

    placeholder_decls = [
        decl.name
        for decl in decls.values()
        if PLACEHOLDER_NAME_RE.search(decl.name) or PLACEHOLDER_NAME_RE.search(decl.text[:300])
    ]
    if placeholder_decls:
        shown = ", ".join(placeholder_decls[:20])
        more = "" if len(placeholder_decls) <= 20 else f", ... ({len(placeholder_decls)} total)"
        issues.append(f"contains placeholder/gap declarations instead of aligned statements: {shown}{more}")

    for label, node in required.items():
        decl = decls.get(_lean_name(label))
        if decl is None:
            continue
        if node.kind == "definition" and decl.kind in {"theorem", "lemma"}:
            issues.append(
                f"{label} is a blueprint definition but generated `{decl.kind} {decl.name}`; "
                "definitions should normally be Lean `def`/`structure`/`inductive` declarations"
            )
        if node.kind in {"lemma", "proposition", "theorem", "corollary"} and decl.kind in {
            "structure",
            "inductive",
            "class",
        }:
            issues.append(f"{label} is theorem-like but generated `{decl.kind} {decl.name}`")
        missing_deps = _nonmathlib_uses_missing_from_decl(label, node, decl, all_nodes, decls)
        if missing_deps:
            shown = ", ".join(f"{dep} -> `{_lean_name(dep)}`" for dep in missing_deps[:12])
            more = "" if len(missing_deps) <= 12 else f", ... ({len(missing_deps)} total)"
            issues.append(
                f"{label} does not mention required blueprint dependency/dependencies: {shown}{more}"
            )
    return issues


def _deterministic_audit_kind(issues: list[str]) -> str:
    """Classify deterministic audit failures without another model call."""
    text = "\n".join(issues).lower()
    blueprint_markers = (
        "blueprint definition but generated",
        "defines propositions as `true`",
        "placeholder/gap declarations",
        "theorem-like but generated",
    )
    if any(marker in text for marker in blueprint_markers):
        return "blueprint"
    return "lean-generation"


def _extract_lean_code(text: str) -> str:
    fence = re.search(r"```(?:lean|lean4)?\s*([\s\S]*?)```", text)
    return (fence.group(1) if fence else text).strip()


def _split_lean_imports_and_body(code: str) -> tuple[list[str], str]:
    imports: list[str] = []
    body_lines: list[str] = []
    for line in code.splitlines():
        stripped = line.strip()
        if stripped.startswith("import "):
            imports.append(stripped)
            continue
        if stripped == "set_option autoImplicit false":
            continue
        body_lines.append(line)
    body = "\n".join(body_lines).strip()
    return imports, body


def _compose_lean_file(imports: list[str], accepted_bodies: list[str], new_code: str = "") -> str:
    new_imports, new_body = _split_lean_imports_and_body(new_code)
    all_imports: list[str] = []
    seen_imports: set[str] = set()
    for item in [*imports, *new_imports]:
        if item not in seen_imports:
            all_imports.append(item)
            seen_imports.add(item)
    if not all_imports:
        all_imports = ["import Mathlib.Data.Real.Basic"]

    body_parts = [part.strip() for part in [*accepted_bodies, new_body] if part.strip()]
    return "\n".join(
        [
            *all_imports,
            "",
            "set_option autoImplicit false",
            "set_option linter.unusedVariables false",
            "",
            *body_parts,
            "",
        ]
    )


def _compose_module_file(module_imports: list[str], new_code: str = "") -> tuple[str, list[str], str]:
    new_imports, new_body = _split_lean_imports_and_body(new_code)
    all_imports: list[str] = []
    seen_imports: set[str] = set()
    for item in [*module_imports, *new_imports]:
        if item not in seen_imports:
            all_imports.append(item)
            seen_imports.add(item)
    if not all_imports:
        all_imports = ["import Mathlib.Data.Real.Basic"]
    code = "\n".join(
        [
            *all_imports,
            "",
            "set_option autoImplicit false",
            "set_option linter.unusedVariables false",
            "",
            new_body.strip(),
            "",
        ]
    )
    return code, new_imports, new_body


def _prune_chunk_to_labels(
    *,
    module_imports: list[str],
    original_chunk_code: str,
    target_labels: list[str],
    keep_labels: list[str],
) -> PrunedChunk | None:
    """Build a module body that exposes only the kept blueprint declarations.

    Helpers are retained because accepted declarations may depend on them, but
    public declarations for rejected/downstream target nodes are removed. The
    caller must still compile and audit the pruned module before accepting it.
    """
    keep_set = set(keep_labels)
    target_names = {_lean_name(label): label for label in target_labels}
    decls = _lean_declarations(original_chunk_code)
    if any(_lean_name(label) not in decls for label in keep_labels):
        return None

    lines = original_chunk_code.splitlines()
    starts: list[tuple[int, re.Match[str]]] = []
    for idx, line in enumerate(lines):
        match = LEAN_DECL_START_RE.match(line)
        if match:
            starts.append((idx, match))
    if not starts:
        return None

    preamble = "\n".join(lines[: starts[0][0]]).strip()
    kept_parts: list[str] = []
    if preamble:
        kept_parts.append(preamble)
    for pos, (start_idx, match) in enumerate(starts):
        end_idx = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        decl_name = match.group(2)
        target_label = target_names.get(decl_name)
        if target_label is not None and target_label not in keep_set:
            continue
        kept_parts.append("\n".join(lines[start_idx:end_idx]).strip())

    pruned_chunk_code = "\n\n".join(part for part in kept_parts if part).strip() + "\n"
    lean_code, new_imports, new_body = _compose_module_file(module_imports, pruned_chunk_code)
    return PrunedChunk(
        labels=list(keep_labels),
        lean_code=lean_code,
        imports=new_imports,
        body=new_body,
        signatures=_decl_signatures(lean_code),
    )


def _default_lean_command() -> list[str]:
    return default_lean_command(REPO_ROOT)


def _lean_env() -> dict[str, str]:
    env = os.environ.copy()
    existing = env.get("LEAN_PATH", "")
    paths = [str(REPO_ROOT)]
    if existing:
        paths.append(existing)
    env["LEAN_PATH"] = os.pathsep.join(paths)
    return env


def _audit_lean_code(code: str) -> list[str]:
    """Reject Lean that compiles by cheating instead of implementing nodes."""
    issues: list[str] = []
    if FORBIDDEN_LEAN_PLACEHOLDERS.search(code):
        issues.append("contains a forbidden placeholder (`sorry`, `admit`, or `by ?`)")
    if "set_option autoImplicit true" in code:
        issues.append("enables `autoImplicit`; generated Lean must keep unknown names explicit")
    if "set_option autoImplicit false" not in code:
        issues.append("missing `set_option autoImplicit false`")
    bad = [f"{kind} {name}" for kind, name in FORBIDDEN_ASSUMPTIONS.findall(code)]
    if bad:
        shown = ", ".join(bad[:12])
        more = "" if len(bad) <= 12 else f", ... ({len(bad)} total)"
        issues.append(
            "uses top-level assumptions instead of implementations: "
            f"{shown}{more}"
        )
    invented = sorted(set(FORBIDDEN_BLUEPRINT_STUBS.findall(code)))
    if invented:
        shown = ", ".join(invented[:12])
        more = "" if len(invented) <= 12 else f", ... ({len(invented)} total)"
        issues.append(
            "calls invented paper/blueprint helper declarations instead of proving "
            f"the nodes: {shown}{more}"
        )
    decls = _lean_declarations(code)
    vacuous = [
        f"{decl.kind} {decl.name}"
        for decl in decls.values()
        if decl.kind in {"theorem", "lemma"} and re.search(r":\s*True\s*:=", decl.text)
    ]
    example_count = len(VACUOUS_TRUE_EXAMPLES.findall(code))
    if vacuous or example_count:
        shown_parts = vacuous[:12]
        if example_count:
            shown_parts.append(f"{example_count} example(s)")
        shown = ", ".join(shown_parts)
        total = len(vacuous) + example_count
        more = "" if total <= 12 else f", ... ({total} total)"
        issues.append(
            "proves only `True` instead of the blueprint's mathematical claims: "
            f"{shown}{more}"
        )
    return issues


def _is_lean_generation_issue(output: str) -> bool:
    low = output.lower()
    return any(pattern in low for pattern in LEAN_GENERATION_ERROR_PATTERNS)


def _statement_audit_prompt(
    name: str,
    nodes: dict[str, Node],
    blueprint_blocks: dict[str, str],
    decls: dict[str, LeanDecl],
    paper_text: str,
) -> str:
    pairs: list[str] = []
    for label, node in sorted(nodes.items(), key=lambda item: (item[1].file, item[1].line, item[0])):
        if node.mathlibok:
            continue
        lean_name = _lean_name(label)
        decl = decls.get(lean_name)
        pairs.append(
            f"## Node {label}\n"
            f"- kind: {node.kind}\n"
            f"- expected Lean declaration name: {lean_name}\n"
            f"- uses: {', '.join(sorted(node.uses)) or '(none)'}\n"
            f"\nBlueprint text:\n```tex\n{blueprint_blocks.get(label, '')[:5000]}\n```\n"
            f"\nGenerated Lean declaration:\n```lean\n{decl.text[:5000] if decl else '(missing)'}\n```\n"
        )
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text[:20000]}\n</paper>\n" if paper_text else ""
    pair_text = "\n\n".join(pairs)
    return f"""TASK: BLUEPRINT-CONTRACT-AUDIT

You are the publication gate for Auto-Blueprint.

Lean has already accepted the generated file, but that is not enough. Decide
whether each generated Lean declaration actually formalizes the corresponding
blueprint node without weakening, erasing parameters, replacing concrete
claims by abstract placeholders, or changing the mathematical content.

Also check proof-obligation coverage at the node level. The Lean declaration
does not need to follow the prose proof line by line, but it must represent the
substantive mathematical obligations the blueprint proof relies on. If the
blueprint proof uses a construction, case split, intermediate claim, reduction,
invariant, or dependency that is not represented by the node statement, a
listed `\\uses{{...}}` dependency, or the generated Lean declaration, reject it.

Return exactly one JSON object:
{{
  "accepted": true,
  "classification": "accepted",
  "issues": []
}}

If anything should block publication, return:
{{
  "accepted": false,
  "classification": "lean_translation_issue" | "blueprint_issue",
  "issues": [
    {{
      "node": "label",
      "severity": "reject",
      "reason": "specific reason"
    }}
  ]
}}

Use `lean_translation_issue` only when the blueprint is already concrete enough
and the generated Lean simply mistranslated it. Use `blueprint_issue` when a
faithful Lean implementation would require making the blueprint more concrete:
adding missing semantics, hypotheses, parameters, promised behavior,
input/output relations, or replacing abstract problem tags by real definitions.

Reject examples:
- Lean statement is just `True`, a placeholder proposition, or an uninterpreted
  problem tag when the blueprint gives concrete hypotheses/conclusions.
- Lean declaration drops parameters, hypotheses, quantifiers, approximation
  factors, complexity assumptions, or dependency requirements.
- Lean declaration proves a different or much weaker theorem.
- Lean bypasses the blueprint proof by using an abstract theorem/tag/witness
  instead of representing the construction or intermediate obligations the
  blueprint proof says establish the result.
- The blueprint proof contains substantive proof obligations that are only prose
  and should be split into explicit helper nodes before Lean can certify them.
- A required non-Mathlib node has no matching Lean declaration.

Do not reject merely because the Lean proof is ugly or uses different low-level
tactics. Judge whether the generated Lean certifies the blueprint proof
obligations, not cosmetic proof shape.

Blueprint name: {name}
{paper_block}
Pairs to audit:
{pair_text}
"""


BLUEPRINT_REPAIR_AUDIT_MARKERS = (
    "abstract",
    "behavior",
    "branch",
    "concrete",
    "drops",
    "dropped",
    "erased",
    "erases",
    "erasing",
    "missing",
    "normalization",
    "omits",
    "omitted",
    "omitting",
    "placeholder",
    "range hypothesis",
    "range hypotheses",
    "semantics",
    "semantic",
    "tag",
    "too weak",
    "too-weak",
    "underspecified",
    "vacuous",
    "weaken",
    "weakens",
    "zeroTransformer",
)


def _alignment_failure_kind(classification: str, formatted_issues: list[str]) -> str:
    """Route compiled-but-wrong Lean to either Lean retry or blueprint repair.

    The auditor's structured classification is authoritative: the audit prompt
    explicitly instructs it to answer `lean_translation_issue` only when the
    blueprint is already concrete and the generated Lean mistranslated it.
    Keyword-sweeping the rejection prose on top of that misfires on generic
    critique vocabulary ("missing", "semantics", "concrete", ...) and sends
    valid blueprints to repair — the repair agent then edits a blueprint with
    nothing wrong in it. The marker sweep is only a fallback for replies that
    carry no usable classification. A genuinely stuck translation still
    reaches blueprint repair through the bounded audit-regeneration rounds.
    """
    if classification == "blueprint_issue":
        return "blueprint"
    if classification == "lean_translation_issue":
        return "lean-generation"
    text = "\n".join(formatted_issues).lower()
    if any(marker.lower() in text for marker in BLUEPRINT_REPAIR_AUDIT_MARKERS):
        return "blueprint"
    return "lean-generation"


def _run_statement_alignment_audit(
    runner,
    name: str,
    nodes: dict[str, Node],
    lean_path: Path,
    paper_text: str,
    *,
    all_nodes: dict[str, Node] | None = None,
    telemetry: TelemetryRun | None = None,
    chunk_number: int | None = None,
) -> LeanAttempt | None:
    """Return None when the compiled Lean is aligned enough to publish."""
    code = lean_path.read_text(encoding="utf-8")
    deterministic_issues = _deterministic_statement_audit(code, nodes, all_nodes)
    if deterministic_issues:
        rejected = set(nodes)
        if telemetry:
            issues_artifact = telemetry.store_text(
                "audit_issues",
                "\n".join(deterministic_issues),
                ext="txt",
            )
            telemetry.record(
                "statement_audit",
                chunk_number=chunk_number,
                labels=list(nodes),
                source="deterministic",
                accepted=False,
                classification=_deterministic_audit_kind(deterministic_issues),
                rejected_labels=sorted(rejected),
                issues=issues_artifact.to_event(REPO_ROOT),
            )
        return LeanAttempt(
            ok=False,
            command=[],
            reason="Statement alignment audit failed deterministic checks:\n- "
            + "\n- ".join(deterministic_issues),
            kind=_deterministic_audit_kind(deterministic_issues),
            rejected_labels=rejected,
        )

    decls = _lean_declarations(code)
    prompt = _statement_audit_prompt(
        name,
        nodes,
        _node_tex_blocks(nodes),
        decls,
        paper_text,
    )
    prompt_artifact = telemetry.store_text("prompt_statement_audit", prompt) if telemetry else None
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        if telemetry:
            telemetry.record(
                "model_call",
                purpose="statement_audit",
                chunk_number=chunk_number,
                labels=list(nodes),
                status="error",
                duration_s=time.monotonic() - started,
                timeout_s=runner.timeout,
                backend=runner.backend_name,
                model=runner.model,
                readonly=runner.readonly,
                prompt=prompt_artifact.to_event(REPO_ROOT) if prompt_artifact else None,
                error=str(exc),
            )
        raise
    if telemetry:
        response_artifact = telemetry.store_text("response_statement_audit", result.text)
        telemetry.record(
            "model_call",
            purpose="statement_audit",
            chunk_number=chunk_number,
            labels=list(nodes),
            status="success",
            duration_s=result.duration_s,
            timeout_s=runner.timeout,
            backend=result.backend,
            model=result.model,
            readonly=runner.readonly,
            prompt=prompt_artifact.to_event(REPO_ROOT) if prompt_artifact else None,
            response=response_artifact.to_event(REPO_ROOT),
        )
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        if telemetry:
            telemetry.record(
                "statement_audit",
                chunk_number=chunk_number,
                labels=list(nodes),
                source="model",
                accepted=False,
                classification="invalid_json",
                rejected_labels=list(nodes),
                reason=str(exc),
            )
        return LeanAttempt(
            ok=False,
            command=[],
            reason=f"Statement alignment audit did not return valid JSON: {exc}\n\n{result.text[-4000:]}",
            kind="lean-generation",
        )

    issues = payload.get("issues") or []
    accepted = bool(payload.get("accepted")) and not any(
        str(issue.get("severity", "")).lower() == "reject" for issue in issues if isinstance(issue, dict)
    )
    if accepted:
        if telemetry:
            telemetry.record(
                "statement_audit",
                chunk_number=chunk_number,
                labels=list(nodes),
                source="model",
                accepted=True,
                classification=str(payload.get("classification") or "accepted"),
                rejected_labels=[],
            )
        return None

    formatted: list[str] = []
    rejected_labels: set[str] = set()
    for issue in issues if isinstance(issues, list) else []:
        if not isinstance(issue, dict):
            continue
        node = str(issue.get("node") or "(unknown node)")
        reason = str(issue.get("reason") or "no reason provided")
        severity = str(issue.get("severity") or "reject")
        formatted.append(f"{node} [{severity}]: {reason}")
        if severity.lower() == "reject" and node in nodes:
            rejected_labels.add(node)
    if not formatted:
        formatted.append(str(payload)[:4000])
    if not rejected_labels:
        rejected_labels = set(nodes)

    classification = str(payload.get("classification") or "lean_translation_issue")
    kind = _alignment_failure_kind(classification, formatted)
    if telemetry:
        issues_artifact = telemetry.store_text(
            "audit_issues",
            "\n".join(formatted),
            ext="txt",
        )
        telemetry.record(
            "statement_audit",
            chunk_number=chunk_number,
            labels=list(nodes),
            source="model",
            accepted=False,
            classification=classification,
            routed_kind=kind,
            rejected_labels=sorted(rejected_labels),
            issues=issues_artifact.to_event(REPO_ROOT),
        )
    return LeanAttempt(
        ok=False,
        command=[],
        reason="Statement alignment audit rejected the compiled Lean:\n- " + "\n- ".join(formatted),
        kind=kind,
        rejected_labels=rejected_labels,
    )


def _run_lean(path: Path, lean_command: list[str]) -> LeanAttempt:
    code = path.read_text(encoding="utf-8")
    audit_issues = _audit_lean_code(code)
    if audit_issues:
        return LeanAttempt(
            ok=False,
            command=lean_command + [str(path)],
            reason="Lean attempt failed the correctness audit:\n- " + "\n- ".join(audit_issues),
            kind="lean-generation",
        )

    try:
        proc = subprocess.Popen(
            lean_command + [str(path)],
            cwd=str(REPO_ROOT),
            env=_lean_env(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
    except FileNotFoundError as exc:
        raise FileNotFoundError(
            "Lake/Lean is not installed for this repo. Run:\n"
            "  uv run python scripts/setup_lean.py --install-elan"
        ) from exc

    start = time.time()
    while True:
        try:
            stdout, stderr = proc.communicate(timeout=30)
            break
        except subprocess.TimeoutExpired:
            elapsed = int(time.time() - start)
            if elapsed >= 600:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = proc.communicate()
                return LeanAttempt(
                    ok=False,
                    command=lean_command + [str(path)],
                    stdout=stdout or "",
                    stderr=stderr or "",
                    reason="Lean check timed out after 600s.",
                    kind="lean-generation",
                )
            print(f"  lean still checking... {elapsed}s elapsed", flush=True)

    combined = "\n".join(part for part in (stdout or "", stderr or "") if part)
    if proc.returncode == 0 and "declaration uses 'sorry'" in combined:
        # Lean treats `sorry` as a warning; for us it voids the verification.
        return LeanAttempt(
            ok=False,
            command=lean_command + [str(path)],
            stdout=stdout or "",
            stderr=stderr or "",
            reason="Lean accepted the file but one or more declarations use `sorry`; "
            "sorried proofs verify nothing and are rejected.",
            kind="lean-generation",
        )
    return LeanAttempt(
        ok=proc.returncode == 0,
        command=lean_command + [str(path)],
        stdout=stdout or "",
        stderr=stderr or "",
        kind="lean-generation" if proc.returncode != 0 and _is_lean_generation_issue(combined) else "blueprint",
    )


def _compile_module_olean(path: Path, lean_command: list[str]) -> LeanAttempt:
    """Compile an accepted generated module to .olean for later chunk imports."""
    olean_path = path.with_suffix(".olean")
    command = lean_command + ["-o", str(olean_path), str(path)]
    try:
        proc = subprocess.Popen(
            command,
            cwd=str(REPO_ROOT),
            env=_lean_env(),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            start_new_session=True,
        )
        stdout, stderr = proc.communicate(timeout=600)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = proc.communicate()
        return LeanAttempt(
            ok=False,
            command=command,
            stdout=stdout or "",
            stderr=stderr or "",
            reason="Lean module object compilation timed out after 600s.",
            kind="lean-generation",
        )
    return LeanAttempt(
        ok=proc.returncode == 0,
        command=command,
        stdout=stdout or "",
        stderr=stderr or "",
        kind="lean-generation" if proc.returncode != 0 else "lean",
    )


def _lean_prompt(
    name: str,
    blueprint_source: str,
    nodes: dict[str, Node],
    *,
    library_context: str = "",
    previous_lean_error: str = "",
) -> str:
    retry_block = ""
    if previous_lean_error:
        retry_block = f"""

Previous generated Lean attempt failed. This is a Lean-generation retry from the
same blueprint; do not change the mathematical content. Fix the Lean encoding,
imports, names, explicit arguments, and proofs.

Previous Lean/audit output:
```text
{previous_lean_error[-12000:]}
```
"""
    return f"""TASK: BLUEPRINT-TO-LEAN-CHECK-ATTEMPT

Return exactly one Lean 4 file. Do not return markdown commentary.

Hard constraints:
- The blueprint below is the only mathematical source of truth.
- The goal is correct Lean, not a file that compiles by assuming the paper.
- Do not strengthen, weaken, skip, or silently reinterpret blueprint statements.
- Do not use facts that are not Mathlib imports, explicit \\lean{{...}} settled
  declarations in the blueprint, or earlier blueprint nodes listed in \\uses{{...}}.
- Do not use `sorry`, `admit`, `by ?`, or comments that stand in for proof.
- Do not emit declarations like `theorem name : True := by trivial`; that is a
  failed formalization, not a proof of the blueprint.
- Do not call invented helpers such as `foo_from_blueprint`,
  `foo_from_paper`, `Karthik_Manurangsi_2020_reduction`, or similar names that
  merely assert a paper result. Every name you use must be imported from a real
  local library, defined earlier in this file, or listed as an existing
  `\\lean{...}` declaration in the blueprint.
- Include `set_option autoImplicit false` near the top of the file.
- Do not use `axiom`, `constant`, or `opaque`; implement definitions and prove theorem nodes.
- Give each generated declaration the Lean name listed in the node summary.
- If the blueprint is missing a lemma/hypothesis/dependency, let Lean fail.
  Do not patch around missing blueprint content.
- Do not compile or run `lake`/`lean` yourself; you have read-only access. A
  separate checker compiles your reply, and its errors come back to you on the
  next trial. Write the complete file in one pass and return it.

Imports:
- Import only the specific Mathlib modules your file needs, e.g.
  `import Mathlib.Analysis.InnerProductSpace.Basic`.
- Local library candidates below came from deterministic local search; trust
  their module paths and snippets instead of reopening Mathlib to verify them.
- Do not use the blanket `import Mathlib` or `import AutoBlueprint`; they load
  every Mathlib module and make each compile check several times slower.
- Prefer the local library candidates below when they are relevant, but do not
  force them if they do not match the blueprint statement.
{retry_block}

Blueprint name: {name}

Node summary:
{_node_summary(nodes)}

Local Lean library candidates:
{library_context or "- No local library candidates were found."}

Lean API idioms:
{LEAN_IDIOM_CHEATSHEET}

Current blueprint source:
```tex
{blueprint_source}
```
"""


def _chunk_lean_prompt(
    name: str,
    blueprint_source: str,
    nodes: dict[str, Node],
    target_labels: list[str],
    accepted_labels: set[str],
    accepted_signatures: str,
    accepted_imports: list[str],
    *,
    library_context: str = "",
    previous_lean_error: str = "",
    previous_chunk_code: str = "",
    audit_history: str = "",
    unavailable_imports: list[str] | None = None,
    model_timeout_s: int | None = None,
) -> str:
    retry_block = ""
    if previous_lean_error:
        previous_code_block = ""
        if previous_chunk_code:
            code = previous_chunk_code
            if len(code) > 45000:
                code = code[:45000] + "\n-- ... (truncated)"
            previous_code_block = f"""
Your previous attempt is below. START FROM IT: keep every declaration that is
not implicated in the errors exactly as written, and change only what is needed
to fix the reported errors. Do not re-derive or restyle unaffected code. Return
the full corrected file.

```lean
{code}
```
"""
        retry_block = f"""

Previous generated Lean attempt for this same chunk failed. Do not change the
mathematical content. Fix only the Lean encoding, imports, explicit arguments,
and proofs for this chunk.

Previous Lean/audit output:
```text
{previous_lean_error[-12000:]}
```
{previous_code_block}"""
    audit_history_block = ""
    if audit_history:
        audit_history_block = f"""

Earlier statement-alignment audit rejections for nodes in this chunk (possibly
from previous attempts or previous chunk numbers). The auditor WILL reject the
same patterns again. Your new Lean must address these complaints directly. In
particular, never satisfy a correctness field with a tautology (`rfl` against a
definition you introduced for that purpose), an identity implication
(`P -> P`), or by assuming the conclusion as an input field of an
oracle-answer/witness structure.

```text
{audit_history[-8000:]}
```
"""
    unavailable_block = ""
    if unavailable_imports:
        unavailable_block = (
            "\nUnavailable imports (no compiled .olean in this local build; NEVER import"
            "\nthese, and avoid tactics/lemmas that require them):\n"
            + "\n".join(f"- {item}" for item in sorted(unavailable_imports))
            + "\n"
        )
    target_set = set(target_labels)
    dependency_labels = [
        label
        for label in _node_order(nodes)
        if label in (_dependency_closure(nodes, target_labels) - target_set)
    ]
    target_blocks = _node_tex_blocks({label: nodes[label] for label in target_labels})
    dependency_blocks = _node_tex_blocks({label: nodes[label] for label in dependency_labels})
    target_text = "\n\n".join(
        f"## {label}\n```tex\n{target_blocks.get(label, '')[:5000]}\n```"
        for label in target_labels
    )
    dependency_text = "\n\n".join(
        f"## {label}\n```tex\n{dependency_blocks.get(label, '')[:2500]}\n```"
        for label in dependency_labels
        if label not in accepted_labels and not nodes[label].mathlibok
    )
    if not dependency_text:
        dependency_text = "- All transitive dependencies are already accepted, Mathlib-backed, or in the target chunk."
    accepted_list = ", ".join(sorted(accepted_labels)) or "(none yet)"
    return f"""TASK: BLUEPRINT-CHUNK-TO-LEAN-CHECK-ATTEMPT

Return exactly one Lean 4 code block/file. Do not return markdown commentary.

You see the whole node graph for global context, but your proof obligation is
only the current dependency-closed chunk. The TeX source blocks below are the
local contract for this generation call.

Hard constraints:
- The blueprint below is the only mathematical source of truth.
- Formalize each node's statement EXACTLY as written: same objects, same
  recursive structure, same fields and claims. Lean exists to verify the
  blueprint, not to prove something adjacent — do not substitute an
  equivalent-but-differently-shaped formulation, and do not weaken.
- If a target node CANNOT be faithfully formalized as stated (it would need
  helper statements the blueprint does not yet have), do NOT emit weakened
  Lean for it. Instead return, as your entire reply, one line:
  NEEDS-DECOMPOSITION: {{"label": "<node label>", "missing_helpers": ["<precise statement of each needed helper>"], "reason": "<why the node is not formalizable as one declaration>"}}
- Generate Lean declarations for every target node in the current chunk.
- Do not redefine accepted declarations from earlier chunks.
- If a target node has `\\uses{{label}}`, the generated public declaration for
  that target node must visibly use the generated Lean declaration for `label`
  (for example `lem_inner_scaled`), either directly or through a same-module
  helper/result structure. Do not duplicate a dependency inline or silently
  ignore it.
- If one blueprint node explicitly introduces several named definitions,
  predicates, fields, or regimes, define those names separately. Do not hide
  them inside one bundled theorem/tuple/structure unless the blueprint itself
  says that bundle is the mathematical object.
- You may introduce helper declarations only when they are concrete Lean
  definitions/lemmas needed for target nodes, and they must not be fake paper
  assumptions.
- Do not call invented helpers such as `foo_from_blueprint`,
  `foo_from_paper`, `Karthik_Manurangsi_2020_reduction`, or similar names that
  merely assert a paper result.
- Do not use `sorry`, `admit`, `by ?`, `axiom`, `constant`, or `opaque`.
- Do not emit declarations like `theorem name : True := by trivial`.
- Include only imports you actually need. Do not use blanket `import Mathlib`
  or `import AutoBlueprint`.
- Keep `set_option autoImplicit false`.
- If this chunk depends on accepted nodes, use the imported accepted
  declarations exactly as written. Do not redefine them.
- If the blueprint is missing a lemma/hypothesis/dependency, let the checker
  fail rather than patching around missing content.
- This model call has a wall-clock budget of about {model_timeout_s or "unknown"}
  seconds. Keep the implementation scoped to the requested declarations; if the
  node is too large to formalize faithfully within this call, use the
  `NEEDS-DECOMPOSITION` response instead of emitting weakened Lean.

The script will compile:

    imports of accepted chunk modules + your new chunk code

So your output should contain imports plus new declarations for this chunk. It
must not repeat accepted declarations.
{unavailable_block}{retry_block}{audit_history_block}

Blueprint name: {name}

Accepted blueprint nodes:
{accepted_list}

Accepted Lean module imports:
```lean
{chr(10).join(accepted_imports) if accepted_imports else "-- none yet"}
```

Current target chunk:
{_chunk_summary(nodes, target_labels)}

Dependency checklist (deterministically enforced — the declaration for each
node MUST textually mention every listed Lean name, directly or via a
same-module helper it uses; a missing mention is an automatic rejection):
{_dependency_checklist(nodes, target_labels)}

Whole blueprint node graph:
{_node_summary(nodes)}

Accepted Lean signatures:
```lean
{accepted_signatures[-12000:] if accepted_signatures else "-- none yet"}
```

Local Lean library candidates:
{library_context or "- No local library candidates were found."}

Lean API idioms:
{LEAN_IDIOM_CHEATSHEET}

Target blueprint source:
{target_text}

Relevant dependency source:
{dependency_text}
"""


def _agent_refine_prompt(
    name: str,
    blueprint_source: str,
    lean_output: str,
    trial: int,
    paper_text: str,
    *,
    escalation_note: str = "",
    model_timeout_s: int | None = None,
) -> str:
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    escalation_block = f"\nIMPORTANT: {escalation_note}\n" if escalation_note else ""
    budget_block = (
        f"\nThis repair call has a wall-clock budget of about {model_timeout_s} seconds.\n"
        if model_timeout_s
        else ""
    )
    return f"""TASK: REFINE-BLUEPRINT-FROM-LEAN-FAILURE

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.

You are the blueprint author. Fix the blueprint, not the Lean implementation.
{escalation_block}
{budget_block}

Rules:
- Edit only `blueprints/{name}/blueprint/src/` and `blueprints/{name}/meta.yml`
  if metadata is genuinely wrong.
- Do not edit `.auto-blueprint/` Lean attempt files.
- Do not make the theorem weaker just to satisfy Lean.
- If Lean failed because the blueprint skipped an argument, add the missing
  lemma/proposition/definition as a blueprint node.
- If the statement audit says the generated Lean used abstract tags, erased
  semantics, dropped parameters, or proved only a vacuous/too-weak behavior,
  strengthen the blueprint itself with concrete mathematical content.
- Definitions for new problem nodes must specify real input/output relations,
  promises, thresholds, approximation factors, and yes/no conditions. They
  cannot merely introduce a family tag.
- Construction lemmas must state the actual constructed object and behavior
  equalities/inequalities, not just existence, continuity, or a placeholder
  predicate.
- If a proof needs an unstated dependency, add or correct `\\uses{{...}}`.
- If a statement is mathematically wrong compared with the paper, correct the
  statement in the blueprint.
- After editing, run `python scripts/validate_blueprint.py {name}`.

{paper_block}
Current blueprint source:
```tex
{blueprint_source}
```

Lean critic output:
```text
{lean_output[-12000:]}
```
"""


def _pre_decomposition_prompt(
    name: str,
    blueprint_source: str,
    nodes: dict[str, Node],
    candidates: list[tuple[str, list[str]]],
    paper_text: str,
    *,
    model_timeout_s: int | None = None,
) -> str:
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    budget_block = (
        f"\nThis prepass has a wall-clock budget of about {model_timeout_s} seconds.\n"
        if model_timeout_s
        else ""
    )
    blocks = _node_tex_blocks(nodes)
    candidate_lines = []
    for label, reasons in candidates:
        node = nodes[label]
        candidate_lines.append(
            f"## {label}\n"
            f"- kind: {node.kind}\n"
            f"- uses: {', '.join(sorted(node.uses)) or '(none)'}\n"
            f"- heuristic reasons: {', '.join(reasons)}\n"
            "```tex\n"
            f"{blocks.get(label, '')[:5000]}\n"
            "```"
        )
    return f"""TASK: PRE-REFINEMENT-BLUEPRINT-DECOMPOSITION

Before Lean generation starts, inspect the listed blueprint nodes and decide
whether any are too coarse for faithful one-to-one Lean formalization.
{budget_block}

You are still editing the blueprint, not Lean. If a candidate proof bundles
several formal steps into one large statement, split it into smaller
definition/lemma nodes and rewire `\\uses{{...}}` so the original claim depends
on the helpers. Keep the mathematical content identical. Do not weaken claims.
Do not add Lean code.

Edit only `blueprints/{name}/blueprint/src/` and `blueprints/{name}/meta.yml`
if metadata is genuinely wrong. After editing, run
`python scripts/validate_blueprint.py {name}`.

If no decomposition is needed, leave the files unchanged.

Candidate nodes selected by deterministic prepass:
{chr(10).join(candidate_lines)}

{paper_block}
Current blueprint source:
```tex
{blueprint_source}
```
"""


def _api_pre_decomposition_prompt(
    name: str,
    blueprint_source: str,
    nodes: dict[str, Node],
    candidates: list[tuple[str, list[str]]],
    paper_text: str,
    *,
    model_timeout_s: int | None = None,
) -> str:
    base = _pre_decomposition_prompt(
        name,
        blueprint_source,
        nodes,
        candidates,
        paper_text,
        model_timeout_s=model_timeout_s,
    )
    return f"""{base}

API MODE: Return exactly one JSON object:
{{
  "content_tex": "full replacement for blueprints/{name}/blueprint/src/content.tex, or the unchanged source if no decomposition is needed",
  "notes": "short explanation of decompositions made or why none were needed"
}}

Do not include `\\begin{{document}}` or `\\end{{document}}`.
"""


def _api_refine_prompt(
    name: str,
    blueprint_source: str,
    lean_output: str,
    trial: int,
    paper_text: str,
    *,
    escalation_note: str = "",
    model_timeout_s: int | None = None,
) -> str:
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    escalation_block = f"\nIMPORTANT: {escalation_note}\n" if escalation_note else ""
    budget_block = (
        f"\nThis repair call has a wall-clock budget of about {model_timeout_s} seconds.\n"
        if model_timeout_s
        else ""
    )
    return f"""TASK: REFINE-BLUEPRINT-CONTENT-TEX

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.
{escalation_block}
{budget_block}

Return exactly one JSON object:
{{
  "content_tex": "full replacement for blueprints/{name}/blueprint/src/content.tex",
  "notes": "short explanation of what changed"
}}

Rules:
- Fix the blueprint, not the Lean code.
- Do not make the theorem weaker just to satisfy Lean.
- Add missing intermediate blueprint nodes when the proof needs them.
- If the statement audit says the generated Lean used abstract tags, erased
  semantics, dropped parameters, or proved only a vacuous/too-weak behavior,
  strengthen the blueprint itself with concrete mathematical content.
- Definitions for new problem nodes must specify real input/output relations,
  promises, thresholds, approximation factors, and yes/no conditions. They
  cannot merely introduce a family tag.
- Construction lemmas must state the actual constructed object and behavior
  equalities/inequalities, not just existence, continuity, or a placeholder
  predicate.
- Correct `\\uses{{...}}` whenever dependencies were missing or wrong.
- Do not include `\\begin{{document}}` or `\\end{{document}}`.

{paper_block}
Current blueprint source:
```tex
{blueprint_source}
```

Lean critic output:
```text
{lean_output[-12000:]}
```
"""


def _write_api_refinement(name: str, text: str) -> None:
    payload = _extract_json(text)
    content_tex = str(payload.get("content_tex") or "").strip()
    if not content_tex:
        raise ValueError("refinement JSON did not include non-empty content_tex")
    if r"\begin{document}" in content_tex or r"\end{document}" in content_tex:
        raise ValueError("content_tex must not include a document environment")
    path = REPO_ROOT / "blueprints" / name / "blueprint" / "src" / "content.tex"
    path.write_text(content_tex.rstrip() + "\n", encoding="utf-8")
    notes = str(payload.get("notes") or "").strip()
    if notes:
        print(f"  refinement notes: {notes}")


def _run_pre_decomposition_pass(
    *,
    name: str,
    runner,
    telemetry: TelemetryRun,
    paper_text: str,
    accepted_labels: set[str],
    candidate_limit: int,
    timeout_s: int,
) -> tuple[bool, int]:
    """Optionally decompose suspicious blueprint nodes before Lean generation.

    Returns ``(changed, changed_count)``. All changes go through ``content.tex``
    and normal blueprint validation; Lean still proves the post-prepass
    blueprint, never a private side plan.
    """
    validation = validate_blueprint(REPO_ROOT, name)
    print_result(validation)
    if not validation.ok:
        raise ValueError("pre-decomposition validation failed before model call")

    blueprint_source = _read_blueprint_source(name)
    current_fingerprints = _node_fingerprints(validation.nodes)
    candidates = _pre_decomposition_candidates(
        validation.nodes,
        accepted_labels=accepted_labels,
        limit=candidate_limit,
    )
    decision_id = f"{telemetry.run_id}:pre-decomposition"
    blocks = _node_tex_blocks(validation.nodes)
    for label, reasons in candidates:
        telemetry.record(
            "pre_decomposition_candidate",
            decision_id=decision_id,
            reasons=reasons,
            **node_structural_features(
                label,
                validation.nodes[label].kind,
                blocks.get(label, ""),
                len(validation.nodes[label].uses),
            ),
        )
    telemetry.record(
        "decision_point",
        decision_id=decision_id,
        kind="pre_refinement_decomposition",
        target_labels=[label for label, _reasons in candidates],
        accepted_before=len(accepted_labels),
        remaining_before=len(validation.nodes) - len(accepted_labels),
        candidate_limit=candidate_limit,
        model_timeout_s=timeout_s,
        available_actions=["skip_pre_decomposition", "decompose_blueprint"],
        chosen_action="decompose_blueprint" if candidates else "skip_pre_decomposition",
    )
    if not candidates:
        telemetry.record(
            "decision_outcome",
            decision_id=decision_id,
            outcome="pre_decomposition_skipped_no_candidates",
        )
        return False, 0

    print(
        "==> Pre-refinement decomposition pass: "
        + ", ".join(label for label, _reasons in candidates),
        flush=True,
    )
    if runner.backend_name in {"codex", "claude"}:
        prompt = _pre_decomposition_prompt(
            name,
            blueprint_source,
            validation.nodes,
            candidates,
            paper_text,
            model_timeout_s=timeout_s,
        )
        prompt_artifact = telemetry.store_text("prompt_pre_decomposition", prompt)
        started = time.monotonic()
        try:
            with _runner_timeout(runner, timeout_s):
                result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
        except RunnerError as exc:
            telemetry.record(
                "model_call",
                purpose="pre_decomposition",
                decision_id=decision_id,
                labels=[label for label, _reasons in candidates],
                status="error",
                duration_s=time.monotonic() - started,
                timeout_s=timeout_s,
                backend=runner.backend_name,
                model=runner.model,
                readonly=runner.readonly,
                prompt=prompt_artifact.to_event(REPO_ROOT),
                error=str(exc),
                environment_error=is_environment_error(exc),
            )
            raise
        response_artifact = telemetry.store_text("response_pre_decomposition", result.text)
        telemetry.record(
            "model_call",
            purpose="pre_decomposition",
            decision_id=decision_id,
            labels=[label for label, _reasons in candidates],
            status="success",
            duration_s=result.duration_s,
            timeout_s=timeout_s,
            backend=result.backend,
            model=result.model,
            readonly=runner.readonly,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            response=response_artifact.to_event(REPO_ROOT),
        )
    else:
        prompt = _api_pre_decomposition_prompt(
            name,
            blueprint_source,
            validation.nodes,
            candidates,
            paper_text,
            model_timeout_s=timeout_s,
        )
        prompt_artifact = telemetry.store_text("prompt_pre_decomposition", prompt)
        started = time.monotonic()
        try:
            with _runner_timeout(runner, timeout_s):
                result = runner.run(prompt, cwd=REPO_ROOT, retries=1)
        except RunnerError as exc:
            telemetry.record(
                "model_call",
                purpose="pre_decomposition",
                decision_id=decision_id,
                labels=[label for label, _reasons in candidates],
                status="error",
                duration_s=time.monotonic() - started,
                timeout_s=timeout_s,
                backend=runner.backend_name,
                model=runner.model,
                readonly=runner.readonly,
                prompt=prompt_artifact.to_event(REPO_ROOT),
                error=str(exc),
                environment_error=is_environment_error(exc),
            )
            raise
        response_artifact = telemetry.store_text("response_pre_decomposition", result.text)
        telemetry.record(
            "model_call",
            purpose="pre_decomposition",
            decision_id=decision_id,
            labels=[label for label, _reasons in candidates],
            status="success",
            duration_s=result.duration_s,
            timeout_s=timeout_s,
            backend=result.backend,
            model=result.model,
            readonly=runner.readonly,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            response=response_artifact.to_event(REPO_ROOT),
        )
        _write_api_refinement(name, result.text)

    repaired_validation = validate_blueprint(REPO_ROOT, name)
    if not repaired_validation.ok:
        print_result(repaired_validation)
        raise ValueError("pre-decomposition produced invalid blueprint")
    repaired_fingerprints = _node_fingerprints(repaired_validation.nodes)
    changed = {
        label
        for label, before in current_fingerprints.items()
        if repaired_fingerprints.get(label) != before
    }
    changed |= {label for label in repaired_fingerprints if label not in current_fingerprints}
    changed_labels = sorted(changed)
    telemetry.record(
        "pre_decomposition_result",
        decision_id=decision_id,
        labels=[label for label, _reasons in candidates],
        changed_labels=changed_labels,
        changed_count=len(changed_labels),
        node_count_before=len(validation.nodes),
        node_count_after=len(repaired_validation.nodes),
        validation_ok=True,
    )
    telemetry.record(
        "decision_outcome",
        decision_id=decision_id,
        outcome="pre_decomposition_changed" if changed_labels else "pre_decomposition_noop",
        labels=[label for label, _reasons in candidates],
        changed_labels=changed_labels,
    )
    if changed_labels:
        print(
            f"  pre-decomposition changed {len(changed_labels)} node(s); "
            f"blueprint now has {len(repaired_validation.nodes)} node(s)",
            flush=True,
        )
    else:
        print("  pre-decomposition made no blueprint changes", flush=True)
    return bool(changed_labels), len(changed_labels)


def _write_report(name: str, lines: list[str]) -> Path:
    out_dir = SCRATCH_DIR / name
    out_dir.mkdir(parents=True, exist_ok=True)
    report = out_dir / "report.md"
    report.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return report


def _publish_passing_lean(name: str, lean_path: Path) -> Path:
    """Save the passing Lean attempt as a tracked blueprint artifact."""
    dest_dir = REPO_ROOT / "blueprints" / name / "blueprint" / "lean"
    dest_dir.mkdir(parents=True, exist_ok=True)
    dest = dest_dir / PUBLISHED_LEAN_NAME
    dest.write_text(lean_path.read_text(encoding="utf-8").rstrip() + "\n", encoding="utf-8")
    return dest


def _publish_lean_text(name: str, code: str) -> Path:
    """Save the assembled passing Lean entrypoint as a tracked blueprint artifact."""
    dest_dir = REPO_ROOT / "blueprints" / name / "blueprint" / "lean"
    dest_dir.mkdir(parents=True, exist_ok=True)
    dest = dest_dir / PUBLISHED_LEAN_NAME
    dest.write_text(code.rstrip() + "\n", encoding="utf-8")
    return dest


def _rebuild_site_for(name: str) -> Path:
    """Rebuild one blueprint so the published site links the Lean viewer."""
    cmd = [sys.executable, "scripts/build.py", name]
    print(f"==> Rebuilding site for {name}", flush=True)
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), text=True)
    if proc.returncode != 0:
        raise subprocess.CalledProcessError(proc.returncode, cmd)
    return REPO_ROOT / "site" / name / "lean" / "index.html"


def _load_existing_accepted_chunks(
    *,
    name: str,
    validation_nodes: dict[str, Node],
    lean_command: list[str],
    audit_runner,
    paper_text: str,
    telemetry: TelemetryRun | None = None,
) -> tuple[list[AcceptedChunk], int]:
    """Resume from generated chunk modules that still pass Lean and audit.

    Continuing is intentionally not a blind trust operation: each existing
    module is checked against the current blueprint before it is accepted as
    context. The first stale/failing module and every later generated module are
    removed, because later modules may import or rely on the failing one.
    """
    generated_dir = _generated_module_dir(name)
    chunk_paths = sorted(generated_dir.glob("Chunk*.lean"))
    accepted: list[AcceptedChunk] = []
    next_number = 1
    if not chunk_paths:
        return accepted, next_number

    print("==> Continuing from existing generated Lean chunks", flush=True)
    manifest = _read_chunk_manifest(name)
    current_fingerprints_all = _node_fingerprints(validation_nodes)
    for index, path in enumerate(chunk_paths):
        match = re.fullmatch(r"Chunk(\d+)\.lean", path.name)
        if not match:
            continue
        chunk_number = int(match.group(1))
        module_name, _module_path = _chunk_module(name, chunk_number)

        # Files absent from a non-empty manifest are leftovers of failed
        # attempts (a failed chunk's file survives renumbering). They were
        # never accepted, no later chunk imports them, and re-checking them
        # would fail and — worse — discard every accepted chunk after them.
        # Delete just the leftover and keep walking.
        if manifest and path.name not in manifest:
            print(
                f"  {path.relative_to(REPO_ROOT)} is not in the accepted-chunk "
                "manifest (leftover failed attempt); deleting it only",
                flush=True,
            )
            for artifact in (path, path.with_suffix(".olean")):
                try:
                    artifact.unlink()
                except FileNotFoundError:
                    pass
            continue

        code = path.read_text(encoding="utf-8")

        # Fast path: the manifest proves this exact code already passed Lean and
        # the alignment audit against blueprint nodes whose TeX is unchanged, so
        # re-running either would recompute a known verdict. Accept directly.
        entry = manifest.get(path.name)
        if (
            entry is not None
            and entry.get("labels")
            and path.with_suffix(".olean").is_file()
            and entry.get("sha256") == _file_sha256(path)
            and all(
                label in validation_nodes
                and current_fingerprints_all.get(label) == fingerprint
                for label, fingerprint in (entry.get("fingerprints") or {}).items()
            )
            and set(entry.get("fingerprints") or {}) == set(entry["labels"])
        ):
            imports, body = _split_lean_imports_and_body(code)
            imports = [item for item in imports if not item.startswith("import AutoBlueprint.Generated.")]
            accepted.append(
                AcceptedChunk(
                    labels=list(entry["labels"]),
                    imports=imports,
                    body=body,
                    fingerprints=dict(entry["fingerprints"]),
                    module=module_name,
                    path=path,
                    signatures=_decl_signatures(code),
                )
            )
            next_number = chunk_number + 1
            print(
                f"  {path.relative_to(REPO_ROOT)} unchanged since acceptance (manifest); "
                "skipping re-check",
                flush=True,
            )
            continue

        decls = _lean_declarations(code)
        labels = [
            label
            for label in _node_order(validation_nodes)
            if not validation_nodes[label].mathlibok and _lean_name(label) in decls
        ]
        if not labels:
            print(f"  {path.relative_to(REPO_ROOT)} has no current blueprint declarations; discarding", flush=True)
            failed_index = index
            next_number = chunk_number
            break

        print(
            f"  checking {path.relative_to(REPO_ROOT)} "
            f"({', '.join(labels)})",
            flush=True,
        )
        lean_attempt = _run_lean(path, lean_command)
        audit_failure = None
        if lean_attempt.ok:
            audit_failure = _run_statement_alignment_audit(
                audit_runner,
                name,
                {label: validation_nodes[label] for label in labels},
                path,
                paper_text,
                all_nodes=validation_nodes,
                telemetry=telemetry,
                chunk_number=chunk_number,
            )
        object_attempt = _compile_module_olean(path, lean_command) if lean_attempt.ok and audit_failure is None else None
        if not lean_attempt.ok or audit_failure is not None or object_attempt is None or not object_attempt.ok:
            print(f"  {path.relative_to(REPO_ROOT)} is stale or no longer passes; discarding from here", flush=True)
            failed_index = index
            next_number = chunk_number
            break

        imports, body = _split_lean_imports_and_body(code)
        imports = [item for item in imports if not item.startswith("import AutoBlueprint.Generated.")]
        current_fingerprints = _node_fingerprints(validation_nodes)
        accepted.append(
            AcceptedChunk(
                labels=labels,
                imports=imports,
                body=body,
                fingerprints={label: current_fingerprints[label] for label in labels},
                module=module_name,
                path=path,
                signatures=_decl_signatures(code),
            )
        )
        next_number = chunk_number + 1
    else:
        failed_index = len(chunk_paths)

    for stale in chunk_paths[failed_index:]:
        for artifact in (stale, stale.with_suffix(".olean")):
            try:
                artifact.unlink()
            except FileNotFoundError:
                pass
    _write_chunk_manifest(name, accepted)
    if accepted:
        accepted_labels, _imports, _signatures = _accepted_state(accepted)
        partial = _standalone_accepted_code(accepted)
        partial_path = SCRATCH_DIR / name / "partial_formalization.lean"
        partial_path.write_text(partial.rstrip() + "\n", encoding="utf-8")
        print(f"  resumed with {len(accepted_labels)} accepted blueprint node(s)", flush=True)
    return accepted, next_number


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name", help="Existing blueprint name under blueprints/<name>/")
    parser.add_argument("--runner", default="codex", help="Runner spec, e.g. codex, openai:gpt-5")
    parser.add_argument("--max-trials", type=int, default=3, help="Stop after this many blueprint-repair trials")
    parser.add_argument(
        "--chunk-size",
        type=int,
        default=AUTO_CHUNK_SIZE,
        help=(
            "Advanced override for the maximum number of dependency-ready nodes "
            "per chunk. Default 0 means automatic graph traversal."
        ),
    )
    parser.add_argument("--paper", help="Optional original paper path/URL/text for refinement context")
    parser.add_argument("--lean-command", help="Override checker command, e.g. 'lake env lean'")
    parser.add_argument(
        "--continue",
        dest="continue_run",
        action="store_true",
        help=(
            "Reuse existing generated ChunkNN.lean modules that still pass Lean "
            "and statement alignment for the current blueprint, then continue "
            "from the next unresolved dependency chunk."
        ),
    )
    parser.add_argument(
        "--reasoning-effort",
        choices=("low", "medium", "high", "xhigh"),
        help="Codex reasoning effort for --runner codex/codex:<model>.",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=DEFAULT_MODEL_TIMEOUT,
        help=(
            "Base timeout in seconds for each non-deterministic model call "
            f"(default: {DEFAULT_MODEL_TIMEOUT}). Deterministic Lean checks use "
            "their own fixed timeouts."
        ),
    )
    parser.add_argument(
        "--hard-timeout",
        type=int,
        default=DEFAULT_HARD_MODEL_TIMEOUT,
        help=(
            "Timeout in seconds for model calls tied to a scheduler-hard "
            f"target chunk (default: {DEFAULT_HARD_MODEL_TIMEOUT}). Must be "
            "at least --timeout."
        ),
    )
    parser.add_argument(
        "--no-pre-decompose",
        dest="pre_decompose",
        action="store_false",
        help=(
            "Skip the pre-refinement blueprint decomposition pass. By default, "
            "the run asks the model to split a small set of structurally "
            "suspicious nodes before Lean generation starts."
        ),
    )
    parser.add_argument(
        "--pre-decompose-limit",
        type=int,
        default=6,
        help=(
            "Maximum number of suspicious unresolved blueprint nodes to show "
            "to the pre-refinement decomposition pass (default: 6)."
        ),
    )
    args = parser.parse_args(argv)

    if args.max_trials < 1:
        raise SystemExit("--max-trials must be at least 1")
    if args.chunk_size < 0:
        raise SystemExit("--chunk-size must be 0 for auto or a positive integer")
    if args.timeout < 1:
        raise SystemExit("--timeout must be a positive number of seconds")
    if args.hard_timeout < args.timeout:
        raise SystemExit("--hard-timeout must be at least --timeout")
    if args.pre_decompose_limit < 0:
        raise SystemExit("--pre-decompose-limit must be non-negative")
    chunk_size = args.chunk_size or DEFAULT_AUTO_CHUNK_LIMIT

    telemetry = TelemetryRun(
        REPO_ROOT,
        blueprint=args.name,
        command=[sys.argv[0], *(argv or sys.argv[1:])],
    )
    telemetry.record(
        "refine_config",
        runner=args.runner,
        max_trials=args.max_trials,
        chunk_size=chunk_size,
        timeout_s=args.timeout,
        hard_timeout_s=args.hard_timeout,
        continue_run=args.continue_run,
        reasoning_effort=args.reasoning_effort or "",
        pre_decompose=args.pre_decompose,
        pre_decompose_limit=args.pre_decompose_limit,
    )

    def finish(code: int, status: str, **fields) -> int:
        telemetry.record("run_end", exit_code=code, status=status, **fields)
        telemetry.flush_upload_queue()
        return code

    runner_kwargs = {}
    if args.reasoning_effort:
        if not args.runner.startswith("codex"):
            raise SystemExit("--reasoning-effort is currently supported only for --runner codex")
        runner_kwargs["reasoning_effort"] = args.reasoning_effort

    paper_text = ""
    if args.paper:
        print(f"==> Reading paper context from {args.paper}", flush=True)
        paper_text, _source = read_paper(args.paper)

    lean_command = shlex.split(args.lean_command) if args.lean_command else _default_lean_command()
    print("==> Checking Lean/Lake/Mathlib setup", flush=True)
    preflight = check_lean_environment(REPO_ROOT, lean_command=lean_command)
    if not preflight.ok:
        raise FileNotFoundError(
            f"{preflight.message}\n"
            f"Command: {' '.join(preflight.command)}\n"
            f"{(preflight.stderr or preflight.stdout).strip()}"
        )
    print(f"  {preflight.message} ({preflight.elapsed_s:.1f}s)", flush=True)
    runner = get_runner(
        args.runner,
        context_files=[SKILL_PATH],
        timeout=args.timeout,
        **runner_kwargs,
    )

    # Lean generation is read-only: the model writes one Lean file as its reply
    # and this script runs the single compile check. Without shell access the
    # agent cannot burn its session repeatedly self-checking against a full
    # Mathlib import. The repair step keeps the unrestricted runner.
    gen_runner = get_runner(
        args.runner,
        context_files=[SKILL_PATH],
        timeout=args.timeout,
        readonly=True,
        **runner_kwargs,
    )

    report_lines = [
        f"# Lean-Guided Blueprint Refinement: `{args.name}`",
        "",
        f"- runner: `{args.runner}`",
        f"- max trials: `{args.max_trials}`",
        f"- chunking: `automatic dependency traversal`",
        f"- internal chunk limit: `{chunk_size}`",
        f"- model-call timeout: `{args.timeout}s`",
        f"- hard-node model-call timeout: `{args.hard_timeout}s`",
        f"- internal Lean-generation retries: `{LEAN_GENERATION_RETRIES}`",
        f"- continue from generated chunks: `{args.continue_run}`",
        f"- pre-refinement decomposition: `{args.pre_decompose}`",
        f"- pre-refinement decomposition limit: `{args.pre_decompose_limit}`",
        f"- Lean command: `{' '.join(lean_command)}`",
    ]
    if CURRENT_LOG_PATH is not None:
        report_lines.append(f"- full log: `{CURRENT_LOG_PATH.relative_to(REPO_ROOT)}`")
    report_lines.append("")

    repair_trials = 0
    if args.pre_decompose and args.pre_decompose_limit:
        changed = False
        changed_count = 0
        prepass_validation = validate_blueprint(REPO_ROOT, args.name)
        prepass_accepted = (
            _manifest_current_accepted_labels(args.name, prepass_validation.nodes)
            if args.continue_run and prepass_validation.ok
            else set()
        )
        try:
            changed, changed_count = _run_pre_decomposition_pass(
                name=args.name,
                runner=runner,
                telemetry=telemetry,
                paper_text=paper_text,
                accepted_labels=prepass_accepted,
                candidate_limit=args.pre_decompose_limit,
                timeout_s=args.hard_timeout,
            )
        except RunnerError as exc:
            if is_environment_error(exc):
                report_lines.append("## Pre-refinement decomposition model call failed")
                report_lines.append("")
                report_lines.append("```text")
                report_lines.append(str(exc)[-4000:])
                report_lines.append("```")
                report = _write_report(args.name, report_lines)
                print(f"Pre-refinement decomposition model call failed: {exc}", flush=True)
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                return finish(1, "environment_error", error=str(exc))
            print(
                f"Pre-refinement decomposition skipped after model-call failure: {exc}",
                flush=True,
            )
            report_lines.append(
                "- pre-refinement decomposition skipped after model-call failure; "
                "continuing with the normal refinement loop"
            )
        except ValueError as exc:
            report_lines.append("## Pre-refinement decomposition failed")
            report_lines.append("")
            report_lines.append("```text")
            report_lines.append(str(exc))
            report_lines.append("```")
            report = _write_report(args.name, report_lines)
            print(f"Pre-refinement decomposition failed: {exc}", flush=True)
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return finish(1, "pre_decomposition_failed", error=str(exc))
        if changed:
            repair_trials += 1
            report_lines.append(
                f"- pre-refinement decomposition changed `{changed_count}` node(s); "
                "counted as one blueprint-repair trial"
            )
            if repair_trials >= args.max_trials:
                report = _write_report(args.name, report_lines)
                print("Pre-refinement decomposition used the configured blueprint-repair budget.")
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                return finish(1, "max_trials_exhausted_after_pre_decomposition")
        else:
            report_lines.append("- pre-refinement decomposition made no blueprint changes")

    removed_stale = _clear_stale_attempt_artifacts(args.name)
    if removed_stale:
        print(f"==> removed {removed_stale} stale Lean attempt artifact(s)", flush=True)

    generated_dir = _generated_module_dir(args.name)
    if generated_dir.exists() and not args.continue_run:
        shutil.rmtree(generated_dir)

    accepted_chunks: list[AcceptedChunk] = []
    if args.continue_run:
        resume_validation = validate_blueprint(REPO_ROOT, args.name)
        if not resume_validation.ok:
            print_result(resume_validation)
            report_lines.append("## Resume validation failed")
            report_lines.extend(f"- {error}" for error in resume_validation.errors)
            report = _write_report(args.name, report_lines)
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return finish(1, "resume_validation_failed")
        accepted_chunks, chunk_number = _load_existing_accepted_chunks(
            name=args.name,
            validation_nodes=resume_validation.nodes,
            lean_command=lean_command,
            audit_runner=gen_runner,
            paper_text=paper_text,
            telemetry=telemetry,
        )
    else:
        chunk_number = 1
    accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
    # Audit rejections per blueprint label. Survives chunk renumbering so a
    # regeneration of the same node after a (possibly no-op) blueprint repair
    # still sees what the auditor rejected last time.
    rejection_history: dict[str, list[str]] = {}
    # Import lines discovered to have no compiled .olean locally; fed back into
    # every later generation prompt so the model stops importing them.
    unavailable_imports: set[str] = set()
    # Fully autonomous refinement: every node failure is a Lean-or-blueprint
    # issue the model must fix in-loop (regenerate, repair, escalate,
    # decompose). The ONLY hard stop is exhausting --max-trials blueprint
    # repairs; there is never a human-intervention exit.
    decomposition_tried: set[str] = set()
    emitted_node_features: set[tuple[str, str]] = set()
    routing_hints = _load_routing_hints(args.name)
    forced_singletons = routing_hints["forced_singletons"]
    timeout_hard_overrides = routing_hints["timeout_hard_overrides"]
    if forced_singletons or timeout_hard_overrides:
        print(
            "==> loaded routing hints: "
            f"{len(forced_singletons)} forced singleton(s), "
            f"{len(timeout_hard_overrides)} hard-timeout override(s)",
            flush=True,
        )

    while True:
        print(
            f"==> Chunk {chunk_number}: validating blueprint "
            f"(blueprint repairs used {repair_trials}/{args.max_trials})",
            flush=True,
        )
        validation = validate_blueprint(REPO_ROOT, args.name)
        print_result(validation)
        if not validation.ok:
            report_lines.append(f"## Chunk {chunk_number}: structural validation failed")
            report_lines.extend(f"- {error}" for error in validation.errors)
            report = _write_report(args.name, report_lines)
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return finish(1, "blueprint_validation_failed")

        blueprint_source = _read_blueprint_source(args.name)
        blueprint_artifact = telemetry.store_text("blueprint", blueprint_source, ext="tex")
        telemetry.record(
            "blueprint_snapshot",
            chunk_number=chunk_number,
            validation_ok=True,
            node_count=len(validation.nodes),
            blueprint_artifact=blueprint_artifact.to_event(REPO_ROOT),
        )
        current_fingerprints = _node_fingerprints(validation.nodes)
        accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
        target_labels = _next_chunk(
            validation.nodes,
            accepted_labels,
            chunk_size=chunk_size,
            force_singletons=forced_singletons,
        )
        if not target_labels:
            assembled = _standalone_accepted_code(accepted_chunks)
            final_path = SCRATCH_DIR / args.name / "assembled_formalization.lean"
            final_path.parent.mkdir(parents=True, exist_ok=True)
            final_path.write_text(assembled.rstrip() + "\n", encoding="utf-8")
            print("==> All chunks accepted; running final module-import Lean check", flush=True)
            final_attempt = _run_lean(final_path, lean_command)
            if not final_attempt.ok:
                report_lines.append("## Final assembled Lean check failed")
                report_lines.append("```text")
                report_lines.append(final_attempt.output[-4000:])
                report_lines.append("```")
                report = _write_report(args.name, report_lines)
                print("Final assembled Lean file did not compile.")
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                return finish(1, "final_lean_failed")
            published = _publish_lean_text(args.name, assembled)
            site_lean = _rebuild_site_for(args.name)
            report_lines.append("## Complete")
            report_lines.append(f"- accepted chunks: `{chunk_number - 1}`")
            report_lines.append(f"- published Lean: `{published.relative_to(REPO_ROOT)}`")
            report_lines.append(f"- site Lean: `{site_lean.relative_to(REPO_ROOT)}`")
            report = _write_report(args.name, report_lines)
            print(f"All chunks passed. Published Lean saved to {published.relative_to(REPO_ROOT)}")
            print(f"Site rebuilt; Lean viewer available at {site_lean.relative_to(REPO_ROOT)}")
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return finish(0, "complete", accepted_chunks=chunk_number - 1)

        print(
            "==> Next dependency-closed chunk: "
            + ", ".join(target_labels)
            + f" ({len(accepted_labels)} accepted, "
            + f"{len(validation.nodes) - len(accepted_labels)} remaining including this chunk)",
            flush=True,
        )
        difficulty_summary = _chunk_difficulty_summary(validation.nodes, target_labels)
        print(f"  scheduler difficulty: {difficulty_summary}", flush=True)
        chunk_model_timeout = (
            args.hard_timeout
            if _chunk_has_hard_node(validation.nodes, target_labels)
            or bool(set(target_labels) & timeout_hard_overrides)
            else args.timeout
        )
        decision_id = f"{telemetry.run_id}:chunk:{chunk_number}"
        if chunk_model_timeout != args.timeout:
            print(
                f"  model-call timeout for this hard chunk: {chunk_model_timeout}s "
                f"(base {args.timeout}s)",
                flush=True,
            )
        library_context, library_candidates = _search_local_lean_libraries(
            args.name,
            validation.nodes,
            blueprint_source,
            term_runner=gen_runner,
        )
        library_artifact = telemetry.store_text("library_candidates", library_context, ext="txt")
        telemetry.record(
            "library_candidates",
            decision_id=decision_id,
            chunk_number=chunk_number,
            labels=target_labels,
            candidate_count=len(library_candidates),
            artifact=library_artifact.to_event(REPO_ROOT),
        )
        report_lines.append(f"- local library candidates: `{len(library_candidates)}`")
        report_lines.append(f"## Chunk {chunk_number}")
        report_lines.append(f"- target nodes: `{', '.join(target_labels)}`")
        report_lines.append(f"- scheduler difficulty: `{difficulty_summary}`")
        report_lines.append(f"- model-call timeout for this chunk: `{chunk_model_timeout}s`")
        blocks_for_features = _node_tex_blocks({label: validation.nodes[label] for label in target_labels})
        for label in target_labels:
            feature_key = (label, current_fingerprints[label])
            if feature_key in emitted_node_features:
                continue
            emitted_node_features.add(feature_key)
            telemetry.record(
                "node_features",
                **node_structural_features(
                    label,
                    validation.nodes[label].kind,
                    blocks_for_features.get(label, ""),
                    len(validation.nodes[label].uses),
                ),
            )
        telemetry.record(
            "decision_point",
            decision_id=decision_id,
            kind="pre_lean_generation",
            chunk_number=chunk_number,
            target_labels=target_labels,
            accepted_before=len(accepted_labels),
            remaining_before=len(validation.nodes) - len(accepted_labels),
            scheduler_difficulty=difficulty_summary,
            model_timeout_s=chunk_model_timeout,
            available_actions=[
                "direct_lean_generation",
                "needs_decomposition",
                "blueprint_repair_after_failure",
            ],
            chosen_action="direct_lean_generation",
        )
        critic_output = ""
        last_attempt_kind = "lean-generation"
        last_chunk_code = ""
        last_rejected_labels: set[str] = set()
        refusal_payload: dict | None = None
        replan_without_repair = False
        for lean_try in range(1, LEAN_GENERATION_RETRIES + 1):
            print(
                f"==> Chunk {chunk_number}, Lean attempt "
                f"{lean_try}/{LEAN_GENERATION_RETRIES}: generating disposable Lean "
                "(read-only model call; Lean check runs locally afterwards)",
                flush=True,
            )
            history_snippets: list[str] = []
            for label in target_labels:
                for snippet in rejection_history.get(label, [])[-2:]:
                    if snippet not in history_snippets:
                        history_snippets.append(snippet)
            lean_prompt = _chunk_lean_prompt(
                args.name,
                blueprint_source,
                validation.nodes,
                target_labels,
                accepted_labels,
                "\n\n".join(accepted_signatures),
                accepted_imports,
                library_context=library_context,
                previous_lean_error=critic_output if last_attempt_kind == "lean-generation" else "",
                previous_chunk_code=last_chunk_code if last_attempt_kind == "lean-generation" else "",
                audit_history="\n\n".join(history_snippets),
                unavailable_imports=sorted(unavailable_imports),
                model_timeout_s=chunk_model_timeout,
            )
            prompt_artifact = telemetry.store_text("prompt_lean_generation", lean_prompt)
            model_call_started = time.monotonic()
            try:
                with _runner_timeout(gen_runner, chunk_model_timeout):
                    lean_result = gen_runner.run(
                        lean_prompt,
                        cwd=REPO_ROOT,
                        retries=0,
                    )
            except RunnerError as exc:
                timed_out = _is_timeout_error(exc)
                telemetry.record(
                    "model_call",
                    purpose="lean_generation",
                    decision_id=decision_id,
                    chunk_number=chunk_number,
                    attempt=lean_try,
                    labels=target_labels,
                    status="error",
                    duration_s=time.monotonic() - model_call_started,
                    timeout_s=chunk_model_timeout,
                    backend=gen_runner.backend_name,
                    model=gen_runner.model,
                    readonly=gen_runner.readonly,
                    prompt=prompt_artifact.to_event(REPO_ROOT),
                    error=str(exc),
                    environment_error=is_environment_error(exc),
                )
                report_lines.append(f"- Lean attempt {lean_try}: model call failed before Lean was generated")
                report_lines.append("")
                report_lines.append("```text")
                report_lines.append(str(exc)[-4000:])
                report_lines.append("```")
                report_lines.append("")
                if is_environment_error(exc):
                    # Quota/auth/CLI failures cannot be fixed by refinement; exit
                    # with resumable state so the run continues once resolved.
                    report_lines.append(
                        "Stopped on an environment error (quota/auth/CLI); rerun with "
                        "--continue once resolved. The blueprint was not changed."
                    )
                    report = _write_report(args.name, report_lines)
                    print(f"Environment error stopped the run: {exc}", flush=True)
                    print(f"Report written to {report.relative_to(REPO_ROOT)}")
                    return finish(1, "environment_error", error=str(exc))
                if timed_out and len(target_labels) > 1:
                    forced_singletons.update(target_labels)
                    timeout_hard_overrides.update(target_labels)
                    _write_routing_hints(
                        args.name,
                        forced_singletons=forced_singletons,
                        timeout_hard_overrides=timeout_hard_overrides,
                    )
                    critic_output = (
                        "The Lean-generation model timed out before returning code for a "
                        "multi-node chunk. Replan the same blueprint frontier as singleton "
                        "chunks and use the hard-node timeout for these labels:\n- "
                        + "\n- ".join(target_labels)
                    )
                    telemetry.record(
                        "decision_outcome",
                        decision_id=decision_id,
                        outcome="timeout_replan_singletons",
                        labels=target_labels,
                        attempt=lean_try,
                        timeout_s=chunk_model_timeout,
                    )
                    report_lines.append(
                        "- model timed out before generating Lean; replanning this batch "
                        "as singleton hard-timeout chunks instead of retrying the same call"
                    )
                    print(
                        "  model timed out before returning Lean; replanning this batch "
                        "as singleton hard-timeout chunks",
                        flush=True,
                    )
                    replan_without_repair = True
                    break
                if timed_out and chunk_model_timeout < args.hard_timeout:
                    timeout_hard_overrides.update(target_labels)
                    _write_routing_hints(
                        args.name,
                        forced_singletons=forced_singletons,
                        timeout_hard_overrides=timeout_hard_overrides,
                    )
                    telemetry.record(
                        "decision_outcome",
                        decision_id=decision_id,
                        outcome="timeout_reclassify_hard",
                        labels=target_labels,
                        attempt=lean_try,
                        timeout_s=chunk_model_timeout,
                        next_timeout_s=args.hard_timeout,
                    )
                    report_lines.append(
                        "- singleton model call timed out at the base timeout; "
                        "reclassifying this node as hard and retrying with the hard timeout"
                    )
                    print(
                        "  singleton model call timed out at the base timeout; "
                        "reclassifying as hard and retrying with hard timeout",
                        flush=True,
                    )
                    replan_without_repair = True
                    break
                if timed_out:
                    timeout_hard_overrides.update(target_labels)
                    _write_routing_hints(
                        args.name,
                        forced_singletons=forced_singletons,
                        timeout_hard_overrides=timeout_hard_overrides,
                    )
                    critic_output = (
                        "The Lean-generation model timed out before returning code for "
                        "the current singleton chunk even with the hard-node timeout. "
                        "Treat this as evidence that the blueprint node may be too large "
                        "or underspecified for faithful 1-1 formalization as a single "
                        "declaration, and repair by decomposing it into smaller blueprint "
                        "nodes.\n\nTimed-out labels:\n- "
                        + "\n- ".join(target_labels)
                    )
                    last_attempt_kind = "blueprint"
                    last_rejected_labels = set(target_labels)
                    refusal_payload = {
                        "missing_helpers": [
                            "split the timed-out node into smaller explicit formalization helper nodes"
                        ],
                        "reason": "Lean-generation model call timed out before producing code with the hard-node timeout.",
                    }
                    telemetry.record(
                        "decision_outcome",
                        decision_id=decision_id,
                        outcome="timeout_decomposition",
                        labels=target_labels,
                        attempt=lean_try,
                        timeout_s=chunk_model_timeout,
                    )
                    print(
                        "  model timed out before returning Lean for a singleton chunk "
                        "with the hard-node timeout; routing to blueprint decomposition",
                        flush=True,
                    )
                    break
                # Anything else (post-retry transient, malformed reply) is
                # handled in-loop: count it as a failed attempt and continue.
                print(
                    f"  model call failed ({str(exc)[:200]}); treating as a failed "
                    f"attempt and continuing refinement",
                    flush=True,
                )
                time.sleep(15)
                continue
            response_artifact = telemetry.store_text("response_lean_generation", lean_result.text)
            telemetry.record(
                "model_call",
                purpose="lean_generation",
                decision_id=decision_id,
                chunk_number=chunk_number,
                attempt=lean_try,
                labels=target_labels,
                status="success",
                duration_s=lean_result.duration_s,
                timeout_s=chunk_model_timeout,
                backend=lean_result.backend,
                model=lean_result.model,
                readonly=gen_runner.readonly,
                prompt=prompt_artifact.to_event(REPO_ROOT),
                response=response_artifact.to_event(REPO_ROOT),
            )
            refusal = _parse_decomposition_refusal(lean_result.text)
            if refusal is not None:
                refused = [refusal["label"]] if refusal["label"] in target_labels else list(target_labels)
                telemetry.record(
                    "decomposition_requested",
                    decision_id=decision_id,
                    chunk_number=chunk_number,
                    labels=refused,
                    source="model_refusal",
                    missing_helpers=refusal["missing_helpers"],
                    reason=refusal["reason"],
                )
                telemetry.record(
                    "decision_outcome",
                    decision_id=decision_id,
                    outcome="needs_decomposition",
                    source="model_refusal",
                    labels=refused,
                )
                print(
                    f"  generation refused: node(s) {', '.join(refused)} not formalizable "
                    "as stated; routing to blueprint decomposition",
                    flush=True,
                )
                report_lines.append(
                    f"  - generation refused (NEEDS-DECOMPOSITION) for `{', '.join(refused)}`"
                )
                critic_output = (
                    "The Lean generator determined the node cannot be formalized 1-1 as "
                    "stated and needs blueprint helper nodes.\n"
                    f"Reason: {refusal['reason']}\n"
                    "Missing helpers:\n- " + "\n- ".join(refusal["missing_helpers"] or ["(unspecified)"])
                )
                last_attempt_kind = "blueprint"
                last_rejected_labels = set(refused)
                refusal_payload = refusal
                break

            trial_dir = SCRATCH_DIR / args.name
            trial_dir.mkdir(parents=True, exist_ok=True)
            module_name, module_path = _chunk_module(args.name, chunk_number)
            module_path.parent.mkdir(parents=True, exist_ok=True)
            lean_path = module_path
            chunk_code = _extract_lean_code(lean_result.text).rstrip() + "\n"
            chunk_import_lines, _chunk_body = _split_lean_imports_and_body(chunk_code)
            missing_imports = _missing_olean_imports(chunk_import_lines)
            removed_imports_note = ""
            if missing_imports:
                # Deterministic pre-check: these imports would fail Lean with
                # "object file ... does not exist" after a full (expensive)
                # generation. Strip them, let Lean judge the rest, and remember
                # them so later prompts forbid them up front.
                unavailable_imports.update(missing_imports)
                print(
                    "  removed import(s) with no compiled .olean in the local build: "
                    + ", ".join(item[len("import "):] for item in missing_imports),
                    flush=True,
                )
                report_lines.append(
                    f"  - removed unavailable import(s): `{', '.join(missing_imports)}`"
                )
                missing_set = set(missing_imports)
                chunk_code = "\n".join(
                    line for line in chunk_code.splitlines() if line.strip() not in missing_set
                ).rstrip() + "\n"
                removed_imports_note = (
                    "\n\nNote: the following imports were removed before compiling because "
                    "their modules have no compiled .olean in the local Mathlib build. Do "
                    "not import them; avoid tactics/lemmas that need them: "
                    + ", ".join(missing_imports)
                )
            lean_code, new_imports, new_body = _compose_module_file(accepted_imports, chunk_code)
            last_chunk_code = chunk_code
            lean_path.write_text(lean_code, encoding="utf-8")
            scratch_attempt = trial_dir / f"chunk_{chunk_number:02d}_attempt_{lean_try:02d}.lean"
            scratch_attempt.write_text(lean_code, encoding="utf-8")
            lean_artifact = telemetry.store_text("lean_attempt", lean_code, ext="lean")
            print(
                f"  wrote {lean_path.relative_to(REPO_ROOT)} "
                f"({len(lean_code.splitlines())} lines, model took {lean_result.duration_s:.0f}s)",
                flush=True,
            )
            if re.search(r"^import (Mathlib|AutoBlueprint)\s*$", lean_code, re.MULTILINE):
                print(
                    "  note: attempt uses a blanket Mathlib import; the compile check will be slower",
                    flush=True,
                )

            precheck_issues = _audit_lean_code(lean_code)
            if precheck_issues:
                # Free text-level rejection (sorry/admit, vacuous True, invented
                # helpers) before paying for a Lean run.
                critic_output = (
                    "Deterministic code audit rejected the attempt before compiling:\n- "
                    + "\n- ".join(precheck_issues)
                ) + removed_imports_note
                last_attempt_kind = "lean-generation"
                print("  deterministic code audit failed pre-Lean; last lines:", flush=True)
                for line in precheck_issues[:8]:
                    print(f"    {line}", flush=True)
                report_lines.append("  - result: failed deterministic pre-Lean code audit")
                report_lines.append("")
                report_lines.append("```text")
                report_lines.append(critic_output[-4000:])
                report_lines.append("```")
                report_lines.append("")
                telemetry.record(
                    "lean_attempt",
                    decision_id=decision_id,
                    chunk_number=chunk_number,
                    attempt=lean_try,
                    labels=target_labels,
                    status="precheck_failed",
                    lean=lean_artifact.to_event(REPO_ROOT),
                    lean_lines=len(lean_code.splitlines()),
                    imports=new_imports,
                    issues=precheck_issues,
                )
                continue

            print(f"==> Chunk {chunk_number}: running Lean", flush=True)
            lean_started = time.monotonic()
            attempt = _run_lean(lean_path, lean_command)
            lean_duration = time.monotonic() - lean_started
            lean_output_artifact = (
                telemetry.store_text("lean_output", attempt.output, ext="txt")
                if attempt.output
                else None
            )
            telemetry.record(
                "lean_attempt",
                decision_id=decision_id,
                chunk_number=chunk_number,
                attempt=lean_try,
                labels=target_labels,
                status="compile_passed" if attempt.ok else "compile_failed",
                routed_kind=attempt.kind,
                duration_s=lean_duration,
                lean=lean_artifact.to_event(REPO_ROOT),
                lean_lines=len(lean_code.splitlines()),
                imports=new_imports,
                command=attempt.command,
                output_sha256=hashlib.sha256(attempt.output.encode("utf-8")).hexdigest(),
                output=lean_output_artifact.to_event(REPO_ROOT) if lean_output_artifact else None,
            )
            report_lines.append(f"- Lean attempt {lean_try}: `{scratch_attempt.relative_to(REPO_ROOT)}`")

            if attempt.ok:
                print(f"==> Chunk {chunk_number}: auditing statement alignment", flush=True)
                audit_failure = _run_statement_alignment_audit(
                    gen_runner,
                    args.name,
                    {label: validation.nodes[label] for label in target_labels},
                    lean_path,
                    paper_text,
                    all_nodes=validation.nodes,
                    telemetry=telemetry,
                    chunk_number=chunk_number,
                )
                if audit_failure is not None:
                    attempt = audit_failure
                    critic_output = attempt.output
                    last_attempt_kind = attempt.kind
                    rejected_for_history = (
                        set(attempt.rejected_labels or []) & set(target_labels)
                    ) or set(target_labels)
                    last_rejected_labels = set(rejected_for_history)
                    for label in rejected_for_history:
                        rejection_history.setdefault(label, []).append(critic_output[-2500:])
                    print(
                        f"  statement alignment audit failed ({attempt.kind}); last lines:",
                        flush=True,
                    )
                    for line in critic_output.strip().splitlines()[-8:]:
                        print(f"    {line}", flush=True)
                    report_lines.append(f"  - result: failed statement alignment audit ({attempt.kind})")
                    report_lines.append("")
                    report_lines.append("```text")
                    report_lines.append(critic_output[-4000:])
                    report_lines.append("```")
                    report_lines.append("")
                    if attempt.kind == "blueprint" and attempt.rejected_labels:
                        rejected_in_chunk = set(attempt.rejected_labels) & set(target_labels)
                        affected_in_chunk = _dependency_descendants_within(
                            validation.nodes,
                            rejected_in_chunk,
                            set(target_labels),
                        )
                        keep_labels = [label for label in target_labels if label not in affected_in_chunk]
                        if keep_labels:
                            pruned = _prune_chunk_to_labels(
                                module_imports=accepted_imports,
                                original_chunk_code=chunk_code,
                                target_labels=target_labels,
                                keep_labels=keep_labels,
                            )
                            if pruned is not None:
                                lean_path.write_text(pruned.lean_code, encoding="utf-8")
                                pruned_attempt_path = (
                                    trial_dir / f"chunk_{chunk_number:02d}_accepted_subset.lean"
                                )
                                pruned_attempt_path.write_text(pruned.lean_code, encoding="utf-8")
                                print(
                                    "  trying to keep independent passing subset: "
                                    + ", ".join(keep_labels),
                                    flush=True,
                                )
                                subset_lean = _run_lean(lean_path, lean_command)
                                subset_audit = None
                                if subset_lean.ok:
                                    subset_audit = _run_statement_alignment_audit(
                                        gen_runner,
                                        args.name,
                                        {label: validation.nodes[label] for label in keep_labels},
                                        lean_path,
                                        paper_text,
                                        all_nodes=validation.nodes,
                                        telemetry=telemetry,
                                        chunk_number=chunk_number,
                                    )
                                if subset_lean.ok and subset_audit is None:
                                    object_attempt = _compile_module_olean(module_path, lean_command)
                                    if object_attempt.ok:
                                        accepted_chunks.append(
                                            AcceptedChunk(
                                                labels=list(keep_labels),
                                                imports=list(pruned.imports),
                                                body=pruned.body,
                                                fingerprints={
                                                    label: current_fingerprints[label]
                                                    for label in keep_labels
                                                },
                                                module=module_name,
                                                path=module_path,
                                                signatures=pruned.signatures,
                                            )
                                        )
                                        _write_chunk_manifest(args.name, accepted_chunks)
                                        accepted_labels, accepted_imports, accepted_signatures = (
                                            _accepted_state(accepted_chunks)
                                        )
                                        partial = _standalone_accepted_code(accepted_chunks)
                                        partial_path = trial_dir / "partial_formalization.lean"
                                        partial_path.write_text(partial.rstrip() + "\n", encoding="utf-8")
                                        print(
                                            "  kept independent subset; rejected/downstream nodes "
                                            "will be repaired/regenerated",
                                            flush=True,
                                        )
                                        telemetry.record(
                                            "partial_subset_kept",
                                            decision_id=decision_id,
                                            chunk_number=chunk_number,
                                            kept_labels=keep_labels,
                                            rejected_labels=sorted(rejected_in_chunk),
                                            accepted_after=len(accepted_labels),
                                            lean=pruned_attempt_path.relative_to(REPO_ROOT),
                                        )
                                        report_lines.append(
                                            "  - kept independent passing subset: "
                                            f"`{', '.join(keep_labels)}`"
                                        )
                                        report_lines.append(
                                            f"  - pruned subset Lean: `{pruned_attempt_path.relative_to(REPO_ROOT)}`"
                                        )
                                    else:
                                        print(
                                            "  independent subset did not compile as an importable module; "
                                            "discarding it",
                                            flush=True,
                                        )
                                else:
                                    print(
                                        "  independent subset did not pass Lean/audit after pruning; "
                                        "discarding it",
                                        flush=True,
                                    )
                    if attempt.kind != "lean-generation":
                        break
                    continue

                object_attempt = _compile_module_olean(module_path, lean_command)
                if not object_attempt.ok:
                    critic_output = object_attempt.output
                    last_attempt_kind = "lean-generation"
                    print("  accepted chunk failed .olean compilation; last lines:", flush=True)
                    for line in critic_output.strip().splitlines()[-8:]:
                        print(f"    {line}", flush=True)
                    report_lines.append("  - result: failed generated module .olean compilation")
                    report_lines.append("")
                    report_lines.append("```text")
                    report_lines.append(critic_output[-4000:])
                    report_lines.append("```")
                    report_lines.append("")
                    continue

                signatures = _decl_signatures(lean_code)
                accepted_chunks.append(
                    AcceptedChunk(
                        labels=list(target_labels),
                        imports=list(new_imports),
                        body=new_body,
                        fingerprints={label: current_fingerprints[label] for label in target_labels},
                        module=module_name,
                        path=module_path,
                        signatures=signatures,
                    )
                )
                _write_chunk_manifest(args.name, accepted_chunks)
                accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
                partial = _standalone_accepted_code(accepted_chunks)
                partial_path = trial_dir / "partial_formalization.lean"
                partial_path.write_text(partial.rstrip() + "\n", encoding="utf-8")
                report_lines.append("- result: chunk passed")
                report_lines.append("- statement alignment audit: passed")
                report_lines.append(f"- accepted through nodes: `{len(accepted_labels)}`")
                report_lines.append(f"- partial Lean: `{partial_path.relative_to(REPO_ROOT)}`")
                print(
                    f"Chunk {chunk_number} passed; accepted {len(accepted_labels)} "
                    f"of {len(validation.nodes)} blueprint nodes.",
                    flush=True,
                )
                telemetry.record(
                    "decision_outcome",
                    decision_id=decision_id,
                    outcome="accepted",
                    accepted_labels=target_labels,
                    accepted_after=len(accepted_labels),
                    attempts=lean_try,
                )
                forced_singletons.difference_update(target_labels)
                timeout_hard_overrides.difference_update(target_labels)
                _write_routing_hints(
                    args.name,
                    forced_singletons=forced_singletons,
                    timeout_hard_overrides=timeout_hard_overrides,
                )
                telemetry.record(
                    "chunk_end",
                    decision_id=decision_id,
                    chunk_number=chunk_number,
                    labels=target_labels,
                    status="accepted",
                    accepted_after=len(accepted_labels),
                    attempts=lean_try,
                )
                chunk_number += 1
                break

            critic_output = attempt.output + removed_imports_note
            last_attempt_kind = attempt.kind
            print(
                f"  lean failed on chunk {chunk_number}, attempt {lean_try} "
                f"({attempt.kind}); last lines of output:",
                flush=True,
            )
            for line in critic_output.strip().splitlines()[-8:]:
                print(f"    {line}", flush=True)
            report_lines.append(f"  - result: failed ({attempt.kind})")
            report_lines.append("")
            report_lines.append("```text")
            report_lines.append(critic_output[-4000:])
            report_lines.append("```")
            report_lines.append("")

            if attempt.kind != "lean-generation":
                break

        if replan_without_repair:
            chunk_number += 1
            continue

        if set(target_labels) <= accepted_labels:
            continue

        if last_attempt_kind == "lean-generation":
            # Persistent proof/encoding failure means the blueprint is steering
            # the generator into an unprovable or fragile encoding. That is a
            # blueprint issue: fall through to repair (bounded by --max-trials)
            # so the model fixes it autonomously.
            print(
                "  Lean generation retries exhausted; escalating to blueprint repair "
                "with the accumulated error output.",
                flush=True,
            )
            report_lines.append("- generation retries exhausted; escalated to blueprint repair")
            telemetry.record(
                "decision_outcome",
                decision_id=decision_id,
                outcome="generation_retries_exhausted",
                labels=target_labels,
                attempts=LEAN_GENERATION_RETRIES,
            )

        stuck_labels = sorted(last_rejected_labels or set(target_labels))
        if repair_trials >= args.max_trials:
            break

        stuck_key = ",".join(stuck_labels)
        escalation_note = ""
        if refusal_payload is not None:
            # The generator itself asked for decomposition; start there.
            escalation_note = _decomposition_note(
                stuck_labels, refusal_payload.get("missing_helpers") or None
            )
            decomposition_tried.add(stuck_key)
        while True:
            repair_trials += 1
            print(
                f"==> Blueprint repair {repair_trials}/{args.max_trials} "
                f"from chunk {chunk_number} Lean/audit output",
                flush=True,
            )
            if runner.mode == "agent":
                repair_prompt = _agent_refine_prompt(
                    args.name,
                    blueprint_source,
                    critic_output,
                    repair_trials,
                    paper_text,
                    escalation_note=escalation_note,
                    model_timeout_s=chunk_model_timeout,
                )
                repair_prompt_artifact = telemetry.store_text("prompt_blueprint_repair", repair_prompt)
                repair_started = time.monotonic()
                try:
                    with _runner_timeout(runner, chunk_model_timeout):
                        repair = runner.run(
                            repair_prompt,
                            cwd=REPO_ROOT,
                            retries=0,
                        )
                except RunnerError as exc:
                    telemetry.record(
                        "model_call",
                        purpose="blueprint_repair",
                        decision_id=decision_id,
                        chunk_number=chunk_number,
                        repair_trial=repair_trials,
                        labels=stuck_labels,
                        status="error",
                        duration_s=time.monotonic() - repair_started,
                        timeout_s=chunk_model_timeout,
                        backend=runner.backend_name,
                        model=runner.model,
                        readonly=runner.readonly,
                        prompt=repair_prompt_artifact.to_event(REPO_ROOT),
                        error=str(exc),
                        environment_error=is_environment_error(exc),
                    )
                    report_lines.append("## Blueprint repair model call failed")
                    report_lines.append("")
                    report_lines.append("```text")
                    report_lines.append(str(exc)[-4000:])
                    report_lines.append("```")
                    report = _write_report(args.name, report_lines)
                    print(f"Blueprint repair model call failed: {exc}", flush=True)
                    print(f"Report written to {report.relative_to(REPO_ROOT)}")
                    status = "environment_error" if is_environment_error(exc) else "blueprint_repair_model_failed"
                    return finish(1, status, error=str(exc))
                repair_response_artifact = telemetry.store_text("response_blueprint_repair", repair.text)
                telemetry.record(
                    "model_call",
                    purpose="blueprint_repair",
                    decision_id=decision_id,
                    chunk_number=chunk_number,
                    repair_trial=repair_trials,
                    labels=stuck_labels,
                    status="success",
                    duration_s=repair.duration_s,
                    timeout_s=chunk_model_timeout,
                    backend=repair.backend,
                    model=repair.model,
                    readonly=runner.readonly,
                    prompt=repair_prompt_artifact.to_event(REPO_ROOT),
                    response=repair_response_artifact.to_event(REPO_ROOT),
                    elapsed_s=time.monotonic() - repair_started,
                    escalation_note=bool(escalation_note),
                )
                print(f"  blueprint repair finished ({repair.duration_s:.0f}s)", flush=True)
            else:
                repair_prompt = _api_refine_prompt(
                    args.name,
                    blueprint_source,
                    critic_output,
                    repair_trials,
                    paper_text,
                    escalation_note=escalation_note,
                    model_timeout_s=chunk_model_timeout,
                )
                repair_prompt_artifact = telemetry.store_text("prompt_blueprint_repair", repair_prompt)
                repair_started = time.monotonic()
                try:
                    with _runner_timeout(runner, chunk_model_timeout):
                        refine_result = runner.run(
                            repair_prompt,
                            cwd=REPO_ROOT,
                            retries=1,
                        )
                except RunnerError as exc:
                    telemetry.record(
                        "model_call",
                        purpose="blueprint_repair",
                        decision_id=decision_id,
                        chunk_number=chunk_number,
                        repair_trial=repair_trials,
                        labels=stuck_labels,
                        status="error",
                        duration_s=time.monotonic() - repair_started,
                        timeout_s=chunk_model_timeout,
                        backend=runner.backend_name,
                        model=runner.model,
                        readonly=runner.readonly,
                        prompt=repair_prompt_artifact.to_event(REPO_ROOT),
                        error=str(exc),
                        environment_error=is_environment_error(exc),
                    )
                    report_lines.append("## Blueprint repair model call failed")
                    report_lines.append("")
                    report_lines.append("```text")
                    report_lines.append(str(exc)[-4000:])
                    report_lines.append("```")
                    report = _write_report(args.name, report_lines)
                    print(f"Blueprint repair model call failed: {exc}", flush=True)
                    print(f"Report written to {report.relative_to(REPO_ROOT)}")
                    status = "environment_error" if is_environment_error(exc) else "blueprint_repair_model_failed"
                    return finish(1, status, error=str(exc))
                repair_response_artifact = telemetry.store_text("response_blueprint_repair", refine_result.text)
                telemetry.record(
                    "model_call",
                    purpose="blueprint_repair",
                    decision_id=decision_id,
                    chunk_number=chunk_number,
                    repair_trial=repair_trials,
                    labels=stuck_labels,
                    status="success",
                    duration_s=refine_result.duration_s,
                    timeout_s=chunk_model_timeout,
                    backend=refine_result.backend,
                    model=refine_result.model,
                    readonly=runner.readonly,
                    prompt=repair_prompt_artifact.to_event(REPO_ROOT),
                    response=repair_response_artifact.to_event(REPO_ROOT),
                    elapsed_s=time.monotonic() - repair_started,
                    escalation_note=bool(escalation_note),
                )
                try:
                    _write_api_refinement(args.name, refine_result.text)
                except ValueError as exc:
                    report_lines.append("## API blueprint repair returned invalid JSON/content")
                    report_lines.append("")
                    report_lines.append("```text")
                    report_lines.append(str(exc))
                    report_lines.append("")
                    report_lines.append(refine_result.text[-4000:])
                    report_lines.append("```")
                    report = _write_report(args.name, report_lines)
                    print(f"API blueprint repair failed: {exc}", flush=True)
                    print(f"Report written to {report.relative_to(REPO_ROOT)}")
                    return finish(1, "api_repair_invalid_json", error=str(exc))

            repaired_validation = validate_blueprint(REPO_ROOT, args.name)
            if not repaired_validation.ok:
                print_result(repaired_validation)
                report_lines.append("## Blueprint repair produced invalid structure")
                report_lines.extend(f"- {error}" for error in repaired_validation.errors)
                report = _write_report(args.name, report_lines)
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                return finish(1, "repair_validation_failed")

            repaired_fingerprints = _node_fingerprints(repaired_validation.nodes)
            changed = {
                label
                for label, before in current_fingerprints.items()
                if repaired_fingerprints.get(label) != before
            }
            changed |= {label for label in repaired_fingerprints if label not in current_fingerprints}
            telemetry.record(
                "blueprint_repair_result",
                decision_id=decision_id,
                chunk_number=chunk_number,
                repair_trial=repair_trials,
                labels=stuck_labels,
                changed_labels=sorted(changed),
                changed_count=len(changed),
                validation_ok=True,
                escalation_note=bool(escalation_note),
            )
            if changed or repair_trials >= args.max_trials:
                break
            # No-op repair ladder: plain -> explicit escalation -> forced
            # decomposition -> regenerate with accumulated audit feedback. A
            # repair that changes zero nodes guarantees the audit rejects the
            # same content again, so each rung must materially change strategy.
            if not escalation_note:
                print(
                    "  blueprint repair did not change parsed node text; escalating once "
                    "with explicit instructions",
                    flush=True,
                )
                report_lines.append("- blueprint repair was a no-op; escalated with explicit instructions")
                telemetry.record(
                    "repair_escalation",
                    decision_id=decision_id,
                    chunk_number=chunk_number,
                    repair_trial=repair_trials,
                    labels=stuck_labels,
                    mode="explicit_instructions",
                )
                escalation_note = (
                    "Your previous repair attempt changed NOTHING in the parsed node text — "
                    "the validator found zero modified nodes, so the audit will reject the "
                    "same content again. You MUST materially edit the TeX of the rejected "
                    "node(s) this time: add the missing concrete semantics, hypotheses, "
                    "parameters, or split the node into smaller nodes. If you believe the "
                    "blueprint is already correct and the Lean generation is at fault, "
                    "still make the node text more explicit about the required statement "
                    "shape so the generator cannot satisfy it with a tautology."
                )
                continue
            if stuck_key not in decomposition_tried:
                decomposition_tried.add(stuck_key)
                print(
                    "  repair still a no-op after escalation; forcing decomposition mode",
                    flush=True,
                )
                report_lines.append("- repair no-op after escalation; forced decomposition mode")
                telemetry.record(
                    "repair_escalation",
                    decision_id=decision_id,
                    chunk_number=chunk_number,
                    repair_trial=repair_trials,
                    labels=stuck_labels,
                    mode="forced_decomposition",
                )
                escalation_note = _decomposition_note(stuck_labels)
                continue
            # Every repair strategy no-oped this round. Refinement continues
            # autonomously: regenerate the chunk with the accumulated audit
            # feedback (generation is stochastic and the rejection history
            # grows each round). Only --max-trials can end the run.
            print(
                "  repair strategies all no-oped this round; regenerating with "
                "accumulated audit feedback",
                flush=True,
            )
            report_lines.append("- repairs no-oped; regenerating with accumulated audit feedback")
            telemetry.record(
                "repair_escalation",
                decision_id=decision_id,
                chunk_number=chunk_number,
                repair_trial=repair_trials,
                labels=stuck_labels,
                mode="regenerate_with_audit_history",
            )
            break

        invalidated = _dependency_descendants(repaired_validation.nodes, changed) if changed else set()
        before_count = len(accepted_chunks)
        kept_chunks: list[AcceptedChunk] = []
        dropped_chunks: list[AcceptedChunk] = []
        for chunk in accepted_chunks:
            if set(chunk.labels) & invalidated:
                dropped_chunks.append(chunk)
            else:
                kept_chunks.append(chunk)
        for chunk in dropped_chunks:
            for artifact in (chunk.path, chunk.path.with_suffix(".olean")):
                try:
                    artifact.unlink()
                except FileNotFoundError:
                    pass
        accepted_chunks = kept_chunks
        _write_chunk_manifest(args.name, accepted_chunks)
        accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
        dropped = before_count - len(accepted_chunks)
        if changed:
            print(
                f"  blueprint changed {len(changed)} node(s); invalidated "
                f"{len(invalidated)} downstream node(s); kept {len(accepted_chunks)} accepted chunk(s)",
                flush=True,
            )
            report_lines.append(
                f"- blueprint repair changed `{len(changed)}` node(s), invalidated "
                f"`{len(invalidated)}` downstream node(s), dropped `{dropped}` accepted chunk(s)"
            )
            telemetry.record(
                "blueprint_repair_applied",
                decision_id=decision_id,
                chunk_number=chunk_number,
                labels=stuck_labels,
                changed_labels=sorted(changed),
                invalidated_labels=sorted(invalidated),
                dropped_chunks=dropped,
                accepted_chunks_kept=len(accepted_chunks),
            )
        else:
            print("  blueprint repair did not change parsed node text; keeping accepted chunks", flush=True)
            report_lines.append("- blueprint repair did not change parsed node text; kept accepted chunks")
            telemetry.record(
                "blueprint_repair_noop",
                decision_id=decision_id,
                chunk_number=chunk_number,
                labels=stuck_labels,
                accepted_chunks_kept=len(accepted_chunks),
            )
        # The failed chunk's module file was never accepted; remove it so a
        # later --continue does not re-check it and discard accepted work.
        failed_module_path = _chunk_module(args.name, chunk_number)[1]
        if not any(chunk.path == failed_module_path for chunk in accepted_chunks):
            for artifact in (failed_module_path, failed_module_path.with_suffix(".olean")):
                try:
                    artifact.unlink()
                except FileNotFoundError:
                    pass
        chunk_number += 1

    report_lines.append(f"Stopped after {args.max_trials} failed trial(s).")
    report = _write_report(args.name, report_lines)
    print(f"Lean did not pass after {args.max_trials} trial(s).")
    print(f"Report written to {report.relative_to(REPO_ROOT)}")
    return finish(1, "max_trials_exhausted")


def logged_main(argv: list[str] | None = None) -> int:
    """Run main while saving the complete terminal transcript to a log file."""
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("name", nargs="?")
    known, _unknown = parser.parse_known_args(argv)
    if not known.name:
        return main(argv)

    global CURRENT_LOG_PATH
    log_path = _run_log_path(known.name)
    CURRENT_LOG_PATH = log_path
    with log_path.open("w", encoding="utf-8") as log_file:
        log_file.write(f"# Auto-Blueprint Lean refinement log\n")
        log_file.write(f"# cwd: {REPO_ROOT}\n")
        log_file.write(f"# command: {' '.join([sys.argv[0], *(argv or sys.argv[1:])])}\n\n")
        started_at = time.monotonic()
        with contextlib.redirect_stdout(TeeStream(sys.stdout, log_file, started_at=started_at)), contextlib.redirect_stderr(
            TeeStream(sys.stderr, log_file, started_at=started_at)
        ):
            print(f"Log file: {log_path.relative_to(REPO_ROOT)}", flush=True)
            try:
                code = main(argv)
            except (FileNotFoundError, RunnerError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
                print(f"error: {exc}", file=sys.stderr)
                code = 2
            finally:
                print(f"Log file: {log_path.relative_to(REPO_ROOT)}", flush=True)
            return code


if __name__ == "__main__":
    raise SystemExit(logged_main())
