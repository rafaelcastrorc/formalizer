#!/usr/bin/env python3
"""Refine a blueprint by using Lean as the critic.

This is the author/critic loop:

1. validate the current blueprint;
2. choose the next dependency-closed chunk from the blueprint ``\\uses`` graph;
3. ask a read-only model call to generate disposable Lean for that chunk only,
   while still showing the whole blueprint as context;
4. run Lean on accepted chunk context plus the new chunk;
5. audit that the compiled Lean statements actually align with the target nodes;
6. if Lean/audit fails because the generated Lean is malformed or mistranslated,
   retry Lean generation for the same chunk;
7. if Lean/audit fails because the blueprint is missing mathematical content, ask
   a second model call to fix the blueprint, not the Lean file;
8. after a blueprint repair, revalidate and replan chunks from the repaired
   blueprint;
9. publish only when every chunk has passed.

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
from validate_blueprint import Node, print_result, validate_blueprint

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
SKILL_PATH = REPO_ROOT / ".claude" / "skills" / "paper-to-blueprint" / "SKILL.md"
SCRATCH_DIR = REPO_ROOT / ".auto-blueprint" / "formalization"
PUBLISHED_LEAN_NAME = "formalization.lean"
LEAN_GENERATION_RETRIES = 5
AUTO_CHUNK_SIZE = 0
DEFAULT_AUTO_CHUNK_LIMIT = 8
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
    r"^\s*(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?"
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


class TeeStream:
    """Mirror script output to the terminal and a persistent run log."""

    def __init__(self, terminal, log_file):
        self.terminal = terminal
        self.log_file = log_file

    def write(self, text: str) -> int:
        self.terminal.write(text)
        self.log_file.write(text)
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


def _next_chunk(nodes: dict[str, Node], accepted: set[str], *, chunk_size: int) -> list[str]:
    """Pick the next dependency-closed frontier of blueprint nodes to formalize."""
    available = set(accepted) | {label for label, node in nodes.items() if node.mathlibok}
    remaining = [label for label in _node_order(nodes) if label not in available]
    chunk: list[str] = []
    progressed = True
    while progressed and len(chunk) < chunk_size:
        progressed = False
        for label in remaining:
            if label in chunk:
                continue
            node = nodes[label]
            if node.uses <= (available | set(chunk)):
                chunk.append(label)
                progressed = True
                if len(chunk) >= chunk_size:
                    break
    return chunk


def _chunk_summary(nodes: dict[str, Node], labels: list[str]) -> str:
    return _node_summary({label: nodes[label] for label in labels})


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


def _deterministic_statement_audit(code: str, nodes: dict[str, Node]) -> list[str]:
    """Catch obvious coverage and weakening failures before using model judgment."""
    issues: list[str] = []
    decls = _lean_declarations(code)
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
    return f"""TASK: STATEMENT-ALIGNMENT-AUDIT

You are the publication gate for Auto-Blueprint.

Lean has already accepted the generated file, but that is not enough. Decide
whether each generated Lean declaration actually formalizes the corresponding
blueprint node without weakening, erasing parameters, replacing concrete
claims by abstract placeholders, or changing the mathematical content.

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
- A required non-Mathlib node has no matching Lean declaration.

Do not reject merely because the Lean proof is ugly. Judge statement alignment.

Blueprint name: {name}
{paper_block}
Pairs to audit:
{"\n\n".join(pairs)}
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
    """Route compiled-but-wrong Lean to either Lean retry or blueprint repair."""
    if classification == "blueprint_issue":
        return "blueprint"
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
) -> LeanAttempt | None:
    """Return None when the compiled Lean is aligned enough to publish."""
    code = lean_path.read_text(encoding="utf-8")
    deterministic_issues = _deterministic_statement_audit(code, nodes)
    if deterministic_issues:
        return LeanAttempt(
            ok=False,
            command=[],
            reason="Statement alignment audit failed deterministic checks:\n- "
            + "\n- ".join(deterministic_issues),
            kind=_deterministic_audit_kind(deterministic_issues),
        )

    decls = _lean_declarations(code)
    prompt = _statement_audit_prompt(
        name,
        nodes,
        _node_tex_blocks(nodes),
        decls,
        paper_text,
    )
    result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
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
        return None

    formatted: list[str] = []
    for issue in issues if isinstance(issues, list) else []:
        if not isinstance(issue, dict):
            continue
        node = str(issue.get("node") or "(unknown node)")
        reason = str(issue.get("reason") or "no reason provided")
        severity = str(issue.get("severity") or "reject")
        formatted.append(f"{node} [{severity}]: {reason}")
    if not formatted:
        formatted.append(str(payload)[:4000])

    classification = str(payload.get("classification") or "lean_translation_issue")
    kind = _alignment_failure_kind(classification, formatted)
    return LeanAttempt(
        ok=False,
        command=[],
        reason="Statement alignment audit rejected the compiled Lean:\n- " + "\n- ".join(formatted),
        kind=kind,
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
) -> str:
    retry_block = ""
    if previous_lean_error:
        retry_block = f"""

Previous generated Lean attempt for this same chunk failed. Do not change the
mathematical content. Fix only the Lean encoding, imports, explicit arguments,
and proofs for this chunk.

Previous Lean/audit output:
```text
{previous_lean_error[-12000:]}
```
"""
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
- Generate Lean declarations for every target node in the current chunk.
- Do not redefine accepted declarations from earlier chunks.
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

The script will compile:

    imports of accepted chunk modules + your new chunk code

So your output should contain imports plus new declarations for this chunk. It
must not repeat accepted declarations.
{retry_block}

Blueprint name: {name}

Accepted blueprint nodes:
{accepted_list}

Accepted Lean module imports:
```lean
{chr(10).join(accepted_imports) if accepted_imports else "-- none yet"}
```

Current target chunk:
{_chunk_summary(nodes, target_labels)}

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


def _agent_refine_prompt(name: str, blueprint_source: str, lean_output: str, trial: int, paper_text: str) -> str:
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    return f"""TASK: REFINE-BLUEPRINT-FROM-LEAN-FAILURE

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.

You are the blueprint author. Fix the blueprint, not the Lean implementation.

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


def _api_refine_prompt(name: str, blueprint_source: str, lean_output: str, trial: int, paper_text: str) -> str:
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    return f"""TASK: REFINE-BLUEPRINT-CONTENT-TEX

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.

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
        "--reasoning-effort",
        choices=("low", "medium", "high", "xhigh"),
        help="Codex reasoning effort for --runner codex/codex:<model>.",
    )
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args(argv)

    if args.max_trials < 1:
        raise SystemExit("--max-trials must be at least 1")
    if args.chunk_size < 0:
        raise SystemExit("--chunk-size must be 0 for auto or a positive integer")
    chunk_size = args.chunk_size or DEFAULT_AUTO_CHUNK_LIMIT

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
        f"- internal Lean-generation retries: `{LEAN_GENERATION_RETRIES}`",
        f"- Lean command: `{' '.join(lean_command)}`",
    ]
    if CURRENT_LOG_PATH is not None:
        report_lines.append(f"- full log: `{CURRENT_LOG_PATH.relative_to(REPO_ROOT)}`")
    report_lines.append("")

    removed_stale = _clear_stale_attempt_artifacts(args.name)
    if removed_stale:
        print(f"==> removed {removed_stale} stale Lean attempt artifact(s)", flush=True)

    generated_dir = _generated_module_dir(args.name)
    if generated_dir.exists():
        shutil.rmtree(generated_dir)

    accepted_chunks: list[AcceptedChunk] = []
    accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
    repair_trials = 0
    chunk_number = 1

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
            return 1

        blueprint_source = _read_blueprint_source(args.name)
        current_fingerprints = _node_fingerprints(validation.nodes)
        accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
        target_labels = _next_chunk(validation.nodes, accepted_labels, chunk_size=chunk_size)
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
                return 1
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
            return 0

        print(
            "==> Next dependency-closed chunk: "
            + ", ".join(target_labels)
            + f" ({len(accepted_labels)} accepted, "
            + f"{len(validation.nodes) - len(accepted_labels)} remaining including this chunk)",
            flush=True,
        )
        library_context, library_candidates = _search_local_lean_libraries(
            args.name,
            validation.nodes,
            blueprint_source,
            term_runner=gen_runner,
        )
        report_lines.append(f"- local library candidates: `{len(library_candidates)}`")
        report_lines.append(f"## Chunk {chunk_number}")
        report_lines.append(f"- target nodes: `{', '.join(target_labels)}`")
        critic_output = ""
        last_attempt_kind = "lean-generation"
        for lean_try in range(1, LEAN_GENERATION_RETRIES + 1):
            print(
                f"==> Chunk {chunk_number}, Lean attempt "
                f"{lean_try}/{LEAN_GENERATION_RETRIES}: generating disposable Lean "
                "(read-only model call; Lean check runs locally afterwards)",
                flush=True,
            )
            try:
                lean_result = gen_runner.run(
                    _chunk_lean_prompt(
                        args.name,
                        blueprint_source,
                        validation.nodes,
                        target_labels,
                        accepted_labels,
                        "\n\n".join(accepted_signatures),
                        accepted_imports,
                        library_context=library_context,
                        previous_lean_error=critic_output if last_attempt_kind == "lean-generation" else "",
                    ),
                    cwd=REPO_ROOT,
                    retries=0,
                )
            except RunnerError as exc:
                report_lines.append(f"- Lean attempt {lean_try}: model call failed before Lean was generated")
                report_lines.append("")
                report_lines.append("```text")
                report_lines.append(str(exc)[-4000:])
                report_lines.append("```")
                report_lines.append("")
                report_lines.append(
                    "Stopped because the read-only Lean-generation model call failed before "
                    "producing a chunk; the blueprint was not changed."
                )
                report = _write_report(args.name, report_lines)
                print(f"Lean generation model call failed: {exc}", flush=True)
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                return 1
            trial_dir = SCRATCH_DIR / args.name
            trial_dir.mkdir(parents=True, exist_ok=True)
            module_name, module_path = _chunk_module(args.name, chunk_number)
            module_path.parent.mkdir(parents=True, exist_ok=True)
            lean_path = module_path
            chunk_code = _extract_lean_code(lean_result.text).rstrip() + "\n"
            lean_code, new_imports, new_body = _compose_module_file(accepted_imports, chunk_code)
            lean_path.write_text(lean_code, encoding="utf-8")
            scratch_attempt = trial_dir / f"chunk_{chunk_number:02d}_attempt_{lean_try:02d}.lean"
            scratch_attempt.write_text(lean_code, encoding="utf-8")
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

            print(f"==> Chunk {chunk_number}: running Lean", flush=True)
            attempt = _run_lean(lean_path, lean_command)
            report_lines.append(f"- Lean attempt {lean_try}: `{scratch_attempt.relative_to(REPO_ROOT)}`")

            if attempt.ok:
                print(f"==> Chunk {chunk_number}: auditing statement alignment", flush=True)
                audit_failure = _run_statement_alignment_audit(
                    gen_runner,
                    args.name,
                    {label: validation.nodes[label] for label in target_labels},
                    lean_path,
                    paper_text,
                )
                if audit_failure is not None:
                    attempt = audit_failure
                    critic_output = attempt.output
                    last_attempt_kind = attempt.kind
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
                chunk_number += 1
                break

            critic_output = attempt.output
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

        if set(target_labels) <= accepted_labels:
            continue

        if last_attempt_kind == "lean-generation":
            report_lines.append(
                "Stopped because Lean generation failed repeatedly for the same chunk; "
                "the blueprint was not changed."
            )
            report = _write_report(args.name, report_lines)
            print(
                "Lean generation failed repeatedly; not safe to repair the blueprint from "
                "syntax/elaboration/audit errors.",
                flush=True,
            )
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return 1

        if repair_trials >= args.max_trials:
            break

        repair_trials += 1
        print(
            f"==> Blueprint repair {repair_trials}/{args.max_trials} "
            f"from chunk {chunk_number} Lean/audit output",
            flush=True,
        )
        if runner.mode == "agent":
            repair = runner.run(
                _agent_refine_prompt(args.name, blueprint_source, critic_output, repair_trials, paper_text),
                cwd=REPO_ROOT,
                retries=0,
            )
            print(f"  blueprint repair finished ({repair.duration_s:.0f}s)", flush=True)
        else:
            refine_result = runner.run(
                _api_refine_prompt(args.name, blueprint_source, critic_output, repair_trials, paper_text),
                cwd=REPO_ROOT,
                retries=1,
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
                return 1

        repaired_validation = validate_blueprint(REPO_ROOT, args.name)
        if not repaired_validation.ok:
            print_result(repaired_validation)
            report_lines.append("## Blueprint repair produced invalid structure")
            report_lines.extend(f"- {error}" for error in repaired_validation.errors)
            report = _write_report(args.name, report_lines)
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return 1

        repaired_fingerprints = _node_fingerprints(repaired_validation.nodes)
        changed = {
            label
            for label, before in current_fingerprints.items()
            if repaired_fingerprints.get(label) != before
        }
        changed |= {label for label in repaired_fingerprints if label not in current_fingerprints}
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
        else:
            print("  blueprint repair did not change parsed node text; keeping accepted chunks", flush=True)
            report_lines.append("- blueprint repair did not change parsed node text; kept accepted chunks")
        chunk_number += 1

    report_lines.append(f"Stopped after {args.max_trials} failed trial(s).")
    report = _write_report(args.name, report_lines)
    print(f"Lean did not pass after {args.max_trials} trial(s).")
    print(f"Report written to {report.relative_to(REPO_ROOT)}")
    return 1


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
        with contextlib.redirect_stdout(TeeStream(sys.stdout, log_file)), contextlib.redirect_stderr(
            TeeStream(sys.stderr, log_file)
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
