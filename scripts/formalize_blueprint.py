#!/usr/bin/env python3
"""Statements-first Lean formalization pipeline.

This is the fast successor to ``refine_blueprint_with_lean.py``. The blueprint
remains the only mathematical source of truth and Lean remains the critic; what
changes is *when* model calls happen and how much each one is asked to do:

Phase 1 (skeleton). A few batched model calls generate one Lean declaration per
blueprint node, section by section in dependency order: real bodies for
definition nodes, ``:= sorry`` proofs for theorem-like nodes. Each section is
compiled locally, compile errors are fixed in batched rounds, and the
blueprint-contract audit (deterministic coverage + one batched model audit per
section) checks the frozen statements against the node text and proof
obligations before proof effort is spent. Accepted statements are frozen: later
phases may only replace ``sorry`` bodies, never edit a statement. A statement
that cannot faithfully encode its node routes to blueprint repair, exactly as
before.

Phase 2 (proofs). For every frozen ``sorry``:
1. a deterministic tactic ladder (``rfl``/``omega``/``norm_num``/``ring``/
   ``simp``/``aesop``) runs first, with zero model cost;
2. survivors are filled by batched model calls (10-20 proofs per call);
3. the residue escalates to singleton calls at high reasoning effort;
4. persistent failures become *evidence* for a bounded blueprint repair.

Timeouts are treated as latency, never as mathematical difficulty: a timed-out
call is bisected or retried at higher effort. Only real Lean/audit output (or
an explicit NEEDS-DECOMPOSITION refusal) can trigger a blueprint repair, and
repairs invalidate downstream nodes by the full per-node blueprint contract, so
proof-sketch edits recheck the Lean that is supposed to certify them.

Published output is unchanged in meaning: ``formalization.lean`` contains no
``sorry``, passes the strict correctness audit and a from-scratch Lean check,
and has a 1-1 statement correspondence with the blueprint. ``sorry`` exists
only inside the internal scratch skeleton, which is never published.
"""
from __future__ import annotations

import argparse
import concurrent.futures
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
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

from generate_blueprint import _extract_json, read_paper
from lean_preflight import check_lean_environment
from model_runners import RunnerError, get_runner
from model_runners.api import choose_model, list_anthropic_model_ids, list_openai_model_ids
from model_runners.base import is_environment_error
from model_runners.cli import choose_codex_base_model, choose_codex_escalation_model, list_codex_model_ids
from refine_blueprint_with_lean import (
    LEAN_IDIOM_CHEATSHEET,
    FORBIDDEN_ASSUMPTIONS,
    FORBIDDEN_BLUEPRINT_STUBS,
    PLACEHOLDER_NAME_RE,
    TeeStream,
    _agent_refine_prompt,
    _alignment_failure_kind,
    _api_refine_prompt,
    _compile_module_olean,
    _compose_lean_file,
    _decomposition_note,
    _default_lean_command,
    _dependency_descendants,
    _deterministic_statement_audit,
    _extract_lean_code,
    _generated_module_dir,
    _is_timeout_error,
    _lean_declarations,
    _lean_env,
    _lean_name,
    _missing_olean_imports,
    _module_safe_name,
    _node_order,
    _node_summary,
    _node_tex_blocks,
    _nonmathlib_uses_missing_from_decl,
    _parse_decomposition_refusal,
    _publish_lean_text,
    _read_blueprint_source,
    _rebuild_site_for,
    _run_lean,
    _run_log_path,
    _search_local_lean_libraries,
    _statement_audit_prompt,
    _write_api_refinement,
    _write_report,
)
from telemetry import TelemetryRun, node_structural_features
from validate_blueprint import Node, print_result, validate_blueprint

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
SKILL_PATH = REPO_ROOT / ".claude" / "skills" / "paper-to-blueprint" / "SKILL.md"
SCRATCH_DIR = REPO_ROOT / ".auto-blueprint" / "formalization"

THEOREM_LIKE_KINDS = {"lemma", "proposition", "theorem", "corollary"}
DEFAULT_SECTION_SIZE = 24
DEFAULT_PROOF_BATCH = 12
DEFAULT_WORKERS = 3
STATEMENT_FIX_ROUNDS = 3
AUDIT_REGEN_ROUNDS = 2
TARGETED_DECL_PATCH_ROUNDS = 2
TARGETED_DECL_PATCH_MAX_LABELS = 4
SECTION_NORMALIZATION_REPAIR_TRIGGER = 1
SECTION_NORMALIZATION_MAX_CHANGED = 16
SECTION_STUCK_MAX_REPAIRS_AFTER_NORMALIZATION = 2
PROOF_SINGLETON_RETRIES = 2
LEAN_CHECK_TIMEOUT = 900
LADDER_HEARTBEATS = 400_000


def _default_fast_runner_specs() -> tuple[str, str]:
    """Default two-tier model policy for the statements-first pipeline.

    Prefer cheap hosted API calls for the wide batched skeleton/proof work, then
    reserve the stronger tier for singleton proof retries and blueprint repair.
    If no API credentials are configured, fall back to local Codex models so the
    command still works on a developer machine.
    """
    def spec(backend: str, model: str) -> str:
        return f"{backend}:{model}" if model else backend

    if os.environ.get("OPENAI_API_KEY"):
        models: list[str] = []
        with contextlib.suppress(Exception):
            models = list_openai_model_ids(timeout=5)
        return (
            spec("openai", choose_model(models, prefer=("mini", "nano"))),
            spec("openai", choose_model(models, prefer=("gpt", "o"), avoid=("mini", "nano"))),
        )
    if os.environ.get("ANTHROPIC_API_KEY"):
        models = []
        with contextlib.suppress(Exception):
            models = list_anthropic_model_ids(timeout=5)
        return (
            spec("anthropic", choose_model(models, prefer=("haiku",))),
            spec("anthropic", choose_model(models, prefer=("sonnet", "opus"), avoid=("haiku",))),
        )
    models = list_codex_model_ids(timeout=5)
    return (
        spec("codex", choose_codex_base_model(models)),
        spec("codex", choose_codex_escalation_model(models)),
    )

# Tactic ladder: cheap-first closers for the micro-lemma tail. Each entry may
# require an import; unavailable imports drop the tactic deterministically.
LADDER_IMPORTS = [
    "import Mathlib.Tactic.Ring",
    "import Mathlib.Tactic.NormNum",
    "import Aesop",
]

# Declaration starts: rbl's regex plus `instance` (skeletons may need instance
# helpers such as Fintype witnesses) with an optional name.
_DECL_START_RE = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)*"
    r"(?:(?:noncomputable|private|protected|unsafe|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)\b"
    r"(?:\s+([A-Za-z_][A-Za-z0-9_'.]*))?"
)
_DECL_PREFIX_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]?\s*|set_option\s+\S+\s+\S+\s+in\s*|/--.*-/\s*|--.*)$"
)
_TERMINAL_SORRY_RE = re.compile(r":=\s*(?:by\s+)?sorry\s*$")
_LOC_RE = re.compile(
    r"^(?P<path>[^\s].*?\.lean):(?P<line>\d+):(?P<col>\d+):\s*(?P<sev>error|warning)"
)
_FORBIDDEN_TOPLEVEL_RE = re.compile(
    r"^\s*(variable|variables|namespace|section|end|example)\b", re.MULTILINE
)

_PRINT_LOCK = threading.Lock()
_TELEMETRY_LOCK = threading.Lock()
_STATE_LOCK = threading.Lock()


def _log(message: str, *, tag: str = "") -> None:
    with _PRINT_LOCK:
        prefix = f"[{tag}] " if tag else ""
        print(f"{prefix}{message}", flush=True)


def _record(telemetry: TelemetryRun, event: str, **fields) -> None:
    with _TELEMETRY_LOCK:
        telemetry.record(event, **fields)


def _store_text(telemetry: TelemetryRun, kind: str, text: str, *, ext: str = "txt"):
    with _TELEMETRY_LOCK:
        return telemetry.store_text(kind, text, ext=ext)


# ---------------------------------------------------------------------------
# Blueprint statement extraction


def _statement_blocks(nodes: dict[str, Node]) -> dict[str, str]:
    """Per-node TeX with the trailing proof environment stripped.

    The statement block is the alignment contract for the frozen Lean
    statement. It is not the full cache contract: proof sketches also matter
    because accepted Lean is supposed to certify the blueprint proof.
    """
    blocks = _node_tex_blocks(nodes)
    return {
        label: re.sub(r"\\begin\{proof\}[\s\S]*\\end\{proof\}\s*$", "", block).strip()
        for label, block in blocks.items()
    }


def _statement_fingerprints(nodes: dict[str, Node]) -> dict[str, str]:
    return {
        label: hashlib.sha256(block.encode("utf-8")).hexdigest()
        for label, block in _statement_blocks(nodes).items()
    }


def _contract_fingerprints(nodes: dict[str, Node]) -> dict[str, str]:
    """Hash the full per-node TeX contract, including proof sketches.

    Fast-mode resume uses this broader fingerprint so a proof-prose repair does
    not silently keep Lean generated for the old proof obligation structure.
    """
    return {
        label: hashlib.sha256(block.encode("utf-8")).hexdigest()
        for label, block in _node_tex_blocks(nodes).items()
    }


def _topo_order(nodes: dict[str, Node]) -> list[str]:
    """Dependency-respecting node order, stable by blueprint source position."""
    position = {label: idx for idx, label in enumerate(_node_order(nodes))}
    indegree = {label: 0 for label in nodes}
    dependents: dict[str, list[str]] = {label: [] for label in nodes}
    for label, node in nodes.items():
        for dep in node.uses:
            if dep in nodes:
                indegree[label] += 1
                dependents[dep].append(label)
    ready = sorted((label for label, deg in indegree.items() if deg == 0), key=position.get)
    order: list[str] = []
    while ready:
        label = ready.pop(0)
        order.append(label)
        changed = False
        for dep in dependents[label]:
            indegree[dep] -= 1
            if indegree[dep] == 0:
                ready.append(dep)
                changed = True
        if changed:
            ready.sort(key=position.get)
    # Validation guarantees acyclicity; any leftover means a validator bug.
    order.extend(label for label in position if label not in set(order))
    return order


def _partition_sections(
    nodes: dict[str, Node], pending: set[str], section_size: int
) -> list[list[str]]:
    """Contiguous topo-order groups so every dependency lives in an earlier
    section, an already-frozen section, or Mathlib."""
    sections: list[list[str]] = []
    current: list[str] = []
    for label in _topo_order(nodes):
        if label not in pending or nodes[label].mathlibok:
            continue
        current.append(label)
        if len(current) >= section_size:
            sections.append(current)
            current = []
    if current:
        sections.append(current)
    return sections


# ---------------------------------------------------------------------------
# Lean module parsing / composition


@dataclass
class DeclBlock:
    kind: str
    name: str | None
    text: str


@dataclass
class ParsedModule:
    imports: list[str]
    preamble: list[str]
    decls: list[DeclBlock]


@dataclass
class SkeletonFinding:
    """One Phase-1 skeleton audit finding, optionally tied to one blueprint node.

    Targeted findings let Phase 1 ask the model to replace only the bad Lean
    declaration instead of regenerating or repairing a whole section.
    """

    message: str
    label: str | None = None
    lean_name: str | None = None


def _parse_module(code: str) -> ParsedModule:
    lines = code.splitlines()
    imports: list[str] = []
    body_lines: list[tuple[int, str]] = []
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("import "):
            if stripped not in imports:
                imports.append(stripped)
            continue
        if stripped in {
            "set_option autoImplicit false",
            "set_option linter.unusedVariables false",
        }:
            continue
        body_lines.append((idx, line))

    starts: list[int] = []  # indices into body_lines
    for pos, (_orig, line) in enumerate(body_lines):
        if _DECL_START_RE.match(line):
            start = pos
            while start > 0 and _DECL_PREFIX_RE.match(body_lines[start - 1][1]):
                start -= 1
            if not starts or start > starts[-1]:
                starts.append(start)

    preamble = [
        line for _orig, line in body_lines[: starts[0] if starts else len(body_lines)]
        if line.strip()
    ]
    decls: list[DeclBlock] = []
    for i, start in enumerate(starts):
        end = starts[i + 1] if i + 1 < len(starts) else len(body_lines)
        text = "\n".join(line for _orig, line in body_lines[start:end]).strip()
        match = next(
            (
                _DECL_START_RE.match(line)
                for _orig, line in body_lines[start:end]
                if _DECL_START_RE.match(line)
            ),
            None,
        )
        decls.append(
            DeclBlock(
                kind=match.group(1) if match else "def",
                name=match.group(2) if match else None,
                text=text,
            )
        )
    return ParsedModule(imports=imports, preamble=preamble, decls=decls)


def _compose_module(
    imports: list[str], preamble: list[str], decl_texts: list[str]
) -> tuple[str, list[tuple[int, int]]]:
    """Compose a module file; return (text, per-decl (start,end) 1-based line ranges)."""
    lines: list[str] = []
    seen: set[str] = set()
    for item in imports:
        if item not in seen:
            seen.add(item)
            lines.append(item)
    if not lines:
        lines.append("import Mathlib.Data.Real.Basic")
    lines += ["", "set_option autoImplicit false", "set_option linter.unusedVariables false", ""]
    lines += [line for line in preamble if line.strip()]
    if preamble:
        lines.append("")
    ranges: list[tuple[int, int]] = []
    for text in decl_texts:
        start = len(lines) + 1
        decl_lines = text.splitlines()
        lines.extend(decl_lines)
        ranges.append((start, len(lines)))
        lines.append("")
    return "\n".join(lines) + "\n", ranges


def _has_terminal_sorry(decl_text: str) -> bool:
    return bool(_TERMINAL_SORRY_RE.search(decl_text.rstrip()))


def _normalize_terminal_sorry(decl_text: str) -> str:
    return _TERMINAL_SORRY_RE.sub(":= sorry", decl_text.rstrip())


def _splice_proof(decl_text: str, proof: str) -> str:
    """Replace a terminal ``:= sorry`` with a ``by`` proof; statement untouched."""
    base = _TERMINAL_SORRY_RE.sub("", decl_text.rstrip()).rstrip()
    if base.endswith(":="):
        base = base[: -len(":=")].rstrip()
    return f"{base} := {proof.strip()}"


def _extract_by_proof(model_decl_text: str) -> str | None:
    """Pull the ``by ...`` proof out of a model-returned declaration.

    Only the proof is ever used; the frozen statement in our module is the one
    that gets compiled, so a model that silently reshapes the statement cannot
    smuggle the change in.
    """
    match = re.search(r":=\s*(by\b[\s\S]*)", model_decl_text)
    if match is None:
        return None
    proof = match.group(1).strip()
    return proof or None


def _errors_by_decl(
    output: str, file_name: str, ranges: list[tuple[int, int]]
) -> tuple[dict[int, list[str]], list[str]]:
    """Group Lean error messages by declaration index; extras are file-level."""
    records: list[tuple[int, str]] = []
    current: list[str] | None = None
    current_line = 0
    for line in output.splitlines():
        match = _LOC_RE.match(line)
        if match:
            if current is not None:
                records.append((current_line, "\n".join(current)))
            if match.group("sev") == "error" and file_name in match.group("path"):
                current = [line]
                current_line = int(match.group("line"))
            else:
                current = None
        elif current is not None:
            current.append(line)
    if current is not None:
        records.append((current_line, "\n".join(current)))

    by_decl: dict[int, list[str]] = {}
    file_level: list[str] = []
    for line_no, text in records:
        idx = next(
            (i for i, (start, end) in enumerate(ranges) if start <= line_no <= end), None
        )
        if idx is None:
            file_level.append(text)
        else:
            by_decl.setdefault(idx, []).append(text)
    return by_decl, file_level


def _check_lean(path: Path, lean_command: list[str], *, timeout: int = LEAN_CHECK_TIMEOUT) -> tuple[bool, str]:
    """Compile a module, allowing sorry warnings (skeleton phase only)."""
    proc = subprocess.Popen(
        lean_command + [str(path)],
        cwd=str(REPO_ROOT),
        env=_lean_env(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    start = time.time()
    while True:
        try:
            stdout, stderr = proc.communicate(timeout=30)
            break
        except subprocess.TimeoutExpired:
            elapsed = int(time.time() - start)
            if elapsed >= timeout:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = proc.communicate()
                combined = "\n".join(p for p in (stdout or "", stderr or "") if p)
                return False, f"Lean check timed out after {timeout}s.\n{combined}"
    combined = "\n".join(p for p in (stdout or "", stderr or "") if p)
    return proc.returncode == 0, combined


def _skeleton_code_findings(
    code: str, target_kinds: dict[str, str], label_by_lean_name: dict[str, str]
) -> list[SkeletonFinding]:
    """Correctness audit variant for the skeleton phase.

    Like ``_audit_lean_code`` but ``sorry`` is legal exactly as the terminal
    proof of a theorem-like declaration; everywhere else (definition bodies,
    preamble, mid-proof) it is rejected.
    """
    findings: list[SkeletonFinding] = []

    def decl_finding(name: str | None, message: str) -> SkeletonFinding:
        return SkeletonFinding(
            message=message,
            label=label_by_lean_name.get(name or ""),
            lean_name=name,
        )

    if re.search(r"\badmit\b|by\s*\?", code):
        findings.append(SkeletonFinding("contains a forbidden placeholder (`admit` or `by ?`)"))
    if "set_option autoImplicit true" in code:
        findings.append(SkeletonFinding("enables `autoImplicit`"))
    bad = [f"{kind} {name}" for kind, name in FORBIDDEN_ASSUMPTIONS.findall(code)]
    if bad:
        findings.append(
            SkeletonFinding(
                f"uses top-level assumptions instead of implementations: {', '.join(bad[:12])}"
            )
        )
    invented = sorted(set(FORBIDDEN_BLUEPRINT_STUBS.findall(code)))
    if invented:
        findings.append(
            SkeletonFinding(f"calls invented paper/blueprint helpers: {', '.join(invented[:12])}")
        )
    if _FORBIDDEN_TOPLEVEL_RE.search(code):
        findings.append(
            SkeletonFinding(
                "contains top-level `variable`/`namespace`/`section`/`example` commands; "
                "each declaration must be self-contained"
            )
        )
    parsed = _parse_module(code)
    # Comment-aware preamble lint. Lean block comments (`/- ... -/`, including
    # doc comments) span lines and nest; a continuation line of a multi-line
    # comment is comment TEXT, not a command. Flagging it produced an
    # unfixable false positive: the model's file was valid Lean, so identical
    # regens looped until the round budget was exhausted.
    comment_depth = 0
    for line in parsed.preamble:
        stripped = line.strip()
        inside_comment = comment_depth > 0
        if not inside_comment and not stripped.startswith("--"):
            if stripped and not stripped.startswith(("open", "/-")):
                findings.append(
                    SkeletonFinding(f"unexpected non-`open` preamble command: `{stripped[:80]}`")
                )
        # Track block-comment depth. `--` starts a line comment (its content
        # has no delimiter meaning) unless we are already inside a block
        # comment, where `--` is plain text and `-/` still closes.
        if inside_comment or not stripped.startswith("--"):
            comment_depth += stripped.count("/-") - stripped.count("-/")
            if comment_depth < 0:
                comment_depth = 0
    for decl in parsed.decls:
        if "sorry" not in decl.text:
            continue
        expected_kind = target_kinds.get(decl.name or "")
        if expected_kind in THEOREM_LIKE_KINDS and _has_terminal_sorry(decl.text):
            inner = _TERMINAL_SORRY_RE.sub("", decl.text)
            if re.search(r"\bsorry\b", inner):
                findings.append(
                    decl_finding(decl.name, f"`{decl.name}` uses sorry outside the terminal proof position")
                )
            continue
        findings.append(
            decl_finding(
                decl.name,
                f"`{decl.name or decl.kind}` contains sorry but is not a theorem-like "
                "blueprint target; definition bodies and helpers must be complete",
            )
        )
    for decl in parsed.decls:
        name = decl.name or ""
        if PLACEHOLDER_NAME_RE.search(name):
            findings.append(decl_finding(name, f"placeholder declaration name `{name}`"))
        if decl.kind in {"def", "abbrev"} and re.search(r":\s*Prop\s*:=\s*True\b", decl.text):
            findings.append(decl_finding(name, f"`{name}` defines a proposition as `True`"))
        if decl.kind in {"theorem", "lemma"} and re.search(r":\s*True\s*:=", decl.text):
            findings.append(decl_finding(name, f"`{name}` proves only `True`"))
    return findings


def _skeleton_code_issues(code: str, target_kinds: dict[str, str]) -> list[str]:
    return [finding.message for finding in _skeleton_code_findings(code, target_kinds, {})]


def _format_skeleton_findings(findings: list[SkeletonFinding]) -> str:
    lines: list[str] = []
    for finding in findings:
        prefix = ""
        if finding.label and finding.lean_name:
            prefix = f"{finding.label} / `{finding.lean_name}`: "
        elif finding.label:
            prefix = f"{finding.label}: "
        elif finding.lean_name:
            prefix = f"`{finding.lean_name}`: "
        lines.append(prefix + finding.message)
    return "Deterministic skeleton audit rejected the file:\n- " + "\n- ".join(lines)


def _skeleton_finding_class(message: str) -> str:
    """Stable, paper-independent class for deterministic skeleton routing."""
    if "missing generated declaration" in message:
        return "missing_decl"
    if "placeholder declaration name" in message:
        return "placeholder_name"
    if "outside the terminal proof position" in message:
        return "nonterminal_sorry"
    if "contains sorry but is not a theorem-like" in message:
        return "non_theorem_sorry"
    if "does not mention required dependency" in message:
        return "missing_dependency_mention"
    if "is a definition but generated" in message:
        return "wrong_kind"
    if "is theorem-like but generated" in message:
        return "wrong_kind"
    if "forbidden placeholder" in message:
        return "forbidden_placeholder"
    if "invented paper/blueprint helpers" in message:
        return "invented_helper"
    if "unexpected non-`open` preamble" in message or "top-level" in message:
        return "bad_file_shape"
    return "other"


def _skeleton_findings_fingerprint(findings: list[SkeletonFinding]) -> tuple[tuple[str, str, str, str], ...]:
    """Deterministic stagnation key for Phase 1 audit failures.

    If this key is unchanged after a model patch, the model call did not move
    the section toward acceptance; route to a smaller/escalated attempt instead
    of repeating the same patch/regenerate cycle.
    """
    return tuple(
        sorted(
            (
                finding.label or "",
                finding.lean_name or "",
                _skeleton_finding_class(finding.message),
                finding.message,
            )
            for finding in findings
        )
    )


def _dependency_closed_subset(ctx: Ctx, labels: list[str], targets: list[str]) -> list[str]:
    """Smallest original-order subset containing targets and same-section deps."""
    label_set = set(labels)
    needed: set[str] = set()

    def visit(label: str) -> None:
        if label in needed or label not in label_set:
            return
        needed.add(label)
        node = ctx.nodes.get(label)
        if node is None:
            return
        for dep in sorted(node.uses):
            if dep in label_set:
                visit(dep)

    for label in targets:
        visit(label)
    return [label for label in labels if label in needed]


# ---------------------------------------------------------------------------
# Model call plumbing


@dataclass
class CallResult:
    status: str  # ok | timeout | error
    text: str = ""
    error: str = ""
    duration_s: float = 0.0


class RepairRequest(Exception):
    """Raised when only a blueprint edit can unblock progress."""

    def __init__(
        self,
        evidence: str,
        labels: list[str],
        *,
        decomposition_helpers: list[str] | None = None,
        section_labels: list[str] | None = None,
    ):
        super().__init__(evidence[:500])
        self.evidence = evidence
        self.labels = labels
        self.decomposition_helpers = decomposition_helpers or []
        self.section_labels = section_labels or list(labels)


@dataclass
class SectionStuckState:
    """Tracks a repeatedly failing Phase-1 section across blueprint edits."""

    labels: set[str]
    repairs: int = 0
    normalized: bool = False
    repairs_after_normalization: int = 0


class SectionNormalizationRejected(RuntimeError):
    """A normalization attempt was rolled back and should not stop the run."""


@dataclass
class Ctx:
    name: str
    runner_spec: str
    escalation_runner_spec: str
    base_effort: str | None
    escalation_effort: str | None
    base_timeout: int
    hard_timeout: int
    lean_command: list[str]
    telemetry: TelemetryRun
    paper_text: str
    library_context: str
    section_size: int
    proof_batch: int
    use_ladder: bool
    # Run-scoped adaptive Phase-1 section size: starts at section_size, halves
    # when a skeleton call times out (see _freeze_section), and creeps back up
    # after consecutive clean sections (see _run_phase1). 0 = not initialized.
    effective_section_size: int = 0
    # Largest size at which a group froze without a timeout-shrink this run.
    # Recovery back up to this size is fast (doubling per clean group);
    # exploring beyond it uses the cautious rule.
    proven_section_size: int = 0
    nodes: dict[str, Node] = field(default_factory=dict)
    stmt_blocks: dict[str, str] = field(default_factory=dict)
    tex_blocks: dict[str, str] = field(default_factory=dict)
    stmt_fps: dict[str, str] = field(default_factory=dict)
    contract_fps: dict[str, str] = field(default_factory=dict)
    unavailable_imports: set[str] = field(default_factory=set)

    def refresh_nodes(self, nodes: dict[str, Node]) -> None:
        self.nodes = nodes
        self.stmt_blocks = _statement_blocks(nodes)
        self.tex_blocks = _node_tex_blocks(nodes)
        self.stmt_fps = _statement_fingerprints(nodes)
        self.contract_fps = _contract_fingerprints(nodes)


def _make_runner(
    spec: str,
    *,
    timeout: int,
    readonly: bool,
    effort: str | None,
    with_skill: bool = False,
    resume_session_id: str | None = None,
):
    kwargs = {}
    if spec.partition(":")[0] == "codex" and effort:
        kwargs["reasoning_effort"] = effort
    return get_runner(
        spec,
        context_files=[SKILL_PATH] if with_skill else None,
        timeout=timeout,
        readonly=readonly,
        resume_session_id=resume_session_id,
        **kwargs,
    )


def _call_model(
    ctx: Ctx,
    prompt: str,
    *,
    purpose: str,
    timeout: int,
    effort: str | None,
    labels: list[str],
    readonly: bool = True,
    escalated: bool = False,
    tag: str = "",
    sessions: dict[str, str] | None = None,
) -> CallResult:
    """One model call. When ``sessions`` is given (a per-lifecycle dict keyed
    by runner spec), the call resumes that spec's backend session so follow-up
    calls keep the context they already built (claude-code and codex support
    this; other backends ignore it). Successful calls update the dict; failed
    or timed-out calls drop the session so the next call starts clean."""
    runner_spec = ctx.escalation_runner_spec if escalated else ctx.runner_spec
    resume_session_id = sessions.get(runner_spec) if sessions is not None else None
    runner = _make_runner(
        runner_spec,
        timeout=timeout,
        readonly=readonly,
        effort=effort,
        resume_session_id=resume_session_id,
    )
    prompt_artifact = _store_text(ctx.telemetry, f"prompt_{purpose}", prompt)
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        if sessions is not None:
            sessions.pop(runner_spec, None)
        duration = time.monotonic() - started
        _record(
            ctx.telemetry,
            "model_call",
            purpose=purpose,
            labels=labels,
            status="error",
            duration_s=duration,
            timeout_s=timeout,
            effort=effort or "",
            backend=runner.backend_name,
            model=runner.model,
            resumed_session=bool(resume_session_id),
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
        )
        if is_environment_error(exc):
            raise
        status = "timeout" if _is_timeout_error(exc) else "error"
        _log(f"model call ({purpose}) {status}: {str(exc)[:160]}", tag=tag)
        return CallResult(status=status, error=str(exc), duration_s=duration)
    if sessions is not None:
        if result.session_id:
            sessions[runner_spec] = result.session_id
        else:
            sessions.pop(runner_spec, None)
    response_artifact = _store_text(ctx.telemetry, f"response_{purpose}", result.text)
    _record(
        ctx.telemetry,
        "model_call",
        purpose=purpose,
        labels=labels,
        status="success",
        duration_s=result.duration_s,
        timeout_s=timeout,
        effort=effort or "",
        backend=result.backend,
        model=result.model,
        resumed_session=bool(resume_session_id),
        prompt=prompt_artifact.to_event(REPO_ROOT),
        response=response_artifact.to_event(REPO_ROOT),
    )
    return CallResult(status="ok", text=result.text, duration_s=result.duration_s)


# ---------------------------------------------------------------------------
# Persistent skeleton state


@dataclass
class Section:
    number: int
    labels: list[str]
    path: Path
    module: str
    import_modules: list[str]

    @property
    def file_name(self) -> str:
        return self.path.name


def _state_path(name: str) -> Path:
    return SCRATCH_DIR / name / "skeleton_state.json"


def _section_module(name: str, number: int) -> tuple[str, Path]:
    base = _module_safe_name(name)
    module = f"AutoBlueprint.Generated.{base}.Skeleton{number:02d}"
    path = REPO_ROOT / "AutoBlueprint" / "Generated" / base / f"Skeleton{number:02d}.lean"
    return module, path


def _save_state(
    name: str,
    sections: list[Section],
    stmt_fps: dict[str, str],
    contract_fps: dict[str, str],
) -> None:
    entries = []
    for sec in sections:
        try:
            sha = hashlib.sha256(sec.path.read_bytes()).hexdigest()
        except OSError:
            continue
        entries.append(
            {
                "number": sec.number,
                "file": sec.file_name,
                "module": sec.module,
                "labels": sec.labels,
                "import_modules": sec.import_modules,
                "sha256": sha,
                "statement_fps": {label: stmt_fps.get(label, "") for label in sec.labels},
                "contract_fps": {label: contract_fps.get(label, "") for label in sec.labels},
            }
        )
    path = _state_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"version": 1, "sections": entries}, indent=2) + "\n", encoding="utf-8")


def _load_state(ctx: Ctx, lean_command: list[str]) -> list[Section]:
    """Resume: keep sections whose file and blueprint contracts are unchanged.

    Any dropped label cascades to its blueprint descendants and to sections
    importing a dropped module, because their frozen statements may reference
    declarations that no longer exist or changed meaning.
    """
    try:
        payload = json.loads(_state_path(ctx.name).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    entries = payload.get("sections") or []
    generated_dir = _generated_module_dir(ctx.name)

    kept: list[Section] = []
    dropped_labels: set[str] = set()
    dropped_modules: set[str] = set()
    for entry in entries:
        path = generated_dir / str(entry.get("file") or "")
        labels = [str(label) for label in entry.get("labels") or []]
        stmt_fps = entry.get("statement_fps") or {}
        contract_fps = entry.get("contract_fps") or {}
        ok = (
            path.is_file()
            and labels
            and all(
                label in ctx.nodes
                and ctx.stmt_fps.get(label) == stmt_fps.get(label)
                and ctx.contract_fps.get(label) == contract_fps.get(label)
                for label in labels
            )
            and not any(dep in dropped_modules for dep in entry.get("import_modules") or [])
        )
        if ok:
            invalidated = _dependency_descendants(ctx.nodes, dropped_labels) - dropped_labels
            ok = not (set(labels) & invalidated)
        if ok and hashlib.sha256(path.read_bytes()).hexdigest() != entry.get("sha256"):
            # The file changed after the last state save (e.g. proofs were
            # spliced right before a crash). The full blueprint contracts still
            # match, so salvage instead of discarding: all labels must still
            # have declarations and the module must recompile.
            code = path.read_text(encoding="utf-8")
            decls = _lean_declarations(code)
            ok = all(_lean_name(label) in decls for label in labels)
            if ok:
                ok, _output = _check_lean(path, lean_command)
            if ok:
                _log(f"resume: salvaged modified section {path.name} (recompiled clean)")
        if not ok:
            dropped_labels.update(labels)
            dropped_modules.add(str(entry.get("module") or ""))
            for artifact in (path, path.with_suffix(".olean")):
                with contextlib.suppress(FileNotFoundError, OSError):
                    artifact.unlink()
            continue
        sec = Section(
            number=int(entry.get("number") or 0),
            labels=labels,
            path=path,
            module=str(entry.get("module") or ""),
            import_modules=[str(m) for m in entry.get("import_modules") or []],
        )
        if not path.with_suffix(".olean").is_file():
            attempt = _compile_module_olean(path, lean_command)
            if not attempt.ok:
                dropped_labels.update(labels)
                dropped_modules.add(sec.module)
                with contextlib.suppress(FileNotFoundError, OSError):
                    path.unlink()
                continue
        kept.append(sec)
    if dropped_labels:
        _log(f"resume: dropped {len(dropped_labels)} stale label(s); kept {len(kept)} section(s)")
    return kept


def _prune_stale_generated(ctx: Ctx, kept: list[Section]) -> None:
    """Remove generated Lean artifacts not owned by a kept section.

    Fresh runs rmtree the generated dir; this is the ``--continue`` analog.
    Stale files are actively harmful, not just clutter: agent runners glob the
    generated dir and mine old implementations (e.g. legacy ChunkNN modules
    from the per-chunk pipeline) whose statements predate blueprint repairs —
    burning call budget on exploration and risking stale formulations being
    copied into new sections. Only the pipeline's own artifact patterns are
    touched; anything else in the directory is left alone.
    """
    generated_dir = _generated_module_dir(ctx.name)
    if not generated_dir.is_dir():
        return
    owned = {sec.path.resolve() for sec in kept}
    owned |= {sec.path.with_suffix(".olean").resolve() for sec in kept}
    removed: list[str] = []
    for pattern in ("Chunk*.lean", "Chunk*.olean", "Skeleton*.lean", "Skeleton*.olean"):
        for artifact in sorted(generated_dir.glob(pattern)):
            if artifact.resolve() in owned:
                continue
            with contextlib.suppress(FileNotFoundError, OSError):
                artifact.unlink()
                removed.append(artifact.name)
    if removed:
        _log(
            f"pruned {len(removed)} stale generated artifact(s): "
            + ", ".join(removed[:8])
            + ("..." if len(removed) > 8 else "")
        )
        _record(
            ctx.telemetry,
            "stale_artifacts_pruned",
            count=len(removed),
            files=removed,
        )


def _frozen_labels(sections: list[Section]) -> set[str]:
    return {label for sec in sections for label in sec.labels}


def _proved_labels(sections: list[Section]) -> set[str]:
    proved: set[str] = set()
    for sec in sections:
        try:
            parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        except OSError:
            continue
        by_name = {decl.name: decl for decl in parsed.decls if decl.name}
        for label in sec.labels:
            decl = by_name.get(_lean_name(label))
            if decl is not None and not _has_terminal_sorry(decl.text):
                proved.add(label)
    return proved


def _sections_for_deps(ctx: Ctx, labels: list[str], sections: list[Section]) -> list[str]:
    """Skeleton modules a new section must import: owners of transitive deps."""
    owner = {label: sec.module for sec in sections for label in sec.labels}
    needed: set[str] = set()
    stack = list(labels)
    seen: set[str] = set()
    while stack:
        label = stack.pop()
        if label in seen:
            continue
        seen.add(label)
        for dep in ctx.nodes.get(label, Node(label, "", Path("."), 0)).uses:
            if dep in owner:
                needed.add(owner[dep])
            if dep in ctx.nodes:
                stack.append(dep)
    return sorted(needed)


# Terminal tactic/sorry proof on a theorem-like declaration; everything before
# it is the statement, which is the declaration's entire interface.
_TERMINAL_PROOF_RE = re.compile(r":=\s*(?:by\b[\s\S]*|sorry\s*)\Z")
# Per-declaration cap for definition-kind interface text. Generated skeleton
# bodies are one-node-sized, so this triggers rarely; it exists so one huge
# body cannot evict whole modules from the digest budget.
_INTERFACE_DECL_CAP = 2400

FROZEN_INTERFACE_NOTE = """\
This interface listing is generated deterministically from the frozen skeleton
files and is COMPLETE for the modules it covers — including structure fields
and definition bodies. Do NOT spend budget re-reading Skeleton*.lean or any
generated Lean files to rediscover names, signatures, or fields: everything
referenceable is below. It is an interface reference ONLY. The blueprint TeX
is the sole mathematical source of truth, and the Lean you write exists to
certify the blueprint — not to be self-consistent Lean on its own terms.
Derive every statement 1-1 from the blueprint node text; use this interface
solely to spell frozen dependencies with their exact names, types, and fields.
If this interface ever seems to conflict with the blueprint, follow the
blueprint and surface the mismatch — never adapt the mathematics to the Lean."""


def _decl_interface_text(decl) -> str:
    """One declaration's interface: full text for definition kinds (their body
    IS their meaning), statement-only for theorem kinds (their proof is not
    part of the interface, and in the skeleton is usually `sorry` anyway)."""
    text = decl.text.strip()
    if decl.kind in {"theorem", "lemma"}:
        stripped = _TERMINAL_PROOF_RE.sub("", text).rstrip()
        if stripped != text:
            return stripped
        head = text.split(":=", 1)[0].rstrip()
        return head
    if len(text) > _INTERFACE_DECL_CAP:
        return text[:_INTERFACE_DECL_CAP].rstrip() + "\n-- ... body truncated; the name and signature above are frozen"
    return text


def _frozen_interface_digest(sections: list[Section], modules: list[str], *, budget: int = 24000) -> str:
    """Complete, module-grouped interface digest of the frozen declarations in
    ``modules``. Budgeting is module-granular: when over budget, the OLDEST
    modules are dropped whole and named explicitly — never a silent mid-
    declaration cut (a truncated structure is worse than an omitted one,
    because the model then re-reads files to fill the gap)."""
    blocks: list[tuple[str, str]] = []
    for sec in sections:
        if sec.module not in modules:
            continue
        try:
            code = sec.path.read_text(encoding="utf-8")
        except OSError:
            continue
        parts = [_decl_interface_text(decl) for decl in _lean_declarations(code).values()]
        body = "\n\n".join(part for part in parts if part)
        if body:
            blocks.append((sec.module, f"-- ==== {sec.module} (frozen) ====\n{body}"))
    total = sum(len(text) + 2 for _, text in blocks)
    omitted: list[str] = []
    while len(blocks) > 1 and total > budget:
        module, text = blocks.pop(0)
        omitted.append(module)
        total -= len(text) + 2
    digest = "\n\n".join(text for _, text in blocks)
    if omitted:
        digest = (
            "-- NOTE: for space, interfaces of these older imported modules are omitted:\n"
            f"-- {', '.join(omitted)}\n"
            "-- Their declarations are still imported and frozen; any of their names used\n"
            "-- by the modules below can be referenced as-is.\n\n" + digest
        )
    return digest


# ---------------------------------------------------------------------------
# Prompts


def _common_rules(ctx: Ctx) -> str:
    unavailable = ""
    if ctx.unavailable_imports:
        unavailable = (
            "\nUnavailable imports (no compiled .olean locally; NEVER import these):\n"
            + "\n".join(f"- {item}" for item in sorted(ctx.unavailable_imports))
        )
    return f"""Hard constraints:
- The blueprint TeX below is the only mathematical source of truth. Formalize
  each node's statement EXACTLY as written: same objects, same hypotheses, same
  claims. Do not weaken, strengthen, or substitute an adjacent formulation.
- Give each blueprint node exactly the Lean name listed for it.
- No `sorry` outside the places these instructions explicitly allow, and never
  `admit`, `by ?`, `axiom`, `constant`, or `opaque`.
- No invented helpers that merely assert a paper result (`foo_from_paper`,
  author-year names, etc.). Every name must come from an imported library, this
  file, or an earlier accepted skeleton module.
- No top-level `variable`/`namespace`/`section`/`example` commands. Each
  declaration must be self-contained. Preamble may only contain `open` lines.
- Import only the specific modules you need; never blanket `import Mathlib` or
  `import AutoBlueprint`.
- If a node CANNOT be faithfully formalized as stated (it needs helper nodes
  the blueprint does not have), do NOT emit weakened Lean. Return, as your
  entire reply, one line:
  NEEDS-DECOMPOSITION: {{"label": "<node label>", "missing_helpers": ["<each needed helper statement>"], "reason": "<why>"}}
{unavailable}

Local Lean library candidates (module paths verified by deterministic search):
{ctx.library_context or "- none found"}

Lean API idioms:
{LEAN_IDIOM_CHEATSHEET}"""


def _skeleton_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    feedback: str = "",
    previous_code: str = "",
    timeout_s: int = 0,
) -> str:
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"uses [{', '.join(sorted(ctx.nodes[label].uses)) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:5000]}\n```"
        for label in labels
    )
    feedback_block = ""
    if feedback:
        previous_block = (
            f"\nYour previous file (START FROM IT; change only what the feedback requires):\n"
            f"```lean\n{previous_code[:45000]}\n```\n"
            if previous_code
            else ""
        )
        feedback_block = f"""

Previous attempt feedback (fix ALL of it; statements may still be adjusted at
this phase, but only to encode the SAME blueprint content correctly):
```text
{feedback[-14000:]}
```
{previous_block}"""
    signatures = _frozen_interface_digest(sections, import_modules, budget=24000)
    return f"""TASK: BLUEPRINT-SKELETON-SECTION

Return exactly one Lean 4 file (one code block). No commentary.

Generate ONE declaration per target node listed below — statements only:
- definition-kind nodes: complete `def`/`structure`/`inductive` with real
  bodies (a definition's body IS its statement; `sorry` is forbidden there);
- theorem-like nodes (lemma/proposition/theorem/corollary): the exact statement
  with the proof deferred as `:= sorry`. You MAY give a full proof instead only
  when it is a one-liner you are certain of; if unsure, use `:= sorry`.
- You may add a small concrete helper `def`/`instance` (e.g. a Fintype
  instance) when a statement genuinely needs it. Helpers must be complete.
- Order declarations so nothing is used before it is declared.
- A statement should visibly use the generated Lean declarations of the
  definition nodes it `uses`; imports of earlier skeleton modules make them
  available (do not redefine them).
- This call has a wall-clock budget of about {timeout_s}s.

{_common_rules(ctx)}
{feedback_block}

Blueprint name: {ctx.name}

Available imports for earlier accepted skeleton declarations:
```lean
{chr(10).join(f'import {m}' for m in import_modules) or '-- none'}
```

Frozen Lean interface of those modules (use these exact names; never redefine).
{FROZEN_INTERFACE_NOTE}
```lean
{signatures or '-- none'}
```

Whole blueprint node graph (orientation only):
{_node_summary(ctx.nodes)}

Target nodes for THIS file:
{target_text}
"""


def _targeted_skeleton_patch_prompt(
    ctx: Ctx,
    patch_labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    module_code: str,
    findings: list[SkeletonFinding],
    *,
    timeout_s: int,
) -> str:
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"uses [{', '.join(sorted(ctx.nodes[label].uses)) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:5000]}\n```"
        for label in patch_labels
    )
    relevant = [
        finding
        for finding in findings
        if finding.label in set(patch_labels) or finding.lean_name in {_lean_name(label) for label in patch_labels}
    ]
    signatures = _frozen_interface_digest(sections, import_modules, budget=12000)
    return f"""TASK: PATCH-BLUEPRINT-SKELETON-DECLARATIONS

Return exactly one Lean 4 code block. No commentary.

The large skeleton section below was generated in one batch. Most of it may be
usable. Replace ONLY the target declaration(s) listed below so the whole section
can pass the deterministic skeleton audit.

Rules:
- Return replacement declarations only; do not return the whole file.
- For each target blueprint node, include exactly one declaration with the
  required Lean name.
- Definition-kind nodes must have real bodies; `sorry` is forbidden there.
- Theorem-like nodes may end with terminal `:= sorry`.
- The replacement statement must still encode the same blueprint node. Do not
  weaken, abstract away, or replace it with `True`.
- If a replacement must use another blueprint node listed in `uses`, visibly
  mention that node's generated Lean name.
- You may include a small complete helper declaration immediately before a
  replacement only if the replacement genuinely needs it.
- This call has a wall-clock budget of about {timeout_s}s.

{_common_rules(ctx)}

Blueprint name: {ctx.name}

Available imports for earlier accepted skeleton declarations:
```lean
{chr(10).join(f'import {m}' for m in import_modules) or '-- none'}
```

Frozen Lean interface of those modules (complete; do not re-read skeleton files):
```lean
{signatures or '-- none'}
```

Deterministic audit findings to fix:
```text
{_format_skeleton_findings(relevant)[-10000:]}
```

Current section file:
```lean
{module_code[:50000]}
```

Target blueprint nodes to patch:
{target_text}
"""


def _patchable_skeleton_labels(findings: list[SkeletonFinding], labels: list[str]) -> list[str]:
    """Return the small set of labels worth repairing in-place.

    Global file-shape problems still use the existing whole-section retry path.
    Targeted replacement is for declaration-local deterministic failures only.
    """
    section_labels = set(labels)
    targeted = [finding.label for finding in findings if finding.label in section_labels]
    if not targeted:
        return []
    if any(finding.label is None for finding in findings):
        return []
    ordered = [label for label in labels if label in set(targeted)]
    if len(ordered) > TARGETED_DECL_PATCH_MAX_LABELS:
        return []
    return ordered


def _apply_skeleton_replacements(
    parsed: ParsedModule, labels: list[str], patch_labels: list[str], replacement_code: str
) -> ParsedModule | None:
    """Merge replacement declarations into a generated section.

    The section remains a section: this only swaps or inserts declarations for
    the listed target labels. Helpers returned by the model are kept, but the
    caller re-runs the deterministic audit on the whole module before freezing.
    """
    patch_parsed = _parse_module(replacement_code)
    target_names = {_lean_name(label) for label in labels}
    patch_names = {_lean_name(label) for label in patch_labels}
    replacements = {decl.name: decl for decl in patch_parsed.decls if decl.name in patch_names}
    if set(replacements) != patch_names:
        return None

    helper_decls = [
        decl
        for decl in patch_parsed.decls
        if decl.name and decl.name not in patch_names and decl.name not in target_names
    ]
    original = list(parsed.decls)

    helper_inserted = False
    used_replacements: set[str] = set()
    new_decls: list[DeclBlock] = []
    for decl in original:
        if decl.name in patch_names:
            if not helper_inserted:
                new_decls.extend(helper_decls)
                helper_inserted = True
            new_decls.append(replacements[decl.name])
            used_replacements.add(decl.name)
        else:
            new_decls.append(decl)

    for label in patch_labels:
        lean_name = _lean_name(label)
        if lean_name in used_replacements:
            continue
        insert_at = None
        label_pos = labels.index(label)
        for previous in reversed(labels[:label_pos]):
            idx = next((i for i, decl in enumerate(new_decls) if decl.name == _lean_name(previous)), None)
            if idx is not None:
                insert_at = idx + 1
                break
        if insert_at is None:
            for following in labels[label_pos + 1 :]:
                idx = next((i for i, decl in enumerate(new_decls) if decl.name == _lean_name(following)), None)
                if idx is not None:
                    insert_at = idx
                    break
        if insert_at is None:
            insert_at = len(new_decls)
        if not helper_inserted:
            new_decls[insert_at:insert_at] = helper_decls
            helper_inserted = True
            insert_at += len(helper_decls)
        new_decls.insert(insert_at, replacements[lean_name])
        used_replacements.add(lean_name)

    # Drop obsolete duplicate target declarations if a missing-declaration patch
    # inserted one while an unnamed malformed declaration remained nearby.
    seen_targets: set[str] = set()
    deduped: list[DeclBlock] = []
    for decl in new_decls:
        if decl.name in target_names:
            if decl.name in seen_targets:
                continue
            seen_targets.add(decl.name)
        deduped.append(decl)
    return ParsedModule(imports=parsed.imports, preamble=parsed.preamble, decls=deduped)


def _targeted_patch_skeleton_decls(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    parsed: ParsedModule,
    module_code: str,
    findings: list[SkeletonFinding],
    *,
    timeout: int,
    sessions: dict[str, str] | None = None,
) -> tuple[ParsedModule | None, str]:
    patch_labels = _patchable_skeleton_labels(findings, labels)
    if not patch_labels:
        return None, "not patchable"
    _log(
        "  deterministic audit isolated "
        + f"{len(patch_labels)} declaration(s); patching: "
        + ", ".join(patch_labels)
    )
    prompt = _targeted_skeleton_patch_prompt(
        ctx,
        patch_labels,
        sections,
        import_modules,
        module_code,
        findings,
        timeout_s=timeout,
    )
    result = _call_model(
        ctx,
        prompt,
        purpose="skeleton_declaration_patch",
        timeout=timeout,
        effort=ctx.base_effort,
        labels=patch_labels,
        sessions=sessions,
    )
    if result.status == "timeout":
        result = _call_model(
            ctx,
            prompt,
            purpose="skeleton_declaration_patch",
            timeout=ctx.hard_timeout,
            effort=ctx.escalation_effort,
            labels=patch_labels,
            escalated=True,
            sessions=sessions,
        )
    if result.status != "ok":
        return None, f"targeted declaration patch {result.status}: {result.error}"
    try:
        replacement_code = _extract_lean_code(result.text)
    except ValueError as exc:
        return None, f"targeted declaration patch did not return Lean code: {exc}"
    patched = _apply_skeleton_replacements(parsed, labels, patch_labels, replacement_code)
    if patched is None:
        return None, "targeted declaration patch omitted one or more required replacement declarations"
    _record(
        ctx.telemetry,
        "skeleton_declaration_patch_result",
        labels=patch_labels,
        status="applied",
    )
    return patched, "patched"


def _proof_prompt(
    ctx: Ctx,
    targets: list[tuple[str, str]],  # (label, frozen decl text)
    sections: list[Section],
    import_modules: list[str],
    *,
    errors: dict[str, str] | None = None,
    singleton: bool = False,
    timeout_s: int = 0,
) -> str:
    errors = errors or {}
    parts: list[str] = []
    for label, decl_text in targets:
        node = ctx.nodes[label]
        deps = [
            _lean_name(dep)
            for dep in sorted(node.uses)
            if dep in ctx.nodes and not ctx.nodes[dep].mathlibok
        ]
        error_block = (
            f"\nPrevious attempt failed with:\n```text\n{errors[label][-4000:]}\n```"
            if label in errors
            else ""
        )
        parts.append(
            f"## {label}\n"
            f"Frozen declaration (statement is IMMUTABLE):\n```lean\n{decl_text[:6000]}\n```\n"
            f"Required dependency mentions in the proof or statement: "
            f"{', '.join(deps) or '(none)'}\n"
            f"Blueprint node with proof sketch:\n```tex\n{ctx.tex_blocks.get(label, '')[:6000]}\n```"
            f"{error_block}"
        )
    signatures = _frozen_interface_digest(sections, import_modules, budget=20000)
    single_note = (
        "\nThis is an escalated single-declaration call; think as long as needed "
        "within the budget.\n"
        if singleton
        else ""
    )
    return f"""TASK: FILL-SKELETON-PROOFS

Return exactly one Lean 4 code block. No commentary.

For EACH target declaration below, return the declaration with its `sorry`
replaced by a real proof:
- Copy the statement EXACTLY as frozen and end it with `:= by` followed by your
  tactic proof. Only the proof after `:= by` is used; the frozen statement
  cannot be edited, so any statement change you make will be discarded.
- Proofs must be self-contained tactic blocks (`have`/`let`/`calc` inside are
  fine). Do NOT add new top-level declarations; if a proof genuinely needs a
  helper lemma, reply with NEEDS-DECOMPOSITION for that label instead.
- The proof must certify the blueprint proof obligations for this node. It does
  not need to mirror the prose line by line, but it must not bypass the
  blueprint argument by using an abstract theorem/tag/witness that erases the
  construction, case split, reduction, invariant, or intermediate claim the
  blueprint proof relies on.
- If a node's blueprint entry lists dependencies, the proof (or statement)
  must visibly use their generated Lean names; a proof that re-derives a
  dependency inline will be rejected.
- You may add `import` lines for tactic modules you need.
- Dependency lemmas may still be `sorry`-proved in the skeleton; using their
  statements is exactly how the blueprint dependency graph is supposed to work.
- This call has a wall-clock budget of about {timeout_s}s.
{single_note}
{_common_rules(ctx)}

Blueprint name: {ctx.name}

Frozen Lean interface (same module and imported skeleton modules; use these
exact names — dependencies must be cited by them).
{FROZEN_INTERFACE_NOTE}
```lean
{signatures or '-- none'}
```

Target declarations:
{chr(10).join(parts)}
"""


# ---------------------------------------------------------------------------
# Alignment audit (skeleton-aware)


def _skeleton_deterministic_findings(code: str, ctx: Ctx, labels: list[str]) -> list[SkeletonFinding]:
    """Coverage/kind checks for a section. Dependency-mention checks are only
    applied to declarations that are already complete (definitions and eagerly
    proved theorem-likes); sorry-proved statements get theirs at proof time."""
    findings: list[SkeletonFinding] = []
    decls = _lean_declarations(code)
    for label in labels:
        node = ctx.nodes[label]
        if node.mathlibok:
            continue
        lean_name = _lean_name(label)
        decl = decls.get(_lean_name(label))
        if decl is None:
            findings.append(
                SkeletonFinding(
                    f"missing generated declaration for {label} -> `{lean_name}`",
                    label=label,
                    lean_name=lean_name,
                )
            )
            continue
        if node.kind == "definition" and decl.kind in {"theorem", "lemma"}:
            findings.append(
                SkeletonFinding(
                    f"{label} is a definition but generated `{decl.kind} {decl.name}`",
                    label=label,
                    lean_name=lean_name,
                )
            )
        if node.kind in THEOREM_LIKE_KINDS and decl.kind in {"structure", "inductive", "class"}:
            findings.append(
                SkeletonFinding(
                    f"{label} is theorem-like but generated `{decl.kind} {decl.name}`",
                    label=label,
                    lean_name=lean_name,
                )
            )
        if not _has_terminal_sorry(decl.text):
            missing = _nonmathlib_uses_missing_from_decl(label, node, decl, ctx.nodes, decls)
            if missing:
                findings.append(
                    SkeletonFinding(
                        f"{label} does not mention required dependency generated name(s): "
                        + ", ".join(f"`{_lean_name(dep)}`" for dep in missing[:12]),
                        label=label,
                        lean_name=lean_name,
                    )
                )
    return findings


def _skeleton_deterministic_audit(code: str, ctx: Ctx, labels: list[str]) -> list[str]:
    return [finding.message for finding in _skeleton_deterministic_findings(code, ctx, labels)]


def _model_alignment_audit(
    ctx: Ctx,
    labels: list[str],
    code: str,
    *,
    tag: str = "",
) -> tuple[str, str, set[str]] | None:
    """Batched blueprint-contract audit. None means accepted.

    Returns (kind, reason, rejected_labels) on rejection, where kind is
    ``blueprint`` or ``lean-generation`` (statement re-generation).
    """
    decls = _lean_declarations(code)
    nodes = {label: ctx.nodes[label] for label in labels}
    prompt = _statement_audit_prompt(ctx.name, nodes, ctx.tex_blocks, decls, ctx.paper_text)
    # Judge independence: the audit NEVER shares a session with the generator
    # or with its own earlier verdicts (no `sessions` passed — each audit is a
    # fresh conversation seeing only the artifact and the blueprint). A judge
    # that resumes the producer's session inherits its self-justification
    # (rubber-stamp risk) or anchors on its own prior verdict instead of
    # re-reading the new file. Producers share sessions; judges must not.
    result = _call_model(
        ctx,
        prompt,
        purpose="statement_audit",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=labels,
        tag=tag,
    )
    if result.status != "ok":
        # An unavailable auditor must not silently pass statements; retry once
        # via the escalation budget, then treat as generation-side failure.
        result = _call_model(
            ctx,
            prompt,
            purpose="statement_audit",
            timeout=ctx.hard_timeout,
            effort=ctx.escalation_effort,
            labels=labels,
            escalated=True,
            tag=tag,
        )
        if result.status != "ok":
            return ("lean-generation", f"blueprint contract audit call failed: {result.error}", set(labels))
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        return ("lean-generation", f"blueprint contract audit returned invalid JSON: {exc}", set(labels))
    issues = payload.get("issues") or []
    accepted = bool(payload.get("accepted")) and not any(
        str(issue.get("severity", "")).lower() == "reject"
        for issue in issues
        if isinstance(issue, dict)
    )
    _record(
        ctx.telemetry,
        "statement_audit",
        labels=labels,
        source="model",
        accepted=accepted,
        classification=str(payload.get("classification") or ""),
    )
    if accepted:
        return None
    formatted: list[str] = []
    rejected: set[str] = set()
    for issue in issues if isinstance(issues, list) else []:
        if not isinstance(issue, dict):
            continue
        node = str(issue.get("node") or "(unknown)")
        formatted.append(f"{node} [{issue.get('severity', 'reject')}]: {issue.get('reason', '')}")
        if str(issue.get("severity", "reject")).lower() == "reject" and node in nodes:
            rejected.add(node)
    if not rejected:
        rejected = set(labels)
    kind = _alignment_failure_kind(str(payload.get("classification") or ""), formatted)
    return (kind, "Blueprint contract audit rejected:\n- " + "\n- ".join(formatted), rejected)


# ---------------------------------------------------------------------------
# Phase 1: skeleton


def _freeze_section(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    next_number: int,
    *,
    force_first_escalated: bool = False,
) -> list[Section]:
    """Generate, compile-fix, audit, and freeze one section (possibly bisected).

    Returns the newly frozen Section objects (appended by the caller). Raises
    RepairRequest when the blueprint itself must change first.
    """
    import_modules = _sections_for_deps(ctx, labels, sections)
    target_kinds = {_lean_name(label): ctx.nodes[label].kind for label in labels}
    label_by_lean_name = {_lean_name(label): label for label in labels}
    module, path = _section_module(ctx.name, next_number)
    path.parent.mkdir(parents=True, exist_ok=True)
    _log(f"==> Skeleton section {next_number:02d}: {len(labels)} node(s): " + ", ".join(labels[:6]) + ("..." if len(labels) > 6 else ""))

    # One backend session per runner spec for this section's whole lifecycle
    # (generation, patches, error-fix rounds, audit): follow-up calls keep the
    # Mathlib exploration and module context instead of rebuilding it cold.
    sessions: dict[str, str] = {}
    feedback = ""
    previous_code = ""
    audit_rounds = 0
    escalated_refusals: set[str] = set()
    force_escalated_round = force_first_escalated
    escalated_stagnation_fps: set[tuple[tuple[str, str, str, str], ...]] = set()
    regen_signatures: set[tuple[str, tuple[tuple[str, str, str, str], ...]]] = set()
    for round_no in range(1, STATEMENT_FIX_ROUNDS + AUDIT_REGEN_ROUNDS + 2):
        use_escalated_runner = force_escalated_round
        force_escalated_round = False
        effort = ctx.escalation_effort if use_escalated_runner else ctx.base_effort
        timeout = ctx.hard_timeout if use_escalated_runner or round_no > 1 else ctx.base_timeout
        prompt = _skeleton_prompt(
            ctx,
            labels,
            sections,
            import_modules,
            feedback=feedback,
            previous_code=previous_code,
            timeout_s=timeout,
        )
        result = _call_model(
            ctx,
            prompt,
            purpose="skeleton_generation",
            timeout=timeout,
            effort=effort,
            labels=labels,
            escalated=use_escalated_runner,
            sessions=sessions,
        )
        result_was_escalated = use_escalated_runner
        if result.status == "timeout" and len(labels) > 1 and timeout < ctx.hard_timeout:
            # First timeout on a batch is ambiguous: output-bound (too many
            # nodes for the budget — bisection helps) or exploration-bound
            # (context gathering costs the same at any batch size — bisection
            # cannot help and just multiplies the waste). One retry of the
            # SAME labels at the hard budget, same runner and effort,
            # distinguishes the two for the price of a single call; only a
            # second timeout justifies bisecting.
            _log(
                f"  section call timed out at {timeout}s; retrying the same "
                f"{len(labels)} node(s) once at {ctx.hard_timeout}s before bisecting"
            )
            retry_prompt = _skeleton_prompt(
                ctx,
                labels,
                sections,
                import_modules,
                feedback=feedback,
                previous_code=previous_code,
                timeout_s=ctx.hard_timeout,
            )
            result = _call_model(
                ctx,
                retry_prompt,
                purpose="skeleton_generation",
                timeout=ctx.hard_timeout,
                effort=effort,
                labels=labels,
                escalated=use_escalated_runner,
                sessions=sessions,
            )
            if result.status == "ok":
                # The batch fits the hard budget but not the base budget, so
                # this size would pay the base-timeout tax on every future
                # group. Shrink mildly and pin fast recovery below the rescued
                # size so the sizes settle where the base budget suffices.
                rescued_size = max(1, len(labels) * 3 // 4)
                if rescued_size < (ctx.effective_section_size or ctx.section_size):
                    ctx.effective_section_size = rescued_size
                    if ctx.proven_section_size:
                        ctx.proven_section_size = min(ctx.proven_section_size, rescued_size)
                    _log(f"  adaptive section size reduced to {rescued_size} (batch needed the hard budget)")
                    _record(
                        ctx.telemetry,
                        "adaptive_section_size",
                        size=rescued_size,
                        reason="hard_budget_rescue",
                        labels=labels,
                    )
        if result.status == "timeout":
            if len(labels) > 1:
                # Still timing out at the hard budget: output-bound after all.
                # Bisect the section and recurse.
                mid = len(labels) // 2
                _log(f"  section call timed out; bisecting into {mid} + {len(labels) - mid} node(s)")
                # This size demonstrably does not fit the base timeout, so
                # don't make future groups rediscover that: shrink the
                # run-scoped section size (Phase 2 already does this for
                # proof batches).
                if 0 < mid < (ctx.effective_section_size or ctx.section_size):
                    ctx.effective_section_size = mid
                    _log(f"  adaptive section size reduced to {mid} for the rest of this run")
                    _record(
                        ctx.telemetry,
                        "adaptive_section_size",
                        size=mid,
                        reason="skeleton_timeout",
                        labels=labels,
                    )
                first = _freeze_section(ctx, labels[:mid], sections, next_number)
                combined = sections + first
                second = _freeze_section(
                    ctx, labels[mid:], combined, next_number + len(first)
                )
                return first + second
            result = _call_model(
                ctx,
                prompt,
                purpose="skeleton_generation",
                timeout=ctx.hard_timeout,
                effort=ctx.escalation_effort,
                labels=labels,
                escalated=True,
                sessions=sessions,
            )
            result_was_escalated = True
            if result.status == "error":
                feedback = f"model call failed: {result.error}"
                continue
            if result.status == "timeout":
                # Two full timeout budgets on a single-statement call is the one
                # place a timeout counts as evidence: the node cannot even be
                # *stated* within a generous budget.
                raise RepairRequest(
                    "Statement generation for this node timed out twice, including at "
                    "escalated effort; the node is likely too large or underspecified "
                    "to state as one declaration. Decompose it into smaller nodes.",
                    labels,
                    section_labels=labels,
                )
        elif result.status == "error":
            feedback = f"model call failed: {result.error}"
            continue

        refusal = _parse_decomposition_refusal(result.text)
        if refusal is not None:
            refused = [refusal["label"]] if refusal["label"] in labels else list(labels)
            refusal_key = ",".join(refused)
            if not result_was_escalated and refusal_key not in escalated_refusals:
                escalated_refusals.add(refusal_key)
                force_escalated_round = True
                missing = refusal.get("missing_helpers") or []
                feedback = (
                    "The base skeleton generator returned NEEDS-DECOMPOSITION. "
                    "Treat that as a statement-generation claim, not blueprint "
                    "repair evidence yet. Before editing the blueprint, make an "
                    "escalated attempt to state the same blueprint node(s) inside "
                    "this section. You may introduce small complete local helper "
                    "declarations in this same Lean file when needed, but you must "
                    "not weaken the blueprint statement.\n\n"
                    f"Refused label(s): {', '.join(refused)}\n"
                    f"Reason: {refusal['reason']}\n"
                    f"Requested helper(s): {', '.join(missing) or '(none)'}"
                )
                previous_code = ""
                _log(
                    "  skeleton generator requested decomposition for "
                    + ", ".join(refused)
                    + "; escalating statement generation before blueprint repair"
                )
                continue
            raise RepairRequest(
                "The escalated statement generator determined node(s) cannot be "
                "stated 1-1 as written.\n"
                f"Reason: {refusal['reason']}",
                refused,
                decomposition_helpers=refusal["missing_helpers"],
                section_labels=labels,
            )

        code = _extract_lean_code(result.text)
        parsed = _parse_module(code)
        missing_imports = _missing_olean_imports(parsed.imports)
        if missing_imports:
            ctx.unavailable_imports.update(missing_imports)
            parsed.imports = [item for item in parsed.imports if item not in set(missing_imports)]
        # Normalize `:= by sorry` to the canonical terminal form.
        for decl in parsed.decls:
            if target_kinds.get(decl.name or "") in THEOREM_LIKE_KINDS and _has_terminal_sorry(decl.text):
                decl.text = _normalize_terminal_sorry(decl.text)
        all_imports = [f"import {m}" for m in import_modules] + parsed.imports
        module_code, _ranges = _compose_module(all_imports, parsed.preamble, [d.text for d in parsed.decls])

        findings = _skeleton_code_findings(module_code, target_kinds, label_by_lean_name)
        findings += _skeleton_deterministic_findings(module_code, ctx, labels)
        patch_note = ""
        patch_round = 0
        while findings and patch_round < TARGETED_DECL_PATCH_ROUNDS:
            before_patch_fp = _skeleton_findings_fingerprint(findings)
            patch_round += 1
            patched, patch_note = _targeted_patch_skeleton_decls(
                ctx,
                labels,
                sections,
                import_modules,
                parsed,
                module_code,
                findings,
                timeout=ctx.base_timeout if patch_round == 1 else ctx.hard_timeout,
                sessions=sessions,
            )
            if patched is None:
                break
            parsed = patched
            all_imports = [f"import {m}" for m in import_modules] + parsed.imports
            module_code, _ranges = _compose_module(
                all_imports, parsed.preamble, [d.text for d in parsed.decls]
            )
            findings = _skeleton_code_findings(module_code, target_kinds, label_by_lean_name)
            findings += _skeleton_deterministic_findings(module_code, ctx, labels)
            if findings:
                after_patch_fp = _skeleton_findings_fingerprint(findings)
                if after_patch_fp == before_patch_fp:
                    patch_labels = _patchable_skeleton_labels(findings, labels)
                    support_labels = _dependency_closed_subset(ctx, labels, patch_labels)
                    _record(
                        ctx.telemetry,
                        "skeleton_stagnation_detected",
                        labels=labels,
                        patch_labels=patch_labels,
                        support_labels=support_labels,
                        failure_classes=sorted(
                            {
                                _skeleton_finding_class(finding.message)
                                for finding in findings
                            }
                        ),
                    )
                    if support_labels and len(support_labels) < len(labels):
                        _log(
                            "  targeted patch made no deterministic progress; "
                            "retrying dependency-closed subset with escalation: "
                            + ", ".join(support_labels)
                        )
                        first = _freeze_section(
                            ctx,
                            support_labels,
                            sections,
                            next_number,
                            force_first_escalated=True,
                        )
                        combined = sections + first
                        support_set = set(support_labels)
                        remaining = [label for label in labels if label not in support_set]
                        if not remaining:
                            return first
                        second = _freeze_section(
                            ctx,
                            remaining,
                            combined,
                            next_number + len(first),
                        )
                        return first + second
                    if after_patch_fp not in escalated_stagnation_fps and not result_was_escalated:
                        escalated_stagnation_fps.add(after_patch_fp)
                        force_escalated_round = True
                        feedback = (
                            "Targeted declaration patch made no deterministic "
                            "progress. Regenerate this same section once with "
                            "escalated effort, paying special attention to these "
                            "unchanged audit findings:\n"
                            + _format_skeleton_findings(findings)[-10000:]
                        )
                        previous_code = module_code
                        _log(
                            "  targeted patch made no deterministic progress; "
                            "escalating the same section once"
                        )
                        break
                    raise RepairRequest(
                        "Targeted skeleton declaration patch made no "
                        "deterministic progress on the same audit failures.\n"
                        + _format_skeleton_findings(findings)[-10000:],
                        patch_labels or labels,
                        section_labels=labels,
                    )
                _log(
                    "  targeted declaration patch still has "
                    + f"{len(findings)} deterministic issue(s)"
                )
        if force_escalated_round:
            continue
        issues = [finding.message for finding in findings]
        if issues:
            feedback = _format_skeleton_findings(findings)
            if patch_note and patch_note != "not patchable":
                feedback += f"\n\nTargeted declaration patch result: {patch_note}"
            previous_code = module_code
            # Stagnation guard: if this round produced the SAME file failing
            # the SAME findings as a previous round, the regen prompt is
            # byte-identical and another round cannot make progress. Escalate
            # once; if the escalated round is also identical, stop and say so
            # instead of burning the remaining rounds on the same question.
            signature = (
                hashlib.sha256(module_code.encode("utf-8")).hexdigest(),
                _skeleton_findings_fingerprint(findings),
            )
            if signature in regen_signatures:
                if not result_was_escalated:
                    force_escalated_round = True
                    _log(
                        "  regeneration is stagnant (identical file and findings); "
                        "escalating once"
                    )
                    continue
                raise RepairRequest(
                    "Skeleton regeneration is stagnant: repeated rounds return an "
                    "identical file failing identical deterministic findings, "
                    "including at escalated effort. The generated Lean may actually "
                    "be valid and the findings may reflect a harness/lint issue "
                    "rather than a blueprint problem — verify the findings against "
                    "the file before editing any blueprint statement:\n" + feedback,
                    labels,
                    section_labels=labels,
                )
            regen_signatures.add(signature)
            _log(f"  deterministic audit failed ({len(issues)} issue(s)); regenerating")
            continue

        path.write_text(module_code, encoding="utf-8")
        # The Lean compile (subprocess) and the model alignment audit (model
        # call) are independent checks of the same artifact — run them
        # concurrently and pay max() instead of sum(). Lean's verdict stays
        # authoritative: if the file doesn't compile, the audit outcome is
        # discarded — a non-compiling file gets compile feedback, and its
        # audit must not count toward audit_rounds or trigger repair.
        lean_outcome: list = []

        def _lean_worker() -> None:
            try:
                lean_outcome.append(("result", _check_lean(path, ctx.lean_command)))
            except BaseException as exc:  # noqa: BLE001 - re-raised on the main thread
                lean_outcome.append(("raised", exc))

        lean_thread = threading.Thread(target=_lean_worker, daemon=True)
        lean_thread.start()
        try:
            audit = _model_alignment_audit(ctx, labels, module_code)
        finally:
            lean_thread.join()
        outcome_kind, payload = lean_outcome[0]
        if outcome_kind == "raised":
            raise payload
        ok, output = payload
        if not ok:
            feedback = f"Lean rejected the file:\n{output[-12000:]}"
            previous_code = module_code
            _log("  lean rejected skeleton section; sending errors back")
            continue

        if audit is not None:
            kind, reason, rejected = audit
            if kind == "blueprint":
                raise RepairRequest(reason, sorted(rejected), section_labels=labels)
            audit_rounds += 1
            if audit_rounds > AUDIT_REGEN_ROUNDS:
                raise RepairRequest(
                    "Blueprint contract audit kept rejecting regenerated statements; "
                    "the blueprint text likely under-determines the statement.\n" + reason,
                    sorted(rejected),
                    section_labels=labels,
                )
            feedback = reason
            previous_code = module_code
            _log("  alignment audit rejected statements; regenerating rejected part")
            continue

        object_attempt = _compile_module_olean(path, ctx.lean_command)
        if not object_attempt.ok:
            feedback = f".olean compilation failed:\n{object_attempt.output[-8000:]}"
            previous_code = module_code
            continue
        _log(f"  section {next_number:02d} frozen ({len(parsed.decls)} declaration(s))")
        _record(
            ctx.telemetry,
            "skeleton_section_frozen",
            section=next_number,
            labels=labels,
            decls=len(parsed.decls),
        )
        return [
            Section(
                number=next_number,
                labels=list(labels),
                path=path,
                module=module,
                import_modules=import_modules,
            )
        ]

    raise RepairRequest(
        "Skeleton generation exhausted its fix rounds for this section. Last feedback:\n"
        + feedback,
        labels,
        section_labels=labels,
    )


def _run_phase1(ctx: Ctx, sections: list[Section], pending: set[str]) -> list[Section]:
    next_number = max((sec.number for sec in sections), default=0) + 1
    if ctx.effective_section_size <= 0:
        ctx.effective_section_size = ctx.section_size
    # Same filter as _partition_sections, but sliced lazily so each group is
    # cut at the *current* adaptive size rather than pre-chunked at the
    # configured size: a timeout in group 1 shrinks every later group too.
    order = [
        label
        for label in _topo_order(ctx.nodes)
        if label in pending and not ctx.nodes[label].mathlibok
    ]
    clean_streak = 0
    index = 0
    while index < len(order):
        size = max(1, min(ctx.effective_section_size, ctx.section_size))
        group = order[index : index + size]
        index += len(group)
        size_before = ctx.effective_section_size
        new_sections = _freeze_section(ctx, group, sections, next_number)
        sections.extend(new_sections)
        next_number = max(sec.number for sec in sections) + 1
        _save_state(ctx.name, sections, ctx.stmt_fps, ctx.contract_fps)
        if ctx.effective_section_size != size_before:
            # A nested timeout shrank the run-scoped size mid-group.
            clean_streak = 0
            continue
        clean_streak += 1
        ctx.proven_section_size = max(ctx.proven_section_size, len(group))
        recovery_target = min(ctx.proven_section_size, ctx.section_size)
        if ctx.effective_section_size < recovery_target:
            # Fast recovery: a bigger size already froze cleanly this run, so
            # a post-collapse crawl (1 -> 2 -> 3 -> ...) is wasted overhead.
            # Double back toward the proven size after every clean group.
            grown = min(recovery_target, max(ctx.effective_section_size * 2, ctx.effective_section_size + 1))
            _log(f"  adaptive section size recovering to {grown} (proven this run: {recovery_target})")
            _record(
                ctx.telemetry,
                "adaptive_section_size",
                size=grown,
                reason="recovery",
                labels=[],
            )
            ctx.effective_section_size = grown
            clean_streak = 0
        elif clean_streak >= 2 and ctx.effective_section_size < ctx.section_size:
            grown = min(
                ctx.section_size,
                max(ctx.effective_section_size + 1, ctx.effective_section_size * 3 // 2),
            )
            _log(f"  adaptive section size grown to {grown} after {clean_streak} clean section(s)")
            _record(
                ctx.telemetry,
                "adaptive_section_size",
                size=grown,
                reason="clean_streak",
                labels=[],
            )
            ctx.effective_section_size = grown
            clean_streak = 0
    return sections


# ---------------------------------------------------------------------------
# Phase 2: proofs


@dataclass
class SectionProofOutcome:
    section: Section
    proved: list[str] = field(default_factory=list)
    failed: dict[str, str] = field(default_factory=dict)  # label -> evidence
    decomposition: dict[str, list[str]] = field(default_factory=dict)  # label -> helpers


def _module_decl_texts(sec: Section) -> tuple[ParsedModule, dict[str, int]]:
    parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
    index = {decl.name: i for i, decl in enumerate(parsed.decls) if decl.name}
    return parsed, index


def _write_section(sec: Section, parsed: ParsedModule) -> list[tuple[int, int]]:
    code, ranges = _compose_module(parsed.imports, parsed.preamble, [d.text for d in parsed.decls])
    sec.path.write_text(code, encoding="utf-8")
    return ranges


def _ladder_tactic(ctx: Ctx, label: str) -> str:
    node = ctx.nodes[label]
    deps = [
        _lean_name(dep)
        for dep in sorted(node.uses)
        if dep in ctx.nodes and not ctx.nodes[dep].mathlibok
    ][:8]
    statement = ctx.stmt_blocks.get(label, "")
    unmentioned = [dep for dep in deps if dep not in statement]
    simp_deps = f"(simp [{', '.join(deps)}])" if deps else "simp"
    if unmentioned:
        # The dependency contract requires these names to appear in the decl;
        # only a simp call naming them can satisfy it for a ladder proof.
        return f"by first | (simp [{', '.join(deps)}]) | (simp_all [{', '.join(deps)}])"
    return f"by first | rfl | omega | norm_num | ring | {simp_deps} | simp | aesop"


def _run_tactic_ladder(ctx: Ctx, sec: Section, sorry_labels: list[str], *, tag: str) -> list[str]:
    """Try to close sorries with zero model calls. Returns labels proved."""
    parsed, index = _module_decl_texts(sec)
    ladder_imports = [
        item for item in LADDER_IMPORTS if item not in _missing_olean_imports(LADDER_IMPORTS)
    ]
    candidates: dict[str, str] = {}
    originals: dict[str, str] = {}
    for label in sorry_labels:
        name = _lean_name(label)
        if name not in index:
            continue
        decl = parsed.decls[index[name]]
        originals[label] = decl.text
        tactic = _ladder_tactic(ctx, label)
        candidates[label] = (
            f"set_option maxHeartbeats {LADDER_HEARTBEATS} in\n"
            + _splice_proof(decl.text, tactic)
        )
    if not candidates:
        return []
    for label, text in candidates.items():
        parsed.decls[index[_lean_name(label)]].text = text
    parsed.imports = list(dict.fromkeys(parsed.imports + ladder_imports))
    ranges = _write_section(sec, parsed)
    ok, output = _check_lean(sec.path, ctx.lean_command, timeout=LEAN_CHECK_TIMEOUT)
    errors_by_decl, _file_level = ({}, []) if ok else _errors_by_decl(output, sec.file_name, ranges)
    proved: list[str] = []
    for label in list(candidates):
        idx = index[_lean_name(label)]
        if idx in errors_by_decl or (not ok and not errors_by_decl):
            parsed.decls[idx].text = originals[label]
        else:
            proved.append(label)
    if not proved:
        # Revert imports too; nothing kept from the ladder pass.
        parsed.imports = [item for item in parsed.imports if item not in set(ladder_imports)]
    _write_section(sec, parsed)
    if proved and (not ok):
        # Mixed outcome: recompile to confirm the kept subset stands alone.
        ok2, output2 = _check_lean(sec.path, ctx.lean_command)
        if not ok2:
            for label in proved:
                parsed.decls[index[_lean_name(label)]].text = originals[label]
            parsed.imports = [item for item in parsed.imports if item not in set(ladder_imports)]
            _write_section(sec, parsed)
            _log(f"ladder subset failed recompile; reverted ({output2.splitlines()[-1] if output2 else ''})", tag=tag)
            proved = []
    if proved:
        _log(f"tactic ladder closed {len(proved)}/{len(candidates)} proof(s) for free", tag=tag)
    _record(
        ctx.telemetry,
        "tactic_ladder_result",
        section=sec.number,
        labels=sorted(candidates),
        candidate_count=len(candidates),
        proved_labels=proved,
        proved_count=len(proved),
        imports=ladder_imports,
    )
    return proved


def _apply_proof_batch(
    ctx: Ctx,
    sec: Section,
    response_code: str,
    targets: dict[str, str],  # label -> frozen decl text
    *,
    tag: str,
) -> tuple[list[str], dict[str, str]]:
    """Splice returned proofs into the module; compile; keep survivors.

    Returns (proved_labels, errors_by_label).
    """
    parsed, index = _module_decl_texts(sec)
    model_parsed = _parse_module(_extract_lean_code(response_code))
    model_decls = {decl.name: decl for decl in model_parsed.decls if decl.name}
    new_imports = [
        item
        for item in model_parsed.imports
        if item not in _missing_olean_imports(model_parsed.imports)
    ]
    errors: dict[str, str] = {}
    originals: dict[str, str] = {}
    spliced: list[str] = []
    for label, frozen_text in targets.items():
        name = _lean_name(label)
        model_decl = model_decls.get(name)
        if model_decl is None:
            errors[label] = "response did not contain a declaration with the frozen name"
            continue
        proof = _extract_by_proof(model_decl.text)
        if proof is None:
            errors[label] = "response proof must be a tactic proof introduced by `:= by`"
            continue
        if re.search(r"\bsorry\b|\badmit\b", proof):
            errors[label] = "response proof still contains sorry/admit"
            continue
        originals[label] = parsed.decls[index[name]].text
        parsed.decls[index[name]].text = _splice_proof(frozen_text, proof)
        spliced.append(label)
    if not spliced:
        return [], errors
    parsed.imports = list(dict.fromkeys(parsed.imports + new_imports))
    ranges = _write_section(sec, parsed)
    ok, output = _check_lean(sec.path, ctx.lean_command)
    if ok:
        proved = list(spliced)
    else:
        errors_by_decl, file_level = _errors_by_decl(output, sec.file_name, ranges)
        if file_level and not errors_by_decl:
            # Un-attributable failure: revert everything from this batch.
            for label in spliced:
                parsed.decls[index[_lean_name(label)]].text = originals[label]
            _write_section(sec, parsed)
            for label in spliced:
                errors[label] = "\n".join(file_level)[-4000:]
            return [], errors
        proved = []
        for label in spliced:
            idx = index[_lean_name(label)]
            if idx in errors_by_decl:
                errors[label] = "\n".join(errors_by_decl[idx])[-4000:]
                parsed.decls[idx].text = originals[label]
            else:
                proved.append(label)
        ranges = _write_section(sec, parsed)
        if proved:
            ok2, output2 = _check_lean(sec.path, ctx.lean_command)
            if not ok2:
                for label in proved:
                    errors[label] = output2[-2000:]
                    parsed.decls[index[_lean_name(label)]].text = originals[label]
                _write_section(sec, parsed)
                proved = []
    # Dependency-mention contract: now that the proof exists, every non-Mathlib
    # `\uses` name must be visible in the finished declaration.
    if proved:
        module_code = sec.path.read_text(encoding="utf-8")
        decls = _lean_declarations(module_code)
        kept: list[str] = []
        for label in proved:
            decl = decls.get(_lean_name(label))
            missing = (
                _nonmathlib_uses_missing_from_decl(label, ctx.nodes[label], decl, ctx.nodes, decls)
                if decl is not None
                else []
            )
            if missing:
                errors[label] = (
                    "proof compiled but does not visibly use required dependency "
                    "declaration(s): "
                    + ", ".join(f"`{_lean_name(dep)}`" for dep in missing)
                    + ". Use them instead of re-deriving inline."
                )
                parsed.decls[index[_lean_name(label)]].text = originals[label]
            else:
                kept.append(label)
        if len(kept) != len(proved):
            _write_section(sec, parsed)
            if kept:
                ok3, _out3 = _check_lean(sec.path, ctx.lean_command)
                if not ok3:
                    for label in kept:
                        parsed.decls[index[_lean_name(label)]].text = originals[label]
                        errors[label] = "kept subset failed recompile after dependency pruning"
                    _write_section(sec, parsed)
                    kept = []
        proved = kept
    if proved:
        _log(f"accepted {len(proved)} proof(s): {', '.join(proved[:6])}", tag=tag)
    return proved, errors


def _prove_section(ctx: Ctx, sec: Section, sections: list[Section]) -> SectionProofOutcome:
    tag = f"S{sec.number:02d}"
    outcome = SectionProofOutcome(section=sec)
    # Per-section backend sessions (worker-thread local): proof rounds over the
    # same file reuse the context built by earlier rounds. See _call_model.
    sessions: dict[str, str] = {}
    parsed, index = _module_decl_texts(sec)
    sorry_labels = [
        label
        for label in sec.labels
        if _lean_name(label) in index and _has_terminal_sorry(parsed.decls[index[_lean_name(label)]].text)
    ]
    if not sorry_labels:
        return outcome

    # Blueprint repairs may add proof-level `\uses` without touching statements;
    # make sure every dependency's skeleton module is imported before proving.
    needed = [m for m in _sections_for_deps(ctx, sec.labels, sections) if m != sec.module]
    new_lines = [f"import {m}" for m in needed if f"import {m}" not in parsed.imports]
    if new_lines:
        parsed.imports = list(dict.fromkeys(parsed.imports + new_lines))
        _write_section(sec, parsed)
        sec.import_modules = sorted(set(sec.import_modules) | set(needed))

    if ctx.use_ladder:
        try:
            proved = _run_tactic_ladder(ctx, sec, sorry_labels, tag=tag)
        except Exception as exc:  # noqa: BLE001 - the ladder is best-effort only
            _log(f"tactic ladder crashed ({exc}); continuing with model proofs", tag=tag)
            proved = []
        outcome.proved.extend(proved)
        sorry_labels = [label for label in sorry_labels if label not in proved]

    import_modules = sec.import_modules
    remaining = list(sorry_labels)
    errors: dict[str, str] = {}
    batch_size = ctx.proof_batch
    round_no = 0
    while remaining and round_no < 2:
        round_no += 1
        next_remaining: list[str] = []
        for i in range(0, len(remaining), batch_size):
            batch = remaining[i : i + batch_size]
            parsed, index = _module_decl_texts(sec)
            targets = {
                label: parsed.decls[index[_lean_name(label)]].text
                for label in batch
                if _lean_name(label) in index
            }
            prompt = _proof_prompt(
                ctx,
                list(targets.items()),
                sections,
                import_modules + [sec.module],
                errors={label: errors[label] for label in batch if label in errors},
                timeout_s=ctx.base_timeout,
            )
            result = _call_model(
                ctx,
                prompt,
                purpose="proof_batch",
                timeout=ctx.base_timeout,
                effort=ctx.base_effort,
                labels=batch,
                tag=tag,
                sessions=sessions,
            )
            if result.status == "timeout" and len(batch) > 1:
                # Latency: halve the batch size for the rest of this section.
                batch_size = max(1, batch_size // 2)
                next_remaining.extend(batch)
                _log(f"batch timed out; reducing batch size to {batch_size}", tag=tag)
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_batch",
                    round=round_no,
                    labels=batch,
                    status="timeout_bisected",
                    proved_labels=[],
                    failed_labels=batch,
                    decomposition_labels=[],
                    next_batch_size=batch_size,
                )
                continue
            if result.status != "ok":
                next_remaining.extend(batch)
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_batch",
                    round=round_no,
                    labels=batch,
                    status=result.status,
                    proved_labels=[],
                    failed_labels=batch,
                    decomposition_labels=[],
                    error=result.error,
                )
                continue
            refusal = _parse_decomposition_refusal(result.text)
            if refusal is not None:
                refused = refusal["label"] if refusal["label"] in batch else batch[0]
                outcome.decomposition[refused] = refusal["missing_helpers"]
                errors[refused] = f"generator refusal: {refusal['reason']}"
                next_remaining.extend(label for label in batch if label != refused)
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_batch",
                    round=round_no,
                    labels=batch,
                    status="needs_decomposition",
                    proved_labels=[],
                    failed_labels=[label for label in batch if label != refused],
                    decomposition_labels=[refused],
                    missing_helpers={refused: refusal["missing_helpers"]},
                )
                continue
            proved, batch_errors = _apply_proof_batch(ctx, sec, result.text, targets, tag=tag)
            outcome.proved.extend(proved)
            errors.update(batch_errors)
            failed_batch = [
                label
                for label in batch
                if label not in proved and label not in outcome.decomposition
            ]
            _record(
                ctx.telemetry,
                "proof_attempt_result",
                section=sec.number,
                phase="proof_batch",
                round=round_no,
                labels=batch,
                status="partial" if proved and failed_batch else ("success" if proved else "failed"),
                proved_labels=proved,
                failed_labels=failed_batch,
                decomposition_labels=[],
                errors={label: batch_errors[label] for label in failed_batch if label in batch_errors},
            )
            next_remaining.extend(
                label for label in batch if label not in proved and label not in outcome.decomposition
            )
        remaining = next_remaining

    # Escalation: singleton calls at high effort for the residue.
    still: list[str] = []
    for label in remaining:
        parsed, index = _module_decl_texts(sec)
        name = _lean_name(label)
        if name not in index or not _has_terminal_sorry(parsed.decls[index[name]].text):
            continue
        solved = False
        for attempt in range(1, PROOF_SINGLETON_RETRIES + 1):
            targets = {label: parsed.decls[index[name]].text}
            prompt = _proof_prompt(
                ctx,
                list(targets.items()),
                sections,
                import_modules + [sec.module],
                errors={label: errors[label]} if label in errors else None,
                singleton=True,
                timeout_s=ctx.hard_timeout,
            )
            result = _call_model(
                ctx,
                prompt,
                purpose="proof_singleton",
                timeout=ctx.hard_timeout,
                effort=ctx.escalation_effort,
                labels=[label],
                escalated=True,
                tag=tag,
                sessions=sessions,
            )
            if result.status != "ok":
                errors.setdefault(
                    label,
                    f"escalated proof call {result.status}: {result.error[:400]}",
                )
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_singleton",
                    attempt=attempt,
                    labels=[label],
                    status=result.status,
                    proved_labels=[],
                    failed_labels=[label],
                    decomposition_labels=[],
                    error=result.error,
                )
                continue
            refusal = _parse_decomposition_refusal(result.text)
            if refusal is not None:
                outcome.decomposition[label] = refusal["missing_helpers"]
                errors[label] = f"generator refusal: {refusal['reason']}"
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_singleton",
                    attempt=attempt,
                    labels=[label],
                    status="needs_decomposition",
                    proved_labels=[],
                    failed_labels=[],
                    decomposition_labels=[label],
                    missing_helpers={label: refusal["missing_helpers"]},
                )
                break
            proved, batch_errors = _apply_proof_batch(ctx, sec, result.text, targets, tag=tag)
            errors.update(batch_errors)
            if proved:
                outcome.proved.extend(proved)
                solved = True
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_singleton",
                    attempt=attempt,
                    labels=[label],
                    status="success",
                    proved_labels=proved,
                    failed_labels=[],
                    decomposition_labels=[],
                )
                break
            _record(
                ctx.telemetry,
                "proof_attempt_result",
                section=sec.number,
                phase="proof_singleton",
                attempt=attempt,
                labels=[label],
                status="failed",
                proved_labels=[],
                failed_labels=[label],
                decomposition_labels=[],
                errors={label: batch_errors.get(label, errors.get(label, ""))},
            )
            parsed, index = _module_decl_texts(sec)
        if not solved and label not in outcome.decomposition:
            still.append(label)

    for label in still:
        outcome.failed[label] = errors.get(label, "no proof found within the configured budgets")
    _record(
        ctx.telemetry,
        "proof_section_result",
        section=sec.number,
        labels=sec.labels,
        proved_labels=outcome.proved,
        failed_labels=sorted(outcome.failed),
        decomposition_labels=sorted(outcome.decomposition),
        proved_count=len(outcome.proved),
        failed_count=len(outcome.failed),
        decomposition_count=len(outcome.decomposition),
    )
    # Deliberately no .olean recompile here: statements never change in phase 2,
    # so importers keep working against the frozen (sorry-proved) oleans, and
    # skipping the rebuild avoids racing concurrent section workers. The final
    # assembled check compiles everything from scratch anyway.
    with _STATE_LOCK:
        _save_state(ctx.name, sections, ctx.stmt_fps, ctx.contract_fps)
    return outcome


# ---------------------------------------------------------------------------
# Blueprint repair (evidence-driven, batched)


def _invalidate_after_repair(
    ctx: Ctx,
    sections: list[Section],
    changed: set[str],
    lean_command: list[str],
) -> tuple[list[Section], set[str]]:
    """Prune declarations of changed/descendant labels out of frozen sections.

    Returns (kept_sections, invalidated_labels). A section whose pruned
    remainder no longer compiles is dropped entirely (its labels rejoin the
    pending set) — deterministic and safe, never silently kept.
    """
    invalidated = _dependency_descendants(ctx.nodes, changed) | changed
    kept: list[Section] = []
    dropped_modules: set[str] = set()
    for sec in sections:
        if not sec.path.is_file():
            invalidated |= set(sec.labels)
            dropped_modules.add(sec.module)
            continue
        if any(m in dropped_modules for m in sec.import_modules):
            hit = set(sec.labels)
        else:
            hit = set(sec.labels) & invalidated
        if not hit:
            kept.append(sec)
            continue
        survivors = [label for label in sec.labels if label not in invalidated]
        if not survivors:
            dropped_modules.add(sec.module)
            for artifact in (sec.path, sec.path.with_suffix(".olean")):
                with contextlib.suppress(FileNotFoundError, OSError):
                    artifact.unlink()
            continue
        parsed, index = _module_decl_texts(sec)
        removed_names = {_lean_name(label) for label in hit}
        parsed.decls = [d for d in parsed.decls if d.name not in removed_names]
        _write_section(sec, parsed)
        ok, _output = _check_lean(sec.path, lean_command)
        if ok and _compile_module_olean(sec.path, lean_command).ok:
            sec.labels = survivors
            kept.append(sec)
        else:
            invalidated |= set(survivors)
            dropped_modules.add(sec.module)
            for artifact in (sec.path, sec.path.with_suffix(".olean")):
                with contextlib.suppress(FileNotFoundError, OSError):
                    artifact.unlink()
    return kept, invalidated


def _repair_blueprint(
    ctx: Ctx,
    evidence: str,
    labels: list[str],
    *,
    trial: int,
    max_trials: int,
    escalation_note: str,
    repair_runner_agent: bool,
) -> set[str]:
    """One bounded blueprint-repair model call. Returns changed labels."""
    blueprint_source = _read_blueprint_source(ctx.name)
    before_fps = dict(ctx.contract_fps)
    _log(f"==> Blueprint repair {trial}/{max_trials} for: " + ", ".join(labels[:8]))
    prompt_builder = _agent_refine_prompt if repair_runner_agent else _api_refine_prompt
    prompt = prompt_builder(
        ctx.name,
        blueprint_source,
        evidence,
        trial,
        ctx.paper_text,
        escalation_note=escalation_note,
        model_timeout_s=ctx.hard_timeout,
    )
    runner = _make_runner(
        ctx.escalation_runner_spec,
        timeout=ctx.hard_timeout,
        readonly=False,
        effort=ctx.escalation_effort,
        with_skill=True,
    )
    prompt_artifact = _store_text(ctx.telemetry, "prompt_blueprint_repair", prompt)
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        duration = time.monotonic() - started
        status = "timeout" if _is_timeout_error(exc) else "error"
        _record(
            ctx.telemetry,
            "model_call",
            purpose="blueprint_repair",
            labels=labels,
            status=status,
            duration_s=duration,
            timeout_s=ctx.hard_timeout,
            backend=runner.backend_name,
            model=runner.model,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
        )
        if status == "timeout" and len(labels) > 1 and not is_environment_error(exc):
            mid = len(labels) // 2
            _log(
                "  blueprint repair timed out; splitting target into "
                + f"{mid} + {len(labels) - mid} label(s)"
            )
            left = _repair_blueprint(
                ctx,
                evidence,
                labels[:mid],
                trial=trial,
                max_trials=max_trials,
                escalation_note=escalation_note,
                repair_runner_agent=repair_runner_agent,
            )
            right = _repair_blueprint(
                ctx,
                evidence,
                labels[mid:],
                trial=trial,
                max_trials=max_trials,
                escalation_note=escalation_note,
                repair_runner_agent=repair_runner_agent,
            )
            return left | right
        raise
    _record(
        ctx.telemetry,
        "model_call",
        purpose="blueprint_repair",
        labels=labels,
        status="success",
        duration_s=time.monotonic() - started,
        timeout_s=ctx.hard_timeout,
        backend=runner.backend_name,
        model=runner.model,
        prompt=prompt_artifact.to_event(REPO_ROOT),
        response=_store_text(ctx.telemetry, "response_blueprint_repair", result.text).to_event(REPO_ROOT),
    )
    if not repair_runner_agent:
        _write_api_refinement(ctx.name, result.text)
    validation = validate_blueprint(REPO_ROOT, ctx.name)
    if not validation.ok:
        print_result(validation)
        raise ValueError("blueprint repair produced an invalid blueprint")
    ctx.refresh_nodes(validation.nodes)
    changed = {
        label
        for label, fp in ctx.contract_fps.items()
        if before_fps.get(label) != fp
    }
    changed |= {label for label in before_fps if label not in ctx.contract_fps}
    changed |= {label for label in ctx.contract_fps if label not in before_fps}
    _record(
        ctx.telemetry,
        "blueprint_repair_result",
        labels=labels,
        changed_labels=sorted(changed),
        changed_count=len(changed),
    )
    return changed


def _section_overlap(a: set[str], b: set[str]) -> float:
    if not a or not b:
        return 0.0
    return len(a & b) / min(len(a), len(b))


def _stuck_state_for(
    states: list[SectionStuckState], section_labels: list[str]
) -> SectionStuckState:
    current = set(section_labels)
    best = max(states, key=lambda state: _section_overlap(state.labels, current), default=None)
    if best is not None and _section_overlap(best.labels, current) >= 0.5:
        best.labels |= current
        return best
    state = SectionStuckState(labels=current)
    states.append(state)
    return state


def _section_normalization_prompt(
    ctx: Ctx,
    blueprint_source: str,
    section_labels: list[str],
    evidence: str,
    *,
    model_timeout_s: int,
    api_mode: bool,
) -> str:
    blocks = _node_tex_blocks(ctx.nodes)
    section_nodes = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; uses "
        f"{', '.join(sorted(ctx.nodes[label].uses)) or 'none'})\n"
        f"```tex\n{blocks.get(label, '')[:5000]}\n```"
        for label in section_labels
        if label in ctx.nodes
    )
    paper_block = f"\nOriginal paper context:\n<paper>\n{ctx.paper_text}\n</paper>\n" if ctx.paper_text else ""
    base = f"""TASK: NORMALIZE-STUCK-BLUEPRINT-SECTION

Phase 1 is repeatedly failing to freeze one dependency-ordered section. Do a
single constrained blueprint normalization pass for that section only.

Goal:
- Make the listed blueprint nodes easier to state one-to-one in Lean.
- Preserve the mathematical content.
- Keep the blueprint as the source of truth; do not write Lean code.

Hard constraints:
- Edit only `blueprints/{ctx.name}/blueprint/src/content.tex`.
- Do not weaken, delete, or replace claims with placeholders.
- Preserve existing labels unless a node must be split.
- If splitting is necessary, insert helper nodes immediately before the node
  that uses them and add explicit `\\uses{{...}}` edges.
- Do not touch unrelated downstream sections.
- Do not rewrite the whole blueprint.
- Keep changes small: target the listed section plus direct helper nodes only.
- After editing, run `python scripts/validate_blueprint.py {ctx.name}`.
- This call has a wall-clock budget of about {model_timeout_s}s.

The recurring evidence is:
```text
{evidence[-12000:]}
```

Section nodes to normalize:
{section_nodes}

{paper_block}
Current blueprint source:
```tex
{blueprint_source}
```
"""
    if not api_mode:
        return base
    return f"""{base}

API MODE: Return exactly one JSON object:
{{
  "content_tex": "full replacement for blueprints/{ctx.name}/blueprint/src/content.tex",
  "notes": "short explanation of the small section-normalization changes"
}}

Do not include `\\begin{{document}}` or `\\end{{document}}`.
"""


def _normalize_stuck_section(
    ctx: Ctx,
    evidence: str,
    section_labels: list[str],
    *,
    trial: int,
    max_trials: int,
    repair_runner_agent: bool,
) -> set[str]:
    """One constrained normalization pass for a repeatedly failing section.

    Rolls back if the model invalidates the blueprint or edits too broadly.
    """
    content_path = REPO_ROOT / "blueprints" / ctx.name / "blueprint" / "src" / "content.tex"
    before_content = content_path.read_text(encoding="utf-8")
    blueprint_source = _read_blueprint_source(ctx.name)
    before_fps = dict(ctx.contract_fps)
    _log(
        f"==> Section normalization {trial}/{max_trials} for: "
        + ", ".join(section_labels[:8])
    )
    prompt = _section_normalization_prompt(
        ctx,
        blueprint_source,
        section_labels,
        evidence,
        model_timeout_s=ctx.hard_timeout,
        api_mode=not repair_runner_agent,
    )
    runner = _make_runner(
        ctx.escalation_runner_spec,
        timeout=ctx.hard_timeout,
        readonly=False,
        effort=ctx.escalation_effort,
        with_skill=True,
    )
    prompt_artifact = _store_text(ctx.telemetry, "prompt_section_normalization", prompt)
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        _record(
            ctx.telemetry,
            "model_call",
            purpose="section_normalization",
            labels=section_labels,
            status="timeout" if _is_timeout_error(exc) else "error",
            duration_s=time.monotonic() - started,
            timeout_s=ctx.hard_timeout,
            backend=runner.backend_name,
            model=runner.model,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
        )
        raise
    _record(
        ctx.telemetry,
        "model_call",
        purpose="section_normalization",
        labels=section_labels,
        status="success",
        duration_s=time.monotonic() - started,
        timeout_s=ctx.hard_timeout,
        backend=runner.backend_name,
        model=runner.model,
        prompt=prompt_artifact.to_event(REPO_ROOT),
        response=_store_text(ctx.telemetry, "response_section_normalization", result.text).to_event(REPO_ROOT),
    )
    try:
        if not repair_runner_agent:
            _write_api_refinement(ctx.name, result.text)
        validation = validate_blueprint(REPO_ROOT, ctx.name)
        if not validation.ok:
            print_result(validation)
            raise ValueError("section normalization produced an invalid blueprint")
        ctx.refresh_nodes(validation.nodes)
        changed = {
            label
            for label, fp in ctx.contract_fps.items()
            if before_fps.get(label) != fp
        }
        changed |= {label for label in before_fps if label not in ctx.contract_fps}
        changed |= {label for label in ctx.contract_fps if label not in before_fps}
        if len(changed) > SECTION_NORMALIZATION_MAX_CHANGED:
            raise SectionNormalizationRejected(
                "section normalization changed too many node contracts "
                f"({len(changed)} > {SECTION_NORMALIZATION_MAX_CHANGED})"
            )
    except SectionNormalizationRejected as exc:
        content_path.write_text(before_content, encoding="utf-8")
        validation = validate_blueprint(REPO_ROOT, ctx.name)
        if validation.ok:
            ctx.refresh_nodes(validation.nodes)
        _record(
            ctx.telemetry,
            "section_normalization_result",
            labels=section_labels,
            status="rejected",
            reason=str(exc),
        )
        raise
    except Exception:
        content_path.write_text(before_content, encoding="utf-8")
        validation = validate_blueprint(REPO_ROOT, ctx.name)
        if validation.ok:
            ctx.refresh_nodes(validation.nodes)
        raise
    _record(
        ctx.telemetry,
        "section_normalization_result",
        labels=section_labels,
        status="applied",
        changed_labels=sorted(changed),
        changed_count=len(changed),
    )
    return changed


# ---------------------------------------------------------------------------
# Final assembly


def _assemble_final(ctx: Ctx, sections: list[Section]) -> str:
    imports: list[str] = []
    bodies: list[str] = []
    for sec in sorted(sections, key=lambda s: s.number):
        parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        for item in parsed.imports:
            if item.startswith("import AutoBlueprint"):
                continue
            if item not in imports:
                imports.append(item)
        body = "\n".join(parsed.preamble + [""] if parsed.preamble else [])
        body += "\n\n".join(d.text for d in parsed.decls)
        bodies.append(body)
    return _compose_lean_file(imports, bodies)


# ---------------------------------------------------------------------------
# Main


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name", help="Existing blueprint name under blueprints/<name>/")
    parser.add_argument(
        "--runner",
        help=(
            "Base runner spec for batched skeleton/proof calls. If omitted, "
            "uses a cheap API runner when OPENAI_API_KEY or ANTHROPIC_API_KEY "
            "is set, otherwise falls back to local Codex."
        ),
    )
    parser.add_argument(
        "--escalation-runner",
        help="Runner spec for escalated singleton/repair calls (default: same as --runner)",
    )
    parser.add_argument("--paper", help="Optional original paper path/URL/text")
    parser.add_argument("--max-trials", type=int, default=8, help="Blueprint-repair budget")
    parser.add_argument("--timeout", type=int, default=300, help="Base per-model-call timeout (s)")
    parser.add_argument("--hard-timeout", type=int, default=600, help="Escalated per-call timeout (s)")
    parser.add_argument("--section-size", type=int, default=DEFAULT_SECTION_SIZE)
    parser.add_argument("--proof-batch-size", type=int, default=DEFAULT_PROOF_BATCH)
    parser.add_argument("--workers", type=int, default=DEFAULT_WORKERS, help="Parallel proof workers")
    parser.add_argument(
        "--reasoning-effort",
        choices=("low", "medium", "high", "xhigh"),
        default="medium",
        help="Codex reasoning effort for batched calls (escalations use --escalation-effort)",
    )
    parser.add_argument(
        "--escalation-effort",
        choices=("low", "medium", "high", "xhigh"),
        default="high",
    )
    parser.add_argument("--continue", dest="continue_run", action="store_true")
    parser.add_argument("--no-ladder", dest="ladder", action="store_false", help="Skip the free tactic ladder")
    parser.add_argument("--no-build", dest="build", action="store_false", help="Skip the site rebuild")
    parser.add_argument("--lean-command", help="Override checker command, e.g. 'lake env lean'")
    args = parser.parse_args(argv)
    default_runner, default_escalation_runner = _default_fast_runner_specs()
    runner = args.runner or default_runner
    escalation_runner = args.escalation_runner or (runner if args.runner else default_escalation_runner)

    if args.max_trials < 1:
        raise SystemExit("--max-trials must be at least 1")
    if args.hard_timeout < args.timeout:
        raise SystemExit("--hard-timeout must be at least --timeout")

    telemetry = TelemetryRun(
        REPO_ROOT,
        blueprint=args.name,
        command=[sys.argv[0], *(argv or sys.argv[1:])],
    )
    telemetry.record(
        "formalize_config",
        runner=runner,
        escalation_runner=escalation_runner,
        runner_was_auto=args.runner is None,
        escalation_runner_was_auto=args.escalation_runner is None,
        max_trials=args.max_trials,
        timeout_s=args.timeout,
        hard_timeout_s=args.hard_timeout,
        section_size=args.section_size,
        proof_batch=args.proof_batch_size,
        workers=args.workers,
        base_effort=args.reasoning_effort,
        escalation_effort=args.escalation_effort,
        continue_run=args.continue_run,
        ladder=args.ladder,
    )

    def finish(code: int, status: str, **fields) -> int:
        telemetry.record("run_end", exit_code=code, status=status, **fields)
        telemetry.flush_upload_queue()
        return code

    paper_text = ""
    if args.paper:
        print(f"==> Reading paper context from {args.paper}", flush=True)
        paper_text, _source = read_paper(args.paper)

    lean_command = shlex.split(args.lean_command) if args.lean_command else _default_lean_command()
    print("==> Checking Lean/Lake/Mathlib setup", flush=True)
    preflight = check_lean_environment(REPO_ROOT, lean_command=lean_command)
    if not preflight.ok:
        raise FileNotFoundError(
            f"{preflight.message}\n{(preflight.stderr or preflight.stdout).strip()}"
        )
    print(f"  {preflight.message} ({preflight.elapsed_s:.1f}s)", flush=True)

    validation = validate_blueprint(REPO_ROOT, args.name)
    print_result(validation)
    if not validation.ok:
        return finish(1, "blueprint_validation_failed")
    node_blocks = _node_tex_blocks(validation.nodes)
    for label, node in validation.nodes.items():
        telemetry.record(
            "node_features",
            **node_structural_features(label, node.kind, node_blocks.get(label, ""), len(node.uses)),
        )

    blueprint_source = _read_blueprint_source(args.name)
    print("==> Searching local Lean libraries once for this run", flush=True)
    library_context, library_candidates = _search_local_lean_libraries(
        args.name, validation.nodes, blueprint_source, term_runner=None
    )

    ctx = Ctx(
        name=args.name,
        runner_spec=runner,
        escalation_runner_spec=escalation_runner,
        base_effort=args.reasoning_effort,
        escalation_effort=args.escalation_effort,
        base_timeout=args.timeout,
        hard_timeout=args.hard_timeout,
        lean_command=lean_command,
        telemetry=telemetry,
        paper_text=paper_text,
        library_context=library_context,
        section_size=args.section_size,
        proof_batch=args.proof_batch_size,
        use_ladder=args.ladder,
    )
    ctx.refresh_nodes(validation.nodes)

    generated_dir = _generated_module_dir(args.name)
    if not args.continue_run and generated_dir.exists():
        # Fresh run: clear skeleton modules from previous runs (old ChunkNN
        # files from the legacy pipeline are cleared too; the two pipelines do
        # not share caches).
        shutil.rmtree(generated_dir)
        with contextlib.suppress(FileNotFoundError, OSError):
            _state_path(args.name).unlink()

    sections: list[Section] = _load_state(ctx, lean_command) if args.continue_run else []
    _prune_stale_generated(ctx, sections)

    report_lines = [
        f"# Statements-First Formalization: `{args.name}`",
        "",
        f"- base runner: `{runner}` (effort `{args.reasoning_effort}`)",
        f"- escalation runner: `{escalation_runner}` (effort `{args.escalation_effort}`)",
        f"- timeouts: `{args.timeout}s` base / `{args.hard_timeout}s` escalated",
        f"- section size: `{args.section_size}`; proof batch: `{args.proof_batch_size}`; workers: `{args.workers}`",
        f"- blueprint repair budget: `{args.max_trials}`",
        f"- library candidates: `{len(library_candidates)}`",
        "",
    ]

    repair_trials = 0
    noop_repairs = 0
    escalation_note = ""
    stuck_sections: list[SectionStuckState] = []
    started = time.monotonic()
    try:
        while True:
            frozen = _frozen_labels(sections)
            pending = {
                label
                for label, node in ctx.nodes.items()
                if not node.mathlibok and label not in frozen
            }
            evidence_for_repair: str | None = None
            repair_labels: list[str] = []
            repair_helpers: list[str] = []
            repair_section_labels: list[str] = []
            phase1_repair = False

            if pending:
                print(
                    f"==> Phase 1: freezing statements for {len(pending)} node(s) "
                    f"({len(frozen)} already frozen)",
                    flush=True,
                )
                try:
                    sections = _run_phase1(ctx, sections, pending)
                    _save_state(args.name, sections, ctx.stmt_fps, ctx.contract_fps)
                except RepairRequest as request:
                    evidence_for_repair = request.evidence
                    repair_labels = request.labels
                    repair_helpers = request.decomposition_helpers
                    repair_section_labels = request.section_labels
                    phase1_repair = True

            if evidence_for_repair is None:
                unproved_sections = []
                for sec in sections:
                    parsed, index = _module_decl_texts(sec)
                    if any(
                        _lean_name(label) in index
                        and _has_terminal_sorry(parsed.decls[index[_lean_name(label)]].text)
                        for label in sec.labels
                    ):
                        unproved_sections.append(sec)
                if unproved_sections:
                    print(
                        f"==> Phase 2: filling proofs in {len(unproved_sections)} section(s) "
                        f"with {args.workers} worker(s)",
                        flush=True,
                    )
                    outcomes: list[SectionProofOutcome] = []
                    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
                        futures = [
                            pool.submit(_prove_section, ctx, sec, sections)
                            for sec in unproved_sections
                        ]
                        for future in concurrent.futures.as_completed(futures):
                            outcomes.append(future.result())
                    _save_state(args.name, sections, ctx.stmt_fps, ctx.contract_fps)
                    failed: dict[str, str] = {}
                    helpers: list[str] = []
                    for outcome in outcomes:
                        failed.update(outcome.failed)
                        for label, missing in outcome.decomposition.items():
                            failed[label] = failed.get(label, "generator requested decomposition")
                            helpers.extend(missing)
                    if failed:
                        parts = []
                        for label, error in sorted(failed.items()):
                            parts.append(
                                f"== Node {label} ==\n"
                                f"Blueprint statement:\n{ctx.stmt_blocks.get(label, '')[:2500]}\n"
                                f"Lean evidence:\n{error[-3500:]}"
                            )
                        evidence_for_repair = (
                            "Proof search failed for the nodes below after batched and "
                            "escalated attempts. Repair the blueprint: add the missing "
                            "intermediate lemma/definition nodes, hypotheses, or split "
                            "nodes whose proofs are too large for one declaration.\n\n"
                            + "\n\n".join(parts)
                        )
                        repair_labels = sorted(failed)
                        repair_helpers = helpers
                        repair_section_labels = repair_labels

            if evidence_for_repair is None:
                proved = _proved_labels(sections)
                required = {
                    label for label, node in ctx.nodes.items() if not node.mathlibok
                }
                if required <= proved:
                    final_code = _assemble_final(ctx, sections)
                    final_path = SCRATCH_DIR / args.name / "assembled_formalization.lean"
                    final_path.parent.mkdir(parents=True, exist_ok=True)
                    final_path.write_text(final_code, encoding="utf-8")
                    print("==> Final from-scratch Lean check on the assembled file", flush=True)
                    final_attempt = _run_lean(final_path, lean_command)
                    coverage_issues = (
                        _deterministic_statement_audit(
                            final_code,
                            {l: n for l, n in ctx.nodes.items() if not n.mathlibok},
                            ctx.nodes,
                        )
                        if final_attempt.ok
                        else []
                    )
                    _record(
                        ctx.telemetry,
                        "final_check_result",
                        lean_ok=final_attempt.ok,
                        coverage_ok=not coverage_issues,
                        coverage_issues=coverage_issues,
                        output_tail=final_attempt.output[-4000:] if not final_attempt.ok else "",
                    )
                    if final_attempt.ok and not coverage_issues:
                        published = _publish_lean_text(args.name, final_code)
                        report_lines += [
                            "## Complete",
                            f"- elapsed: `{int(time.monotonic() - started)}s`",
                            f"- blueprint repairs used: `{repair_trials}/{args.max_trials}`",
                            f"- published Lean: `{published.relative_to(REPO_ROOT)}`",
                        ]
                        if args.build:
                            site_lean = _rebuild_site_for(args.name)
                            report_lines.append(f"- site Lean: `{site_lean.relative_to(REPO_ROOT)}`")
                        report = _write_report(args.name, report_lines)
                        print(f"All nodes formalized. Published {published.relative_to(REPO_ROOT)}")
                        print(f"Report written to {report.relative_to(REPO_ROOT)}")
                        return finish(0, "complete", repairs=repair_trials)
                    evidence_for_repair = (
                        "Final assembled check failed:\n"
                        + (final_attempt.output[-8000:] if not final_attempt.ok else "")
                        + "\n".join(coverage_issues)
                    )
                    repair_labels = sorted(required - proved) or sorted(required)
                    repair_section_labels = repair_labels
                else:
                    # Shouldn't happen: no failures reported but nodes unproved.
                    evidence_for_repair = "Internal inconsistency: unproved nodes without failure evidence: " + ", ".join(sorted(required - proved))
                    repair_labels = sorted(required - proved)
                    repair_section_labels = repair_labels

            # --- blueprint repair path (the ONLY route that edits the blueprint)
            if repair_trials >= args.max_trials:
                report_lines += [
                    "## Stopped: blueprint repair budget exhausted",
                    "",
                    "```text",
                    evidence_for_repair[-6000:],
                    "```",
                ]
                report = _write_report(args.name, report_lines)
                print(f"Stopped after {args.max_trials} blueprint repair trial(s).")
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                print("Frozen statements and accepted proofs are kept; rerun with --continue.")
                return finish(1, "max_trials_exhausted", unresolved=repair_labels)

            stuck_state: SectionStuckState | None = None
            use_section_normalization = False
            if phase1_repair and repair_section_labels:
                stuck_state = _stuck_state_for(stuck_sections, repair_section_labels)
                use_section_normalization = (
                    stuck_state.repairs >= SECTION_NORMALIZATION_REPAIR_TRIGGER
                    and not stuck_state.normalized
                )

            repair_trials += 1
            note = escalation_note
            if repair_helpers:
                note = _decomposition_note(repair_labels, repair_helpers)
            action = "normalization" if use_section_normalization else "repair"
            if use_section_normalization and stuck_state is not None:
                try:
                    changed = _normalize_stuck_section(
                        ctx,
                        evidence_for_repair,
                        repair_section_labels,
                        trial=repair_trials,
                        max_trials=args.max_trials,
                        repair_runner_agent=escalation_runner.partition(":")[0] in {"codex", "claude-code"},
                    )
                    stuck_state.normalized = True
                    report_lines.append(
                        f"- section normalization {repair_trials}: {len(changed)} node contract(s) changed "
                        f"for `{', '.join(repair_section_labels[:8])}`"
                    )
                except SectionNormalizationRejected as exc:
                    stuck_state.normalized = True
                    action = "repair"
                    fallback_note = (
                        f"Constrained section normalization was rolled back automatically: {exc}. "
                        "Do a narrower repair/decomposition now. Edit only the listed failing "
                        "node contracts unless a new helper node is strictly required by their "
                        "dependency-closed proof structure."
                    )
                    report_lines.append(
                        f"- section normalization {repair_trials}: rejected and rolled back ({exc}); "
                        "falling back to targeted repair"
                    )
                    changed = _repair_blueprint(
                        ctx,
                        evidence_for_repair,
                        repair_labels,
                        trial=repair_trials,
                        max_trials=args.max_trials,
                        escalation_note=fallback_note,
                        repair_runner_agent=escalation_runner.partition(":")[0] in {"codex", "claude-code"},
                    )
                    report_lines.append(
                        f"- fallback repair {repair_trials}: {len(changed)} node statement(s) changed "
                        f"for `{', '.join(repair_labels[:8])}`"
                    )
                    stuck_state.repairs += 1
                    stuck_state.repairs_after_normalization += 1
            else:
                changed = _repair_blueprint(
                    ctx,
                    evidence_for_repair,
                    repair_labels,
                    trial=repair_trials,
                    max_trials=args.max_trials,
                    escalation_note=note,
                    repair_runner_agent=escalation_runner.partition(":")[0] in {"codex", "claude-code"},
                )
                report_lines.append(
                    f"- repair {repair_trials}: {len(changed)} node statement(s) changed "
                    f"for `{', '.join(repair_labels[:8])}`"
                )
                if stuck_state is not None:
                    stuck_state.repairs += 1
                    if stuck_state.normalized:
                        stuck_state.repairs_after_normalization += 1
            if changed:
                noop_repairs = 0
                escalation_note = ""
                sections, invalidated = _invalidate_after_repair(
                    ctx, sections, changed, lean_command
                )
                _save_state(args.name, sections, ctx.stmt_fps, ctx.contract_fps)
                print(
                    f"  {action} changed {len(changed)} statement(s); invalidated "
                    f"{len(invalidated)} node(s); kept {len(sections)} skeleton section(s)",
                    flush=True,
                )
            else:
                noop_repairs += 1
                if noop_repairs == 1:
                    escalation_note = (
                        "Your previous repair changed NOTHING in the parsed node "
                        "statements. You MUST materially edit the TeX of the listed "
                        "node(s): add missing concrete semantics, hypotheses, or split "
                        "them into smaller nodes."
                    )
                else:
                    escalation_note = _decomposition_note(repair_labels)
                print("  repair was a no-op; escalating instructions", flush=True)
    except RunnerError as exc:
        report_lines += ["## Stopped on runner error", "", "```text", str(exc)[-4000:], "```"]
        report = _write_report(args.name, report_lines)
        print(f"Runner error stopped the run: {exc}", flush=True)
        print(f"Report written to {report.relative_to(REPO_ROOT)}")
        print("State is saved; rerun with --continue once the environment is fixed.")
        status = "environment_error" if is_environment_error(exc) else "runner_error"
        return finish(1, status, error=str(exc))
    except ValueError as exc:
        report_lines += ["## Stopped", "", "```text", str(exc)[-4000:], "```"]
        report = _write_report(args.name, report_lines)
        print(f"Stopped: {exc}", flush=True)
        print(f"Report written to {report.relative_to(REPO_ROOT)}")
        return finish(1, "invalid_state", error=str(exc))


def logged_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("name", nargs="?")
    known, _unknown = parser.parse_known_args(argv)
    if not known.name:
        return main(argv)
    log_path = _run_log_path(known.name)
    with log_path.open("w", encoding="utf-8") as log_file:
        log_file.write("# Auto-Blueprint statements-first formalization log\n")
        log_file.write(f"# cwd: {REPO_ROOT}\n")
        log_file.write(f"# command: {' '.join([sys.argv[0], *(argv or sys.argv[1:])])}\n\n")
        started_at = time.monotonic()
        with contextlib.redirect_stdout(
            TeeStream(sys.stdout, log_file, started_at=started_at)
        ), contextlib.redirect_stderr(TeeStream(sys.stderr, log_file, started_at=started_at)):
            print(f"Log file: {log_path.relative_to(REPO_ROOT)}", flush=True)
            try:
                return main(argv)
            except (FileNotFoundError, RunnerError, subprocess.CalledProcessError) as exc:
                print(f"error: {exc}", file=sys.stderr)
                return 2
            finally:
                print(f"Log file: {log_path.relative_to(REPO_ROOT)}", flush=True)


if __name__ == "__main__":
    raise SystemExit(logged_main())
