#!/usr/bin/env python3
"""Statements-first Lean formalization pipeline.

This is the fast successor to ``refine_blueprint_with_lean.py``. The blueprint
remains the only mathematical source of truth and Lean remains the critic; what
changes is *when* model calls happen and how much each one is asked to do:

Phase 1 (skeleton). A few batched model calls generate one Lean declaration per
blueprint node, section by section in dependency order: real bodies for
definition nodes, ``:= sorry`` proofs for theorem-like nodes. Each section is
compiled locally; compiler-isolated declarations are patched before broad
regeneration. The blueprint-contract audit (deterministic coverage + one
batched model audit per section) then checks the frozen statements against the
node text and proof obligations before proof effort is spent, with isolated
semantic rejections patched in place too. Accepted statements are frozen: later
phases may only replace ``sorry`` bodies, never edit a statement. A statement
that cannot faithfully encode its node routes to blueprint repair, exactly as
before.

Phase 2 (proofs). By default, theorem-like roots are proved first against the
frozen interfaces of their still-``sorry`` dependencies. The scheduler then
walks backward through the blueprint dependency graph, discharging the next
required frontier while preserving accepted root proofs. For every frozen
``sorry``:
1. a deterministic tactic ladder (``rfl``/``omega``/``norm_num``/``ring``/
   ``simp``/``aesop``) runs first, with zero model cost;
2. survivors are filled by batched model calls (10-20 proofs per call);
3. the residue escalates to singleton calls at high reasoning effort;
4. persistent failures become *evidence* for a bounded blueprint repair.

Timeouts are treated as latency, never as mathematical difficulty: a timed-out
call is bisected or retried at higher effort. Only real Lean/audit output (or
an explicit NEEDS-DECOMPOSITION refusal) can trigger a blueprint repair, and
repairs regenerate changed full-node contracts. Unchanged descendants are
deferred, rebound to the repaired modules, and deterministically recompiled;
only failed rechecks return to model generation. Proof-sketch edits therefore
still recheck the Lean that is supposed to certify them.

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
from typing import Iterable

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
    _alignment_failure_kind,
    _compile_module_olean,
    _compose_lean_file,
    _decomposition_note,
    _default_lean_command,
    _dependency_closure,
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
    _search_terms_from_blueprint,
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

# Node kinds whose Lean form is a definition with a real body. Everything
# else — the builtin theorem environments plus any \newtheorem-declared
# environment a blueprint author adds (claim, fact, remark, observation, ...)
# — is theorem-like: a Prop statement whose proof is deferred with `:= sorry`
# in the skeleton and supplied in Phase 2. validate_blueprint accepts
# arbitrary \newtheorem environments as node kinds, so theorem-likeness must
# be computed by exclusion: enumerating theorem-like names made a `claim`
# node simultaneously require a sorry-free definition (deterministic audit)
# and a theorem (alignment audit) — an unsatisfiable contradiction.
DEFINITION_LIKE_KINDS = {"definition", "defn", "construction", "notation", "convention", "setup"}


def _is_theorem_like_kind(kind: str | None) -> bool:
    return bool(kind) and kind not in DEFINITION_LIKE_KINDS
DEFAULT_SECTION_SIZE = 24
DEFAULT_PROOF_BATCH = 12
DEFAULT_WORKERS = 3
DEFAULT_PROOF_ORDER = "top-down"
# Bounded per-section transaction: one base generation attempt plus at most
# one escalated retry. Every stage (deterministic patch, compile patch, audit
# correction) gets exactly one targeted fix before the attempt is spent; a
# section that survives neither attempt routes to blueprint repair with fresh
# attempts after the contract changes. The old 6-round nested retry maze
# burned 7+ model calls per stuck node and still ended in the same repair.
SKELETON_GENERATION_ATTEMPTS = 2
# Front-loaded design pass: state the whole pending graph in one call before
# the per-section loop runs. Statements must COMPILE leaf-first, but designing
# each definition in isolation from the results that consume it is what
# produced contradictory foundations (a class defined as a subset of the set a
# theorem was meant to prove it equals). One pass that reasons root-first over
# the whole graph both fixes that and collapses ~20 section calls into ~1-3.
# Below the minimum the per-section loop is already cheap enough to just run.
BULK_SKELETON_MIN_NODES = 6
# Emission chunk. The design decisions are already fixed by the plan pass, so
# a chunk is transcription rather than thinking; keep it near section size so
# each call comfortably fits its budget. (A single 39-node emit-and-design
# call blew the 600s hard budget without delivering anything.)
BULK_SKELETON_CHUNK = 12
# The plan pass emits ~1-2 lines per node, so the whole graph fits one call.
DESIGN_PLAN_MAX_NODES = 120
# One declaration-local patch is enough to tell whether the current model tier
# can use the compiler feedback; a second failure moves to the fresh escalated
# attempt. Repeating declaration patches was responsible for most of the model
# calls in long Phase 1 runs.
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


def _immediate_theorem_dependencies(
    nodes: dict[str, Node], label: str, theorem_labels: set[str]
) -> set[str]:
    """The nearest theorem-like dependencies below ``label``.

    Definition nodes are transparent for proof scheduling: if a theorem uses a
    definition that in turn uses a lemma, that lemma is still the next proof
    frontier. This changes only proof order; the original ``uses`` graph remains
    the source of truth for imports, audits, and invalidation.
    """
    found: set[str] = set()
    seen: set[str] = set()
    stack = list(nodes[label].uses) if label in nodes else []
    while stack:
        dep = stack.pop()
        if dep in seen or dep not in nodes:
            continue
        seen.add(dep)
        if dep in theorem_labels:
            found.add(dep)
            continue
        stack.extend(nodes[dep].uses)
    return found


def _top_down_proof_layers(nodes: dict[str, Node]) -> list[list[str]]:
    """Return theorem-like nodes from public roots down to proof leaves.

    Roots are theorem-like nodes that no other theorem-like node depends on.
    Breadth-first layers then follow the nearest theorem dependencies. Stable
    source order keeps telemetry and resumes deterministic.
    """
    source_order = _node_order(nodes)
    position = {label: index for index, label in enumerate(source_order)}
    theorem_labels = {
        label
        for label, node in nodes.items()
        if not node.mathlibok and _is_theorem_like_kind(node.kind)
    }
    immediate = {
        label: _immediate_theorem_dependencies(nodes, label, theorem_labels)
        for label in theorem_labels
    }
    consumed = {dep for deps in immediate.values() for dep in deps}
    roots = sorted(theorem_labels - consumed, key=position.get)
    if not roots:
        roots = sorted(theorem_labels, key=position.get)

    depth: dict[str, int] = {}
    frontier = list(roots)
    current_depth = 0
    while frontier:
        next_frontier: set[str] = set()
        for label in frontier:
            previous = depth.get(label)
            # Keep the longest root-to-node depth. A theorem may be referenced
            # both directly by a root and through another theorem; assigning
            # the shortest depth would put consumer and dependency in the same
            # parallel frontier.
            if previous is not None and previous >= current_depth:
                continue
            depth[label] = current_depth
            next_frontier.update(immediate.get(label, set()))
        frontier = sorted(next_frontier, key=position.get)
        current_depth += 1

    # Defensive coverage for disconnected or malformed subgraphs. Validation
    # normally makes this unnecessary, but no theorem should disappear from a
    # scheduler because of an unexpected graph shape.
    for label in theorem_labels:
        depth.setdefault(label, current_depth)
    return [
        sorted((label for label, item_depth in depth.items() if item_depth == layer), key=position.get)
        for layer in range(max(depth.values(), default=-1) + 1)
    ]


def _next_top_down_frontier(
    nodes: dict[str, Node], unproved: set[str]
) -> tuple[int, list[str], list[str]]:
    """Return ``(layer, unresolved labels, all roots)`` for the next proof wave."""
    layers = _top_down_proof_layers(nodes)
    roots = layers[0] if layers else []
    for layer, labels in enumerate(layers):
        pending = [label for label in labels if label in unproved]
        if pending:
            return layer, pending, roots
    return -1, [], roots


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


def _lean_compile_findings(
    parsed: ParsedModule,
    labels: list[str],
    ranges: list[tuple[int, int]],
    output: str,
    file_name: str,
) -> list[SkeletonFinding]:
    """Turn Lean diagnostics into declaration-targeted skeleton findings."""
    by_decl, file_level = _errors_by_decl(output, file_name, ranges)
    label_by_name = {_lean_name(label): label for label in labels}
    findings: list[SkeletonFinding] = []
    for index, messages in sorted(by_decl.items()):
        decl = parsed.decls[index] if index < len(parsed.decls) else None
        lean_name = decl.name if decl is not None else None
        label = label_by_name.get(lean_name or "")
        findings.append(
            SkeletonFinding(
                "Lean rejected this generated declaration:\n"
                + "\n".join(messages)[-6000:],
                label=label,
                lean_name=lean_name,
            )
        )
    findings.extend(
        SkeletonFinding("Lean file-level error:\n" + message[-6000:])
        for message in file_level
    )
    if not findings:
        findings.append(SkeletonFinding("Lean rejected the file:\n" + output[-6000:]))
    return findings


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
        if _is_theorem_like_kind(expected_kind) and _has_terminal_sorry(decl.text):
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
    # Output the backend had already emitted when a timeout killed it. Callers
    # may salvage complete declarations from it instead of discarding the call.
    partial_text: str = ""


class RepairRequest(Exception):
    """Raised when only a blueprint edit can unblock progress."""

    def __init__(
        self,
        evidence: str,
        labels: list[str],
        *,
        decomposition_helpers: list[str] | None = None,
        section_labels: list[str] | None = None,
        frozen_sections: list["Section"] | None = None,
    ):
        super().__init__(evidence[:500])
        self.evidence = evidence
        self.labels = labels
        self.decomposition_helpers = decomposition_helpers or []
        self.section_labels = section_labels or list(labels)
        # Recursive section routing may freeze an easy prefix before a later
        # singleton proves that the blueprint needs repair. Preserve that work
        # across the exception instead of regenerating it after the repair.
        self.frozen_sections = frozen_sections or []


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
    # Run-scoped adaptive Phase-1 section size. Only measured latency changes
    # capacity; a refusal about one named node is routed around that node.
    effective_section_size: int = 0
    # Largest size at which a group froze without a timeout-shrink this run.
    # Recovery back up to this size is fast (doubling per clean group);
    # exploring beyond it uses the cautious rule.
    proven_section_size: int = 0
    # Kept on the context so blueprint repairs and recursive splits do not
    # erase evidence that recent sections fit within the current budget.
    section_clean_streak: int = 0
    # Labels that repeatedly failed or explicitly requested isolation. Keep
    # them out of broad batches until their current contract freezes; this is
    # scheduler state, not a claim that the blueprint node is mathematically
    # hard.
    quarantined_labels: set[str] = field(default_factory=set)
    # Quarantine is valid only for the exact blueprint statement that produced
    # the routing evidence. Keeping the fingerprint and failure class prevents
    # a repaired statement (or an old --continue run) from inheriting a stale
    # singleton decision that would destroy Phase-1 batching.
    quarantine: dict[str, dict[str, str]] = field(default_factory=dict)
    nodes: dict[str, Node] = field(default_factory=dict)
    stmt_blocks: dict[str, str] = field(default_factory=dict)
    tex_blocks: dict[str, str] = field(default_factory=dict)
    stmt_fps: dict[str, str] = field(default_factory=dict)
    contract_fps: dict[str, str] = field(default_factory=dict)
    unavailable_imports: set[str] = field(default_factory=set)
    # Raw library candidates behind ``library_context``; prompts slice these
    # per target node instead of repeating the full global blob.
    library_candidates: list = field(default_factory=list)
    # Compact root-first interface plan for the pending graph (one or two
    # lines per node). Produced once per Phase-1 wave and injected into every
    # skeleton prompt so sections transcribe agreed decisions instead of
    # re-deriving them in isolation.
    design_plan: str = ""

    def refresh_nodes(self, nodes: dict[str, Node]) -> None:
        self.nodes = nodes
        self.stmt_blocks = _statement_blocks(nodes)
        self.tex_blocks = _node_tex_blocks(nodes)
        self.stmt_fps = _statement_fingerprints(nodes)
        self.contract_fps = _contract_fingerprints(nodes)
        _prune_stale_quarantine(self)


def _quarantine_labels(ctx: Ctx, labels: Iterable[str], failure_class: str) -> None:
    """Route exact failing statement versions as singletons.

    Quarantine is scheduling evidence, not a permanent property of a label.
    A later blueprint repair changes the statement fingerprint and
    ``refresh_nodes`` removes the stale entry automatically.
    """
    added: dict[str, dict[str, str]] = {}
    for label in labels:
        statement_fp = ctx.stmt_fps.get(label, "")
        if not statement_fp:
            continue
        previous = ctx.quarantine.get(label)
        ctx.quarantined_labels.add(label)
        if previous and previous.get("statement_fp") == statement_fp:
            # Preserve the first observed failure class for classifier data;
            # repeated symptoms for the same contract do not change routing.
            continue
        ctx.quarantine[label] = {
            "statement_fp": statement_fp,
            "failure_class": failure_class,
        }
        added[label] = dict(ctx.quarantine[label])
    telemetry = getattr(ctx, "telemetry", None)
    if added and telemetry is not None:
        _record(
            telemetry,
            "skeleton_quarantine_created",
            labels=sorted(added),
            records={label: added[label] for label in sorted(added)},
        )


def _release_quarantine(
    ctx: Ctx, labels: Iterable[str], *, reason: str = "statement_frozen"
) -> None:
    released: dict[str, dict[str, str]] = {}
    for label in labels:
        if label in ctx.quarantine:
            released[label] = dict(ctx.quarantine[label])
        ctx.quarantined_labels.discard(label)
        ctx.quarantine.pop(label, None)
    telemetry = getattr(ctx, "telemetry", None)
    if released and telemetry is not None:
        _record(
            telemetry,
            "skeleton_quarantine_released",
            labels=sorted(released),
            reason=reason,
            records={label: released[label] for label in sorted(released)},
        )


def _prune_stale_quarantine(ctx: Ctx) -> set[str]:
    """Drop routing evidence whose label or statement version has changed."""
    stale = {
        label
        for label in ctx.quarantined_labels
        if label not in ctx.nodes
        or ctx.quarantine.get(label, {}).get("statement_fp")
        != ctx.stmt_fps.get(label)
    }
    if stale:
        _release_quarantine(
            ctx, stale, reason="statement_fingerprint_changed"
        )
    return stale


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
    prompt_artifact = _store_text(ctx.telemetry, f"prompt_{purpose}", prompt)
    try:
        runner = _make_runner(
            runner_spec,
            timeout=timeout,
            readonly=readonly,
            effort=effort,
            resume_session_id=resume_session_id,
        )
    except RunnerError as exc:
        _record(
            ctx.telemetry,
            "model_call",
            purpose=purpose,
            labels=labels,
            status="error",
            duration_s=0.0,
            timeout_s=timeout,
            effort=effort or "",
            backend=runner_spec.partition(":")[0],
            model=runner_spec.partition(":")[2],
            resumed_session=bool(resume_session_id),
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
        )
        if is_environment_error(exc):
            # Missing CLI, expired auth, exhausted quota: no amount of
            # retrying, escalating, or repairing the blueprint can fix this.
            # Propagate so the run stops with saved state instead of spinning
            # generation -> escalation -> repair and burning the repair budget
            # against a dead backend (observed: 33 trials in 3 seconds).
            raise
        return CallResult(status="error", error=str(exc), duration_s=0.0)
    _log(
        f"==> Model call: {purpose} "
        f"({len(labels)} node(s), timeout {timeout}s"
        + (", escalated" if escalated else "")
        + (", resumed" if resume_session_id else "")
        + ")",
        tag=tag,
    )
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        duration = time.monotonic() - started
        status = "timeout" if _is_timeout_error(exc) else "error"
        if is_environment_error(exc):
            if sessions is not None:
                sessions.pop(runner_spec, None)
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
                environment_error=True,
            )
            _log(f"model call ({purpose}) environment error: {str(exc)[:160]}", tag=tag)
            raise
        observed = getattr(runner, "observed_session_id", None)
        captured_for_resume = bool(status == "timeout" and observed)
        if sessions is not None:
            if captured_for_resume:
                # The killed CLI already persisted its transcript and printed
                # its session id, so the retry can resume the exploration
                # instead of restarting cold. Resume is best-effort: both
                # runners fall back to a fresh session if the id is unusable.
                sessions[runner_spec] = observed
            else:
                sessions.pop(runner_spec, None)
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
            session_captured_for_resume=captured_for_resume,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
        )
        _log(f"model call ({purpose}) {status}: {str(exc)[:160]}", tag=tag)
        return CallResult(
            status=status,
            error=str(exc),
            duration_s=duration,
            partial_text=getattr(runner, "partial_text", "") if status == "timeout" else "",
        )
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
    # A blueprint repair changed an upstream contract, but this section's own
    # node contracts did not change. Deferred sections are retained as local
    # cache candidates, not counted as frozen, until their imports are rebound
    # and Lean recompiles them against the repaired dependencies.
    deferred: bool = False

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


def _lake_olean_path(path: Path) -> Path:
    source_rel = path.resolve().relative_to(REPO_ROOT)
    return (REPO_ROOT / ".lake" / "build" / "lib" / "lean" / source_rel).with_suffix(".olean")


def _discard_section_artifacts(path: Path) -> None:
    """Remove the source and objects of a section that was NOT frozen.

    A section file is written before Lean checks it, so an abandoned attempt
    used to survive on disk. Later generation calls glob the generated
    directory, find that orphan, and `import` it — resolving the import
    against a stale `.olean` from an earlier run, which fails in ways that
    have nothing to do with the nodes being stated. Every abandoned section
    must leave the workspace exactly as it found it.
    """
    with contextlib.suppress(OSError):
        path.unlink(missing_ok=True)
    with contextlib.suppress(OSError, ValueError):
        _lake_olean_path(path).unlink(missing_ok=True)
    with contextlib.suppress(OSError):
        path.with_suffix(".olean").unlink(missing_ok=True)


def _save_state(
    name: str,
    sections: list[Section],
    stmt_fps: dict[str, str],
    contract_fps: dict[str, str],
    *,
    quarantined_labels: set[str] | None = None,
    quarantine: dict[str, dict[str, str]] | None = None,
    effective_section_size: int = 0,
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
                "deferred": sec.deferred,
            }
        )
    # Direct callers may still provide only labels. Persist them with the
    # statement fingerprints available to this save so even that compatibility
    # path cannot create label-only quarantine state.
    quarantine_payload = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "failure_class": str(entry.get("failure_class") or "unknown"),
        }
        for label, entry in (quarantine or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
    }
    for label in quarantined_labels or set():
        if label in stmt_fps and label not in quarantine_payload:
            quarantine_payload[label] = {
                "statement_fp": stmt_fps[label],
                "failure_class": "unspecified",
            }

    path = _state_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "version": 3,
                "sections": entries,
                "scheduler": {
                    "quarantine": {
                        label: quarantine_payload[label]
                        for label in sorted(quarantine_payload)
                    },
                    "effective_section_size": effective_section_size,
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def _save_ctx_state(ctx: Ctx, sections: list[Section]) -> None:
    _save_state(
        ctx.name,
        sections,
        ctx.stmt_fps,
        ctx.contract_fps,
        quarantined_labels=ctx.quarantined_labels,
        quarantine=ctx.quarantine,
        effective_section_size=ctx.effective_section_size,
    )


def _load_state(ctx: Ctx, lean_command: list[str]) -> list[Section]:
    """Resume: keep sections whose file and blueprint contracts are unchanged.

    A section importing a stale module is loaded as deferred when all of its
    own full contracts still match. It cannot count as frozen until imports are
    rebound and Lean recompiles it against regenerated dependencies.
    """
    try:
        payload = json.loads(_state_path(ctx.name).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    entries = payload.get("sections") or []
    scheduler = payload.get("scheduler") or {}
    raw_quarantine = scheduler.get("quarantine") or {}
    ctx.quarantine = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "failure_class": str(entry.get("failure_class") or "unknown"),
        }
        for label, entry in raw_quarantine.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
    }
    ctx.quarantined_labels = set(ctx.quarantine)
    legacy_quarantine = {
        str(label)
        for label in scheduler.get("quarantined_labels") or []
        if str(label) in ctx.nodes
    }
    if legacy_quarantine:
        # Version-2 state did not identify which statement version failed.
        # Reusing it after blueprint repairs is precisely what caused resumed
        # runs to degrade into one model call per node, so migrate by dropping
        # it rather than guessing.
        telemetry = getattr(ctx, "telemetry", None)
        if telemetry is not None:
            _record(
                telemetry,
                "skeleton_quarantine_released",
                labels=sorted(legacy_quarantine),
                reason="legacy_state_missing_statement_fingerprint",
            )
    saved_size = int(scheduler.get("effective_section_size") or 0)
    if saved_size > 0:
        ctx.effective_section_size = min(ctx.section_size, saved_size)
    generated_dir = _generated_module_dir(ctx.name)

    kept: list[Section] = []
    dropped_labels: set[str] = set()
    dropped_modules: set[str] = set()
    for entry in entries:
        path = generated_dir / str(entry.get("file") or "")
        labels = [str(label) for label in entry.get("labels") or []]
        entry_deferred = bool(entry.get("deferred", False))
        stmt_fps = entry.get("statement_fps") or {}
        contract_fps = entry.get("contract_fps") or {}
        own_contracts_ok = (
            path.is_file()
            and labels
            and all(
                label in ctx.nodes
                and ctx.stmt_fps.get(label) == stmt_fps.get(label)
                and ctx.contract_fps.get(label) == contract_fps.get(label)
                for label in labels
            )
        )
        dependency_stale = any(
            dep in dropped_modules for dep in entry.get("import_modules") or []
        )
        if own_contracts_ok and dropped_labels:
            invalidated = (
                _dependency_descendants(ctx.nodes, dropped_labels) - dropped_labels
            )
            dependency_stale = dependency_stale or bool(set(labels) & invalidated)
        if own_contracts_ok and dependency_stale:
            # This section's own contract is still current. Preserve its source
            # as deferred cache even though an imported dependency was dropped.
            entry_deferred = True
        ok = own_contracts_ok
        if (
            ok
            and entry_deferred
            and hashlib.sha256(path.read_bytes()).hexdigest() != entry.get("sha256")
        ):
            # Deferred code is not accepted and cannot be semantically audited
            # from state alone. A modified cache candidate is regenerated.
            ok = False
        if (
            ok
            and not entry_deferred
            and hashlib.sha256(path.read_bytes()).hexdigest() != entry.get("sha256")
        ):
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
            deferred=entry_deferred,
        )
        if sec.deferred:
            with contextlib.suppress(FileNotFoundError, OSError):
                path.with_suffix(".olean").unlink()
        elif not path.with_suffix(".olean").is_file() or not _lake_olean_path(path).is_file():
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
    return {
        label for sec in sections if not sec.deferred for label in sec.labels
    }


def _reserved_labels(sections: list[Section]) -> set[str]:
    """Contracts owned by active or deterministically deferred sections."""
    return {label for sec in sections for label in sec.labels}


def _proved_labels(sections: list[Section]) -> set[str]:
    proved: set[str] = set()
    for sec in sections:
        if sec.deferred:
            continue
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
    owner = {
        label: sec.module
        for sec in sections
        if not sec.deferred
        for label in sec.labels
    }
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


def _dependency_contract_table(
    ctx: Ctx, labels: list[str], sections: list[Section]
) -> str:
    """Deterministically tell the model how every direct dependency is owned.

    In particular, ``\\mathlibok`` nodes use their settled ``\\lean{...}`` name;
    their generated label name must never be requested as a missing helper.
    """
    target_set = set(labels)
    owner = {
        label: sec.module
        for sec in sections
        if not sec.deferred
        for label in sec.labels
    }
    lines: list[str] = []
    for label in labels:
        for dep in sorted(ctx.nodes[label].uses):
            node = ctx.nodes.get(dep)
            if node is None:
                continue
            if node.mathlibok:
                actual = node.lean_decl or "(missing \\lean mapping)"
                ownership = (
                    f"Mathlib-owned; use `{actual}` exactly; "
                    f"do NOT generate or request `{_lean_name(dep)}`"
                )
            elif dep in target_set:
                ownership = f"generated earlier in this same file as `{_lean_name(dep)}`"
            elif dep in owner:
                ownership = f"frozen in `{owner[dep]}` as `{_lean_name(dep)}`"
            else:
                ownership = f"generated dependency not frozen yet as `{_lean_name(dep)}`"
            lines.append(f"- {label} -> {dep}: {ownership}")
    return "\n".join(dict.fromkeys(lines)) or "- no direct dependencies"


def _transitive_dependencies(nodes: dict[str, Node], label: str) -> set[str]:
    found: set[str] = set()
    stack = list(nodes.get(label, Node(label, "", Path("."), 0)).uses)
    while stack:
        dep = stack.pop()
        if dep in found:
            continue
        found.add(dep)
        if dep in nodes:
            stack.extend(nodes[dep].uses)
    return found


def _repair_graph_distances(
    before: dict[str, Node],
    after: dict[str, Node],
    targets: list[str],
    changed: set[str],
) -> dict[str, int | None]:
    """Distance of each changed contract from a requested repair target.

    The union of the old and new undirected dependency graphs handles helper
    insertion, edge reversal during normalization, and deleted labels. This is
    deterministic repair-scope evidence for telemetry; it does not overrule a
    valid repair or add a critic call.
    """
    adjacency: dict[str, set[str]] = {}
    for nodes in (before, after):
        for label, node in nodes.items():
            adjacency.setdefault(label, set())
            for dep in node.uses:
                if dep not in nodes:
                    continue
                adjacency.setdefault(dep, set())
                adjacency[label].add(dep)
                adjacency[dep].add(label)
    distance: dict[str, int] = {}
    queue = [label for label in targets if label in adjacency]
    for label in queue:
        distance[label] = 0
    index = 0
    while index < len(queue):
        label = queue[index]
        index += 1
        for neighbor in adjacency.get(label, set()):
            if neighbor in distance:
                continue
            distance[neighbor] = distance[label] + 1
            queue.append(neighbor)
    return {label: distance.get(label) for label in sorted(changed)}


def _upstream_contract_closure(nodes: dict[str, Node], labels: Iterable[str]) -> set[str]:
    """Labels whose contracts may legitimately change to repair ``labels``.

    A Phase 1 statement repair is allowed to change the failing labels and the
    dependency/helper side of those labels. It should not rewrite downstream
    consumers just because those consumers will later need to recompile against
    the repaired contract.
    """
    allowed: set[str] = set()
    stack = [label for label in labels if label in nodes]
    while stack:
        label = stack.pop()
        if label in allowed:
            continue
        allowed.add(label)
        stack.extend(dep for dep in nodes[label].uses if dep in nodes)
    return allowed


def _phase1_repair_scope_violations(
    before: dict[str, Node],
    after: dict[str, Node],
    targets: list[str],
    changed: set[str],
) -> set[str]:
    """Changed contracts outside the target/dependency side of a Phase 1 repair."""
    allowed = _upstream_contract_closure(before, targets) | _upstream_contract_closure(
        after, targets
    )
    return {label for label in changed if label not in allowed}


def _invalid_mathlib_refusal_mappings(ctx: Ctx, refusal: dict) -> dict[str, str]:
    """Return generated-name -> settled-name mappings misread by a refusal."""
    label = str(refusal.get("label") or "")
    if label not in ctx.nodes:
        return {}
    refusal_text = "\n".join(
        [str(refusal.get("reason") or "")]
        + [str(item) for item in refusal.get("missing_helpers") or []]
    )
    mappings: dict[str, str] = {}
    for dep in _transitive_dependencies(ctx.nodes, label):
        node = ctx.nodes.get(dep)
        if node is None or not node.mathlibok or not node.lean_decl:
            continue
        generated = _lean_name(dep)
        if dep in refusal_text or re.search(rf"\b{re.escape(generated)}\b", refusal_text):
            mappings[generated] = node.lean_decl
    return mappings


def _parts_around_labels(labels: list[str], isolated: list[str]) -> list[list[str]]:
    """Preserve dependency order while splitting named nodes into singletons."""
    isolated_set = set(isolated)
    parts: list[list[str]] = []
    current: list[str] = []
    for label in labels:
        if label in isolated_set:
            if current:
                parts.append(current)
                current = []
            parts.append([label])
        else:
            current.append(label)
    if current:
        parts.append(current)
    return parts


def _lean_failure_fingerprint(code: str, output: str) -> tuple[str, str]:
    """Stable identity for a generated file failing with the same Lean output."""
    normalized = re.sub(r"\x1b\[[0-9;]*m", "", output)
    return (
        hashlib.sha256(code.encode("utf-8")).hexdigest(),
        hashlib.sha256(normalized.strip().encode("utf-8")).hexdigest(),
    )


def _lean_error_shape(output: str) -> str:
    """Hash the stable compiler failure shape, ignoring generated locations.

    Exact code/error hashes remain useful for proving byte-for-byte stagnation,
    but model rewrites often move the same error to another line or rename a
    metavariable. This normalized shape catches that repeated work without
    treating different Lean diagnostics as equivalent.
    """
    normalized = re.sub(r"\x1b\[[0-9;]*m", "", output)
    normalized = re.sub(r"(?m)^.*?\.lean:\d+:\d+:\s*", "", normalized)
    normalized = re.sub(r"\?m[._]?[0-9]+", "?m", normalized)
    normalized = re.sub(r"(?:^|\s)\d+:\d+(?=\s|$)", " <loc>", normalized)
    normalized = re.sub(r"[ \t]+", " ", normalized)
    normalized = re.sub(r"\n{3,}", "\n\n", normalized).strip()
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


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


def _frozen_interface_digest(
    sections: list[Section],
    modules: list[str],
    *,
    budget: int = 24000,
    priority_modules: set[str] | None = None,
) -> str:
    """Complete, module-grouped interface digest of the frozen declarations in
    ``modules``. Budgeting is module-granular: when over budget, the OLDEST
    modules are dropped whole and named explicitly — never a silent mid-
    declaration cut (a truncated structure is worse than an omitted one,
    because the model then re-reads files to fill the gap). Modules in
    ``priority_modules`` (owners of the targets' direct dependencies) are
    dropped only after every other module is gone."""
    blocks: list[tuple[str, str]] = []
    for sec in sections:
        if sec.deferred or sec.module not in modules:
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
    priority = priority_modules or set()
    omitted: list[str] = []
    while len(blocks) > 1 and total > budget:
        drop_index = next(
            (i for i, (module, _text) in enumerate(blocks) if module not in priority),
            0,
        )
        module, text = blocks.pop(drop_index)
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


def _frozen_decl_for_label(sections: list[Section], label: str) -> str:
    lean_name = _lean_name(label)
    for sec in sections:
        if sec.deferred or label not in sec.labels or not sec.path.is_file():
            continue
        parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        for decl in parsed.decls:
            if decl.name == lean_name:
                return _decl_interface_text(decl)
    return ""


def _downstream_proof_context(
    ctx: Ctx, target_labels: list[str], sections: list[Section], *, budget: int = 10000
) -> str:
    """Explain how higher-level blueprint proofs consume the current frontier.

    Top-down proof search establishes public results first. When it later proves
    their dependencies, this compact read-only context carries the intended use
    of each dependency downward without introducing a Lean import cycle.
    """
    theorem_labels = {
        label
        for label, node in ctx.nodes.items()
        if not node.mathlibok and _is_theorem_like_kind(node.kind)
    }
    proved = _proved_labels(sections)
    consumers: set[str] = set()
    target_set = set(target_labels)
    for consumer in theorem_labels - target_set:
        if _immediate_theorem_dependencies(ctx.nodes, consumer, theorem_labels) & target_set:
            consumers.add(consumer)
    ordered = sorted(
        consumers,
        key=lambda label: (label not in proved, _node_order(ctx.nodes).index(label)),
    )[:8]
    blocks: list[str] = []
    for label in ordered:
        status = "proof already accepted" if label in proved else "higher-level frozen obligation"
        lean_decl = _frozen_decl_for_label(sections, label)
        blocks.append(
            f"### {label} ({status})\n"
            f"Blueprint contract:\n```tex\n{ctx.tex_blocks.get(label, '')[:2600]}\n```\n"
            f"Frozen Lean interface:\n```lean\n{lean_decl[:2200] or '-- unavailable'}\n```"
        )
    text = "\n\n".join(blocks)
    return text[:budget]


# ---------------------------------------------------------------------------
# Prompts


def _format_library_candidates(candidates: list) -> str:
    """Render a candidate subset in the same shape as the global search summary."""
    lines = [
        "- Candidate modules below were found by deterministic local search; "
        "treat module paths as already verified."
    ]
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
    return "\n".join(lines)


def _library_context_for(ctx: Ctx, labels: list[str], *, max_candidates: int = 12) -> str:
    """Slice the run-global library candidates down to the ones whose matched
    search term comes from the target nodes or their direct dependencies. The
    global list is derived from the whole blueprint; repeating all of it in
    every prompt is the single largest fixed prompt cost."""
    if not ctx.library_candidates:
        return ctx.library_context
    subset = set(labels)
    for label in labels:
        node = ctx.nodes.get(label)
        if node is not None:
            subset.update(dep for dep in node.uses if dep in ctx.nodes)
    subset_nodes = {label: ctx.nodes[label] for label in subset if label in ctx.nodes}
    subset_blocks = {label: ctx.tex_blocks.get(label, "") for label in subset_nodes}
    terms = {
        term.lower() for term in _search_terms_from_blueprint(subset_nodes, subset_blocks)
    }
    chosen = [
        cand for cand in ctx.library_candidates if cand.matched.lower() in terms
    ][:max_candidates]
    if not chosen:
        chosen = ctx.library_candidates[:8]
    return _format_library_candidates(chosen)


def _local_node_summary(ctx: Ctx, labels: list[str]) -> str:
    """Node-graph orientation limited to targets, direct deps, and direct
    consumers; the whole-graph summary scaled with blueprint size, not with
    the work in this call."""
    target_set = set(labels)
    nearby = set(labels)
    for label in labels:
        node = ctx.nodes.get(label)
        if node is not None:
            nearby.update(dep for dep in node.uses if dep in ctx.nodes)
    nearby.update(
        consumer
        for consumer, node in ctx.nodes.items()
        if node.uses & target_set
    )
    return _node_summary({label: ctx.nodes[label] for label in nearby if label in ctx.nodes})


def _common_rules(ctx: Ctx, labels: list[str] | None = None) -> str:
    unavailable = ""
    if ctx.unavailable_imports:
        unavailable = (
            "\nUnavailable imports (no compiled .olean locally; NEVER import these):\n"
            + "\n".join(f"- {item}" for item in sorted(ctx.unavailable_imports))
        )
    library_block = (
        _library_context_for(ctx, labels) if labels else ctx.library_context
    )
    return f"""Hard constraints:
- The blueprint TeX below is the only mathematical source of truth. Formalize
  each node's statement EXACTLY as written: same objects, same hypotheses, same
  claims. Do not weaken, strengthen, or substitute an adjacent formulation.
- Give each blueprint node exactly the Lean name listed for it.
- Dependencies marked Mathlib-owned are the exception to generated label
  names: use their settled external declaration exactly as shown in the
  dependency contract table. Never generate or request the label-derived name
  for a Mathlib-owned node.
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
  the blueprint does not have), do NOT emit weakened Lean for it — but DO
  still return the Lean code block with every other target node you can
  formalize (omit only declarations that would need the refused node). After
  the code block, add one line:
  NEEDS-DECOMPOSITION: {{"label": "<node label>", "missing_helpers": ["<each needed helper statement>"], "reason": "<why>"}}
  If no target node can be formalized, reply with only that line.
{unavailable}

Local Lean library candidates (module paths verified by deterministic search):
{library_block or "- none found"}

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
    direct_deps = {
        dep
        for label in labels
        for dep in ctx.nodes.get(label, Node(label, "", Path("."), 0)).uses
    }
    priority_modules = {
        sec.module
        for sec in sections
        if not sec.deferred and set(sec.labels) & direct_deps
    }
    signatures = _frozen_interface_digest(
        sections, import_modules, budget=14000, priority_modules=priority_modules
    )
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    return f"""TASK: BLUEPRINT-SKELETON-SECTION

Return exactly one Lean 4 file (one code block). No commentary.

Generate ONE declaration per target node listed below — statements only:
- definition-kind nodes (definition/defn/construction/notation/convention):
  complete `def`/`structure`/`inductive` with real bodies (a definition's body
  IS its statement; `sorry` is forbidden there);
- theorem-like nodes (lemma/proposition/theorem/corollary and EVERY other
  environment kind, e.g. claim/fact/remark): the exact statement as a
  `theorem` ending in `:= sorry`. Do NOT attempt proofs at this phase: a
  partial or failing tactic block is rejected deterministically and wastes
  the whole call. The ONLY exception is a complete single-tactic closer you
  are certain of (e.g. `:= rfl`); when in any doubt, use `:= sorry`. If a
  proof attempt is unfinished when your budget runs short, replace it with
  `:= sorry` before replying. Never encode a theorem-like node as a bare
  `def : Prop`.
- You may add a small concrete helper `def`/`instance` (e.g. a Fintype
  instance) when a statement genuinely needs it. Helpers must be complete.
- Order declarations so nothing is used before it is declared.
- A statement should visibly use the generated Lean declarations of the
  definition nodes it `uses`; imports of earlier skeleton modules make them
  available (do not redefine them).
- This call has a wall-clock budget of about {timeout_s}s. Spend AT MOST half
  of it verifying library APIs or exploring; always leave time to emit your
  complete Lean reply. An imperfect reply beats no reply: the Lean compiler
  and the audits exist precisely to catch and correct mistakes, while a
  timeout wastes the entire call and its exploration. Never end the budget
  without having produced the requested code.

{_common_rules(ctx, labels)}
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

Resolved direct dependency contracts (generated deterministically):
```text
{dependency_contracts}
```
The ownership above is authoritative. In particular, a Mathlib-owned
dependency is already available under its settled declaration name and is not
a reason to return NEEDS-DECOMPOSITION.

{_design_plan_block(ctx)}

Nearby blueprint nodes (orientation only; targets, their direct dependencies,
and their direct consumers):
{_local_node_summary(ctx, labels)}

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
    patch_direct_deps = {
        dep
        for label in patch_labels
        for dep in ctx.nodes.get(label, Node(label, "", Path("."), 0)).uses
    }
    signatures = _frozen_interface_digest(
        sections,
        import_modules,
        budget=8000,
        priority_modules={
            sec.module
            for sec in sections
            if not sec.deferred and set(sec.labels) & patch_direct_deps
        },
    )
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
- If a finding concerns a partial or failing proof on a theorem-like node,
  replace that proof with terminal `:= sorry` — do not try to complete it;
  proofs are a later phase.
- The replacement statement must still encode the same blueprint node. Do not
  weaken, abstract away, or replace it with `True`.
- If a replacement must use another blueprint node listed in `uses`, visibly
  mention that node's generated Lean name.
- You may include a small complete helper declaration immediately before a
  replacement only if the replacement genuinely needs it.
- This call has a wall-clock budget of about {timeout_s}s. Spend AT MOST half
  of it verifying library APIs or exploring; always leave time to emit your
  complete Lean reply. An imperfect reply beats no reply: the Lean compiler
  and the audits exist precisely to catch and correct mistakes, while a
  timeout wastes the entire call and its exploration. Never end the budget
  without having produced the requested code.

{_common_rules(ctx, patch_labels)}

Blueprint name: {ctx.name}

Available imports for earlier accepted skeleton declarations:
```lean
{chr(10).join(f'import {m}' for m in import_modules) or '-- none'}
```

Frozen Lean interface of those modules (complete; do not re-read skeleton files):
```lean
{signatures or '-- none'}
```

{_design_plan_block(ctx, budget=4000)}

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
    escalated: bool = False,
) -> tuple[ParsedModule | None, str]:
    patch_labels = _patchable_skeleton_labels(findings, labels)
    if not patch_labels:
        return None, "not patchable"
    _log(
        "  targeted check isolated "
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
        effort=ctx.escalation_effort if escalated else ctx.base_effort,
        labels=patch_labels,
        escalated=escalated,
        sessions=sessions,
    )
    if result.status == "timeout" and not escalated:
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
    downstream_context = _downstream_proof_context(
        ctx, [label for label, _decl in targets], sections
    )
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
- This call has a wall-clock budget of about {timeout_s}s. Spend AT MOST half
  of it verifying library APIs or exploring; always leave time to emit your
  complete Lean reply. An imperfect reply beats no reply: the Lean compiler
  and the audits exist precisely to catch and correct mistakes, while a
  timeout wastes the entire call and its exploration. Never end the budget
  without having produced the requested code.
{single_note}
{_common_rules(ctx, [label for label, _decl in targets])}

Blueprint name: {ctx.name}

Frozen Lean interface (same module and imported skeleton modules; use these
exact names — dependencies must be cited by them).
{FROZEN_INTERFACE_NOTE}
```lean
{signatures or '-- none'}
```

Higher-level obligations that consume this frontier (orientation only; do not
reference these downstream declarations from the current proof):
{downstream_context or '- This frontier contains public roots or has no theorem-like consumers.'}

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
        if node.kind in DEFINITION_LIKE_KINDS and decl.kind in {"theorem", "lemma"}:
            findings.append(
                SkeletonFinding(
                    f"{label} is a definition but generated `{decl.kind} {decl.name}`",
                    label=label,
                    lean_name=lean_name,
                )
            )
        if _is_theorem_like_kind(node.kind) and decl.kind in {"structure", "inductive", "class"}:
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
    prompt = _statement_audit_prompt(
        ctx.name, nodes, ctx.tex_blocks, decls, ctx.paper_text, skeleton_phase=True
    )
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


class _SectionNumberAllocator:
    """Thread-safe monotonically increasing skeleton section numbers.

    Recursive splits each claim a fresh number; gaps from abandoned attempts
    are fine — state loading and final assembly key on relative order only,
    and a dependency always freezes (and therefore allocates) before its
    consumers are scheduled, so the number-sorted assembly order stays
    dependency-safe.
    """

    def __init__(self, start: int):
        self._next = start
        self._lock = threading.Lock()

    def __call__(self) -> int:
        with self._lock:
            number = self._next
            self._next += 1
            return number


def _design_plan_block(ctx: Ctx, *, budget: int = 9000) -> str:
    """Render the agreed interface plan for injection into skeleton prompts."""
    if not ctx.design_plan:
        return ""
    return (
        "Agreed interface plan for this wave (decided root-first over the whole\n"
        "pending graph; follow these names and shapes):\n```text\n"
        + ctx.design_plan[:budget]
        + "\n```\n"
    )


def _blueprint_roots(nodes: dict[str, Node], labels: Iterable[str]) -> list[str]:
    """Theorem-like labels nothing else depends on: the paper's public results."""
    label_set = set(labels)
    consumed = {dep for label in nodes for dep in nodes[label].uses}
    return [
        label
        for label in label_set
        if _is_theorem_like_kind(nodes[label].kind) and label not in consumed
    ]


def _design_plan_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    timeout_s: int,
) -> str:
    """Ask for the interface plan only — no bodies, no proofs.

    Deciding the vocabulary root-first is cheap reasoning; writing every
    declaration is not. Splitting them keeps this call small enough to always
    land, and the resulting plan is short enough to inject into every later
    skeleton prompt, so all sections share one coherent design instead of each
    re-deriving it.
    """
    roots = _blueprint_roots(ctx.nodes, labels)
    root_text = "\n\n".join(
        f"### ROOT {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`)\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:2500]}\n```"
        for label in roots[:12]
    )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"uses [{', '.join(sorted(ctx.nodes[label].uses)) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:1200]}\n```"
        for label in labels
    )
    signatures = _frozen_interface_digest(sections, import_modules, budget=10000)
    return f"""TASK: BLUEPRINT-SKELETON-DESIGN-PLAN

Return a PLAN only. No proofs, no definition bodies, no code block per node —
one compact block of Lean-ish signature lines. Do NOT write the full file.

You are fixing the shared vocabulary for a Lean skeleton before it is written
section by section. Reason ROOT-FIRST: start from the public results under
"Root obligations", decide what each needs in order to be a NON-TRIVIAL,
faithful claim, and let that determine the shape of every definition beneath
it. The declarations themselves will be emitted later in dependency order.

Hard design rule: a definition must never assume the conclusion of a theorem
that depends on it. If a root asserts `X = Y` or `X ⊆ Y`, then `X` and `Y`
must be defined independently — folding the relation into either definition
makes the root vacuous.

Output format — exactly one line per target node, in dependency order:
  <lean-name> : <intended Lean type/signature>   -- <=12-word note on intent
Then, if the statements need shared scaffolding, a short `HELPERS:` list in
the same one-line form (structures, abbreviations, instances).
Finally a `DECISIONS:` list of at most 5 lines recording any choice a writer
could otherwise get wrong (e.g. "ReLU_{{n,k}} is defined by network depth
alone; CPWL membership is NOT part of it — thm:cpwl-depth must prove it").

Keep the whole reply under ~120 lines. This call has a budget of about
{timeout_s}s; it is a planning call, so do not verify every Mathlib API now —
note the intended type and move on.

{_common_rules(ctx, labels)}

Blueprint name: {ctx.name}

Frozen Lean interface already available (do not redesign these):
```lean
{signatures or '-- none'}
```

Root obligations — design everything below to serve these:
{root_text or '- (no unconsumed theorem-like roots in this batch)'}

Target nodes to plan ({len(labels)} node(s), dependency order):
{target_text}
"""


def _bulk_skeleton_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    timeout_s: int,
) -> str:
    """Emit one chunk of the skeleton against the already-agreed design plan.

    Statements are compiled leaf-first (Lean cannot elaborate a reference to a
    declaration that does not exist yet), but they were *designed* root-first
    by the plan pass, so this call is transcription rather than design.
    """
    roots = _blueprint_roots(ctx.nodes, labels)
    root_text = "\n\n".join(
        f"### ROOT {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`)\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:3000]}\n```"
        for label in roots[:12]
    )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"uses [{', '.join(sorted(ctx.nodes[label].uses)) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:2500]}\n```"
        for label in labels
    )
    signatures = _frozen_interface_digest(sections, import_modules, budget=14000)
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    return f"""TASK: BLUEPRINT-SKELETON-SECTION

Return exactly one Lean 4 file (one code block). No commentary.

Emit the statement of EVERY target node below — statements only, no proofs.
The interface plan above already fixed the design decisions: follow it, and
emit declarations in dependency order so nothing is referenced before it is
declared. This call is transcription, not redesign; deviate from the plan
only where it is impossible to compile, and keep the deviation minimal.

Per-node rules:
- definition-kind nodes (definition/defn/construction/notation/convention):
  complete `def`/`structure`/`inductive` with real bodies; `sorry` is
  forbidden there.
- theorem-like nodes (lemma/proposition/theorem/corollary and EVERY other
  environment kind, e.g. claim/fact/remark): the exact statement as a
  `theorem` ending in `:= sorry`. Do NOT attempt proofs in this pass.
- Give each blueprint node exactly the Lean name listed for it.
- You may add small complete shared helper declarations (an abbreviation, a
  Fintype instance, a structure the statements need); place each immediately
  before the first declaration that uses it.
- Emit a declaration for EVERY target node listed. Coverage is checked
  deterministically.
- This call has a wall-clock budget of about {timeout_s}s. Spend AT MOST half
  of it verifying library APIs; always leave time to emit the complete file.
  An imperfect file beats no file: the compiler and the audits exist to catch
  mistakes, while a timeout wastes the entire pass.

{_common_rules(ctx, labels)}

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

Resolved direct dependency contracts (generated deterministically):
```text
{dependency_contracts}
```

{_design_plan_block(ctx)}

Root obligations these statements must serve:
{root_text or '- (no unconsumed theorem-like roots in this batch)'}

Target nodes for THIS file ({len(labels)} node(s), listed in dependency order):
{target_text}
"""


def _delivered_decl_texts(
    parsed: ParsedModule, part_labels: list[str], all_target_names: set[str]
) -> list[str] | None:
    """Select the delivered declarations belonging to one routed part.

    Unowned declarations (local helpers) are attributed to the next owned
    declaration following them in file order, matching the prompt rule that a
    helper appears immediately before the declaration that needs it. Returns
    None unless every part label has a delivered declaration.
    """
    part_names = {_lean_name(label) for label in part_labels}
    chosen: list[str] = []
    pending: list[str] = []
    seen: set[str] = set()
    for decl in parsed.decls:
        name = decl.name or ""
        if name in all_target_names:
            if name in part_names:
                chosen.extend(pending)
                chosen.append(decl.text)
                seen.add(name)
            pending = []
        else:
            pending.append(decl.text)
    if not part_names <= seen:
        return None
    return chosen


def _salvage_timeout_declarations(
    ctx: Ctx, labels: list[str], partial_text: str
) -> tuple[ParsedModule, list[str]] | None:
    """Recover complete target declarations from a timed-out call's output.

    Timeouts are the largest single category of wasted model time, and the
    output is usually not empty — the backend had already streamed part or all
    of the file when the watchdog killed it. Anything syntactically complete
    for a target label is worth keeping; the caller still puts it through every
    normal gate, so a bad salvage costs a Lean check, not correctness.
    """
    if not partial_text or "```" not in partial_text:
        return None
    try:
        code = _extract_lean_code(partial_text)
    except ValueError:
        return None
    if not code.strip():
        return None
    try:
        parsed = _parse_module(code)
    except Exception:
        return None
    delivered_names = {decl.name for decl in parsed.decls if decl.name}
    delivered = [label for label in labels if _lean_name(label) in delivered_names]
    if not delivered:
        return None
    return parsed, delivered


def _freeze_section_from_code(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    decl_texts: list[str],
    imports: list[str],
    preamble: list[str],
    *,
    origin: str = "delivered code",
    allow_patch: bool = False,
) -> list[Section] | None:
    """Try to freeze one section from declarations the model already delivered
    (a design-pass chunk, or the healthy remainder beside a refusal/compile
    isolation). Same gates as fresh code — deterministic checks, Lean,
    alignment audit, .olean.

    With ``allow_patch`` the section gets the same single targeted patch the
    normal path gets before being abandoned; without it, any failure returns
    None and the caller regenerates. Discarding a whole delivered file because
    one declaration needs a fix is exactly the rollback-at-95% waste this
    pipeline avoids elsewhere, so callers whose delivered code IS the product
    (the design pass) pass allow_patch=True.
    Raises RepairRequest when the audit blames the blueprint."""
    import_modules = _sections_for_deps(ctx, labels, sections)
    target_kinds = {_lean_name(label): ctx.nodes[label].kind for label in labels}
    label_by_lean_name = {_lean_name(label): label for label in labels}
    next_number = alloc()
    module, path = _section_module(ctx.name, next_number)
    path.parent.mkdir(parents=True, exist_ok=True)
    _log(
        f"==> Skeleton section {next_number:02d}: {len(labels)} node(s) from "
        f"{origin}: " + ", ".join(labels[:6]) + ("..." if len(labels) > 6 else "")
    )
    missing_imports = _missing_olean_imports(imports)
    if missing_imports:
        ctx.unavailable_imports.update(missing_imports)
        imports = [item for item in imports if item not in set(missing_imports)]
    all_imports = [f"import {m}" for m in import_modules] + imports
    module_code, _ranges = _compose_module(all_imports, preamble, decl_texts)
    parsed = _parse_module(module_code)
    for decl in parsed.decls:
        if _is_theorem_like_kind(target_kinds.get(decl.name or "")) and _has_terminal_sorry(decl.text):
            decl.text = _normalize_terminal_sorry(decl.text)
    module_code, _ranges = _compose_module(
        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
    )
    sessions: dict[str, str] = {}
    findings = _skeleton_code_findings(module_code, target_kinds, label_by_lean_name)
    findings += _skeleton_deterministic_findings(module_code, ctx, labels)
    if findings and allow_patch:
        _log(
            f"  {origin} has {len(findings)} deterministic issue(s); patching in place"
        )
        patched, _note = _targeted_patch_skeleton_decls(
            ctx, labels, sections, import_modules, parsed, module_code, findings,
            timeout=ctx.base_timeout, sessions=sessions,
        )
        if patched is not None:
            parsed = patched
            for decl in parsed.decls:
                if _is_theorem_like_kind(target_kinds.get(decl.name or "")) and _has_terminal_sorry(decl.text):
                    decl.text = _normalize_terminal_sorry(decl.text)
            module_code, _ranges = _compose_module(
                all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
            )
            findings = _skeleton_code_findings(module_code, target_kinds, label_by_lean_name)
            findings += _skeleton_deterministic_findings(module_code, ctx, labels)
    if findings:
        _log(
            f"  delivered code failed deterministic checks ({len(findings)} "
            "issue(s)); regenerating the part"
        )
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="deterministic_rejected")
        _discard_section_artifacts(path)
        return None
    path.write_text(module_code, encoding="utf-8")
    ok, output = _check_lean(path, ctx.lean_command)
    if not ok and allow_patch:
        compile_findings = _lean_compile_findings(parsed, labels, _ranges, output, path.name)
        if _patchable_skeleton_labels(compile_findings, labels):
            _log(f"  {origin} failed Lean; patching the isolated declaration(s)")
            patched, _note = _targeted_patch_skeleton_decls(
                ctx, labels, sections, import_modules, parsed, module_code,
                compile_findings, timeout=ctx.base_timeout, sessions=sessions,
            )
            if patched is not None:
                parsed = patched
                for decl in parsed.decls:
                    if _is_theorem_like_kind(target_kinds.get(decl.name or "")) and _has_terminal_sorry(decl.text):
                        decl.text = _normalize_terminal_sorry(decl.text)
                module_code, _ranges = _compose_module(
                    all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
                )
                post = _skeleton_code_findings(module_code, target_kinds, label_by_lean_name)
                post += _skeleton_deterministic_findings(module_code, ctx, labels)
                if not post:
                    path.write_text(module_code, encoding="utf-8")
                    ok, output = _check_lean(path, ctx.lean_command)
    if not ok:
        _log("  delivered code failed Lean; regenerating the part")
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="lean_rejected")
        _discard_section_artifacts(path)
        return None
    audit = _model_alignment_audit(ctx, labels, module_code, tag="delivered")
    if audit is not None:
        kind, reason, rejected = audit
        if kind == "blueprint":
            _discard_section_artifacts(path)
            raise RepairRequest(reason, sorted(rejected), section_labels=labels)
        _log("  delivered code rejected by alignment audit; regenerating the part")
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="audit_rejected")
        _discard_section_artifacts(path)
        return None
    object_attempt = _compile_module_olean(path, ctx.lean_command)
    if not object_attempt.ok:
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="olean_failed")
        _discard_section_artifacts(path)
        return None
    _log(f"  section {next_number:02d} frozen ({len(parsed.decls)} declaration(s)) from {origin}")
    _record(
        ctx.telemetry,
        "skeleton_section_frozen",
        section=next_number,
        labels=labels,
        decls=len(parsed.decls),
        source="delivered",
    )
    _note_frozen_section(ctx, labels)
    return [
        Section(
            number=next_number,
            labels=list(labels),
            path=path,
            module=module,
            import_modules=import_modules,
        )
    ]


def _bulk_skeleton_pass(
    ctx: Ctx,
    order: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
) -> tuple[list[Section], set[str]]:
    """One cheap design pass that states the whole pending graph at once.

    Returns ``(frozen_sections, covered_labels)``. Every declaration still
    goes through the normal gates (deterministic checks, Lean, alignment
    audit, .olean) via ``_freeze_section_from_code``; whatever the pass fails
    to deliver or freeze is simply left to the per-section loop, so the worst
    case is the previous behaviour plus one call.
    """
    if len(order) < BULK_SKELETON_MIN_NODES:
        return [], set()
    import_modules = _sections_for_deps(ctx, order, sections)
    # Stage 1: fix the shared vocabulary root-first. Small output, so it lands
    # reliably, and the plan then guides every emission chunk AND the
    # per-section fallback loop.
    if not ctx.design_plan:
        plan_labels = order[:DESIGN_PLAN_MAX_NODES]
        _log(
            f"==> Skeleton design plan: fixing the interface for {len(plan_labels)} "
            "pending node(s), root-first"
        )
        plan_result = _call_model(
            ctx,
            _design_plan_prompt(
                ctx, plan_labels, sections, import_modules, timeout_s=ctx.base_timeout
            ),
            purpose="skeleton_design_plan",
            timeout=ctx.base_timeout,
            effort=ctx.base_effort,
            labels=plan_labels,
        )
        if plan_result.status == "ok" and plan_result.text.strip():
            ctx.design_plan = _extract_lean_code(plan_result.text) or plan_result.text.strip()
            _record(
                ctx.telemetry,
                "skeleton_design_plan",
                labels=plan_labels,
                chars=len(ctx.design_plan),
            )
            _log(f"  design plan fixed ({len(ctx.design_plan)} chars); guiding all sections")
        else:
            _log(
                f"  design plan {plan_result.status}; sections continue without a "
                "shared plan"
            )
    # Stage 2: transcribe the plan in section-sized chunks.
    frozen: list[Section] = []
    covered: set[str] = set()
    chunk_sessions: dict[str, str] = {}
    for start in range(0, len(order), BULK_SKELETON_CHUNK):
        chunk = order[start : start + BULK_SKELETON_CHUNK]
        _log(
            f"==> Skeleton design pass: stating {len(chunk)} node(s) in one call "
            f"({len(order) - start - len(chunk)} node(s) after this chunk)"
        )
        prompt = _bulk_skeleton_prompt(
            ctx, chunk, sections + frozen, import_modules, timeout_s=ctx.base_timeout
        )
        result = _call_model(
            ctx,
            prompt,
            purpose="skeleton_design_pass",
            timeout=ctx.base_timeout,
            effort=ctx.base_effort,
            labels=chunk,
            sessions=chunk_sessions,
        )
        if result.status == "timeout":
            # Same ladder the section loop gets: one retry at the hard budget,
            # resuming the timed-out session so its work is not re-paid.
            _log(
                f"  design pass timed out at {ctx.base_timeout}s; retrying once at "
                f"{ctx.hard_timeout}s"
            )
            result = _call_model(
                ctx,
                prompt,
                purpose="skeleton_design_pass",
                timeout=ctx.hard_timeout,
                effort=ctx.base_effort,
                labels=chunk,
                sessions=chunk_sessions,
            )
        if result.status != "ok":
            _log(f"  design pass {result.status}; falling back to per-section generation")
            break
        if _parse_decomposition_refusal(result.text) is not None:
            _log("  design pass returned a decomposition refusal; leaving it to the section loop")
            break
        try:
            parsed = _parse_module(_extract_lean_code(result.text))
        except ValueError:
            _log("  design pass returned no Lean code; falling back")
            break
        delivered_names = {decl.name for decl in parsed.decls if decl.name}
        delivered_labels = [
            label for label in chunk if _lean_name(label) in delivered_names
        ]
        _log(
            f"  design pass delivered {len(delivered_labels)}/{len(chunk)} target "
            f"declaration(s); verifying them section by section"
        )
        if not delivered_labels:
            break
        # Freeze the chunk as ONE section. The model authored it as a single
        # coherent file, so splitting it strands shared helper declarations in
        # whichever part happened to precede them and breaks cross-part
        # references — the chunk is already section-sized by construction.
        added = _freeze_section_from_code(
            ctx,
            delivered_labels,
            sections + frozen,
            alloc,
            [decl.text for decl in parsed.decls],
            list(parsed.imports),
            list(parsed.preamble),
            origin="design pass",
            allow_patch=True,
        )
        if added is not None:
            frozen.extend(added)
            covered.update(delivered_labels)
            _save_ctx_state(ctx, sections + frozen)
    if frozen:
        _record(
            ctx.telemetry,
            "skeleton_design_pass",
            requested=len(order),
            frozen_labels=sorted(covered),
            frozen_count=len(covered),
            sections=len(frozen),
        )
        _log(
            f"  design pass froze {len(covered)}/{len(order)} node(s) in "
            f"{len(frozen)} section(s); the rest continue through the normal loop"
        )
    return frozen, covered


def _freeze_parts(
    ctx: Ctx,
    parts: list[list[str]],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    delivered: ParsedModule | None = None,
    delivered_exclude: set[str] | None = None,
) -> list[Section]:
    """Freeze ordered subgroups and carry partial success through repairs.

    ``delivered`` carries declarations the model already produced in the call
    that triggered this split; parts fully covered by them (and not in
    ``delivered_exclude``, e.g. the refused or compile-failing labels) try a
    no-generation freeze first and fall back to normal generation."""
    frozen: list[Section] = []
    combined = list(sections)
    exclude = delivered_exclude or set()
    all_target_names = {_lean_name(label) for part in parts for label in part}
    if exclude:
        # A refused/failing part usually ends in RepairRequest, which aborts
        # the remaining parts. Freeze every part that does not depend on the
        # excluded labels first (relative order preserved), so delivered work
        # lands before the refusal bubbles up to repair.
        def _depends_on_excluded(part: list[str]) -> bool:
            return any(
                label in exclude or exclude & _transitive_dependencies(ctx.nodes, label)
                for label in part
            )

        independent = [part for part in parts if not _depends_on_excluded(part)]
        dependent = [part for part in parts if _depends_on_excluded(part)]
        parts = independent + dependent
    try:
        for part in parts:
            if not part:
                continue
            added: list[Section] | None = None
            if delivered is not None and not (set(part) & exclude):
                decl_texts = _delivered_decl_texts(delivered, part, all_target_names)
                if decl_texts:
                    added = _freeze_section_from_code(
                        ctx,
                        part,
                        combined,
                        alloc,
                        decl_texts,
                        list(delivered.imports),
                        list(delivered.preamble),
                    )
            if added is None:
                added = _freeze_section(
                    ctx,
                    part,
                    combined,
                    alloc,
                )
            frozen.extend(added)
            combined.extend(added)
            # Persist each frozen part (and any scheduler change it caused):
            # a later part can raise RepairRequest or the process can die, and
            # unsaved frozen parts were being pruned as stale artifacts on the
            # next --continue.
            _save_ctx_state(ctx, combined)
    except RepairRequest as request:
        request.frozen_sections = frozen + request.frozen_sections
        raise
    return frozen


def _note_frozen_section(ctx: Ctx, labels: list[str]) -> None:
    """Advance the persistent capacity controller after an accepted section."""
    if ctx.effective_section_size <= 0:
        ctx.effective_section_size = ctx.section_size
    old_size = ctx.effective_section_size
    _release_quarantine(ctx, labels)
    # A routed singleton or short tail proves only that those declarations are
    # acceptable; it is not evidence that the current broad batch capacity is
    # safe. Count clean capacity evidence only when a full-sized group freezes.
    if len(labels) < old_size:
        return
    ctx.proven_section_size = max(ctx.proven_section_size, len(labels))
    ctx.section_clean_streak += 1
    if ctx.section_clean_streak < 2 or old_size >= ctx.section_size:
        return
    # Two clean groups at the current capacity are enough to probe upward.
    # This still recovers exponentially, but an isolated easy declaration can
    # no longer jump the scheduler from 6 straight back to 12.
    new_size = min(ctx.section_size, max(old_size + 1, old_size * 2))
    ctx.effective_section_size = new_size
    ctx.section_clean_streak = 0
    _log(f"  adaptive section size increased to {new_size} after accepted section(s)")
    _record(
        ctx.telemetry,
        "adaptive_section_size",
        previous_size=old_size,
        size=new_size,
        reason="clean_full_sections",
        labels=labels,
    )


def _next_phase1_group(
    order: list[str], index: int, size: int, quarantined: set[str]
) -> list[str]:
    """Choose one group without remixing known-problematic labels."""
    if index >= len(order):
        return []
    if order[index] in quarantined:
        return [order[index]]
    group: list[str] = []
    for label in order[index : index + size]:
        if label in quarantined:
            break
        group.append(label)
    return group or [order[index]]


def _freeze_section(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    force_first_escalated: bool = False,
) -> list[Section]:
    """Generate, compile-fix, audit, and freeze one section (possibly bisected).

    Bounded transaction per statement version: attempt 1 (base tier) and, only
    when a stage reports a fixable failure, attempt 2 (escalated tier). Each
    attempt is generate -> deterministic checks (one targeted patch) -> Lean
    compile (one targeted patch) -> alignment audit (one escalated targeted
    correction + one re-audit). Anything the second attempt cannot land raises
    RepairRequest; the timeout ladder (retry at hard budget, bisect, escalate)
    and failing-subset isolation are unchanged.

    Returns the newly frozen Section objects (appended by the caller). Raises
    RepairRequest when the blueprint itself must change first.
    """
    import_modules = _sections_for_deps(ctx, labels, sections)
    target_kinds = {_lean_name(label): ctx.nodes[label].kind for label in labels}
    label_by_lean_name = {_lean_name(label): label for label in labels}
    next_number = alloc()
    module, path = _section_module(ctx.name, next_number)
    path.parent.mkdir(parents=True, exist_ok=True)
    _log(f"==> Skeleton section {next_number:02d}: {len(labels)} node(s): " + ", ".join(labels[:6]) + ("..." if len(labels) > 6 else ""))

    froze = False
    try:
        # One backend session per runner spec for this section's whole lifecycle
        # (generation, patches, error-fix rounds, audit): follow-up calls keep the
        # Mathlib exploration and module context instead of rebuilding it cold.
        sessions: dict[str, str] = {}
        feedback = ""
        previous_code = ""
        escalated_refusals: set[str] = set()
        force_escalated_round = force_first_escalated
        completed_exchanges: set[tuple[str, str, str]] = set()
        invalid_mathlib_refusal_count = 0
        for attempt in range(1, SKELETON_GENERATION_ATTEMPTS + 1):
            use_escalated_runner = force_escalated_round or attempt > 1
            force_escalated_round = False
            effort = ctx.escalation_effort if use_escalated_runner else ctx.base_effort
            timeout = ctx.hard_timeout if use_escalated_runner else ctx.base_timeout
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
            if result.status == "timeout":
                # A timed-out request is NEVER re-issued unchanged at a larger
                # budget: that pattern cost 300s + 600s before any subdivision,
                # and timeouts are the largest category of wasted model time.
                # Instead: keep whatever the backend already emitted, then split.
                salvage = _salvage_timeout_declarations(ctx, labels, result.partial_text)
                if salvage is not None:
                    parsed_partial, delivered = salvage
                    _log(
                        f"  call timed out but had already emitted "
                        f"{len(delivered)}/{len(labels)} target declaration(s); "
                        "verifying the salvage instead of discarding the call"
                    )
                    _record(
                        ctx.telemetry,
                        "timeout_salvage",
                        labels=labels,
                        salvaged_labels=delivered,
                        salvaged_count=len(delivered),
                    )
                    added = _freeze_section_from_code(
                        ctx,
                        delivered,
                        sections,
                        alloc,
                        [decl.text for decl in parsed_partial.decls],
                        list(parsed_partial.imports),
                        list(parsed_partial.preamble),
                        origin="timeout salvage",
                        allow_patch=True,
                    )
                    if added:
                        # NOTE: deliberately do not set `froze` — the salvage
                        # allocated its own section number, so this attempt's
                        # `path` is still an orphan and must be discarded by
                        # the finally.
                        remaining = [
                            label for label in labels if label not in set(delivered)
                        ]
                        if not remaining:
                            return added
                        try:
                            rest = _freeze_section(ctx, remaining, sections + added, alloc)
                        except RepairRequest as request:
                            request.frozen_sections = added + request.frozen_sections
                            raise
                        return added + rest
                # Nothing salvageable: subdivide rather than re-ask the same
                # question with a bigger stopwatch.
                if len(labels) > 1:
                    mid = len(labels) // 2
                    _log(f"  section call timed out; bisecting into {mid} + {len(labels) - mid} node(s)")
                    # This size demonstrably does not fit the base timeout, so
                    # don't make future groups rediscover that: shrink the
                    # run-scoped section size (Phase 2 already does this for
                    # proof batches).
                    if 0 < mid < (ctx.effective_section_size or ctx.section_size):
                        ctx.effective_section_size = mid
                        ctx.section_clean_streak = 0
                        _log(f"  adaptive section size reduced to {mid} for the rest of this run")
                        _record(
                            ctx.telemetry,
                            "adaptive_section_size",
                            size=mid,
                            reason="skeleton_timeout",
                            labels=labels,
                        )
                        _save_ctx_state(ctx, sections)
                    return _freeze_parts(
                        ctx,
                        [labels[:mid], labels[mid:]],
                        sections,
                        alloc,
                    )
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

            # A resumed CLI session can replay its previous final answer when it is
            # given the same correction prompt. The response is then guaranteed to
            # recreate the same candidate, so compiling and asking again only burns
            # another model call. Escalate once from a duplicate base exchange; a
            # duplicate escalation is genuine generation stagnation.
            exchange = (
                ctx.escalation_runner_spec if result_was_escalated else ctx.runner_spec,
                hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
                hashlib.sha256(result.text.encode("utf-8")).hexdigest(),
            )
            if exchange in completed_exchanges:
                _record(
                    ctx.telemetry,
                    "duplicate_model_exchange",
                    purpose="skeleton_generation",
                    labels=labels,
                    escalated=result_was_escalated,
                    prompt_sha256=exchange[1],
                    response_sha256=exchange[2],
                )
                sessions.pop(exchange[0], None)
                if not result_was_escalated:
                    force_escalated_round = True
                    feedback = (
                        "The base generator replayed a byte-identical response to "
                        "the same compiler-feedback prompt. Start fresh at the "
                        "escalation tier and produce a materially corrected Lean "
                        "declaration."
                    )
                    _log(
                        "  duplicate skeleton response detected; skipping the "
                        "redundant compile and escalating once"
                    )
                    continue
                raise RepairRequest(
                    "Skeleton generation repeated a byte-identical response to the "
                    "same correction prompt at escalated effort. The current node "
                    "needs a different formal interface or explicit helper "
                    "decomposition; do not weaken its mathematical claim.",
                    labels,
                    section_labels=labels,
                )
            completed_exchanges.add(exchange)

            refusal = _parse_decomposition_refusal(result.text)
            if refusal is not None:
                refused = [refusal["label"]] if refusal["label"] in labels else list(labels)
                invalid_mappings = _invalid_mathlib_refusal_mappings(ctx, refusal)
                if invalid_mappings:
                    invalid_mathlib_refusal_count += 1
                    mapping_text = ", ".join(
                        f"`{generated}` is Mathlib-owned as `{actual}`"
                        for generated, actual in sorted(invalid_mappings.items())
                    )
                    _log(
                        "  rejected false Mathlib dependency refusal for "
                        + ", ".join(refused)
                        + f": {mapping_text}"
                    )
                    _record(
                        ctx.telemetry,
                        "skeleton_refusal_rejected",
                        labels=labels,
                        refused_labels=refused,
                        reason="mathlib_dependency_already_settled",
                        attempt=invalid_mathlib_refusal_count,
                        mappings=invalid_mappings,
                        refusal_reason=refusal.get("reason", ""),
                    )
                if len(labels) > 1 and len(refused) < len(labels):
                    # The response identified a node-specific problem. Isolate
                    # exactly that node while preserving dependency order; it says
                    # nothing about how many unrelated nodes fit in one call.
                    _quarantine_labels(ctx, refused, "model_refusal")
                    parts = _parts_around_labels(labels, refused)
                    _log(
                        "  skeleton generator isolated "
                        + ", ".join(refused)
                        + "; preserving global section size and routing "
                        + " + ".join(str(len(part)) for part in parts)
                        + " node(s)"
                    )
                    _record(
                        ctx.telemetry,
                        "skeleton_refusal_isolated",
                        labels=labels,
                        refused_labels=refused,
                        part_sizes=[len(part) for part in parts],
                        invalid_mathlib_refusal=bool(invalid_mappings),
                        missing_helpers=refusal.get("missing_helpers") or [],
                        refusal_reason=refusal.get("reason", ""),
                    )
                    delivered = None
                    if "```" in result.text:
                        delivered_code = _extract_lean_code(result.text)
                        if delivered_code.strip():
                            candidate = _parse_module(delivered_code)
                            if candidate.decls:
                                delivered = candidate
                                _log(
                                    f"  refusal reply also delivered {len(candidate.decls)} "
                                    "declaration(s); reusing them for the healthy parts"
                                )
                    return _freeze_parts(
                        ctx,
                        parts,
                        sections,
                        alloc,
                        delivered=delivered,
                        delivered_exclude=set(refused),
                    )
                if invalid_mappings:
                    # A singleton refusal based on a nonexistent generated name is
                    # not blueprint-repair evidence. Correct it in-context and use
                    # the escalation runner once before normal fix rounds continue.
                    feedback = (
                        "Your NEEDS-DECOMPOSITION response was invalid because its "
                        "supposedly missing helpers are settled Mathlib dependencies: "
                        + mapping_text
                        + ". Use those exact external declarations and generate the "
                        "requested blueprint statement without changing its meaning."
                    )
                    previous_code = ""
                    if not result_was_escalated:
                        force_escalated_round = True
                    continue
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
                if _is_theorem_like_kind(target_kinds.get(decl.name or "")) and _has_terminal_sorry(decl.text):
                    decl.text = _normalize_terminal_sorry(decl.text)
            all_imports = [f"import {m}" for m in import_modules] + parsed.imports
            module_code, _ranges = _compose_module(all_imports, parsed.preamble, [d.text for d in parsed.decls])

            findings = _skeleton_code_findings(module_code, target_kinds, label_by_lean_name)
            findings += _skeleton_deterministic_findings(module_code, ctx, labels)
            patch_note = ""
            if findings:
                patched, patch_note = _targeted_patch_skeleton_decls(
                    ctx,
                    labels,
                    sections,
                    import_modules,
                    parsed,
                    module_code,
                    findings,
                    timeout=ctx.base_timeout,
                    sessions=sessions,
                )
                if patched is not None:
                    parsed = patched
                    all_imports = [f"import {m}" for m in import_modules] + parsed.imports
                    module_code, _ranges = _compose_module(
                        all_imports, parsed.preamble, [d.text for d in parsed.decls]
                    )
                    findings = _skeleton_code_findings(module_code, target_kinds, label_by_lean_name)
                    findings += _skeleton_deterministic_findings(module_code, ctx, labels)
            if findings:
                feedback = _format_skeleton_findings(findings)
                if patch_note and patch_note != "not patchable":
                    feedback += f"\n\nTargeted declaration patch result: {patch_note}"
                previous_code = module_code
                if attempt < SKELETON_GENERATION_ATTEMPTS:
                    _log(
                        f"  deterministic audit failed ({len(findings)} issue(s)) after "
                        "one targeted patch; regenerating once at escalated effort"
                    )
                    continue
                raise RepairRequest(
                    "Targeted skeleton declaration patch made no deterministic "
                    "progress on the same audit failures, including at escalated "
                    "effort.\n" + _format_skeleton_findings(findings)[-10000:],
                    _patchable_skeleton_labels(findings, labels) or labels,
                    section_labels=labels,
                )

            # Compile before paying for a semantic model audit. Most failed
            # candidates in long runs are ordinary Lean encoding errors; auditing
            # those files spends money without producing an acceptable artifact.
            # One targeted patch on the Lean-isolated declarations, then either the
            # failing subset is split out (one bad node must not drag its healthy
            # batchmates into repair) or this attempt is spent.
            path.write_text(module_code, encoding="utf-8")
            ok, output = _check_lean(path, ctx.lean_command)
            patch_labels: list[str] = []
            if not ok:
                compile_findings = _lean_compile_findings(
                    parsed, labels, _ranges, output, path.name
                )
                patch_labels = _patchable_skeleton_labels(compile_findings, labels)
                if not patch_labels and len(labels) == 1:
                    # With one target declaration, any local compile error belongs
                    # to that declaration or its local helpers even when Lean's
                    # source range cannot be mapped precisely.
                    patch_labels = list(labels)
                patched = None
                patch_note = "not patchable"
                post_findings: list[SkeletonFinding] = []
                if patch_labels:
                    _log(
                        "  Lean isolated compile errors in "
                        + f"{len(patch_labels)} declaration(s); patching in place"
                    )
                    patched, patch_note = _targeted_patch_skeleton_decls(
                        ctx,
                        labels,
                        sections,
                        import_modules,
                        parsed,
                        module_code,
                        compile_findings,
                        timeout=ctx.base_timeout,
                        sessions=sessions,
                    )
                if patched is not None:
                    parsed = patched
                    for decl in parsed.decls:
                        if (
                            _is_theorem_like_kind(target_kinds.get(decl.name or ""))
                            and _has_terminal_sorry(decl.text)
                        ):
                            decl.text = _normalize_terminal_sorry(decl.text)
                    all_imports = [f"import {m}" for m in import_modules] + parsed.imports
                    module_code, _ranges = _compose_module(
                        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
                    )
                    post_findings = _skeleton_code_findings(
                        module_code, target_kinds, label_by_lean_name
                    )
                    post_findings += _skeleton_deterministic_findings(
                        module_code, ctx, labels
                    )
                    if not post_findings:
                        path.write_text(module_code, encoding="utf-8")
                        ok, output = _check_lean(path, ctx.lean_command)
                        if ok:
                            _record(
                                ctx.telemetry,
                                "skeleton_compile_patch",
                                section=next_number,
                                round=1,
                                labels=patch_labels,
                                status="applied",
                            )
                if not ok:
                    if patched is not None and post_findings:
                        feedback = (
                            "Targeted compile patch introduced deterministic issues:\n"
                            + _format_skeleton_findings(post_findings)
                        )
                    else:
                        feedback = f"Lean rejected the file:\n{output[-12000:]}"
                        if patch_note != "patched":
                            feedback += f"\n\nTargeted compile patch: {patch_note}"
                    previous_code = module_code
                    failure_labels = tuple(sorted(patch_labels or labels))
                    if len(labels) > 1 and set(failure_labels) < set(labels):
                        # Lean isolated a proper subset: split it out so the
                        # healthy declarations freeze on their own and only the
                        # failing nodes spend further budget.
                        _quarantine_labels(ctx, failure_labels, "lean_compile_failure")
                        _record(
                            ctx.telemetry,
                            "skeleton_compile_isolated",
                            labels=labels,
                            failing_labels=list(failure_labels),
                            lean_error_shape=_lean_error_shape(output),
                            escalated=result_was_escalated,
                        )
                        parts = _parts_around_labels(labels, list(failure_labels))
                        _log(
                            "  Lean failure isolated "
                            + ", ".join(failure_labels)
                            + "; reusing the already-generated declarations for the "
                            + "unrelated parts and routing "
                            + " + ".join(str(len(part)) for part in parts)
                            + " node(s)"
                        )
                        return _freeze_parts(
                            ctx,
                            parts,
                            sections,
                            alloc,
                            delivered=parsed,
                            delivered_exclude=set(failure_labels),
                        )
                    if attempt < SKELETON_GENERATION_ATTEMPTS:
                        # The prompt is self-contained; discard the anchored
                        # producer session and give the stronger tier one fresh
                        # attempt.
                        sessions.pop(
                            ctx.escalation_runner_spec
                            if result_was_escalated
                            else ctx.runner_spec,
                            None,
                        )
                        _record(
                            ctx.telemetry,
                            "singleton_compile_escalation",
                            labels=labels,
                            lean_error_shape=_lean_error_shape(output),
                            base_patch_rounds=1 if patch_labels else 0,
                        )
                        _log(
                            "  section still fails Lean after one targeted compile "
                            "patch; starting one fresh escalated attempt"
                        )
                        continue
                    raise RepairRequest(
                        "A statement still does not compile after one base "
                        "generation/patch and one fresh escalated generation/patch. "
                        "Further Lean variants are not useful; repair or decompose "
                        "the formal interface without weakening the blueprint "
                        "claim.\n" + feedback,
                        list(failure_labels),
                        section_labels=labels,
                    )

            # Alignment audit: one verdict, one escalated targeted correction, one
            # re-audit. A second rejection is blueprint evidence, not a reason to
            # generate more Lean variants.
            audit = _model_alignment_audit(ctx, labels, module_code)
            if audit is not None:
                kind, reason, rejected = audit
                if kind == "blueprint":
                    raise RepairRequest(reason, sorted(rejected), section_labels=labels)
                audit_findings = [
                    SkeletonFinding(
                        reason,
                        label=label,
                        lean_name=_lean_name(label),
                    )
                    for label in sorted(rejected)
                    if label in labels
                ]
                patched, patch_note = _targeted_patch_skeleton_decls(
                    ctx,
                    labels,
                    sections,
                    import_modules,
                    parsed,
                    module_code,
                    audit_findings,
                    timeout=ctx.hard_timeout,
                    sessions=sessions,
                    escalated=True,
                )
                corrected = False
                if patched is not None:
                    parsed = patched
                    for decl in parsed.decls:
                        if (
                            _is_theorem_like_kind(target_kinds.get(decl.name or ""))
                            and _has_terminal_sorry(decl.text)
                        ):
                            decl.text = _normalize_terminal_sorry(decl.text)
                    all_imports = [f"import {m}" for m in import_modules] + parsed.imports
                    module_code, _ranges = _compose_module(
                        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
                    )
                    post_patch_findings = _skeleton_code_findings(
                        module_code, target_kinds, label_by_lean_name
                    )
                    post_patch_findings += _skeleton_deterministic_findings(
                        module_code, ctx, labels
                    )
                    path.write_text(module_code, encoding="utf-8")
                    post_patch_ok, post_patch_output = _check_lean(path, ctx.lean_command)
                    if post_patch_findings or not post_patch_ok:
                        patch_note = (
                            "correction failed deterministic checks:\n"
                            + _format_skeleton_findings(post_patch_findings)
                            if post_patch_findings
                            else "Lean rejected the corrected file:\n"
                            + post_patch_output[-10000:]
                        )
                    else:
                        _record(
                            ctx.telemetry,
                            "skeleton_audit_patch",
                            section=next_number,
                            round=attempt,
                            labels=sorted(rejected),
                            status="applied",
                        )
                        _log("  patched audit-rejected declarations; re-auditing the section")
                        reaudit = _model_alignment_audit(
                            ctx, labels, module_code, tag="post-correction"
                        )
                        if reaudit is None:
                            corrected = True
                        else:
                            kind2, reason2, rejected2 = reaudit
                            if kind2 == "blueprint":
                                raise RepairRequest(
                                    reason2, sorted(rejected2), section_labels=labels
                                )
                            raise RepairRequest(
                                "Blueprint contract audit rejected the section again "
                                "after one escalated targeted correction; the blueprint "
                                "text likely under-determines the statement.\n" + reason2,
                                sorted(rejected2),
                                section_labels=labels,
                            )
                if not corrected:
                    feedback = reason + f"\n\nTargeted audit correction failed: {patch_note}"
                    previous_code = module_code
                    if attempt < SKELETON_GENERATION_ATTEMPTS:
                        _log(
                            "  alignment audit correction failed; regenerating once "
                            "at escalated effort"
                        )
                        continue
                    raise RepairRequest(
                        "Blueprint contract audit kept rejecting regenerated "
                        "statements; the blueprint text likely under-determines the "
                        "statement.\n" + reason,
                        sorted(rejected),
                        section_labels=labels,
                    )

            object_attempt = _compile_module_olean(path, ctx.lean_command)
            if not object_attempt.ok:
                feedback = f".olean compilation failed:\n{object_attempt.output[-8000:]}"
                previous_code = module_code
                if attempt < SKELETON_GENERATION_ATTEMPTS:
                    continue
                raise RepairRequest(
                    ".olean compilation failed on both bounded attempts for this "
                    "section.\n" + feedback,
                    labels,
                    section_labels=labels,
                )
            _log(f"  section {next_number:02d} frozen ({len(parsed.decls)} declaration(s))")
            _record(
                ctx.telemetry,
                "skeleton_section_frozen",
                section=next_number,
                labels=labels,
                decls=len(parsed.decls),
            )
            _note_frozen_section(ctx, labels)
            froze = True
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
            "Skeleton generation exhausted its bounded attempts for this section. "
            "Last feedback:\n" + feedback,
            labels,
            section_labels=labels,
        )
    finally:
        # Any exit that is not a frozen section (RepairRequest, bisect via
        # _freeze_parts, runner error) must leave no artifact behind: a
        # later generation call would otherwise find the orphan file and
        # `import` it against a stale .olean.
        if not froze:
            _discard_section_artifacts(path)


def _run_phase1(ctx: Ctx, sections: list[Section], pending: set[str]) -> list[Section]:
    alloc = _SectionNumberAllocator(max((sec.number for sec in sections), default=0) + 1)
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
    # One root-first design pass over everything pending, then the per-section
    # loop handles whatever it could not deliver or freeze.
    bulk_sections, covered = _bulk_skeleton_pass(ctx, order, sections, alloc)
    if bulk_sections:
        sections.extend(bulk_sections)
        _save_ctx_state(ctx, sections)
        order = [label for label in order if label not in covered]
    index = 0
    # A section that needs a blueprint repair must NOT abort the wave. The
    # failing cluster is usually a small, self-contained corner of the graph
    # (measured: 40 of 41 pending nodes were independent of the cluster that
    # was blocking every wave), so the repair request is parked, its labels
    # and their dependents are skipped, and the rest of the wave proceeds.
    # Collected requests are raised after the wave drains, so the main loop
    # repairs against a blueprint whose independent work is already frozen.
    deferred_requests: list[RepairRequest] = []
    blocked: set[str] = set()
    # _reactivate_deferred_sections rebinds `sections` to a new list, so the
    # caller's list stops receiving this wave's work. Track what we froze by
    # section number and hand it back through the request on the way out.
    incoming_numbers = {sec.number for sec in sections}
    while index < len(order):
        size = max(1, min(ctx.effective_section_size, ctx.section_size))
        group = _next_phase1_group(
            order, index, size, ctx.quarantined_labels | blocked
        )
        index += len(group)
        group = [label for label in group if label not in blocked]
        if not group:
            continue
        try:
            new_sections = _freeze_section(ctx, group, sections, alloc)
        except RepairRequest as request:
            # Keep whatever the section managed to freeze before failing.
            if request.frozen_sections:
                already = _frozen_labels(sections)
                keep = [
                    sec for sec in request.frozen_sections
                    if not (set(sec.labels) & already)
                ]
                sections.extend(keep)
                request.frozen_sections = []
            # Block only the nodes the request actually blames, plus what
            # depends on them. Innocent section-mates are re-queued so they
            # get their own attempt instead of inheriting the failure.
            failing = set(request.labels) or set(request.section_labels or [])
            blocked |= failing
            blocked |= {
                label
                for label in _dependency_descendants(ctx.nodes, failing)
                if label in ctx.nodes
            }
            innocent = [
                label for label in group
                if label not in blocked and label not in _frozen_labels(sections)
            ]
            if innocent:
                order.extend(innocent)
            _quarantine_labels(ctx, sorted(failing), "repair_pending")
            deferred_requests.append(request)
            remaining = sum(
                1 for label in order[index:] if label not in blocked
            )
            _log(
                f"  section needs a blueprint repair ({', '.join(sorted(failing)[:4])}"
                f"{'...' if len(failing) > 4 else ''}); deferring it and continuing "
                f"with {remaining} independent node(s) still in this wave"
            )
            _record(
                ctx.telemetry,
                "phase1_repair_deferred",
                labels=sorted(failing),
                blocked_count=len(blocked),
                remaining_in_wave=remaining,
            )
            _save_ctx_state(ctx, sections)
            continue
        sections.extend(new_sections)
        _save_ctx_state(ctx, sections)
        # Eagerly recover deferred sections as their dependencies refreeze.
        # Reactivation is deterministic (Lean recompiles, no model calls), and
        # a repair can leave a CHAIN of deferred sections whose first link
        # becomes compilable mid-wave; waiting for the whole wave to finish
        # parked a ready 26-node recovery chain for no reason.
        sections, reactivated, dropped = _reactivate_deferred_sections(ctx, sections)
        if reactivated or dropped:
            _save_ctx_state(ctx, sections)
        if dropped:
            # A deferred section that no longer compiles returns its labels to
            # this wave for regeneration, in topological position.
            already = set(order)
            order.extend(
                label
                for label in _topo_order(ctx.nodes)
                if label in dropped and label not in already
            )
    if deferred_requests:
        # The wave is drained: every independently-statable node is frozen.
        # Now surface one repair for the main loop. Remaining clusters raise
        # on the next wave, which will again finish all independent work
        # first, so a hard corner costs its own nodes instead of the run.
        primary = deferred_requests[0]
        if len(deferred_requests) > 1:
            others = sorted(
                {label for req in deferred_requests[1:] for label in req.labels}
            )
            _log(
                f"  wave drained; repairing {', '.join(primary.labels[:4])} first, "
                f"{len(others)} other node(s) still awaiting repair"
            )
        # Carry this wave's frozen sections out through the exception; the
        # caller's list may no longer be the one we appended to.
        primary.frozen_sections = [
            sec for sec in sections if sec.number not in incoming_numbers
        ]
        raise primary
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


def _prove_section(
    ctx: Ctx,
    sec: Section,
    sections: list[Section],
    requested_labels: list[str] | None = None,
) -> SectionProofOutcome:
    tag = f"S{sec.number:02d}"
    outcome = SectionProofOutcome(section=sec)
    # Per-section backend sessions (worker-thread local): proof rounds over the
    # same file reuse the context built by earlier rounds. See _call_model.
    sessions: dict[str, str] = {}
    parsed, index = _module_decl_texts(sec)
    requested = set(requested_labels or sec.labels)
    sorry_labels = [
        label
        for label in sec.labels
        if label in requested
        and _lean_name(label) in index
        and _has_terminal_sorry(parsed.decls[index[_lean_name(label)]].text)
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
        _save_ctx_state(ctx, sections)
    return outcome


# ---------------------------------------------------------------------------
# Blueprint repair (evidence-driven, batched)


def _invalidate_after_repair(
    ctx: Ctx,
    sections: list[Section],
    changed: set[str],
    lean_command: list[str],
    *,
    previous_nodes: dict[str, Node] | None = None,
) -> tuple[list[Section], set[str]]:
    """Invalidate changed contracts and defer unchanged descendants.

    Changed declarations are removed immediately. Descendants whose own full
    blueprint contract fingerprint did not change are retained as untrusted
    cache candidates: their ``.olean`` is removed and they stop counting as
    frozen until ``_reactivate_deferred_sections`` rebinds imports and Lean
    recompiles them against the repaired interfaces.
    """
    descendants = _dependency_descendants(ctx.nodes, changed) | changed
    if previous_nodes is not None:
        descendants |= _dependency_descendants(previous_nodes, changed)
    invalidated = set(changed)
    kept: list[Section] = []
    for sec in sections:
        if not sec.path.is_file():
            invalidated |= set(sec.labels)
            continue
        hit = set(sec.labels) & changed
        affected = set(sec.labels) & descendants
        if not affected:
            sec.deferred = False
            kept.append(sec)
            continue
        if hit:
            parsed, _index = _module_decl_texts(sec)
            owned_names = {_lean_name(label) for label in sec.labels}
            # Unowned local helpers may encode the changed contract. Without a
            # reliable label-level owner, retaining them would be unsafe; drop
            # this directly edited section and regenerate it normally. Broad
            # downstream sections can still be deferred and salvaged.
            if any(
                decl.name is None or decl.name not in owned_names
                for decl in parsed.decls
            ):
                invalidated |= set(sec.labels)
                for artifact in (sec.path, sec.path.with_suffix(".olean")):
                    with contextlib.suppress(FileNotFoundError, OSError):
                        artifact.unlink()
                continue
            first_changed = min(
                index for index, label in enumerate(sec.labels) if label in hit
            )
            prefix = [
                label
                for label in sec.labels[:first_changed]
                if label not in changed
            ]
            invalidated |= set(sec.labels) - set(prefix)
            if not prefix:
                for artifact in (sec.path, sec.path.with_suffix(".olean")):
                    with contextlib.suppress(FileNotFoundError, OSError):
                        artifact.unlink()
                continue
            prefix_names = {_lean_name(label) for label in prefix}
            parsed.decls = [
                decl for decl in parsed.decls if decl.name in prefix_names
            ]
            sec.labels = prefix
            _write_section(sec, parsed)
            ok, _output = _check_lean(sec.path, lean_command)
            if ok and _compile_module_olean(sec.path, lean_command).ok:
                sec.deferred = False
                kept.append(sec)
            else:
                invalidated |= set(prefix)
                for artifact in (sec.path, sec.path.with_suffix(".olean")):
                    with contextlib.suppress(FileNotFoundError, OSError):
                        artifact.unlink()
            continue
        sec.deferred = True
        invalidated |= set(sec.labels)
        with contextlib.suppress(FileNotFoundError, OSError):
            sec.path.with_suffix(".olean").unlink()
        kept.append(sec)
    return kept, invalidated


def _generated_skeleton_import(item: str, name: str) -> bool:
    base = _module_safe_name(name)
    return item.startswith(f"import AutoBlueprint.Generated.{base}.Skeleton")


def _reactivate_deferred_sections(
    ctx: Ctx,
    sections: list[Section],
    *,
    drop_unready: bool = False,
) -> tuple[list[Section], set[str], set[str]]:
    """Rebind and recompile unchanged descendants after a repair.

    Returns ``(sections, reactivated_labels, dropped_labels)``. No model or
    semantic critic is called: the node's full contract fingerprint is already
    unchanged, and Lean recompilation checks it against the final regenerated
    dependency interfaces.
    """
    reactivated: set[str] = set()
    dropped: set[str] = set()
    active = [sec for sec in sections if not sec.deferred]
    waiting = [sec for sec in sections if sec.deferred]
    progress = True
    while waiting and progress:
        progress = False
        owner = {label: sec for sec in active for label in sec.labels}
        for sec in list(waiting):
            own = set(sec.labels)
            external_deps = {
                dep
                for label in sec.labels
                for dep in ctx.nodes.get(
                    label, Node(label, "", Path("."), 0)
                ).uses
                if dep in ctx.nodes
                and not ctx.nodes[dep].mathlibok
                and dep not in own
            }
            if any(dep not in owner for dep in external_deps):
                continue
            try:
                parsed, index = _module_decl_texts(sec)
            except OSError:
                dropped.update(sec.labels)
                waiting.remove(sec)
                progress = True
                continue
            if any(_lean_name(label) not in index for label in sec.labels):
                dropped.update(sec.labels)
                waiting.remove(sec)
                progress = True
                for artifact in (sec.path, sec.path.with_suffix(".olean")):
                    with contextlib.suppress(FileNotFoundError, OSError):
                        artifact.unlink()
                _record(
                    ctx.telemetry,
                    "deferred_section_recheck",
                    section=sec.number,
                    labels=sec.labels,
                    status="missing_declarations",
                    compile_output_tail="",
                )
                continue
            generated_imports = _sections_for_deps(ctx, sec.labels, active)
            parsed.imports = [f"import {module}" for module in generated_imports] + [
                item
                for item in parsed.imports
                if not _generated_skeleton_import(item, ctx.name)
            ]
            sec.import_modules = generated_imports
            _write_section(sec, parsed)
            ok, output = _check_lean(sec.path, ctx.lean_command)
            object_ok = ok and _compile_module_olean(
                sec.path, ctx.lean_command
            ).ok
            if object_ok:
                sec.deferred = False
                active.append(sec)
                waiting.remove(sec)
                reactivated.update(sec.labels)
                progress = True
                _log(
                    f"  reactivated deferred {sec.file_name} "
                    f"({len(sec.labels)} unchanged contract(s))"
                )
                _record(
                    ctx.telemetry,
                    "deferred_section_recheck",
                    section=sec.number,
                    labels=sec.labels,
                    status="reactivated",
                    compile_output_tail="",
                )
            else:
                dropped.update(sec.labels)
                waiting.remove(sec)
                progress = True
                for artifact in (sec.path, sec.path.with_suffix(".olean")):
                    with contextlib.suppress(FileNotFoundError, OSError):
                        artifact.unlink()
                _log(
                    f"  deferred {sec.file_name} no longer compiles; "
                    f"returning {len(sec.labels)} node(s) to Phase 1"
                )
                _record(
                    ctx.telemetry,
                    "deferred_section_recheck",
                    section=sec.number,
                    labels=sec.labels,
                    status="compile_failed",
                    compile_output_tail=output[-4000:],
                )
    if waiting and drop_unready:
        for sec in waiting:
            dropped.update(sec.labels)
            for artifact in (sec.path, sec.path.with_suffix(".olean")):
                with contextlib.suppress(FileNotFoundError, OSError):
                    artifact.unlink()
            _record(
                ctx.telemetry,
                "deferred_section_recheck",
                section=sec.number,
                labels=sec.labels,
                status="dependencies_unavailable",
                compile_output_tail="",
            )
        waiting = []
    retained = active + waiting
    retained.sort(key=lambda sec: sec.number)
    return retained, reactivated, dropped


_PAPER_EXCERPT_HEAD = 2000
_WORD_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_-]{3,}")


def _paper_excerpt_for(ctx: Ctx, labels: list[str], *, budget: int = 20000) -> str:
    """Deterministic paper slice for repair prompts: the head of the paper
    (title/abstract) plus the paragraphs sharing the rarest terms with the
    target nodes' TeX. Repair calls previously carried the full paper."""
    paper = ctx.paper_text or ""
    if len(paper) <= budget:
        return paper
    target_text = " ".join(ctx.tex_blocks.get(label, "") for label in labels)
    target_tokens = set(_WORD_TOKEN_RE.findall(target_text.lower()))
    paragraphs = [para for para in re.split(r"\n\s*\n", paper) if para.strip()]
    freq: dict[str, int] = {}
    para_tokens: list[set[str]] = []
    for para in paragraphs:
        tokens = set(_WORD_TOKEN_RE.findall(para.lower())) & target_tokens
        para_tokens.append(tokens)
        for token in tokens:
            freq[token] = freq.get(token, 0) + 1
    scored = sorted(
        (
            (sum(1.0 / freq[token] for token in tokens), index)
            for index, tokens in enumerate(para_tokens)
        ),
        reverse=True,
    )
    head = paper[:_PAPER_EXCERPT_HEAD]
    used = len(head)
    chosen: set[int] = set()
    for score, index in scored:
        if score <= 0.0:
            break
        size = len(paragraphs[index]) + 2
        if used + size > budget:
            continue
        chosen.add(index)
        used += size
    body = "\n\n".join(paragraphs[index] for index in sorted(chosen))
    if not body:
        return head
    return f"{head}\n\n[... paper excerpted; paragraphs relevant to the failing nodes ...]\n\n{body}"


def _repair_node_context(
    ctx: Ctx,
    labels: list[str],
    *,
    dep_budget: int = 14000,
    consumer_budget: int = 6000,
) -> str:
    """Failing nodes in full, dependency-closure statements, and immediate
    consumer statements — the slice a repair actually needs, instead of the
    entire blueprint."""
    target_set = {label for label in labels if label in ctx.nodes}
    blocks: list[str] = []
    for label in sorted(target_set):
        node = ctx.nodes[label]
        blocks.append(
            f"## FAILING NODE {label} ({node.kind}; uses "
            f"[{', '.join(sorted(node.uses)) or 'none'}])\n"
            f"```tex\n{ctx.tex_blocks.get(label, '')[:5000]}\n```"
        )
    dep_blocks: list[str] = []
    used = 0
    for label in sorted(_dependency_closure(ctx.nodes, sorted(target_set)) - target_set):
        piece = (
            f"### dependency {label} ({ctx.nodes[label].kind})\n"
            f"```tex\n{ctx.stmt_blocks.get(label, '')[:1500]}\n```"
        )
        if used + len(piece) > dep_budget:
            dep_blocks.append(
                f"### (further dependencies omitted for space, starting at {label})"
            )
            break
        dep_blocks.append(piece)
        used += len(piece)
    consumer_blocks: list[str] = []
    used = 0
    consumers = sorted(
        label
        for label, node in ctx.nodes.items()
        if node.uses & target_set and label not in target_set
    )[:8]
    for label in consumers:
        piece = (
            f"### immediate consumer {label} ({ctx.nodes[label].kind})\n"
            f"```tex\n{ctx.stmt_blocks.get(label, '')[:1200]}\n```"
        )
        if used + len(piece) > consumer_budget:
            break
        consumer_blocks.append(piece)
        used += len(piece)
    parts = ["\n\n".join(blocks) or "(failing nodes no longer present in the blueprint)"]
    parts.append(
        "Dependency closure of the failing nodes (statements only):\n"
        + ("\n\n".join(dep_blocks) or "- none")
    )
    parts.append(
        "Immediate consumers of the failing nodes (statements only; their "
        "statements must keep compiling unchanged):\n"
        + ("\n\n".join(consumer_blocks) or "- none")
    )
    return "\n\n".join(parts)


_HARNESS_CONVENTIONS_NOTE = """\
Harness conventions (context for interpreting the evidence — do NOT spend
budget re-reading the pipeline scripts to rediscover them):
- Statements phase freezes every theorem-like node as `theorem ... := sorry`;
  proofs are produced and checked in a later phase. A `sorry` proof in the
  evidence is the designed convention, not a defect.
- Definition-kind nodes must have complete bodies (no `sorry`).
- The deterministic audit rejects: partial/failing tactic proofs, `sorry`
  inside definitions or helpers, statements that do not visibly mention their
  non-Mathlib `\\uses` dependencies, and placeholder names.
- The fix always belongs in the blueprint TeX, never in the pipeline scripts."""


_REPAIR_SCOPE_RULES = """\
- Prefer ADDITIVE repairs: add new helper nodes (with explicit `\\uses{...}`
  edges) rather than editing existing statements. Keep every node outside the
  failing nodes listed below unchanged unless the evidence shows that node
  itself is wrong.
- Do not rewrite downstream consumers of the failing nodes: consumer-side
  contract edits and edits with no dependency path to the failing nodes are
  detected deterministically and roll the whole repair back, wasting this
  trial. Consumers are rechecked automatically after the repaired contract
  freezes."""


def _fast_agent_repair_prompt(
    ctx: Ctx,
    labels: list[str],
    evidence: str,
    trial: int,
    *,
    escalation_note: str = "",
    model_timeout_s: int | None = None,
) -> str:
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

The blueprint source lives at `blueprints/{ctx.name}/blueprint/src/content.tex`;
read it from disk as needed (locate the failing nodes via their `\\label{{...}}`
anchors) and edit it in place. Everything you must know about the failing
nodes is already excerpted below — do not re-read the whole file into context.

Rules:
- Edit only `blueprints/{ctx.name}/blueprint/src/` and
  `blueprints/{ctx.name}/meta.yml` if metadata is genuinely wrong.
- Do not edit `.auto-blueprint/` Lean attempt files.
{_REPAIR_SCOPE_RULES}
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
- After editing, run `python scripts/validate_blueprint.py {ctx.name}`.

{_HARNESS_CONVENTIONS_NOTE}

{_repair_node_context(ctx, labels)}

Relevant paper context (deterministic excerpt):
<paper>
{_paper_excerpt_for(ctx, labels)}
</paper>

Lean critic output:
```text
{evidence[-12000:]}
```
"""


def _fast_api_repair_prompt(
    ctx: Ctx,
    labels: list[str],
    evidence: str,
    trial: int,
    blueprint_source: str,
    *,
    escalation_note: str = "",
    model_timeout_s: int | None = None,
) -> str:
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
  "content_tex": "full replacement for blueprints/{ctx.name}/blueprint/src/content.tex",
  "notes": "short explanation of what changed"
}}

Rules:
- Fix the blueprint, not the Lean code.
{_REPAIR_SCOPE_RULES}
- Copy every node outside the failing nodes byte-for-byte from the current
  source below.
- Do not make the theorem weaker just to satisfy Lean.
- Add missing intermediate blueprint nodes when the proof needs them.
- Correct `\\uses{{...}}` whenever dependencies were missing or wrong.
- Do not include `\\begin{{document}}` or `\\end{{document}}`.

{_HARNESS_CONVENTIONS_NOTE}

{_repair_node_context(ctx, labels)}

Relevant paper context (deterministic excerpt):
<paper>
{_paper_excerpt_for(ctx, labels)}
</paper>

Current blueprint source:
```tex
{blueprint_source}
```

Lean critic output:
```text
{evidence[-12000:]}
```
"""


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
    """Run one transactional blueprint-repair attempt.

    Agent runners can edit ``content.tex`` before timing out. Every unsuccessful
    call therefore restores the exact pre-call source. The caller treats an
    empty result as a consumed no-op repair and continues until the configured
    repair budget is exhausted.
    """
    content_path = (
        REPO_ROOT / "blueprints" / ctx.name / "blueprint" / "src" / "content.tex"
    )
    before_content = content_path.read_text(encoding="utf-8")
    blueprint_source = _read_blueprint_source(ctx.name)
    before_fps = dict(ctx.contract_fps)
    _log(f"==> Blueprint repair {trial}/{max_trials} for: " + ", ".join(labels[:8]))
    if repair_runner_agent:
        prompt = _fast_agent_repair_prompt(
            ctx,
            labels,
            evidence,
            trial,
            escalation_note=escalation_note,
            model_timeout_s=ctx.hard_timeout,
        )
    else:
        prompt = _fast_api_repair_prompt(
            ctx,
            labels,
            evidence,
            trial,
            blueprint_source,
            escalation_note=escalation_note,
            model_timeout_s=ctx.hard_timeout,
        )
    prompt_artifact = _store_text(ctx.telemetry, "prompt_blueprint_repair", prompt)
    try:
        runner = _make_runner(
            ctx.escalation_runner_spec,
            timeout=ctx.hard_timeout,
            readonly=False,
            effort=ctx.escalation_effort,
            with_skill=True,
        )
    except RunnerError as exc:
        _record(
            ctx.telemetry,
            "model_call",
            purpose="blueprint_repair",
            labels=labels,
            status="error",
            duration_s=0.0,
            timeout_s=ctx.hard_timeout,
            backend=ctx.escalation_runner_spec.partition(":")[0],
            model=ctx.escalation_runner_spec.partition(":")[2],
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
        )
        _record(
            ctx.telemetry,
            "blueprint_repair_result",
            labels=labels,
            status="runner_error",
            changed_labels=[],
            changed_count=0,
            reason=str(exc),
        )
        if is_environment_error(exc):
            raise
        return set()
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
        # A CLI agent may have written a partial repair before the process
        # timed out. Never let a failed call mutate the next attempt's input.
        content_path.write_text(before_content, encoding="utf-8")
        restored = validate_blueprint(REPO_ROOT, ctx.name)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        if is_environment_error(exc):
            raise
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
        _record(
            ctx.telemetry,
            "blueprint_repair_result",
            labels=labels,
            status=status,
            changed_labels=[],
            changed_count=0,
            reason=str(exc),
        )
        return set()
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
    try:
        if not repair_runner_agent:
            _write_api_refinement(ctx.name, result.text)
        validation = validate_blueprint(REPO_ROOT, ctx.name)
        if not validation.ok:
            print_result(validation)
            raise ValueError("blueprint repair produced an invalid blueprint")
    except (OSError, ValueError) as exc:
        content_path.write_text(before_content, encoding="utf-8")
        restored = validate_blueprint(REPO_ROOT, ctx.name)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        _record(
            ctx.telemetry,
            "blueprint_repair_result",
            labels=labels,
            status="invalid_rolled_back",
            changed_labels=[],
            changed_count=0,
            reason=str(exc),
        )
        _log(f"  invalid blueprint repair rolled back: {exc}")
        return set()
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
        status="applied" if changed else "noop",
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
    excerpt = _paper_excerpt_for(ctx, section_labels)
    paper_block = (
        f"\nRelevant paper context (deterministic excerpt):\n<paper>\n{excerpt}\n</paper>\n"
        if excerpt
        else ""
    )
    if api_mode:
        source_block = f"""
Current blueprint source:
```tex
{blueprint_source}
```
"""
    else:
        source_block = f"""
The blueprint source lives at `blueprints/{ctx.name}/blueprint/src/content.tex`;
read it from disk as needed (locate the section nodes via their `\\label{{...}}`
anchors) and edit it in place. The section nodes are already excerpted above —
do not re-read the whole file into context.
"""
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

{_HARNESS_CONVENTIONS_NOTE}

The recurring evidence is:
```text
{evidence[-12000:]}
```

Section nodes to normalize:
{section_nodes}

{paper_block}
{source_block}
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
    prompt_artifact = _store_text(ctx.telemetry, "prompt_section_normalization", prompt)
    try:
        runner = _make_runner(
            ctx.escalation_runner_spec,
            timeout=ctx.hard_timeout,
            readonly=False,
            effort=ctx.escalation_effort,
            with_skill=True,
        )
    except RunnerError as exc:
        _record(
            ctx.telemetry,
            "section_normalization_result",
            labels=section_labels,
            status="runner_error",
            changed_labels=[],
            changed_count=0,
            reason=str(exc),
        )
        if is_environment_error(exc):
            raise
        raise SectionNormalizationRejected(str(exc)) from exc
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
        content_path.write_text(before_content, encoding="utf-8")
        restored = validate_blueprint(REPO_ROOT, ctx.name)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        if is_environment_error(exc):
            raise
        raise SectionNormalizationRejected(str(exc)) from exc
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
    except Exception as exc:
        content_path.write_text(before_content, encoding="utf-8")
        validation = validate_blueprint(REPO_ROOT, ctx.name)
        if validation.ok:
            ctx.refresh_nodes(validation.nodes)
        raise SectionNormalizationRejected(str(exc)) from exc
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


def _record_proof_graph_telemetry(
    telemetry: TelemetryRun,
    nodes: dict[str, Node],
    *,
    proof_order: str,
    reason: str,
    focus_labels: set[str] | None = None,
) -> None:
    """Record the current proof graph and node-level scheduling features."""
    proof_layers = _top_down_proof_layers(nodes)
    proof_depth = {
        label: depth for depth, labels in enumerate(proof_layers) for label in labels
    }
    theorem_labels = set(proof_depth)
    immediate_theorem_deps = {
        label: sorted(_immediate_theorem_dependencies(nodes, label, theorem_labels))
        for label in theorem_labels
    }
    theorem_consumers: dict[str, list[str]] = {label: [] for label in theorem_labels}
    for consumer, dependencies in immediate_theorem_deps.items():
        for dependency in dependencies:
            theorem_consumers.setdefault(dependency, []).append(consumer)
    telemetry.record(
        "proof_schedule_graph",
        proof_order=proof_order,
        reason=reason,
        layers=proof_layers,
        roots=proof_layers[0] if proof_layers else [],
        immediate_theorem_dependencies=immediate_theorem_deps,
    )
    node_blocks = _node_tex_blocks(nodes)
    targets = nodes if focus_labels is None else {
        label: node for label, node in nodes.items() if label in focus_labels
    }
    roots = set(proof_layers[0]) if proof_layers else set()
    for label, node in targets.items():
        telemetry.record(
            "node_features",
            **node_structural_features(
                label, node.kind, node_blocks.get(label, ""), len(node.uses)
            ),
            proof_depth=proof_depth.get(label),
            is_proof_root=label in roots,
            immediate_theorem_dependencies=immediate_theorem_deps.get(label, []),
            immediate_theorem_dependency_count=len(immediate_theorem_deps.get(label, [])),
            theorem_consumers=sorted(theorem_consumers.get(label, [])),
            theorem_consumer_count=len(theorem_consumers.get(label, [])),
        )


def _verified_node_labels(ctx: Ctx, sections: list[Section]) -> set[str]:
    """Nodes whose current contract is already discharged in Lean/Mathlib."""
    frozen = _frozen_labels(sections)
    proved = _proved_labels(sections)
    return {
        label
        for label, node in ctx.nodes.items()
        if node.mathlibok
        or label in proved
        or (label in frozen and not _is_theorem_like_kind(node.kind))
    }


def _print_pipeline_progress(
    ctx: Ctx, sections: list[Section], repair_trials: int, max_trials: int
) -> None:
    verified = _verified_node_labels(ctx, sections)
    print(
        f"==> Progress: {len(verified)}/{len(ctx.nodes)} blueprint nodes verified; "
        f"repairs {repair_trials}/{max_trials}",
        flush=True,
    )
    _record(
        ctx.telemetry,
        "pipeline_progress",
        verified_labels=sorted(verified),
        verified_count=len(verified),
        total_nodes=len(ctx.nodes),
        repair_trials_used=repair_trials,
        repair_trials_max=max_trials,
    )


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
        "--proof-order",
        choices=("top-down", "parallel"),
        default=DEFAULT_PROOF_ORDER,
        help=(
            "Proof scheduler: top-down proves public theorem roots before their "
            "dependencies; parallel preserves the previous all-sections behavior"
        ),
    )
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
    resume_group = parser.add_mutually_exclusive_group()
    resume_group.add_argument(
        "--continue",
        dest="continue_run",
        action="store_true",
        default=True,
        help="Reuse compatible frozen statements and accepted proofs (default)",
    )
    resume_group.add_argument(
        "--fresh",
        dest="continue_run",
        action="store_false",
        help="Discard generated fast-pipeline state and start from scratch",
    )
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
        proof_order=args.proof_order,
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
    _record_proof_graph_telemetry(
        telemetry,
        validation.nodes,
        proof_order=args.proof_order,
        reason="initial",
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
        library_candidates=list(library_candidates),
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
        f"- proof order: `{args.proof_order}`",
        f"- blueprint repair budget: `{args.max_trials}`",
        f"- library candidates: `{len(library_candidates)}`",
        "",
    ]

    repair_trials = 0
    noop_repairs = 0
    escalation_note = ""
    stuck_sections: list[SectionStuckState] = []
    started = time.monotonic()
    _print_pipeline_progress(ctx, sections, repair_trials, args.max_trials)
    try:
        while True:
            sections, reactivated, dropped_cached = _reactivate_deferred_sections(
                ctx, sections
            )
            if reactivated or dropped_cached:
                _save_ctx_state(ctx, sections)
            frozen = _frozen_labels(sections)
            reserved = _reserved_labels(sections)
            pending = {
                label
                for label, node in ctx.nodes.items()
                if not node.mathlibok and label not in reserved
            }
            if not pending and any(sec.deferred for sec in sections):
                sections, more_reactivated, more_dropped = (
                    _reactivate_deferred_sections(
                        ctx, sections, drop_unready=True
                    )
                )
                reactivated |= more_reactivated
                dropped_cached |= more_dropped
                _save_ctx_state(ctx, sections)
                if more_dropped:
                    continue
                frozen = _frozen_labels(sections)
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
                    sections, reactivated, dropped_cached = (
                        _reactivate_deferred_sections(
                            ctx, sections, drop_unready=True
                        )
                    )
                    _save_ctx_state(ctx, sections)
                    _print_pipeline_progress(
                        ctx, sections, repair_trials, args.max_trials
                    )
                    if dropped_cached:
                        continue
                except RepairRequest as request:
                    if request.frozen_sections:
                        already_frozen = _frozen_labels(sections)
                        preserved = [
                            sec
                            for sec in request.frozen_sections
                            if not (set(sec.labels) & already_frozen)
                        ]
                        if preserved:
                            sections.extend(preserved)
                            _save_ctx_state(ctx, sections)
                            _log(
                                "  preserved "
                                f"{sum(len(sec.labels) for sec in preserved)} "
                                "frozen node(s) completed before the repair"
                            )
                            _record(
                                ctx.telemetry,
                                "partial_sections_preserved",
                                section_numbers=[sec.number for sec in preserved],
                                labels=[
                                    label
                                    for sec in preserved
                                    for label in sec.labels
                                ],
                            )
                    evidence_for_repair = request.evidence
                    repair_labels = request.labels
                    _quarantine_labels(ctx, request.labels, "blueprint_repair_request")
                    repair_helpers = request.decomposition_helpers
                    repair_section_labels = request.section_labels
                    phase1_repair = True

            if evidence_for_repair is None:
                unproved_by_section: list[tuple[Section, list[str]]] = []
                all_unproved: set[str] = set()
                for sec in sections:
                    parsed, index = _module_decl_texts(sec)
                    labels = [
                        label
                        for label in sec.labels
                        if _lean_name(label) in index
                        and _has_terminal_sorry(
                            parsed.decls[index[_lean_name(label)]].text
                        )
                    ]
                    all_unproved.update(labels)
                    if labels:
                        unproved_by_section.append((sec, labels))
                proof_layer = -1
                proof_roots: list[str] = []
                frontier_labels = sorted(all_unproved)
                if args.proof_order == "top-down" and all_unproved:
                    proof_layer, frontier_labels, proof_roots = _next_top_down_frontier(
                        ctx.nodes, all_unproved
                    )
                    frontier = set(frontier_labels)
                    unproved_by_section = [
                        (sec, [label for label in labels if label in frontier])
                        for sec, labels in unproved_by_section
                    ]
                    unproved_by_section = [
                        (sec, labels)
                        for sec, labels in unproved_by_section
                        if labels
                    ]
                if unproved_by_section:
                    mode_note = (
                        f"top-down frontier {proof_layer} ({len(frontier_labels)} node(s))"
                        if args.proof_order == "top-down"
                        else f"{len(unproved_by_section)} section(s)"
                    )
                    print(
                        f"==> Phase 2: filling proofs for {mode_note} "
                        f"with {args.workers} worker(s)",
                        flush=True,
                    )
                    _record(
                        ctx.telemetry,
                        "proof_frontier_scheduled",
                        proof_order=args.proof_order,
                        layer=proof_layer,
                        labels=frontier_labels,
                        root_labels=proof_roots,
                        unproved_before=len(all_unproved),
                        section_count=len(unproved_by_section),
                    )
                    outcomes: list[SectionProofOutcome] = []
                    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
                        futures = [
                            pool.submit(_prove_section, ctx, sec, sections, labels)
                            for sec, labels in unproved_by_section
                        ]
                        for future in concurrent.futures.as_completed(futures):
                            outcomes.append(future.result())
                    _save_ctx_state(ctx, sections)
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
                    else:
                        proved_now = sorted(
                            {label for outcome in outcomes for label in outcome.proved}
                        )
                        remaining_after = all_unproved - set(proved_now)
                        _record(
                            ctx.telemetry,
                            "proof_frontier_result",
                            proof_order=args.proof_order,
                            layer=proof_layer,
                            labels=frontier_labels,
                            proved_labels=proved_now,
                            remaining_after=len(remaining_after),
                            status="accepted",
                        )
                        if args.proof_order == "top-down" and proof_layer == 0:
                            admitted_dependencies = sorted(
                                {
                                    dep
                                    for label in proved_now
                                    for dep in _dependency_closure(ctx.nodes, [label])
                                    if dep in all_unproved
                                }
                            )
                            _record(
                                ctx.telemetry,
                                "conditional_root_proofs",
                                root_labels=proved_now,
                                admitted_dependency_labels=admitted_dependencies,
                                admitted_dependency_count=len(admitted_dependencies),
                            )
                        _print_pipeline_progress(
                            ctx, sections, repair_trials, args.max_trials
                        )
                        if args.proof_order == "top-down" and remaining_after:
                            # Root/frontier proofs are now cached against immutable
                            # dependency contracts. Descend one graph layer without
                            # falling through to the final-completeness check.
                            continue

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
            nodes_before_repair = dict(ctx.nodes)
            content_path = (
                REPO_ROOT
                / "blueprints"
                / ctx.name
                / "blueprint"
                / "src"
                / "content.tex"
            )
            content_before_repair = content_path.read_text(encoding="utf-8")
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
            disconnected_rollback = False
            if changed:
                graph_distances = _repair_graph_distances(
                    nodes_before_repair, ctx.nodes, repair_labels, changed
                )
                disconnected = {
                    label
                    for label, distance in graph_distances.items()
                    if distance is None
                }
                downstream_scope_violations = (
                    _phase1_repair_scope_violations(
                        nodes_before_repair, ctx.nodes, repair_labels, changed
                    )
                    if phase1_repair
                    else set()
                )
                _record(
                    ctx.telemetry,
                    "blueprint_repair_scope",
                    labels=repair_labels,
                    action=action,
                    changed_labels=sorted(changed),
                    graph_distances=graph_distances,
                    disconnected_labels=sorted(disconnected),
                    added_labels=sorted(
                        set(ctx.nodes) - set(nodes_before_repair)
                    ),
                    removed_labels=sorted(
                        set(nodes_before_repair) - set(ctx.nodes)
                    ),
                    downstream_scope_violations=sorted(downstream_scope_violations),
                )
                if disconnected or downstream_scope_violations:
                    content_path.write_text(
                        content_before_repair, encoding="utf-8"
                    )
                    restored = validate_blueprint(REPO_ROOT, ctx.name)
                    if restored.ok:
                        ctx.refresh_nodes(restored.nodes)
                    else:
                        # The snapshot was validated immediately before the
                        # repair. Keep the in-memory graph coherent and let the
                        # next normal validation pass retry rather than turning
                        # a recoverable repair into a new terminal condition.
                        ctx.refresh_nodes(nodes_before_repair)
                        _record(
                            ctx.telemetry,
                            "blueprint_repair_result",
                            labels=repair_labels,
                            status="rollback_validation_retry",
                            changed_labels=sorted(changed),
                            changed_count=len(changed),
                        )
                    _record(
                        ctx.telemetry,
                        "blueprint_repair_result",
                        labels=repair_labels,
                        status=(
                            "scope_rolled_back"
                            if downstream_scope_violations
                            else "disconnected_rolled_back"
                        ),
                        changed_labels=sorted(changed),
                        changed_count=len(changed),
                        disconnected_labels=sorted(disconnected),
                        downstream_scope_violations=sorted(downstream_scope_violations),
                    )
                    if downstream_scope_violations:
                        report_lines.append(
                            f"- {action} {repair_trials}: rolled back downstream "
                            f"contract changes `{', '.join(sorted(downstream_scope_violations)[:8])}`"
                        )
                    else:
                        report_lines.append(
                            f"- {action} {repair_trials}: rolled back graph-unrelated "
                            f"contract changes `{', '.join(sorted(disconnected)[:8])}`"
                        )
                    changed = set()
                    disconnected_rollback = True
                    if downstream_scope_violations:
                        escalation_note = (
                            "The previous Phase 1 repair was rolled back because it "
                            "changed downstream/consumer blueprint contracts instead "
                            "of only the failing target and its dependency/helper side. "
                            "For the next repair, edit only the listed failing node(s) "
                            "and any helper/dependency nodes they directly need. Do not "
                            "rewrite consumers; they will be rechecked deterministically "
                            "after the repaired contract freezes."
                        )
                    else:
                        escalation_note = (
                            "The previous transaction was rolled back because it changed "
                            "blueprint nodes with no dependency path to the requested "
                            "repair targets in either the old or new uses graph. Keep "
                            "the next repair dependency-connected; add explicit uses "
                            "edges for genuinely necessary helpers or consumers."
                        )
            if changed:
                noop_repairs = 0
                escalation_note = ""
                sections, invalidated = _invalidate_after_repair(
                    ctx,
                    sections,
                    changed,
                    lean_command,
                    previous_nodes=nodes_before_repair,
                )
                deferred_labels = {
                    label
                    for sec in sections
                    if sec.deferred
                    for label in sec.labels
                }
                _record(
                    ctx.telemetry,
                    "repair_invalidation",
                    changed_labels=sorted(changed),
                    invalidated_labels=sorted(invalidated),
                    invalidated_count=len(invalidated),
                    deferred_labels=sorted(deferred_labels),
                    deferred_count=len(deferred_labels),
                    regeneration_labels=sorted(set(invalidated) - deferred_labels),
                    regeneration_count=len(set(invalidated) - deferred_labels),
                    kept_section_count=len(sections),
                    proof_order=args.proof_order,
                )
                _record_proof_graph_telemetry(
                    ctx.telemetry,
                    ctx.nodes,
                    proof_order=args.proof_order,
                    reason="post_repair",
                    focus_labels=invalidated | changed,
                )
                _save_ctx_state(ctx, sections)
                print(
                    f"  {action} changed {len(changed)} contract(s); "
                    f"{len(deferred_labels)} unchanged dependent node(s) queued "
                    "for deterministic recheck; "
                    f"{len(set(invalidated) - deferred_labels)} node(s) require "
                    f"regeneration; kept {len(sections)} skeleton section(s)",
                    flush=True,
                )
            else:
                noop_repairs += 1
                if disconnected_rollback:
                    print(
                        "  out-of-scope repair changes rolled back; "
                        "retrying with narrower scope",
                        flush=True,
                    )
                elif noop_repairs == 1:
                    escalation_note = (
                        "Your previous repair changed NOTHING in the parsed node "
                        "statements. You MUST materially edit the TeX of the listed "
                        "node(s): add missing concrete semantics, hypotheses, or split "
                        "them into smaller nodes."
                    )
                else:
                    escalation_note = _decomposition_note(repair_labels)
                if not disconnected_rollback:
                    print("  repair was a no-op; escalating instructions", flush=True)
            _print_pipeline_progress(ctx, sections, repair_trials, args.max_trials)
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
