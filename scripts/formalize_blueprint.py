#!/usr/bin/env python3
"""Statements-first Lean formalization pipeline.

This is the fast successor to ``refine_blueprint_with_lean.py``. The blueprint
remains the only mathematical source of truth and Lean remains the critic; what
changes is *when* model calls happen and how much each one is asked to do:

Phase 1 (skeleton). A few batched model calls generate one Lean declaration per
blueprint node, section by section in dependency order: real bodies for
definition nodes, ``:= sorry`` proofs for theorem-like nodes. Each section is
compiled locally, compile errors are fixed in batched rounds, and the
statement-alignment audit (deterministic coverage + one batched model audit per
section) runs on the *statements* before any proof effort is spent. Accepted
statements are frozen: later phases may only replace ``sorry`` bodies, never
edit a statement. A statement that cannot faithfully encode its node routes to
blueprint repair, exactly as before.

Phase 2 (proofs). For every frozen ``sorry``:
1. a deterministic tactic ladder (``rfl``/``omega``/``norm_num``/``ring``/
   ``simp``/``aesop``) runs first, with zero model cost;
2. survivors are filled by batched model calls (10-20 proofs per call);
3. the residue escalates to singleton calls at high reasoning effort;
4. persistent failures become *evidence* for a bounded blueprint repair.

Timeouts are treated as latency, never as mathematical difficulty: a timed-out
call is bisected or retried at higher effort. Only real Lean/audit output (or
an explicit NEEDS-DECOMPOSITION refusal) can trigger a blueprint repair, and
repairs invalidate downstream nodes by *statement* fingerprint, so proof-prose
edits never discard accepted work.

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
from model_runners.base import is_environment_error
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
    _decl_signatures,
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
from telemetry import TelemetryRun
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
PROOF_SINGLETON_RETRIES = 2
LEAN_CHECK_TIMEOUT = 900
LADDER_HEARTBEATS = 400_000

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
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance)"
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
    statement; the proof prose is context for the proof phase only. Hashing
    statements (not whole blocks) is what lets proof-prose-only blueprint edits
    keep accepted work.
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


def _skeleton_code_issues(code: str, target_kinds: dict[str, str]) -> list[str]:
    """Correctness audit variant for the skeleton phase.

    Like ``_audit_lean_code`` but ``sorry`` is legal exactly as the terminal
    proof of a theorem-like declaration; everywhere else (definition bodies,
    preamble, mid-proof) it is rejected.
    """
    issues: list[str] = []
    if re.search(r"\badmit\b|by\s*\?", code):
        issues.append("contains a forbidden placeholder (`admit` or `by ?`)")
    if "set_option autoImplicit true" in code:
        issues.append("enables `autoImplicit`")
    bad = [f"{kind} {name}" for kind, name in FORBIDDEN_ASSUMPTIONS.findall(code)]
    if bad:
        issues.append(f"uses top-level assumptions instead of implementations: {', '.join(bad[:12])}")
    invented = sorted(set(FORBIDDEN_BLUEPRINT_STUBS.findall(code)))
    if invented:
        issues.append(f"calls invented paper/blueprint helpers: {', '.join(invented[:12])}")
    if _FORBIDDEN_TOPLEVEL_RE.search(code):
        issues.append(
            "contains top-level `variable`/`namespace`/`section`/`example` commands; "
            "each declaration must be self-contained"
        )
    parsed = _parse_module(code)
    for line in parsed.preamble:
        stripped = line.strip()
        if stripped and not stripped.startswith(("open", "--", "/-")):
            issues.append(f"unexpected non-`open` preamble command: `{stripped[:80]}`")
    for decl in parsed.decls:
        if "sorry" not in decl.text:
            continue
        expected_kind = target_kinds.get(decl.name or "")
        if expected_kind in THEOREM_LIKE_KINDS and _has_terminal_sorry(decl.text):
            inner = _TERMINAL_SORRY_RE.sub("", decl.text)
            if re.search(r"\bsorry\b", inner):
                issues.append(f"`{decl.name}` uses sorry outside the terminal proof position")
            continue
        issues.append(
            f"`{decl.name or decl.kind}` contains sorry but is not a theorem-like "
            "blueprint target; definition bodies and helpers must be complete"
        )
    for decl in parsed.decls:
        name = decl.name or ""
        if PLACEHOLDER_NAME_RE.search(name):
            issues.append(f"placeholder declaration name `{name}`")
        if decl.kind in {"def", "abbrev"} and re.search(r":\s*Prop\s*:=\s*True\b", decl.text):
            issues.append(f"`{name}` defines a proposition as `True`")
        if decl.kind in {"theorem", "lemma"} and re.search(r":\s*True\s*:=", decl.text):
            issues.append(f"`{name}` proves only `True`")
    return issues


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

    def __init__(self, evidence: str, labels: list[str], *, decomposition_helpers: list[str] | None = None):
        super().__init__(evidence[:500])
        self.evidence = evidence
        self.labels = labels
        self.decomposition_helpers = decomposition_helpers or []


@dataclass
class Ctx:
    name: str
    runner_spec: str
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
    nodes: dict[str, Node] = field(default_factory=dict)
    stmt_blocks: dict[str, str] = field(default_factory=dict)
    tex_blocks: dict[str, str] = field(default_factory=dict)
    stmt_fps: dict[str, str] = field(default_factory=dict)
    unavailable_imports: set[str] = field(default_factory=set)

    def refresh_nodes(self, nodes: dict[str, Node]) -> None:
        self.nodes = nodes
        self.stmt_blocks = _statement_blocks(nodes)
        self.tex_blocks = _node_tex_blocks(nodes)
        self.stmt_fps = _statement_fingerprints(nodes)


def _make_runner(spec: str, *, timeout: int, readonly: bool, effort: str | None, with_skill: bool = False):
    kwargs = {}
    if spec.partition(":")[0] == "codex" and effort:
        kwargs["reasoning_effort"] = effort
    return get_runner(
        spec,
        context_files=[SKILL_PATH] if with_skill else None,
        timeout=timeout,
        readonly=readonly,
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
    tag: str = "",
) -> CallResult:
    runner = _make_runner(ctx.runner_spec, timeout=timeout, readonly=readonly, effort=effort)
    prompt_artifact = _store_text(ctx.telemetry, f"prompt_{purpose}", prompt)
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
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
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
        )
        if is_environment_error(exc):
            raise
        status = "timeout" if _is_timeout_error(exc) else "error"
        _log(f"model call ({purpose}) {status}: {str(exc)[:160]}", tag=tag)
        return CallResult(status=status, error=str(exc), duration_s=duration)
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


def _save_state(name: str, sections: list[Section], stmt_fps: dict[str, str]) -> None:
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
            }
        )
    path = _state_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"version": 1, "sections": entries}, indent=2) + "\n", encoding="utf-8")


def _load_state(ctx: Ctx, lean_command: list[str]) -> list[Section]:
    """Resume: keep sections whose file and blueprint statements are unchanged.

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
        fps = entry.get("statement_fps") or {}
        ok = (
            path.is_file()
            and labels
            and all(
                label in ctx.nodes and ctx.stmt_fps.get(label) == fps.get(label)
                for label in labels
            )
            and not any(dep in dropped_modules for dep in entry.get("import_modules") or [])
        )
        if ok:
            invalidated = _dependency_descendants(ctx.nodes, dropped_labels) - dropped_labels
            ok = not (set(labels) & invalidated)
        if ok and hashlib.sha256(path.read_bytes()).hexdigest() != entry.get("sha256"):
            # The file changed after the last state save (e.g. proofs were
            # spliced right before a crash). The blueprint statements still
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


def _accepted_signatures(sections: list[Section], modules: list[str]) -> str:
    parts: list[str] = []
    for sec in sections:
        if sec.module not in modules:
            continue
        try:
            parts.append(_decl_signatures(sec.path.read_text(encoding="utf-8")))
        except OSError:
            continue
    return "\n\n".join(part for part in parts if part)


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
    signatures = _accepted_signatures(sections, import_modules)
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

Signatures already frozen in those modules (use them; never redefine):
```lean
{signatures[-14000:] or '-- none'}
```

Whole blueprint node graph (orientation only):
{_node_summary(ctx.nodes)}

Target nodes for THIS file:
{target_text}
"""


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
    signatures = _accepted_signatures(sections, import_modules)
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

Available frozen signatures (same module and imported skeleton modules):
```lean
{signatures[-14000:] or '-- none'}
```

Target declarations:
{chr(10).join(parts)}
"""


# ---------------------------------------------------------------------------
# Alignment audit (skeleton-aware)


def _skeleton_deterministic_audit(code: str, ctx: Ctx, labels: list[str]) -> list[str]:
    """Coverage/kind checks for a section. Dependency-mention checks are only
    applied to declarations that are already complete (definitions and eagerly
    proved theorem-likes); sorry-proved statements get theirs at proof time."""
    issues: list[str] = []
    decls = _lean_declarations(code)
    for label in labels:
        node = ctx.nodes[label]
        if node.mathlibok:
            continue
        decl = decls.get(_lean_name(label))
        if decl is None:
            issues.append(f"missing generated declaration for {label} -> `{_lean_name(label)}`")
            continue
        if node.kind == "definition" and decl.kind in {"theorem", "lemma"}:
            issues.append(f"{label} is a definition but generated `{decl.kind} {decl.name}`")
        if node.kind in THEOREM_LIKE_KINDS and decl.kind in {"structure", "inductive", "class"}:
            issues.append(f"{label} is theorem-like but generated `{decl.kind} {decl.name}`")
        if not _has_terminal_sorry(decl.text):
            missing = _nonmathlib_uses_missing_from_decl(label, node, decl, ctx.nodes, decls)
            if missing:
                issues.append(
                    f"{label} does not mention required dependency generated name(s): "
                    + ", ".join(f"`{_lean_name(dep)}`" for dep in missing[:12])
                )
    return issues


def _model_alignment_audit(
    ctx: Ctx, labels: list[str], code: str, *, tag: str = ""
) -> tuple[str, str, set[str]] | None:
    """Batched statement-alignment audit. None means accepted.

    Returns (kind, reason, rejected_labels) on rejection, where kind is
    ``blueprint`` or ``lean-generation`` (statement re-generation).
    """
    decls = _lean_declarations(code)
    nodes = {label: ctx.nodes[label] for label in labels}
    prompt = _statement_audit_prompt(ctx.name, nodes, ctx.tex_blocks, decls, ctx.paper_text)
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
            tag=tag,
        )
        if result.status != "ok":
            return ("lean-generation", f"statement audit call failed: {result.error}", set(labels))
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        return ("lean-generation", f"statement audit returned invalid JSON: {exc}", set(labels))
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
    return (kind, "Statement alignment audit rejected:\n- " + "\n- ".join(formatted), rejected)


# ---------------------------------------------------------------------------
# Phase 1: skeleton


def _freeze_section(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    next_number: int,
) -> list[Section]:
    """Generate, compile-fix, audit, and freeze one section (possibly bisected).

    Returns the newly frozen Section objects (appended by the caller). Raises
    RepairRequest when the blueprint itself must change first.
    """
    import_modules = _sections_for_deps(ctx, labels, sections)
    target_kinds = {_lean_name(label): ctx.nodes[label].kind for label in labels}
    module, path = _section_module(ctx.name, next_number)
    path.parent.mkdir(parents=True, exist_ok=True)
    _log(f"==> Skeleton section {next_number:02d}: {len(labels)} node(s): " + ", ".join(labels[:6]) + ("..." if len(labels) > 6 else ""))

    feedback = ""
    previous_code = ""
    audit_rounds = 0
    for round_no in range(1, STATEMENT_FIX_ROUNDS + AUDIT_REGEN_ROUNDS + 2):
        effort = ctx.base_effort
        timeout = ctx.base_timeout if round_no == 1 else ctx.hard_timeout
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
        )
        if result.status == "timeout":
            if len(labels) > 1:
                # Latency, not difficulty: bisect the section and recurse.
                mid = len(labels) // 2
                _log(f"  section call timed out; bisecting into {mid} + {len(labels) - mid} node(s)")
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
            )
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
                )
        elif result.status == "error":
            feedback = f"model call failed: {result.error}"
            continue

        refusal = _parse_decomposition_refusal(result.text)
        if refusal is not None:
            refused = [refusal["label"]] if refusal["label"] in labels else list(labels)
            raise RepairRequest(
                "The statement generator determined node(s) cannot be stated 1-1 as "
                f"written.\nReason: {refusal['reason']}",
                refused,
                decomposition_helpers=refusal["missing_helpers"],
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

        issues = _skeleton_code_issues(module_code, target_kinds)
        issues += _skeleton_deterministic_audit(module_code, ctx, labels)
        if issues:
            feedback = "Deterministic skeleton audit rejected the file:\n- " + "\n- ".join(issues)
            previous_code = code
            _log(f"  deterministic audit failed ({len(issues)} issue(s)); regenerating")
            continue

        path.write_text(module_code, encoding="utf-8")
        ok, output = _check_lean(path, ctx.lean_command)
        if not ok:
            feedback = f"Lean rejected the file:\n{output[-12000:]}"
            previous_code = module_code
            _log("  lean rejected skeleton section; sending errors back")
            continue

        audit = _model_alignment_audit(ctx, labels, module_code)
        if audit is not None:
            kind, reason, rejected = audit
            if kind == "blueprint":
                raise RepairRequest(reason, sorted(rejected))
            audit_rounds += 1
            if audit_rounds > AUDIT_REGEN_ROUNDS:
                raise RepairRequest(
                    "Statement alignment audit kept rejecting regenerated statements; "
                    "the blueprint text likely under-determines the statement.\n" + reason,
                    sorted(rejected),
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
    )


def _run_phase1(ctx: Ctx, sections: list[Section], pending: set[str]) -> list[Section]:
    next_number = max((sec.number for sec in sections), default=0) + 1
    for group in _partition_sections(ctx.nodes, pending, ctx.section_size):
        new_sections = _freeze_section(ctx, group, sections, next_number)
        sections.extend(new_sections)
        next_number = max(sec.number for sec in sections) + 1
        _save_state(ctx.name, sections, ctx.stmt_fps)
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
            )
            if result.status == "timeout" and len(batch) > 1:
                # Latency: halve the batch size for the rest of this section.
                batch_size = max(1, batch_size // 2)
                next_remaining.extend(batch)
                _log(f"batch timed out; reducing batch size to {batch_size}", tag=tag)
                continue
            if result.status != "ok":
                next_remaining.extend(batch)
                continue
            refusal = _parse_decomposition_refusal(result.text)
            if refusal is not None:
                refused = refusal["label"] if refusal["label"] in batch else batch[0]
                outcome.decomposition[refused] = refusal["missing_helpers"]
                errors[refused] = f"generator refusal: {refusal['reason']}"
                next_remaining.extend(label for label in batch if label != refused)
                continue
            proved, batch_errors = _apply_proof_batch(ctx, sec, result.text, targets, tag=tag)
            outcome.proved.extend(proved)
            errors.update(batch_errors)
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
                tag=tag,
            )
            if result.status != "ok":
                errors.setdefault(
                    label,
                    f"escalated proof call {result.status}: {result.error[:400]}",
                )
                continue
            refusal = _parse_decomposition_refusal(result.text)
            if refusal is not None:
                outcome.decomposition[label] = refusal["missing_helpers"]
                errors[label] = f"generator refusal: {refusal['reason']}"
                break
            proved, batch_errors = _apply_proof_batch(ctx, sec, result.text, targets, tag=tag)
            errors.update(batch_errors)
            if proved:
                outcome.proved.extend(proved)
                solved = True
                break
            parsed, index = _module_decl_texts(sec)
        if not solved and label not in outcome.decomposition:
            still.append(label)

    for label in still:
        outcome.failed[label] = errors.get(label, "no proof found within the configured budgets")
    # Deliberately no .olean recompile here: statements never change in phase 2,
    # so importers keep working against the frozen (sorry-proved) oleans, and
    # skipping the rebuild avoids racing concurrent section workers. The final
    # assembled check compiles everything from scratch anyway.
    with _STATE_LOCK:
        _save_state(ctx.name, sections, ctx.stmt_fps)
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
    before_fps = dict(ctx.stmt_fps)
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
        ctx.runner_spec,
        timeout=ctx.hard_timeout,
        readonly=False,
        effort=ctx.escalation_effort,
        with_skill=True,
    )
    prompt_artifact = _store_text(ctx.telemetry, "prompt_blueprint_repair", prompt)
    started = time.monotonic()
    result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
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
        for label, fp in ctx.stmt_fps.items()
        if before_fps.get(label) != fp
    }
    changed |= {label for label in before_fps if label not in ctx.stmt_fps}
    _record(
        ctx.telemetry,
        "blueprint_repair_result",
        labels=labels,
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
    parser.add_argument("--runner", default="codex", help="Runner spec, e.g. codex, claude-code")
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
        runner=args.runner,
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

    blueprint_source = _read_blueprint_source(args.name)
    print("==> Searching local Lean libraries once for this run", flush=True)
    library_context, library_candidates = _search_local_lean_libraries(
        args.name, validation.nodes, blueprint_source, term_runner=None
    )

    ctx = Ctx(
        name=args.name,
        runner_spec=args.runner,
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

    report_lines = [
        f"# Statements-First Formalization: `{args.name}`",
        "",
        f"- runner: `{args.runner}` (base effort `{args.reasoning_effort}`, escalation `{args.escalation_effort}`)",
        f"- timeouts: `{args.timeout}s` base / `{args.hard_timeout}s` escalated",
        f"- section size: `{args.section_size}`; proof batch: `{args.proof_batch_size}`; workers: `{args.workers}`",
        f"- blueprint repair budget: `{args.max_trials}`",
        f"- library candidates: `{len(library_candidates)}`",
        "",
    ]

    repair_trials = 0
    noop_repairs = 0
    escalation_note = ""
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

            if pending:
                print(
                    f"==> Phase 1: freezing statements for {len(pending)} node(s) "
                    f"({len(frozen)} already frozen)",
                    flush=True,
                )
                try:
                    sections = _run_phase1(ctx, sections, pending)
                    _save_state(args.name, sections, ctx.stmt_fps)
                except RepairRequest as request:
                    evidence_for_repair = request.evidence
                    repair_labels = request.labels
                    repair_helpers = request.decomposition_helpers

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
                    _save_state(args.name, sections, ctx.stmt_fps)
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
                else:
                    # Shouldn't happen: no failures reported but nodes unproved.
                    evidence_for_repair = "Internal inconsistency: unproved nodes without failure evidence: " + ", ".join(sorted(required - proved))
                    repair_labels = sorted(required - proved)

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

            repair_trials += 1
            note = escalation_note
            if repair_helpers:
                note = _decomposition_note(repair_labels, repair_helpers)
            changed = _repair_blueprint(
                ctx,
                evidence_for_repair,
                repair_labels,
                trial=repair_trials,
                max_trials=args.max_trials,
                escalation_note=note,
                repair_runner_agent=args.runner.partition(":")[0] in {"codex", "claude-code"},
            )
            report_lines.append(
                f"- repair {repair_trials}: {len(changed)} node statement(s) changed "
                f"for `{', '.join(repair_labels[:8])}`"
            )
            if changed:
                noop_repairs = 0
                escalation_note = ""
                sections, invalidated = _invalidate_after_repair(
                    ctx, sections, changed, lean_command
                )
                _save_state(args.name, sections, ctx.stmt_fps)
                print(
                    f"  repair changed {len(changed)} statement(s); invalidated "
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
