#!/usr/bin/env python3
"""Statements-first Lean formalization pipeline.

This is the fast successor to ``refine_blueprint_with_lean.py``. The blueprint
remains the only mathematical source of truth and Lean remains the critic; what
changes is *when* model calls happen and how much each one is asked to do:

Fixed traversal policy. Phase 1 freezes statements bottom-up from dependency
leaves toward public results. Phase 2 fills deferred bodies top-down from public
results toward supporting declarations. Phase 1 parallelizes independent groups
and routed fragments; Phase 2 parallelizes independent nodes within each
root-first wave.

Phase 1 (statements and interfaces). Traverse the existing blueprint dependency
graph bottom-up and freeze exact Lean statements and interfaces corresponding
one-to-one with the blueprint. A bounded pair of concurrent root-first planning
calls records compact per-node contract decisions. Their mechanically coherent
provider-consumer components are selected and merged before generation; the
alternate is retained as a zero-call fallback. Planning does not generate Lean
or change traversal. Entries are statement-fingerprinted, persisted, and
selectively invalidated by repairs.
All compilation-driven interface correction, deterministic coverage checking,
statement alignment, and any required blueprint repair happen here. Bottom-up
sections remain in-memory candidates while deterministic checks run, compile
in parallel, and then receive the authoritative statement audit. Rejected
declarations alone are corrected and re-audited; accepted siblings keep their
exact text. The final import gate re-audits only declarations (or owned helpers)
changed by compiler feedback.
A Phase-1 candidate may contain only its blueprint targets and exact
plan-owned structure/inductive/class interfaces. Executable helper definitions
or theorems are implementation work and are rejected before compilation.
A contract is frozen only after those checks pass. Later phases may replace ``sorry``
bodies but cannot silently edit an accepted statement.

Model-output boundary. Every Lean response is canonicalized into declarations
before it reaches state: the pipeline owns imports/preamble/module layout,
normalizes theorem-like commands, rejects duplicate names, gives local helpers
stable node-owned global names, and records ownership. Raw model files are never
persisted or merged directly.

Phase 2 (implementations). Follow a top-down traversal across every deferred
body: theorem proofs and ``def``/``abbrev`` implementations. Higher proofs are
therefore checked first against the complete frozen Phase-1 interface; filling
a lower theorem body later does not alter that interface. Completed definition
bodies receive a semantic blueprint audit before acceptance. For every frozen
``sorry``:
1. a deterministic tactic ladder (``rfl``/``omega``/``norm_num``/``ring``/
   ``simp``/``aesop``) runs first, with zero model cost;
2. survivors are filled by batched model calls;
3. the residue is sent to singleton calls through the configured escalation runner;
4. persistent failures become *evidence* for a bounded blueprint repair.

Timeouts are treated as latency, never as mathematical difficulty: a timed-out
call is bisected before any singleton uses the escalation runner. Only real Lean/audit output (or
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
import copy
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
from typing import Any, Iterable

from generate_blueprint import _extract_json, read_paper
from lean_preflight import check_lean_environment
from model_runners import RunnerError, get_runner
from model_runners.api import choose_model, list_anthropic_model_ids, list_openai_model_ids
from model_runners.base import is_environment_error, is_transient_error
from model_runners.cli import choose_codex_base_model, choose_codex_escalation_model, list_codex_model_ids
from refine_blueprint_with_lean import (
    LEAN_IDIOM_CHEATSHEET,
    FORBIDDEN_ASSUMPTIONS,
    FORBIDDEN_BLUEPRINT_STUBS,
    PLACEHOLDER_NAME_RE,
    TeeStream,
    _alignment_failure_kind,
    _authorized_alignment_failure_kind,
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
    _rebuild_site_for,
    _run_lean,
    _run_log_path,
    _search_local_lean_libraries,
    _search_terms_from_blueprint,
    _statement_audit_prompt,
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
DEFAULT_SECTION_SIZE = 12
DEFAULT_PROOF_BATCH = 12
DEFAULT_WORKERS = 3
PHASE1_STATEMENT_ORDER = "bottom-up"
PHASE2_PROOF_ORDER = "top-down"
# Bounded per-section transaction: one base generation attempt plus at most
# one escalated retry. Every stage (deterministic patch, compile patch, audit
# correction) gets exactly one targeted fix before the attempt is spent; a
# section that survives neither attempt routes to blueprint repair with fresh
# attempts after the contract changes. The old 6-round nested retry maze
# burned 7+ model calls per stuck node and still ended in the same repair.
SKELETON_GENERATION_ATTEMPTS = 2
# One declaration-local patch is allowed at each model tier. A second failure
# moves to the escalation tier or blueprint repair instead of looping inside
# the same anchored generation session.
TARGETED_DECL_PATCH_ROUNDS = 1
COMPILER_CORRECTION_ROUNDS = 3


def _requires_initial_declaration_pass(refinement_order: str) -> bool:
    """Only root-first elaboration needs unresolved lower names predeclared."""
    return refinement_order == "top-down"

_ACTIVE_STAGE_LOCK = threading.Lock()
_ACTIVE_STAGE = "startup"


def _set_active_stage(stage: str) -> None:
    global _ACTIVE_STAGE
    with _ACTIVE_STAGE_LOCK:
        _ACTIVE_STAGE = stage


def _active_stage() -> str:
    with _ACTIVE_STAGE_LOCK:
        return _ACTIVE_STAGE


@contextlib.contextmanager
def _stage(stage: str):
    previous = _active_stage()
    _set_active_stage(stage)
    try:
        yield
    finally:
        _set_active_stage(previous)
# Initial declaration pass: create the provisional declarations that Lean must
# be able to resolve before root-first statement refinement can begin. Emission
# is dependency-first solely because Lean imports require providers to exist;
# mathematical contract design and acceptance happen later, root-first, in
# Phase 1. Below the minimum the per-section emitter is already cheap enough.
BULK_SKELETON_MIN_NODES = 6
# Keep provisional emission bounded. A single 39-node call previously exceeded
# the hard budget without returning code, while these chunks only need usable
# signatures and provisional bodies.
BULK_SKELETON_CHUNK = 12
# Bound unusually large planning prompts. Ordinary graphs use one call; graphs
# above this size use a small number of planning batches inside the same stage.
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
    r"(theorem|lemma|corollary|def|abbrev|structure|inductive|class|instance)\b"
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
# Phase 1 workers share retry candidates and rejection evidence.  State helpers
# call one another (for example, a read prunes stale entries first), so this
# must be reentrant and every compound read/modify/write must use it.
_STATE_LOCK = threading.RLock()


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


def _bottom_up_statement_layers(nodes: dict[str, Node]) -> list[list[str]]:
    """All generated nodes in dependency-first graph frontiers.

    A node is eligible only after every generated dependency in its ``uses``
    set has appeared in an earlier layer. Mathlib-settled dependencies are
    already available and therefore do not participate in the scheduler.
    """
    source_order = _node_order(nodes)
    position = {label: index for index, label in enumerate(source_order)}
    remaining = {
        label for label, node in nodes.items() if not node.mathlibok
    }
    layers: list[list[str]] = []
    while remaining:
        layer = sorted(
            (
                label
                for label in remaining
                if not ({dep for dep in nodes[label].uses if dep in remaining})
            ),
            key=position.get,
        )
        if not layer:
            # Validation guarantees acyclicity. Preserve total behavior if a
            # malformed graph somehow reaches the scheduler.
            layer = [min(remaining, key=position.get)]
        layers.append(layer)
        remaining.difference_update(layer)
    return layers


def _bottom_up_ready_frontier(
    nodes: dict[str, Node], pending: set[str], frozen: set[str]
) -> list[str]:
    """Return pending contracts whose generated dependencies are frozen.

    Unlike the static layer partition, this frontier is recomputed after every
    successful transaction. A difficult node therefore blocks only its own
    dependents; accepted siblings can immediately unlock work in other graph
    branches without weakening dependency-first refinement.
    """
    position = {label: index for index, label in enumerate(_node_order(nodes))}
    generated = {label for label, node in nodes.items() if not node.mathlibok}
    return sorted(
        (
            label
            for label in pending
            if {
                dep for dep in nodes[label].uses if dep in generated
            } <= frozen
        ),
        key=position.get,
    )


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


def _bottom_up_proof_layers(nodes: dict[str, Node]) -> list[list[str]]:
    """Theorem-like nodes from proof leaves upward to public roots."""
    return list(reversed(_top_down_proof_layers(nodes)))


def _next_bottom_up_frontier(
    nodes: dict[str, Node], unproved: set[str]
) -> tuple[int, list[str], list[str]]:
    """Return the next dependency-first theorem frontier."""
    layers = _bottom_up_proof_layers(nodes)
    roots = layers[-1] if layers else []
    for layer, labels in enumerate(layers):
        pending = [label for label in labels if label in unproved]
        if pending:
            return layer, pending, roots
    return -1, [], roots


def _next_implementation_frontier(
    nodes: dict[str, Node], unresolved: set[str], refinement_order: str
) -> tuple[int, list[str], list[str]]:
    """Schedule every deferred body, including definitions, in graph order."""
    layers = (
        _top_down_statement_layers(nodes)
        if refinement_order == "top-down"
        else _bottom_up_statement_layers(nodes)
    )
    roots = layers[0] if layers else []
    for layer, labels in enumerate(layers):
        pending = [label for label in labels if label in unresolved]
        if pending:
            return layer, pending, roots
    return -1, [], roots


def _top_down_statement_layers(nodes: dict[str, Node]) -> list[list[str]]:
    """All generated nodes from public theorem roots down to graph leaves.

    The initial declaration pass has already made every name available, so
    Phase 1 is free to refine contracts in the direction required by the
    method: public claims first, then the definitions and lemmas they constrain.
    Unconsumed public definitions start alongside theorem roots; any malformed
    leftover component is appended deterministically as a defensive fallback.
    """
    order = _node_order(nodes)
    position = {label: index for index, label in enumerate(order)}
    generated = {
        label for label, node in nodes.items() if not node.mathlibok
    }
    consumed = {
        dep
        for label in generated
        for dep in nodes[label].uses
        if dep in generated
    }
    theorem_roots = [
        label
        for label in order
        if label in generated
        and _is_theorem_like_kind(nodes[label].kind)
        and label not in consumed
    ]
    # Public generated definitions can be independent outputs rather than
    # dependencies of a theorem. They are roots of their own graph component
    # and should be refined in the same wave, not serialized one per synthetic
    # layer after all theorem work.
    other_roots = [
        label
        for label in order
        if label in generated
        and label not in consumed
        and label not in set(theorem_roots)
    ]
    roots = theorem_roots + other_roots

    depth: dict[str, int] = {}
    frontier = list(roots)
    current_depth = 0
    while frontier:
        next_frontier: set[str] = set()
        for label in frontier:
            previous = depth.get(label)
            if previous is not None and previous >= current_depth:
                continue
            depth[label] = current_depth
            next_frontier.update(
                dep for dep in nodes[label].uses if dep in generated
            )
        frontier = sorted(next_frontier, key=position.get)
        current_depth += 1

    # A blueprint may contain notation or supporting components that are not
    # reachable from a public theorem. They still need Phase-1 alignment. Put
    # them after the root-driven component while preserving a deterministic
    # consumer-before-dependency order.
    remaining = generated - set(depth)
    if remaining:
        topo = [label for label in _topo_order(nodes) if label in remaining]
        for label in reversed(topo):
            depth[label] = current_depth
            current_depth += 1

    return [
        sorted(
            (label for label, item_depth in depth.items() if item_depth == layer),
            key=position.get,
        )
        for layer in range(max(depth.values(), default=-1) + 1)
    ]


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
class CanonicalModelModule:
    """Pipeline-owned representation of one model-produced Lean response.

    ``owner_by_index`` assigns every target declaration and local helper to a
    blueprint node. Raw file wrappers are deliberately absent: the pipeline,
    not the model, owns module structure.
    """

    parsed: ParsedModule
    owner_by_index: dict[int, str]


@dataclass
class SkeletonFinding:
    """One Phase-1 skeleton audit finding, optionally tied to one blueprint node.

    Targeted findings let Phase 1 ask the model to replace only the bad Lean
    declaration instead of regenerating or repairing a whole section.
    """

    message: str
    label: str | None = None
    lean_name: str | None = None
    category: str = ""
    dependencies: tuple[str, ...] = ()


@dataclass(frozen=True)
class PlanClosureFinding:
    """Mechanical plan inconsistency and the contract that can repair it.

    ``consumer`` owns the invalid reference. ``provider`` identifies a missing
    member surface only when the provider is authorized by the consumer's
    dependency closure. Keeping that ownership structured prevents an invented
    consumer reference from needlessly blocking or rewriting a healthy provider.
    """

    consumer: str
    message: str
    provider: str | None = None
    unauthorized_dependencies: tuple[str, ...] = ()
    missing_provider_members: tuple[str, ...] = ()
    cycle_paths: tuple[str, ...] = ()


@dataclass
class DesignPlanCandidate:
    """One independently generated full-plan candidate and its mechanical score."""

    candidate_id: str
    entries: dict[str, dict[str, Any]]
    missing: list[str]
    findings: dict[str, list[str]]
    blocked: set[str]
    components: list[list[str]]

    @property
    def score(self) -> tuple[int, int, int, int]:
        return (
            len(self.missing),
            len(self.blocked),
            sum(len(items) for items in self.findings.values()),
            len(self.components),
        )

    @property
    def closed(self) -> bool:
        return not self.missing and not self.findings


@dataclass
class PlanClosureCorrectionResult:
    """One isolated correction result from a concurrent closure wave."""

    component: tuple[str, ...]
    entries: dict[str, dict[str, Any]]
    status: str
    findings: dict[str, list[str]]
    duration_s: float
    started_at_s: float
    finished_at_s: float


@dataclass(frozen=True)
class AlignmentAuditResult:
    """Semantic rejection plus dependency evidence for failure routing.

    Iteration exposes the historical four fields so existing callers remain
    compatible. Required dependencies are consumed only by the graph-repair
    guard after the corrected Lean independently confirms the same reference.
    """

    kind: str
    reason: str
    rejected: set[str]
    helpers: list[str]
    required_dependencies: dict[str, set[str]] = field(default_factory=dict)
    kinds_by_label: dict[str, str] = field(default_factory=dict)
    helpers_by_label: dict[str, list[str]] = field(default_factory=dict)
    reasons_by_label: dict[str, str] = field(default_factory=dict)
    origins_by_label: dict[str, str] = field(default_factory=dict)
    plan_requirements_by_label: dict[str, list[str]] = field(default_factory=dict)

    def __iter__(self):
        yield self.kind
        yield self.reason
        yield self.rejected
        yield self.helpers

    def __getitem__(self, index: int):
        return (self.kind, self.reason, self.rejected, self.helpers)[index]

    def labels_for(self, *kinds: str) -> set[str]:
        wanted = set(kinds)
        return {
            label
            for label in self.rejected
            if self.kinds_by_label.get(label, self.kind) in wanted
        }

    def helpers_for(self, labels: Iterable[str]) -> list[str]:
        selected_labels = list(labels)
        selected = list(
            dict.fromkeys(
                helper
                for label in selected_labels
                for helper in self.helpers_by_label.get(label, [])
            )
        )
        if not selected and self.kind == "decomposition":
            return list(self.helpers)
        return selected

    def labels_for_origin(self, *origins: str) -> set[str]:
        wanted = set(origins)
        return {
            label
            for label in self.rejected
            if self.origins_by_label.get(label, "lean") in wanted
        }

    def plan_requirements_for(self, labels: Iterable[str]) -> list[str]:
        return sorted(
            {
                requirement
                for label in labels
                for requirement in self.plan_requirements_by_label.get(label, [])
            }
        )

    def reason_for(self, labels: Iterable[str]) -> str:
        selected = [
            self.reasons_by_label[label]
            for label in labels
            if label in self.reasons_by_label
        ]
        if not selected:
            return self.reason
        return "Blueprint contract audit rejected:\n- " + "\n- ".join(selected)


@dataclass(frozen=True)
class RepairBoundaryAuditOutcome:
    """One scoped semantic check of a model-mutated blueprint component."""

    status: str  # accepted | repair | unavailable
    evidence: str = ""
    repair_labels: tuple[str, ...] = ()
    required_dependencies: dict[str, set[str]] = field(default_factory=dict)
    decomposition_helpers: tuple[str, ...] = ()


def _coerce_alignment_audit_result(
    audit: AlignmentAuditResult | tuple,
) -> AlignmentAuditResult:
    """Normalize the historical tuple form at the audit-consumer boundary."""
    if isinstance(audit, AlignmentAuditResult):
        return audit
    values = tuple(audit)
    if len(values) < 4:
        raise ValueError("alignment audit result must contain at least four fields")
    required_dependencies = values[4] if len(values) > 4 else {}
    return AlignmentAuditResult(
        str(values[0]),
        str(values[1]),
        set(values[2]),
        list(values[3]),
        required_dependencies,
    )


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


def _normalize_theorem_like_keywords(
    parsed: ParsedModule, nodes: dict[str, Node], labels: Iterable[str]
) -> ParsedModule:
    """Rewrite model-facing theorem synonyms to Lean's ``theorem`` command.

    Blueprint node kinds include ``corollary``, ``claim``, and other
    theorem-like prose categories, but Lean declarations use ``theorem`` (or
    ``lemma``).  Normalizing after parsing keeps an otherwise useful model
    response from becoming both an invalid command and an apparent omission.
    """
    theorem_names = {
        _lean_name(label)
        for label in labels
        if label in nodes and _is_theorem_like_kind(nodes[label].kind)
    }
    normalized: list[DeclBlock] = []
    for decl in parsed.decls:
        if decl.name in theorem_names and decl.kind == "corollary":
            text = re.sub(
                r"^(\s*(?:@\[[^\]]+\]\s*)*"
                r"(?:(?:noncomputable|private|protected|unsafe|partial)\s+)*)"
                r"corollary\b",
                r"\1theorem",
                decl.text,
                count=1,
            )
            normalized.append(DeclBlock("theorem", decl.name, text))
        else:
            normalized.append(decl)
    return ParsedModule(parsed.imports, parsed.preamble, normalized)


_MODEL_WRAPPER_START_RE = re.compile(
    r"^\s*(?P<kind>namespace|section)(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?\s*$"
)
_MODEL_WRAPPER_END_RE = re.compile(
    r"^\s*end(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?\s*$"
)
_ALLOWED_MODEL_PREAMBLE_RE = re.compile(
    r"^\s*(?:open(?:\s+scoped)?\b.*|noncomputable\s+section)\s*$"
)


def _remove_model_module_wrappers(code: str) -> str:
    """Remove balanced module wrappers that are not part of declarations.

    Models often wrap otherwise valid output in ``namespace`` or ``section``.
    Generated declarations have globally fixed names, so wrappers are response
    formatting rather than mathematical content. They are removed before
    parsing; malformed/unbalanced wrappers are rejected instead of leaking into
    persistent state.
    """
    wrappers: list[tuple[str, str]] = []
    kept: list[str] = []
    for line in code.splitlines():
        start = _MODEL_WRAPPER_START_RE.match(line)
        if start and not line.strip().startswith("noncomputable"):
            wrappers.append((start.group("kind"), start.group("name") or ""))
            continue
        end = _MODEL_WRAPPER_END_RE.match(line)
        if end:
            if not wrappers:
                raise ValueError(f"unmatched model module wrapper `{line.strip()}`")
            _kind, expected_name = wrappers.pop()
            actual_name = end.group("name") or ""
            if expected_name and actual_name and expected_name != actual_name:
                raise ValueError(
                    "mismatched model module wrapper: "
                    f"expected `end {expected_name}`, got `{line.strip()}`"
                )
            continue
        kept.append(line)
    if wrappers:
        kind, name = wrappers[-1]
        raise ValueError(
            f"unclosed model module wrapper `{kind}{(' ' + name) if name else ''}`"
        )
    return "\n".join(kept)


def _declaration_owner_map(
    parsed: ParsedModule,
    label_by_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> dict[int, str]:
    """Assign targets and local helpers to blueprint-node owners.

    Planned helpers have explicit owners fixed by the accepted interface plan.
    Adjacency remains only as a fallback for genuinely unplanned helpers.
    """
    explicit = explicit_owner_by_name or {}
    owners: dict[int, str] = {}
    following: str | None = None
    for index in range(len(parsed.decls) - 1, -1, -1):
        direct = label_by_name.get(parsed.decls[index].name or "")
        if direct is not None:
            following = direct
        if following is not None:
            owners[index] = following
    previous: str | None = None
    for index, decl in enumerate(parsed.decls):
        direct = label_by_name.get(decl.name or "")
        if direct is not None:
            previous = direct
        elif index not in owners and previous is not None:
            owners[index] = previous
    for index, decl in enumerate(parsed.decls):
        owner = explicit.get(decl.name or "")
        if owner is not None:
            owners[index] = owner
    return owners


def _declaration_target_consumers(
    parsed: ParsedModule,
    target_by_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> dict[int, set[str]]:
    """Return every target that transitively references each declaration.

    Model responses may define one local helper that several blueprint targets
    consume. File adjacency cannot represent that relationship. This reference
    graph is the canonical ownership source used by namespacing, semantic cache
    keys, candidate slicing, and persistence.
    """
    index_by_name = {
        decl.name: index
        for index, decl in enumerate(parsed.decls)
        if decl.name
    }
    names = set(index_by_name)
    references: dict[int, set[int]] = {}
    for index, decl in enumerate(parsed.decls):
        own = decl.name or ""
        referenced = {
            name
            for name in names
            if name != own
            and re.search(
                rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'.])",
                decl.text,
            )
        }
        references[index] = {index_by_name[name] for name in referenced}

    consumers: dict[int, set[str]] = {
        index: set() for index in range(len(parsed.decls))
    }
    explicit = explicit_owner_by_name or {}
    for target_name, target in target_by_name.items():
        start = index_by_name.get(target_name)
        if start is None:
            continue
        consumers[start].add(target)
        stack = list(references.get(start, set()))
        seen: set[int] = set()
        while stack:
            index = stack.pop()
            if index in seen:
                continue
            seen.add(index)
            if (parsed.decls[index].name or "") not in target_by_name:
                consumers[index].add(target)
                stack.extend(references.get(index, set()))

    # Phase-1 target bodies are intentionally ``sorry``, so textual references
    # cannot recover ownership for plan-required helper interfaces. The plan is
    # authoritative for those helpers and must win over declaration adjacency.
    for index, decl in enumerate(parsed.decls):
        owner = explicit.get(decl.name or "")
        if owner is not None:
            consumers[index] = {owner}

    # Keep harmless unreferenced helpers deterministic. They cannot join two
    # components, but preserving their adjacent owner avoids silently dropping
    # model output before deterministic checks decide whether it is acceptable.
    fallback = _declaration_owner_map(
        parsed, target_by_name, explicit_owner_by_name
    )
    for index, owner in fallback.items():
        if not consumers[index]:
            consumers[index].add(owner)
    return consumers


def _target_components_from_helpers(
    parsed: ParsedModule,
    target_by_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> list[set[str]]:
    """Connected target components induced by shared local declarations."""
    targets = list(dict.fromkeys(target_by_name.values()))
    parent = {target: target for target in targets}

    def find(item: str) -> str:
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    def union(left: str, right: str) -> None:
        left_root, right_root = find(left), find(right)
        if left_root != right_root:
            parent[right_root] = left_root

    consumers = _declaration_target_consumers(
        parsed, target_by_name, explicit_owner_by_name
    )
    for index, owners in consumers.items():
        name = parsed.decls[index].name or ""
        if name in target_by_name or len(owners) < 2:
            continue
        ordered = sorted(owners)
        for owner in ordered[1:]:
            union(ordered[0], owner)
    grouped: dict[str, set[str]] = {}
    for target in targets:
        grouped.setdefault(find(target), set()).add(target)
    return list(grouped.values())


def _lean_identifier_replace(text: str, old: str, new: str) -> str:
    """Replace one ordinary Lean identifier without touching longer names."""
    return re.sub(
        rf"(?<![A-Za-z0-9_'.]){re.escape(old)}(?![A-Za-z0-9_'.])",
        lambda _match: new,
        text,
    )


def _declared_name_replace(text: str, old: str, new: str) -> str:
    """Rename only the declaration introduced by this block.

    This is distinct from replacing references in the declaration body: a
    structure may bind a field with the same spelling as its own old global
    name, and that field must continue to shadow the global declaration.
    """
    match = _DECL_START_RE.match(text)
    if match is None or match.group(2) != old:
        return text
    start, end = match.span(2)
    return text[:start] + new + text[end:]


def _restore_planned_member_declarations(
    text: str,
    helper: dict[str, Any],
    aliases: dict[str, str],
) -> str:
    """Keep structure/class field names stable while helpers are namespaced.

    A plan may legitimately give a helper and one of its fields the same name,
    for example ``class weightOf where weightOf : ...``. Helper aliases name
    global declarations; they must not rename member declarations that happen
    to use the same token. References to the helper type remain canonicalized.
    """
    members = _planned_member_names(helper)
    for member in sorted(members):
        replacement = aliases.get(member)
        if not member or not replacement or replacement == member:
            continue
        text = re.sub(
            rf"(?m)^(\s*(?:\|\s*)?){re.escape(replacement)}(?=\s*:)",
            lambda match: match.group(1) + member,
            text,
        )
    return text


def _planned_member_names(helper: dict[str, Any]) -> set[str]:
    """Names bound by one planned structure/class declaration.

    These names shadow equally named global helper declarations throughout the
    declaration body. For example, after a field
    ``DensityOperator : Register -> Type``, a later field type
    ``DensityOperator R`` refers to that field, not to a global helper also
    called ``DensityOperator``.
    """
    members = {
        str(item.get("name") or "").strip()
        for item in helper.get("members") or []
        if isinstance(item, dict)
    }
    members.update(
        str(item).strip() for item in helper.get("required_members") or []
    )
    return {member for member in members if member}


def _owned_helper_name(ctx: Ctx, name: str, owners: Iterable[str]) -> str:
    """Canonical global name assigned to one model-created local helper."""
    owner_list = sorted(set(owners))
    if not name or not owner_list:
        return name
    digest = hashlib.sha256(
        (
            f"{getattr(ctx, 'name', 'blueprint')}\0"
            + "\0".join(owner_list)
        ).encode("utf-8")
    ).hexdigest()[:12]
    prefix = f"_autobp_{digest}_"
    if name.startswith(prefix):
        return name
    safe_name = re.sub(r"[^A-Za-z0-9_']", "_", name)
    return prefix + safe_name


def _planned_helper_specs(
    ctx: Ctx, labels: Iterable[str]
) -> list[tuple[str, dict[str, Any]]]:
    """Return valid plan-owned helper contracts for the requested nodes."""
    entries = getattr(ctx, "design_plan_entries", {})
    specs: list[tuple[str, dict[str, Any]]] = []
    for label in labels:
        entry = entries.get(label) or {}
        if int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION:
            continue
        for helper in entry.get("helpers") or []:
            if str(helper.get("name") or "").strip():
                specs.append((label, helper))
    return specs


def _planned_helper_owner_by_name(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, str]:
    """Map canonical plan helper names to their blueprint-node owners."""
    return {
        _owned_helper_name(ctx, str(helper["name"]), [label]): label
        for label, helper in _planned_helper_specs(ctx, labels)
    }


def _semantic_helper_owner_by_name(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, str]:
    """Unambiguous advisory vocabulary ownership for first-pass ingestion."""
    owners: dict[str, set[str]] = {}
    requested = set(labels)
    for label, entry in getattr(ctx, "semantic_plan_entries", {}).items():
        if label not in requested:
            continue
        for item in entry.get("vocabulary") or []:
            if not isinstance(item, dict):
                continue
            name = str(item.get("name") or "").strip()
            if name:
                owners.setdefault(name, set()).add(label)
    return {
        name: next(iter(labels_for_name))
        for name, labels_for_name in owners.items()
        if len(labels_for_name) == 1
    }


def _planned_helper_aliases(ctx: Ctx) -> dict[str, str]:
    """Map model-facing plan spellings to canonical helper declarations.

    Contract plans commonly write an owned helper as ``target.Helper`` while
    generated modules store globally unique names. Later batches do not emit
    the helper again, so canonical ingestion must normalize those dependency
    references using the complete accepted plan, not wait for Lean to reject
    every consumer separately.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    aliases: dict[str, str] = {}
    bare_candidates: dict[str, set[str]] = {}
    for label, entry in entries.items():
        if int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION:
            continue
        owner_name = _lean_name(label)
        for helper in entry.get("helpers") or []:
            helper_name = str(helper.get("name") or "").strip()
            if not helper_name:
                continue
            canonical = _owned_helper_name(ctx, helper_name, [label])
            bare_candidates.setdefault(helper_name, set()).add(canonical)
            qualified = f"{owner_name}.{helper_name}"
            flattened = re.sub(r"[^A-Za-z0-9_']", "_", qualified)
            for alias in (
                qualified,
                flattened,
                _owned_helper_name(ctx, qualified, [label]),
                _owned_helper_name(ctx, flattened, [label]),
            ):
                if alias != canonical:
                    aliases[alias] = canonical
    # Plan target signatures deliberately use compact model-facing helper
    # names. Once providers and consumers are generated in separate modules,
    # those bare names must resolve to the persisted globally unique helper.
    # Rewrite only names that have exactly one owner across the complete plan;
    # ambiguous helper spellings remain untouched and are rejected normally.
    for helper_name, canonical_names in bare_candidates.items():
        if len(canonical_names) == 1:
            canonical = next(iter(canonical_names))
            if helper_name != canonical:
                aliases[helper_name] = canonical
    return aliases


def _planned_helper_assignments(
    ctx: Ctx,
    labels: list[str],
    parsed: ParsedModule,
    target_names: set[str],
) -> dict[int, tuple[str, str]]:
    """Match emitted helper declarations to accepted interface contracts.

    Models often qualify a planned helper with the target namespace or emit an
    already-canonical name. Exact name/suffix matches are unambiguous. If the
    name differs, kind plus the complete required-member surface may identify
    a helper, but only a mutual unique match is accepted. Ambiguous output is
    left untouched for the deterministic handoff gate to reject; this function
    never guesses ownership.
    """
    specs = _planned_helper_specs(ctx, labels)
    candidates = [
        index
        for index, decl in enumerate(parsed.decls)
        if decl.name and decl.name not in target_names
    ]
    assigned: dict[int, tuple[str, str]] = {}
    used_specs: set[int] = set()

    def canonical_for(spec_index: int) -> str:
        label, helper = specs[spec_index]
        return _owned_helper_name(ctx, str(helper["name"]), [label])

    def exact_name_match(decl_name: str, spec_index: int) -> bool:
        _label, helper = specs[spec_index]
        helper_name = str(helper["name"])
        safe_name = re.sub(r"[^A-Za-z0-9_']", "_", helper_name)
        return (
            decl_name == helper_name
            or decl_name == canonical_for(spec_index)
            or decl_name.endswith("." + helper_name)
            or (
                decl_name.startswith("_autobp_")
                and decl_name.endswith("_" + safe_name)
            )
        )

    # Contract names are globally unique within a valid plan. Resolve those
    # matches first, independent of declaration adjacency or target bodies.
    for spec_index, (label, helper) in enumerate(specs):
        matches = [
            index
            for index in candidates
            if index not in assigned
            and exact_name_match(parsed.decls[index].name or "", spec_index)
        ]
        if len(matches) == 1:
            assigned[matches[0]] = (label, str(helper["name"]))
            used_specs.add(spec_index)

    # A model may choose a different local name. Recover it only when the
    # accepted kind/member contract creates a one-to-one correspondence.
    candidate_specs: dict[int, list[int]] = {}
    spec_candidates: dict[int, list[int]] = {}
    for spec_index, (_label, helper) in enumerate(specs):
        if spec_index in used_specs:
            continue
        expected_kind = str(helper.get("kind") or "")
        members = [str(item) for item in helper.get("required_members") or []]
        if not members:
            continue
        for index in candidates:
            if index in assigned:
                continue
            decl = parsed.decls[index]
            if decl.kind != expected_kind:
                continue
            if not all(
                re.search(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(member)}"
                    rf"(?![A-Za-z0-9_'.])",
                    decl.text,
                )
                for member in members
            ):
                continue
            candidate_specs.setdefault(index, []).append(spec_index)
            spec_candidates.setdefault(spec_index, []).append(index)
    for spec_index, matches in spec_candidates.items():
        if len(matches) != 1:
            continue
        index = matches[0]
        if len(candidate_specs.get(index, [])) != 1:
            continue
        label, helper = specs[spec_index]
        assigned[index] = (label, str(helper["name"]))
    return assigned


def _namespace_owned_helpers(
    ctx: Ctx, labels: Iterable[str], parsed: ParsedModule
) -> ParsedModule:
    """Give model-created helpers stable node-owned global names.

    Candidate modules are compiled independently and later imported together.
    A harmless local name such as ``ceilLog`` therefore becomes a global Lean
    collision when two candidates choose it. Public blueprint declarations keep
    their required names; only non-target declarations are alpha-renamed using
    the blueprint name and owning node. The transformation is deterministic and
    requires no model call.
    """
    label_list = list(labels)
    label_by_name = {_lean_name(label): label for label in label_list}
    planned = _planned_helper_assignments(
        ctx, label_list, parsed, set(label_by_name)
    )
    explicit_raw_owners = {
        parsed.decls[index].name or "": label
        for index, (label, _helper_name) in planned.items()
    }
    for name, label in _semantic_helper_owner_by_name(ctx, label_list).items():
        if any(decl.name == name for decl in parsed.decls):
            explicit_raw_owners.setdefault(name, label)
    consumers = _declaration_target_consumers(
        parsed, label_by_name, explicit_raw_owners
    )
    renames: dict[str, str] = {}
    for index, decl in enumerate(parsed.decls):
        name = decl.name or ""
        planned_assignment = planned.get(index)
        if planned_assignment is not None:
            owner, helper_name = planned_assignment
            canonical_name = _owned_helper_name(ctx, helper_name, [owner])
            if canonical_name != name:
                renames[name] = canonical_name
            continue
        owners = sorted(consumers.get(index) or [])
        if not name or name in label_by_name or not owners:
            continue
        canonical_name = _owned_helper_name(ctx, name, owners)
        if canonical_name != name:
            renames[name] = canonical_name
    plan_aliases = _planned_helper_aliases(ctx)
    if not renames and not planned and not plan_aliases:
        return parsed

    renamed: list[DeclBlock] = []
    applied_plan_aliases: set[str] = set()
    helper_specs = {
        (label, str(helper.get("name") or "")): helper
        for label, helper in _planned_helper_specs(ctx, label_list)
    }
    all_aliases = dict(plan_aliases)
    all_aliases.update(renames)
    for index, decl in enumerate(parsed.decls):
        text = decl.text
        assignment = planned.get(index)
        helper = helper_specs.get(assignment) if assignment is not None else None
        shadowed_members = _planned_member_names(helper) if helper else set()
        declared_name = decl.name or ""
        if declared_name in shadowed_members and declared_name in renames:
            text = _declared_name_replace(
                text, declared_name, renames[declared_name]
            )
        # Replace qualified declaration names before their shorter planned
        # aliases so ``target.Helper`` cannot become ``target._autobp_...``.
        for old, new in sorted(renames.items(), key=lambda item: -len(item[0])):
            if old in shadowed_members:
                continue
            text = _lean_identifier_replace(text, old, new)
        for helper_index, (_owner, helper_name) in planned.items():
            if helper_name in shadowed_members:
                continue
            old_name = parsed.decls[helper_index].name or ""
            canonical_name = renames.get(old_name, old_name)
            if helper_name != old_name:
                text = _lean_identifier_replace(text, helper_name, canonical_name)
        for alias, canonical_name in sorted(
            plan_aliases.items(), key=lambda item: -len(item[0])
        ):
            if alias in shadowed_members:
                continue
            rewritten = _lean_identifier_replace(text, alias, canonical_name)
            if rewritten != text:
                applied_plan_aliases.add(alias)
            text = rewritten
        if helper is not None:
            text = _restore_planned_member_declarations(
                text, helper, all_aliases
            )
        renamed.append(
            DeclBlock(decl.kind, renames.get(decl.name or "", decl.name), text)
        )
    if hasattr(ctx, "telemetry"):
        _record(
            ctx.telemetry,
            "model_helpers_namespaced",
            labels=label_list,
            helper_count=len(renames),
            original_names=sorted(renames),
            planned_helpers=len(planned),
            planned_aliases=sorted(applied_plan_aliases),
        )
    return ParsedModule(parsed.imports, parsed.preamble, renamed)


def _canonicalize_model_lean(
    ctx: Ctx,
    labels: Iterable[str],
    code: str,
    *,
    strict_duplicates: bool = True,
) -> CanonicalModelModule:
    """Convert raw model Lean into the only representation the pipeline stores.

    Imports are retained for later availability checks. The pipeline keeps only
    the small preamble it knows how to render, normalizes theorem-like commands,
    enforces globally unique declaration names, and records helper ownership.
    """
    label_list = list(labels)
    wrapper_count = sum(
        1
        for line in code.splitlines()
        if _MODEL_WRAPPER_START_RE.match(line)
        and not line.strip().startswith("noncomputable")
    )
    source = _remove_model_module_wrappers(code)
    parsed = _parse_module(source)
    theorem_keyword_normalizations = sum(
        1
        for decl in parsed.decls
        if decl.kind == "corollary"
        and decl.name in {_lean_name(label) for label in label_list}
    )
    parsed = _normalize_theorem_like_keywords(parsed, ctx.nodes, label_list)

    invalid_preamble = [
        line
        for line in parsed.preamble
        if line.strip()
        and not line.lstrip().startswith(("--", "/-"))
        and not _ALLOWED_MODEL_PREAMBLE_RE.match(line)
    ]
    if invalid_preamble:
        raise ValueError(
            "model response contains unsupported module-level command(s): "
            + ", ".join(repr(line.strip()) for line in invalid_preamble[:4])
        )
    parsed.preamble = [
        line.strip()
        for line in parsed.preamble
        if _ALLOWED_MODEL_PREAMBLE_RE.match(line)
    ]

    seen: set[str] = set()
    unique: list[DeclBlock] = []
    duplicates: list[str] = []
    for decl in parsed.decls:
        if decl.name and decl.name in seen:
            duplicates.append(decl.name)
            if not strict_duplicates:
                continue
        if decl.name:
            seen.add(decl.name)
        unique.append(decl)
    if duplicates and strict_duplicates:
        raise ValueError(
            "model response repeats declaration name(s): "
            + ", ".join(sorted(set(duplicates)))
        )
    parsed.decls = unique

    parsed = _namespace_owned_helpers(ctx, label_list, parsed)

    label_by_name = {_lean_name(label): label for label in label_list}
    owner_by_index = _declaration_owner_map(
        parsed,
        label_by_name,
        _planned_helper_owner_by_name(ctx, label_list),
    )
    helper_count = sum(
        1
        for decl in parsed.decls
        if decl.name and decl.name not in label_by_name
    )
    if hasattr(ctx, "telemetry"):
        _record(
            ctx.telemetry,
            "model_lean_canonicalized",
            labels=label_list,
            declarations=len(parsed.decls),
            helpers=helper_count,
            wrappers_removed=wrapper_count,
            theorem_keywords_normalized=theorem_keyword_normalizations,
            strict_duplicates=strict_duplicates,
        )
    return CanonicalModelModule(
        parsed=parsed,
        owner_by_index=owner_by_index,
    )


def _realize_typed_contracts_from_candidate(
    ctx: Ctx,
    labels: Iterable[str],
    canonical: CanonicalModelModule,
) -> set[str]:
    """Make the checked Lean candidate its own authoritative typed contract.

    Fresh runs no longer ask the global planner to predict Lean signatures.
    The first Phase-1 response supplies the target and structural-helper
    declarations atomically. Any later compiler/audit patch refreshes the same
    entries from the replacement candidate, so code cannot be forced to obey a
    stale independently generated plan.
    """
    requested = [label for label in labels if label in ctx.nodes]
    if not requested or not getattr(ctx, "semantic_plan_entries", {}):
        return set()
    entries = getattr(ctx, "design_plan_entries", {})
    ctx.design_plan_entries = entries
    target_by_name = {_lean_name(label): label for label in requested}
    owner_by_index = dict(canonical.owner_by_index)
    realized: set[str] = set()
    for label in requested:
        previous = entries.get(label) or {}
        # Preserve a resumed legacy contract. Only contracts created at this
        # atomic boundary follow subsequent candidate revisions.
        if previous and previous.get("origin") != "phase1_candidate":
            continue
        target_name = _lean_name(label)
        target = next(
            (decl for decl in canonical.parsed.decls if decl.name == target_name),
            None,
        )
        if target is None:
            continue
        helpers: list[dict[str, Any]] = []
        for index, decl in enumerate(canonical.parsed.decls):
            if (
                not decl.name
                or decl.name in target_by_name
                or owner_by_index.get(index) != label
                or decl.kind not in DESIGN_PLAN_HELPER_KINDS
            ):
                continue
            declaration = _decl_interface_text(decl)
            members = sorted(_planned_target_members(declaration, decl.name))
            helpers.append(
                {
                    "name": decl.name,
                    "kind": decl.kind,
                    "declaration": declaration,
                    "members": [],
                    "required_members": members,
                    "purpose": "Typed structural interface realized with the Phase-1 candidate.",
                }
            )
        semantic = getattr(ctx, "semantic_plan_entries", {}).get(label) or {}
        decisions = []
        representation = str(semantic.get("representation") or "").strip()
        if representation:
            decisions.append("Representation: " + representation)
        decisions.extend(
            "Preserve: " + str(item).strip()
            for item in semantic.get("obligations") or []
            if str(item).strip()
        )
        progress = {
            key: previous.get(key)
            for key in _PLAN_ENTRY_PROGRESS_KEYS
            if key in previous
        }
        entries[label] = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": ctx.stmt_fps[label],
            "target_signature": _decl_interface_text(target),
            "helpers": helpers,
            "decisions": decisions,
            "origin": "phase1_candidate",
            **progress,
        }
        realized.add(label)
    if realized:
        _sync_design_plan(ctx)
        _record(
            ctx.telemetry,
            "phase1_typed_contract_realized",
            labels=sorted(realized),
            source="same_model_response_as_lean_candidate",
            typed_contract_model_calls=0,
            semantic_plan_authoritative=False,
        )
    return realized


def _ingest_model_lean(
    ctx: Ctx,
    labels: Iterable[str],
    response: str,
    *,
    strict_duplicates: bool = True,
    realize_contracts: bool = False,
) -> CanonicalModelModule:
    """Extract and canonicalize a Lean code block returned by a model."""
    canonical = _canonicalize_model_lean(
        ctx,
        labels,
        _extract_lean_code(response),
        strict_duplicates=strict_duplicates,
    )
    if realize_contracts:
        _realize_typed_contracts_from_candidate(ctx, labels, canonical)
    return canonical


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


def _may_defer_target_body(decl: DeclBlock, expected_kind: str | None) -> bool:
    """Whether Phase 1 may leave this target's implementation for Phase 2."""
    if not expected_kind or not _has_terminal_sorry(decl.text):
        return False
    if _is_theorem_like_kind(expected_kind):
        return decl.kind in {"theorem", "lemma"}
    return decl.kind in {"def", "abbrev"}


def _is_phase1_structural_target_alias(
    decl: DeclBlock,
    expected_kind: str | None,
    parsed: ParsedModule,
    owner_by_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None,
) -> bool:
    """Whether a completed target body is only a transparent type interface.

    Phase 1 normally defers every target ``def`` body. A type-valued blueprint
    definition is different when its mathematical contract is a plan-owned
    structure/class/inductive: ``def target : Type := OwnedInterface`` merely
    gives that complete interface its canonical blueprint name. It contains no
    executable implementation for Phase 2 to fill.

    Keep this exception deliberately narrow. The right-hand side must be a
    direct application of one structural helper owned by the same blueprint
    node; arbitrary completed definitions remain forbidden.
    """
    if (
        not expected_kind
        or _is_theorem_like_kind(expected_kind)
        or decl.kind not in {"def", "abbrev"}
        or _has_terminal_sorry(decl.text)
        or ":=" not in decl.text
    ):
        return False
    result_type = _planned_target_result_type(decl.text, decl.name or "")
    if not re.match(r"^(?:Type(?:\s+[A-Za-z0-9_'.]+)?|Sort\s+\S+)$", result_type):
        return False

    owner = owner_by_name.get(decl.name or "")
    if not owner:
        return False
    helper_kinds = {
        helper.name: helper.kind
        for helper in parsed.decls
        if helper.name and helper.kind in {"structure", "class", "inductive"}
    }
    owned_helpers = [
        name
        for name, helper_owner in (explicit_owner_by_name or {}).items()
        if helper_owner == owner and name in helper_kinds
    ]
    rhs = decl.text.split(":=", 1)[1].strip()
    for helper in owned_helpers:
        simple_application = re.fullmatch(
            rf"@?{re.escape(helper)}"
            r"(?:\s+(?:[A-Za-z_][A-Za-z0-9_'.]*|\([^()\n]*\)|\{[^{}\n]*\}))*",
            rhs,
        )
        if simple_application:
            return True
    return False


def _splice_proof(decl_text: str, proof: str) -> str:
    """Replace a terminal ``:= sorry`` with a tactic body; header untouched."""
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
    owner_labels: list[str],
    ranges: list[tuple[int, int]],
    output: str,
    file_name: str,
    explicit_owner_by_name: dict[str, str] | None = None,
) -> list[SkeletonFinding]:
    """Turn Lean diagnostics into declaration-targeted skeleton findings."""
    by_decl, file_level = _errors_by_decl(output, file_name, ranges)
    label_by_name = {_lean_name(label): label for label in owner_labels}
    owner_by_index = _declaration_owner_map(
        parsed, label_by_name, explicit_owner_by_name
    )
    findings: list[SkeletonFinding] = []
    for index, messages in sorted(by_decl.items()):
        decl = parsed.decls[index] if index < len(parsed.decls) else None
        lean_name = decl.name if decl is not None else None
        label = owner_by_index.get(index)
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
    code: str,
    target_kinds: dict[str, str],
    label_by_lean_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> list[SkeletonFinding]:
    """Correctness audit variant for the skeleton phase.

    Like ``_audit_lean_code`` but ``sorry`` is legal exactly as a target's
    terminal deferred body: theorem proofs and typed ``def``/``abbrev`` bodies
    are implemented in Phase 2. Helpers, structures, preamble, and interior
    declaration positions must remain sorry-free.
    """
    findings: list[SkeletonFinding] = []

    parsed = _parse_module(code)
    owner_by_index = _declaration_owner_map(
        parsed, label_by_lean_name, explicit_owner_by_name
    )
    owner_by_name = {
        decl.name: owner_by_index[index]
        for index, decl in enumerate(parsed.decls)
        if decl.name and index in owner_by_index
    }
    target_names = set(target_kinds)
    planned_helper_names = set((explicit_owner_by_name or {}).keys())

    def decl_finding(
        name: str | None, message: str, *, category: str = ""
    ) -> SkeletonFinding:
        return SkeletonFinding(
            message=message,
            label=owner_by_name.get(name or ""),
            lean_name=name,
            category=category,
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
            if stripped and not stripped.startswith(
                ("open", "/-", "noncomputable section")
            ):
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
        expected_kind = target_kinds.get(decl.name or "")
        name = decl.name or ""
        if (
            name
            and name not in target_names
            and name not in planned_helper_names
        ):
            findings.append(
                decl_finding(
                    name,
                    f"Phase 1 emitted unplanned helper `{name}`. The outline may "
                    "contain only blueprint targets and exact plan-owned "
                    "structure/inductive/class interfaces; executable helper "
                    "definitions and theorems belong in Phase 2 or require a "
                    "blueprint contract change",
                    category="unplanned_phase1_helper",
                )
            )
        if (
            expected_kind
            and not _is_theorem_like_kind(expected_kind)
            and decl.kind in {"def", "abbrev"}
            and not _has_terminal_sorry(decl.text)
            and not _is_phase1_structural_target_alias(
                decl,
                expected_kind,
                parsed,
                owner_by_name,
                explicit_owner_by_name,
            )
        ):
            findings.append(
                decl_finding(
                    decl.name,
                    f"Phase 1 target `{decl.name}` must expose only its exact typed "
                    "interface and end in `:= sorry`; its implementation belongs in Phase 2",
                )
            )
        if "sorry" not in decl.text:
            continue
        if _may_defer_target_body(decl, expected_kind):
            inner = _TERMINAL_SORRY_RE.sub("", decl.text)
            if re.search(r"\bsorry\b", inner):
                findings.append(
                    decl_finding(decl.name, f"`{decl.name}` uses sorry outside the terminal proof position")
                )
            continue
        findings.append(
            decl_finding(
                decl.name,
                f"`{decl.name or decl.kind}` contains sorry outside an allowed "
                "terminal target body; helpers and structure declarations must be complete",
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


def _runner_failure_status(exc: Exception) -> str:
    """Classify backend failure without letting infrastructure become math evidence."""
    if _is_timeout_error(exc):
        return "timeout"
    if is_transient_error(exc):
        return "transport_exhausted"
    return "error"


@dataclass(frozen=True)
class FailureScopeDecision:
    """Provider-neutral retry scope for a Lean-generation failure.

    Classification remains the caller's responsibility: blueprint repair and
    confirmed decomposition never enter this policy. This object only prevents
    Phase 1 and Phase 2 from making different decisions about the size of the
    next Lean-generation unit.
    """

    action: str  # isolate | bisect | singleton | independent
    parts: tuple[tuple[str, ...], ...]
    failed_labels: tuple[str, ...]
    accepted_labels: tuple[str, ...]


def _route_lean_generation_failure(
    labels: Iterable[str], attributable_labels: Iterable[str] | None = None
) -> FailureScopeDecision:
    """Choose the next retry scope without interpreting mathematical evidence.

    A known proper subset is isolated while its siblings remain eligible for
    independent validation. Any unresolved multi-label unit is bisected. Only
    a singleton may proceed to the caller's existing escalation policy.
    """
    ordered = list(dict.fromkeys(labels))
    if not ordered:
        raise ValueError("cannot route an empty Lean-generation failure")
    label_set = set(ordered)
    attributable = (
        {label for label in attributable_labels or [] if label in label_set}
        if attributable_labels is not None
        else set()
    )
    if attributable and attributable < label_set:
        failed = tuple(label for label in ordered if label in attributable)
        accepted = tuple(label for label in ordered if label not in attributable)
        return FailureScopeDecision(
            action="isolate",
            parts=tuple(tuple(part) for part in _parts_around_labels(ordered, list(failed))),
            failed_labels=failed,
            accepted_labels=accepted,
        )
    if len(ordered) > 1:
        mid = len(ordered) // 2
        return FailureScopeDecision(
            action="bisect",
            parts=(tuple(ordered[:mid]), tuple(ordered[mid:])),
            failed_labels=tuple(ordered),
            accepted_labels=(),
        )
    return FailureScopeDecision(
        action="singleton",
        parts=(tuple(ordered),),
        failed_labels=tuple(ordered),
        accepted_labels=(),
    )


def _combine_failure_routes(
    routes: Iterable[FailureScopeDecision],
) -> FailureScopeDecision:
    """Represent independent failure scopes without losing their own parts.

    ``failure_route`` predates parallel Phase-1 transactions and can describe
    only one scope.  The combined value remains useful to old callers and log
    consumers, while ``RepairRequest.failure_routes`` retains each original
    decision so the orchestrator can apply isolate/bisect policy separately.
    """
    ordered_routes = list(routes)
    if not ordered_routes:
        raise ValueError("cannot combine an empty set of failure routes")
    if len(ordered_routes) == 1:
        return ordered_routes[0]

    parts: list[tuple[str, ...]] = []
    failed: list[str] = []
    accepted: list[str] = []
    for route in ordered_routes:
        parts.extend(route.parts)
        failed.extend(route.failed_labels)
        accepted.extend(route.accepted_labels)
    return FailureScopeDecision(
        action="independent",
        parts=tuple(dict.fromkeys(parts)),
        failed_labels=tuple(dict.fromkeys(failed)),
        accepted_labels=tuple(dict.fromkeys(accepted)),
    )


class RepairRequest(Exception):
    """Return bounded failure evidence to the main orchestration loop.

    Phase 1/2 requests may authorize blueprint repair. Initial-declaration
    requests are intercepted as provisional regeneration only.
    """

    def __init__(
        self,
        evidence: str,
        labels: list[str],
        *,
        decomposition_helpers: list[str] | None = None,
        section_labels: list[str] | None = None,
        context_labels: list[str] | None = None,
        frozen_sections: list["Section"] | None = None,
        authorizes_blueprint_repair: bool = True,
        failure_route: FailureScopeDecision | None = None,
        failure_routes: Iterable[FailureScopeDecision] | None = None,
        plan_revision_required: bool = False,
        required_dependencies: dict[str, set[str]] | None = None,
        model_repair_labels: Iterable[str] | None = None,
    ):
        super().__init__(evidence[:500])
        self.evidence = evidence
        self.labels = labels
        self.decomposition_helpers = decomposition_helpers or []
        self.section_labels = section_labels or list(labels)
        self.context_labels = context_labels or list(self.section_labels)
        # Recursive section routing may freeze an easy prefix before a later
        # singleton proves that the blueprint needs repair. Preserve that work
        # across the exception instead of regenerating it after the repair.
        self.frozen_sections = frozen_sections or []
        self.authorizes_blueprint_repair = authorizes_blueprint_repair
        routes = list(failure_routes or [])
        if not routes and failure_route is not None:
            routes.append(failure_route)
        self.failure_routes = routes
        if failure_route is not None:
            self.failure_route = failure_route
        elif routes:
            self.failure_route = _combine_failure_routes(routes)
        else:
            self.failure_route = None
        self.plan_revision_required = plan_revision_required
        self.required_dependencies = {
            label: set(dependencies)
            for label, dependencies in (required_dependencies or {}).items()
            if dependencies
        }
        # Some authorized requests can be completed deterministically by adding
        # missing dependency edges; others require the repair model to change or
        # decompose blueprint contracts. Keep those scopes separate so combining
        # concurrent failures cannot silently replace one action with the other.
        if model_repair_labels is None:
            self.model_repair_labels = (
                list(labels)
                if authorizes_blueprint_repair and not self.required_dependencies
                else []
            )
        else:
            self.model_repair_labels = list(dict.fromkeys(model_repair_labels))


def _requires_blueprint_transaction(
    authorizes_blueprint_repair: bool,
    required_dependencies: dict[str, set[str]],
) -> bool:
    """Return whether the outer loop must enter its transactional edit path.

    A semantic critic can classify the remaining declaration problem as Lean
    generation while independently identifying an existing blueprint label
    required by the public statement.  That dependency evidence authorizes
    only the deterministic, cycle-checked ``\\uses`` edge transaction; it does
    not authorize a model rewrite of the blueprint.  Delaying the edge until
    the Lean-generation retry lifecycle is exhausted makes every intervening
    candidate operate against a graph already known to be incomplete.
    """
    return authorizes_blueprint_repair or bool(required_dependencies)


def _aggregate_retry_requests(
    requests: Iterable[RepairRequest],
    *,
    frozen_sections: Iterable["Section"] = (),
) -> RepairRequest:
    """Merge independent non-blueprint failures from one parallel transaction.

    Every candidate has already persisted its own code and evidence.  Returning
    one arbitrary exception would hide the remaining failures until later outer
    iterations.  This aggregate preserves every retry scope and all accepted
    sibling sections while still consuming one outer repair trial.
    """
    ordered = list(requests)
    if not ordered:
        raise ValueError("cannot aggregate an empty set of repair requests")
    if any(request.authorizes_blueprint_repair for request in ordered):
        raise ValueError("blueprint-authorized requests must be handled separately")

    routes = [
        route
        for request in ordered
        for route in (
            request.failure_routes
            or ([request.failure_route] if request.failure_route is not None else [])
        )
    ]
    labels = list(
        dict.fromkeys(label for request in ordered for label in request.labels)
    )
    section_labels = list(
        dict.fromkeys(
            label for request in ordered for label in request.section_labels
        )
    )
    context_labels = list(
        dict.fromkeys(
            label for request in ordered for label in request.context_labels
        )
    )
    sections_by_key: dict[tuple[int, str], Section] = {}
    for section in [
        *frozen_sections,
        *(section for request in ordered for section in request.frozen_sections),
    ]:
        sections_by_key[(section.number, str(section.path))] = section
    dependencies: dict[str, set[str]] = {}
    for request in ordered:
        for label, required in request.required_dependencies.items():
            dependencies.setdefault(label, set()).update(required)
    evidence = "\n\n".join(
        f"== Independent failure {index} ==\n{request.evidence}"
        for index, request in enumerate(ordered, 1)
    )
    combined_route = _combine_failure_routes(routes) if routes else None
    return RepairRequest(
        evidence,
        labels,
        section_labels=section_labels or labels,
        context_labels=context_labels or section_labels or labels,
        frozen_sections=list(sections_by_key.values()),
        authorizes_blueprint_repair=False,
        failure_route=combined_route,
        failure_routes=routes,
        plan_revision_required=any(
            request.plan_revision_required for request in ordered
        ),
        required_dependencies=dependencies,
    )


def _aggregate_authorized_repair_requests(
    requests: Iterable[RepairRequest],
    *,
    frozen_sections: Iterable["Section"] = (),
) -> RepairRequest:
    """Merge every independently authorized repair from one parallel frontier.

    Parallel generation can surface dependency-edge, blueprint, and
    decomposition failures together. The outer loop performs one transaction,
    but it must retain every authorized action instead of selecting whichever
    exception happened to be first in a list.
    """
    ordered = list(requests)
    if not ordered:
        raise ValueError("cannot aggregate an empty set of repair requests")
    if any(not request.authorizes_blueprint_repair for request in ordered):
        raise ValueError("only blueprint-authorized requests can be aggregated")

    labels = list(
        dict.fromkeys(label for request in ordered for label in request.labels)
    )
    model_labels = list(
        dict.fromkeys(
            label
            for request in ordered
            for label in request.model_repair_labels
        )
    )
    helpers = list(
        dict.fromkeys(
            helper
            for request in ordered
            for helper in request.decomposition_helpers
        )
    )
    dependencies: dict[str, set[str]] = {}
    for request in ordered:
        for label, required in request.required_dependencies.items():
            dependencies.setdefault(label, set()).update(required)
    sections_by_key: dict[tuple[int, str], Section] = {}
    for section in [
        *frozen_sections,
        *(section for request in ordered for section in request.frozen_sections),
    ]:
        sections_by_key[(section.number, str(section.path))] = section
    section_labels = list(
        dict.fromkeys(
            label for request in ordered for label in request.section_labels
        )
    )
    context_labels = list(
        dict.fromkeys(
            label for request in ordered for label in request.context_labels
        )
    )
    evidence = "\n\n".join(
        f"== Authorized repair {index} ==\n{request.evidence}"
        for index, request in enumerate(ordered, 1)
    )
    return RepairRequest(
        evidence,
        labels,
        decomposition_helpers=helpers,
        section_labels=section_labels or labels,
        context_labels=context_labels or section_labels or labels,
        frozen_sections=list(sections_by_key.values()),
        authorizes_blueprint_repair=True,
        required_dependencies=dependencies,
        model_repair_labels=model_labels,
    )


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
    blueprint_dir: Path
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
    workers: int
    use_ladder: bool
    refinement_order: str = PHASE1_STATEMENT_ORDER
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
    # A bisection is evidence about one exact failed group, not about the
    # capacity of every unrelated frontier in the run. Persist the resulting
    # local parts by statement fingerprint so only that group is subdivided on
    # retry; accepted or edited statements release the constraint.
    local_group_partitions: dict[str, dict[str, Any]] = field(default_factory=dict)
    # Generation/audit evidence that must survive an outer Phase-1 retry. Each
    # entry is valid only for the exact blueprint statement fingerprint that
    # produced it, so a blueprint repair cannot leak stale criticism into the
    # replacement contract.
    generation_feedback: dict[str, dict[str, str]] = field(default_factory=dict)
    # Rejected Phase-1 declarations are retained as revision inputs instead of
    # being regenerated from an empty file. Entries are statement-fingerprinted
    # for the same reason as feedback: a blueprint edit must invalidate the old
    # Lean candidate automatically.
    generation_candidates: dict[str, dict[str, Any]] = field(default_factory=dict)
    # Per-node retry provenance survives batching, outer-loop retries, and
    # continuation.  An audit may judge many declarations in one call, but it
    # must not collapse independently generated singleton histories back into
    # one fresh base-tier batch.
    retry_lifecycle: dict[str, dict[str, Any]] = field(default_factory=dict)
    nodes: dict[str, Node] = field(default_factory=dict)
    stmt_blocks: dict[str, str] = field(default_factory=dict)
    tex_blocks: dict[str, str] = field(default_factory=dict)
    stmt_fps: dict[str, str] = field(default_factory=dict)
    contract_fps: dict[str, str] = field(default_factory=dict)
    unavailable_imports: set[str] = field(default_factory=set)
    # Raw library candidates behind ``library_context``; prompts slice these
    # per target node instead of repeating the full global blob.
    library_candidates: list = field(default_factory=list)
    # Canonical text rendering of the structured root-first interface plan.
    # The structured per-node entries below are the source of truth; this text
    # exists only for compatibility with prompt helpers that expect a string.
    design_plan: str = ""
    # Versioned per-node contracts. Each preserves the target signature, the
    # compact required surface of every owned helper, and generation decisions.
    # Entries are statement-fingerprinted so repairs invalidate only changed
    # contracts while unchanged planning work remains reusable.
    design_plan_entries: dict[str, dict[str, Any]] = field(default_factory=dict)
    # Lightweight, graph-wide semantic guidance produced before Phase 1. This
    # deliberately contains no Lean signatures or typed helper declarations:
    # the exact typed contract is realized atomically from the Phase-1 Lean
    # candidate and stored in ``design_plan_entries``. Keeping the two stores
    # separate prevents an advisory model plan from becoming mathematical
    # authority or forcing Phase 1 to translate the same interface twice.
    semantic_plan_entries: dict[str, dict[str, Any]] = field(default_factory=dict)
    # The non-selected full-plan candidate is retained as a bounded, zero-call
    # fallback. A rejected selected component may try the alternate contract
    # once before asking a model to correct the plan.
    design_plan_alternates: dict[str, dict[str, Any]] = field(default_factory=dict)
    # A global plan is an optimization, never mathematical authority. If a
    # contract is shown to be unusable, generation falls back to the blueprint
    # plus exact failure evidence for this statement fingerprint. Keeping this
    # separate from the plan prevents a bad model response from trapping Phase
    # 1 in repeated plan-correction cycles.
    blueprint_direct_generation: dict[str, dict[str, Any]] = field(
        default_factory=dict
    )
    # Exact per-node statement/Lean pairs already accepted by the independent
    # statement critic during this run. Phase-1 routing may regroup unchanged
    # declarations after isolating a failing sibling; those declarations must
    # not pay for the same semantic judgment again.
    statement_audit_cache: set[str] = field(default_factory=set)
    # Bottom-up Phase 1 compiles independent groups concurrently, then audits
    # the assembled dependency layer once. While this flag is set, section
    # workers produce candidates rather than accepted/frozen contracts.
    defer_phase1_alignment: bool = False
    # Exact deterministic rejection evidence from the most recent narrow
    # graph edit. These diagnostics are fed into the bounded model repair
    # instead of being reduced to a generic validation failure.
    last_dependency_edge_rejections: dict[str, dict[str, str]] = field(
        default_factory=dict
    )
    last_blueprint_repair_rejection: str = ""
    # A model-mutated blueprint component must be checked before Phase 1 spends
    # generation/compilation calls on it. This record is persisted so killing
    # the process between mutation and audit cannot bypass the boundary.
    repair_boundary_pending: dict[str, Any] = field(default_factory=dict)

    @property
    def blueprint_src_dir(self) -> Path:
        return self.blueprint_dir / "blueprint" / "src"

    @property
    def content_path(self) -> Path:
        return self.blueprint_src_dir / "content.tex"

    def refresh_nodes(self, nodes: dict[str, Node]) -> None:
        self.nodes = nodes
        self.stmt_blocks = _statement_blocks(nodes)
        self.tex_blocks = _node_tex_blocks(nodes)
        self.stmt_fps = _statement_fingerprints(nodes)
        self.contract_fps = _contract_fingerprints(nodes)
        _prune_stale_quarantine(self)
        _prune_stale_local_group_partitions(self)
        _prune_stale_generation_feedback(self)
        _prune_stale_generation_candidates(self)
        _prune_stale_retry_lifecycle(self)
        _prune_stale_design_plan(self)


def _canonical_blueprint_dir(name: str) -> Path:
    return REPO_ROOT / "blueprints" / name


def _draft_blueprint_dir(name: str) -> Path:
    return SCRATCH_DIR / name / "blueprint-draft"


def _prepare_blueprint_draft(name: str, *, continue_run: bool) -> Path:
    """Create or resume the unpublished blueprint working tree."""
    canonical = _canonical_blueprint_dir(name)
    if not canonical.is_dir():
        raise FileNotFoundError(f"blueprints/{name} does not exist")
    draft = _draft_blueprint_dir(name)
    if continue_run and (draft / "blueprint" / "src" / "content.tex").is_file():
        _log(f"==> Continuing from unpublished blueprint draft: {draft.relative_to(REPO_ROOT)}")
        return draft
    if draft.exists():
        shutil.rmtree(draft)
    draft.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(canonical, draft)
    _log(f"==> Created unpublished blueprint draft: {draft.relative_to(REPO_ROOT)}")
    return draft


def _validate_draft(ctx: Ctx):
    return validate_blueprint(REPO_ROOT, ctx.name, blueprint_dir=ctx.blueprint_dir)


def _read_blueprint_source_at(name: str, blueprint_dir: Path) -> str:
    content = blueprint_dir / "blueprint" / "src" / "content.tex"
    parts = [
        f"% FILE: {content.relative_to(REPO_ROOT)}\n"
        + content.read_text(encoding="utf-8")
    ]
    common = blueprint_dir / "blueprint" / "src" / "macros" / "common.tex"
    if common.is_file():
        parts.append(
            f"% FILE: {common.relative_to(REPO_ROOT)}\n"
            + common.read_text(encoding="utf-8")
        )
    return "\n\n".join(parts)


def _read_draft_blueprint_source(ctx: Ctx) -> str:
    return _read_blueprint_source_at(ctx.name, ctx.blueprint_dir)


def _write_api_refinement_to(path: Path, text: str) -> None:
    payload = _extract_json(text)
    content_tex = str(payload.get("content_tex") or "").strip()
    if not content_tex:
        raise ValueError("refinement JSON did not include non-empty content_tex")
    if r"\begin{document}" in content_tex or r"\end{document}" in content_tex:
        raise ValueError("content_tex must not include a document environment")
    path.write_text(content_tex.rstrip() + "\n", encoding="utf-8")
    notes = str(payload.get("notes") or "").strip()
    if notes:
        print(f"  refinement notes: {notes}")


def _promote_blueprint_draft(ctx: Ctx) -> Path:
    """Atomically publish the successful draft content into the blueprint."""
    destination = _canonical_blueprint_dir(ctx.name) / "blueprint" / "src" / "content.tex"
    replacement = destination.with_name(".content.tex.auto-blueprint-promote")
    replacement.write_bytes(ctx.content_path.read_bytes())
    os.replace(replacement, destination)
    _record(
        ctx.telemetry,
        "blueprint_draft_promoted",
        draft=str(ctx.content_path.relative_to(REPO_ROOT)),
        destination=str(destination.relative_to(REPO_ROOT)),
    )
    return destination


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


def _release_local_group_partitions(
    ctx: Ctx, labels: Iterable[str], *, reason: str = "statement_frozen"
) -> None:
    """Release local bisection records involving any accepted/changed label."""
    partitions = getattr(ctx, "local_group_partitions", {})
    touched = set(labels)
    partition_ids = {
        str(entry.get("partition_id") or "")
        for label, entry in partitions.items()
        if label in touched or touched.intersection(entry.get("group") or [])
    }
    removed = {
        label: dict(entry)
        for label, entry in partitions.items()
        if str(entry.get("partition_id") or "") in partition_ids
    }
    for label in removed:
        partitions.pop(label, None)
    if removed and getattr(ctx, "telemetry", None) is not None:
        _record(
            ctx.telemetry,
            "phase1_local_partition_released",
            labels=sorted(removed),
            reason=reason,
        )


def _prune_stale_local_group_partitions(ctx: Ctx) -> set[str]:
    """Drop local bisections once any participating statement has changed."""
    partitions = getattr(ctx, "local_group_partitions", {})
    stale: set[str] = set()
    for label, entry in partitions.items():
        group_fps = entry.get("statement_fps") or {}
        if (
            label not in ctx.nodes
            or entry.get("statement_fp") != ctx.stmt_fps.get(label)
            or any(ctx.stmt_fps.get(item) != fp for item, fp in group_fps.items())
        ):
            stale.add(label)
    if stale:
        _release_local_group_partitions(
            ctx, stale, reason="statement_fingerprint_changed"
        )
    return stale


def _store_local_bisection(ctx: Ctx, route: FailureScopeDecision) -> None:
    """Persist one failure route without reducing unrelated batch capacity."""
    partitions = getattr(ctx, "local_group_partitions", None)
    if partitions is None:
        partitions = {}
        ctx.local_group_partitions = partitions
    _release_local_group_partitions(
        ctx, route.failed_labels, reason="local_bisection_replaced"
    )
    stored_parts: list[list[str]] = []
    for part_index, raw_part in enumerate(route.parts):
        part = [label for label in raw_part if label in ctx.stmt_fps]
        if not part:
            continue
        group_fps = {label: ctx.stmt_fps[label] for label in part}
        partition_id = hashlib.sha256(
            json.dumps(group_fps, sort_keys=True).encode("utf-8")
        ).hexdigest()
        for label in part:
            partitions[label] = {
                "partition_id": f"{partition_id}:{part_index}",
                "statement_fp": ctx.stmt_fps[label],
                "statement_fps": group_fps,
                "group": list(part),
            }
        stored_parts.append(part)
    if stored_parts:
        _record(
            ctx.telemetry,
            "phase1_local_bisection_stored",
            labels=list(route.failed_labels),
            parts=stored_parts,
            global_section_size=ctx.effective_section_size or ctx.section_size,
        )


def _apply_phase1_retry_scheduling(ctx: Ctx, request: RepairRequest) -> None:
    """Apply generation evidence to scheduling without conflating plan shape.

    Adaptive capacity and quarantine describe emitted statement-generation
    behavior. A pre-generation contract-plan closure failure has emitted no
    statements, so it must leave both controls unchanged; its corrected or
    invalidated plan entry already supplies the next retry's state transition.
    """
    if request.plan_revision_required:
        _record(
            ctx.telemetry,
            "phase1_plan_revision_retry_scheduled",
            labels=request.labels,
            scheduler_size=ctx.effective_section_size or ctx.section_size,
            scheduler_unchanged=True,
        )
        return
    if request.failure_route is None:
        _quarantine_labels(ctx, request.labels, "phase1_generation_retry")
        return

    routes = request.failure_routes or [request.failure_route]
    for route in routes:
        if route.action in {"isolate", "singleton", "independent"}:
            _quarantine_labels(
                ctx,
                route.failed_labels,
                "phase1_generation_retry",
            )
        elif route.action == "bisect":
            _store_local_bisection(ctx, route)
    _record(
        ctx.telemetry,
        "phase1_failure_routes_applied",
        route_count=len(routes),
        actions=[route.action for route in routes],
        failing_groups=[list(route.failed_labels) for route in routes],
    )


def _prune_stale_generation_feedback(ctx: Ctx) -> set[str]:
    """Drop retry evidence that no longer describes the current statement."""
    with _STATE_LOCK:
        feedback = getattr(ctx, "generation_feedback", {})
        stale = {
            label
            for label, entry in feedback.items()
            if label not in ctx.nodes
            or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        }
        for label in stale:
            feedback.pop(label, None)
    return stale


def _store_generation_feedback(
    ctx: Ctx, labels: Iterable[str], evidence: str, *, source: str
) -> None:
    """Persist cumulative correction evidence for the current statement epoch.

    A later failure must not erase the finding that motivated the candidate we
    retained.  Keep a compact, deduplicated history so the next correction sees
    both the best candidate and every still-relevant reason it was rejected.
    """
    evidence = evidence.strip()[-12000:]
    if not evidence:
        return
    stored: list[str] = []
    statement_fps: dict[str, str] = {}
    with _STATE_LOCK:
        feedback = getattr(ctx, "generation_feedback", None)
        if feedback is None:
            feedback = {}
            ctx.generation_feedback = feedback
        for label in labels:
            statement_fp = ctx.stmt_fps.get(label, "")
            if not statement_fp:
                continue
            previous = feedback.get(label) or {}
            previous_evidence = (
                str(previous.get("evidence") or "").strip()
                if previous.get("statement_fp") == statement_fp
                else ""
            )
            if previous_evidence and evidence not in previous_evidence:
                evidence_for_label = (
                    previous_evidence
                    + f"\n\nLater evidence ({source}):\n"
                    + evidence
                )[-12000:]
            else:
                evidence_for_label = previous_evidence or evidence
            feedback[label] = {
                "statement_fp": statement_fp,
                "evidence": evidence_for_label,
                "source": source,
            }
            stored.append(label)
            statement_fps[label] = statement_fp
    if stored:
        _record(
            ctx.telemetry,
            "phase1_retry_feedback_saved",
            labels=stored,
            source=source,
            evidence_chars=len(evidence),
            statement_fps=statement_fps,
        )


def _generation_feedback_for(ctx: Ctx, labels: Iterable[str]) -> str:
    """Return deduplicated current-version evidence for a generation prompt."""
    label_list = list(labels)
    with _STATE_LOCK:
        _prune_stale_generation_feedback(ctx)
        feedback = copy.deepcopy(getattr(ctx, "generation_feedback", {}))
    grouped: dict[str, list[str]] = {}
    for label in label_list:
        entry = feedback.get(label)
        if not entry:
            continue
        evidence = str(entry.get("evidence") or "").strip()
        if evidence:
            grouped.setdefault(evidence, []).append(label)
    if not grouped:
        return ""
    text = "\n\n".join(
        "Persisted rejection evidence for " + ", ".join(group_labels) + ":\n" + evidence
        for evidence, group_labels in grouped.items()
    )
    _record(
        ctx.telemetry,
        "phase1_retry_feedback_injected",
        labels=[label for group_labels in grouped.values() for label in group_labels],
        evidence_chars=len(text),
    )
    return text


def _clear_generation_feedback(ctx: Ctx, labels: Iterable[str]) -> None:
    """Forget correction evidence only after those statements are accepted."""
    with _STATE_LOCK:
        feedback = getattr(ctx, "generation_feedback", {})
        for label in labels:
            feedback.pop(label, None)


def _prune_stale_generation_candidates(ctx: Ctx) -> set[str]:
    """Drop candidate Lean that no longer matches its statement or plan."""
    with _STATE_LOCK:
        candidates = getattr(ctx, "generation_candidates", {})
        stale = {
            label
            for label, entry in candidates.items()
            if label not in ctx.nodes
            or entry.get("statement_fp") != ctx.stmt_fps.get(label)
            or str(entry.get("plan_fp") or "")
            != _candidate_plan_fingerprint(ctx, label)
        }
        for label in stale:
            candidates.pop(label, None)
    telemetry = getattr(ctx, "telemetry", None)
    if stale and telemetry is not None:
        _record(
            telemetry,
            "phase1_retry_candidate_invalidated",
            labels=sorted(stale),
            reason="statement_fingerprint_changed",
        )
    return stale


def _candidate_plan_fingerprint(ctx: Ctx, label: str) -> str:
    """Fingerprint the exact untrusted plan contract used for generation."""
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label)
    direct = (getattr(ctx, "blueprint_direct_generation", {}) or {}).get(label)
    if isinstance(direct, dict) and str(direct.get("statement_fp") or "") == (
        ctx.stmt_fps.get(label) or ""
    ):
        return hashlib.sha256(
            json.dumps(
                {
                    "mode": "blueprint_direct",
                    "statement_fp": str(direct.get("statement_fp") or ""),
                    "evidence": str(direct.get("evidence") or ""),
                },
                sort_keys=True,
            ).encode("utf-8")
        ).hexdigest()
    if not isinstance(entry, dict):
        return ""
    material = {
        "schema_version": int(entry.get("schema_version") or 0),
        "target_signature": str(entry.get("target_signature") or ""),
        "helpers": entry.get("helpers") or [],
        "decisions": entry.get("decisions") or [],
    }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _candidate_is_reusable_uncompiled(entry: dict[str, Any]) -> bool:
    """Recognize candidates that completed every deterministic generation gate.

    Older state wrote valid siblings from an incomplete layer transaction with
    the reuse bit unset. Their source is unambiguous: the failing future never
    enters the sibling list stored by the transaction.

    Deterministic validity permits the first compilation attempt; it does not
    permit zero-call reuse after Lean has rejected that exact candidate. The
    failed code remains stored as revision context for the next model call.
    """
    if str(entry.get("lean_status") or "unknown") == "failed":
        return False
    if bool(entry.get("reusable_uncompiled")):
        return True
    return bool(
        re.fullmatch(
            r"phase1_layer_\d+_incomplete_generation",
            str(entry.get("source") or ""),
        )
    )


def _candidate_hash(code: str) -> str:
    return hashlib.sha256(code.strip().encode("utf-8")).hexdigest()


def _finding_obligation_ids(finding: SkeletonFinding) -> set[str]:
    """Map a human-readable deterministic finding to stable obligation IDs.

    Existing deterministic audits remain the source of truth.  This adapter
    only gives their findings stable identities so two candidate revisions can
    be compared without relying on a paper-specific score or model judgment.
    """
    label = finding.label or "file"
    message = " ".join(finding.message.split())
    lower = message.lower()
    symbols = re.findall(r"`([^`]+)`", message)
    category = finding.category or ""

    if finding.dependencies:
        family = category or (
            "outside_dependency_closure"
            if "outside" in lower
            else "required_dependency"
        )
        return {
            f"{label}:{family}:{dependency}"
            for dependency in finding.dependencies
        }
    if "missing generated declaration" in lower:
        return {f"{label}:target_present:{finding.lean_name or label}"}
    if "is a definition but generated" in lower or (
        "is theorem-like but generated" in lower
    ):
        return {f"{label}:target_kind:{finding.lean_name or label}"}
    if "omitted helper" in lower:
        helper = symbols[0] if symbols else (finding.lean_name or "unknown")
        return {f"{label}:helper_present:{helper}"}
    if "helper" in lower and "must be a" in lower:
        helper = symbols[0] if symbols else (finding.lean_name or "unknown")
        return {f"{label}:helper_kind:{helper}"}
    if "omits required member" in lower:
        helper = symbols[0] if symbols else (finding.lean_name or "unknown")
        members = symbols[1:] or ["unknown"]
        return {f"{label}:helper_member:{helper}:{member}" for member in members}
    if "does not mention required dependency" in lower:
        return {
            f"{label}:required_dependency:{symbol}"
            for symbol in (symbols or ["unknown"])
        }
    if "cycle" in lower:
        return {
            f"{label}:declaration_cycle:{symbol}"
            for symbol in (symbols or [finding.lean_name or "unknown"])
        }

    family = category or re.sub(r"[^a-z0-9]+", "_", lower).strip("_")[:120]
    if symbols:
        return {f"{label}:{family}:{symbol}" for symbol in symbols}
    return {f"{label}:{family or 'deterministic_finding'}"}


def _candidate_obligation_universe(ctx: Ctx, labels: Iterable[str]) -> set[str]:
    """Return the provider-neutral deterministic contract surface for labels."""
    obligations = {
        "file:no_forbidden_placeholder",
        "file:no_top_level_assumption",
        "file:no_invented_blueprint_stub",
        "file:canonical_module_structure",
        "file:no_unplanned_declaration",
        "file:no_declaration_cycle",
        "file:phase1_body_policy",
    }
    plan_entries = getattr(ctx, "design_plan_entries", {}) or {}
    nodes = getattr(ctx, "nodes", {}) or {}
    for label in labels:
        node = nodes.get(label)
        if node is None:
            continue
        target = _lean_name(label)
        obligations.update(
            {
                f"{label}:target_present:{target}",
                f"{label}:target_kind:{target}",
            }
        )
        for dependency in sorted(_statement_uses(node)):
            dependency_node = nodes.get(dependency)
            if dependency_node is not None and not dependency_node.mathlibok:
                obligations.add(
                    f"{label}:required_dependency:{_lean_name(dependency)}"
                )
        for helper in (plan_entries.get(label) or {}).get("helpers") or []:
            helper_name = str(helper.get("name") or "").strip()
            if not helper_name:
                continue
            obligations.add(f"{label}:helper_present:{helper_name}")
            obligations.add(f"{label}:helper_kind:{helper_name}")
            for member in helper.get("required_members") or []:
                obligations.add(
                    f"{label}:helper_member:{helper_name}:{str(member)}"
                )
            for member in helper.get("members") or []:
                if isinstance(member, dict) and str(member.get("name") or "").strip():
                    obligations.add(
                        f"{label}:helper_member:{helper_name}:"
                        f"{str(member.get('name'))}"
                    )
    return obligations


def _evaluate_phase1_candidate(
    ctx: Ctx, labels: list[str], code: str
) -> tuple[set[str], set[str], list[SkeletonFinding]]:
    """Run the complete existing deterministic Phase-1 gate on a candidate."""
    target_kinds = {
        _lean_name(label): ctx.nodes[label].kind
        for label in labels
        if label in ctx.nodes
    }
    label_by_name = {_lean_name(label): label for label in labels}
    try:
        findings = _skeleton_code_findings(
            code,
            target_kinds,
            label_by_name,
            _planned_helper_owner_by_name(ctx, labels),
        )
        findings += _skeleton_deterministic_findings(code, ctx, labels)
    except (TypeError, ValueError) as exc:
        findings = [
            SkeletonFinding(
                f"candidate could not be canonically evaluated: {exc}",
                category="canonical_ingest",
            )
        ]
    violations = {
        obligation
        for finding in findings
        for obligation in _finding_obligation_ids(finding)
    }
    universe = _candidate_obligation_universe(ctx, labels) | violations
    return universe, violations, findings


def _lean_error_count(output: str) -> int:
    count = len(re.findall(r"(?m):\d+:\d+:\s*error:", output))
    if count:
        return count
    return 1 if output.strip() else 0


def _candidate_transition_decision(
    previous: dict[str, Any] | None,
    proposed: dict[str, Any],
) -> tuple[bool, str, set[str], set[str]]:
    """Decide whether proposed code advances the same statement/plan epoch."""
    if not previous:
        return True, "initial_candidate", set(), set(
            proposed.get("deterministic_violations") or []
        )
    old_hash = str(previous.get("candidate_hash") or _candidate_hash(str(previous.get("code") or "")))
    new_hash = str(proposed.get("candidate_hash") or "")
    old_violations = set(previous.get("deterministic_violations") or [])
    new_violations = set(proposed.get("deterministic_violations") or [])
    regressed = new_violations - old_violations
    improved = old_violations - new_violations
    if old_hash == new_hash:
        return True, "same_candidate_evidence", regressed, improved
    if regressed:
        return False, "deterministic_regression", regressed, improved
    if improved:
        return True, "deterministic_progress", regressed, improved

    # A compiling candidate that failed semantic alignment is not a valid
    # rollback point. Once exact critic feedback has forced generation of a
    # different deterministic-clean interface, let that revision become the
    # candidate under evaluation even before it has compiled. Otherwise the
    # old candidate's ``lean_status == passed`` permanently dominates every
    # alternative with ``lean_status == unknown`` and the retry loop keeps
    # regenerating corrections that can never reach compilation/audit.
    if (
        previous.get("semantic_status") == "rejected"
        and new_hash != old_hash
        and not new_violations
    ):
        return True, "semantic_rejection_revision", regressed, improved

    old_lean = str(previous.get("lean_status") or "unknown")
    new_lean = str(proposed.get("lean_status") or "unknown")
    if new_lean == "passed" and old_lean != "passed":
        return True, "lean_progress", regressed, improved
    if new_lean == old_lean == "failed":
        old_count = int(previous.get("lean_error_count") or 0)
        new_count = int(proposed.get("lean_error_count") or 0)
        if new_count and (not old_count or new_count < old_count):
            return True, "lean_error_reduction", regressed, improved
    if (
        proposed.get("repair_stage") == "semantic_corrected"
        and previous.get("semantic_status") == "rejected"
    ):
        return True, "semantic_correction_candidate", regressed, improved
    return False, "no_measurable_progress", regressed, improved


def _upgrade_candidate_entry(
    ctx: Ctx, labels: list[str], entry: dict[str, Any]
) -> dict[str, Any]:
    """Lazily add monotonic-state fields to pre-migration candidate entries."""
    if int(entry.get("candidate_state_version") or 0) != 1:
        code, _ = _compose_module(
            [str(item) for item in entry.get("imports") or []],
            [str(item) for item in entry.get("preamble") or []],
            [str(entry.get("code") or "")],
        )
        obligations, violations, findings = _evaluate_phase1_candidate(
            ctx, labels, code
        )
        entry["deterministic_obligations"] = sorted(obligations)
        entry["satisfied_obligations"] = sorted(obligations - violations)
        entry["deterministic_violations"] = sorted(violations)
        entry["deterministic_findings"] = [
            finding.message[-4000:] for finding in findings
        ]
        entry["candidate_state_version"] = 1
    entry.setdefault("candidate_hash", _candidate_hash(str(entry.get("code") or "")))
    entry.setdefault("lean_status", "unknown")
    entry.setdefault("lean_output", "")
    entry.setdefault("lean_output_sha256", "")
    entry.setdefault("lean_error_count", 0)
    entry.setdefault("semantic_status", "unknown")
    entry.setdefault("semantic_evidence", "")
    entry.setdefault("semantic_evidence_sha256", "")
    entry.setdefault("base_attempted", entry.get("generation_tier") == "base")
    entry.setdefault(
        "escalation_attempted", entry.get("generation_tier") == "escalation"
    )
    entry.setdefault("revision", 1)
    entry.setdefault("rejected_transitions", [])
    entry.setdefault("working_candidate", {})
    return entry


def _working_candidate_payload(proposed: dict[str, Any]) -> dict[str, Any]:
    """Persist a deterministic-clean compiler intermediate separately.

    The monotonic candidate remains the rollback point. A compiler transaction
    may nevertheless need several valid rewrites before Lean's error count
    decreases. Keeping that intermediate in a separate slot lets the next
    correction continue from the latest diagnostics without pretending the
    intermediate is already the best candidate.
    """
    return {
        key: copy.deepcopy(proposed.get(key))
        for key in (
            "code",
            "candidate_hash",
            "source",
            "generation_tier",
            "repair_stage",
            "imports",
            "preamble",
            "component_labels",
            "required_dependencies",
            "deterministic_obligations",
            "satisfied_obligations",
            "deterministic_violations",
            "deterministic_findings",
            "lean_status",
            "lean_output",
            "lean_output_sha256",
            "lean_error_count",
            "semantic_status",
            "semantic_evidence",
            "semantic_evidence_sha256",
        )
    }


def _may_retain_working_candidate(
    *,
    source: str,
    proposed: dict[str, Any],
    accepted_as_best: bool,
    regressed: set[str],
) -> bool:
    """Whether a non-best proposal is a usable compiler transaction step."""
    return bool(
        not accepted_as_best
        and not regressed
        and proposed.get("lean_status") == "failed"
        and "compile" in source
        and str(proposed.get("code") or "").strip()
    )


def _store_generation_candidates(
    ctx: Ctx,
    labels: Iterable[str],
    code: str,
    *,
    source: str,
    all_labels: Iterable[str] | None = None,
    reusable_uncompiled: bool = False,
    generation_tier: str = "base",
    repair_stage: str = "generated",
    required_dependencies: dict[str, set[str]] | None = None,
    lean_status: str = "unknown",
    lean_output: str = "",
    semantic_status: str = "unknown",
    semantic_evidence: str = "",
) -> list[str]:
    """Retain only monotonic candidate improvements for the current epoch.

    Local helper declarations are assigned using the same ownership rule as
    routed-section salvage: a helper belongs to the next generated target.
    A proposed replacement is evaluated by the complete deterministic Phase-1
    gate before it can replace the best stored candidate. Shared-helper
    components move atomically. A deterministic regression remains evidence
    only. A deterministic-clean compiler intermediate is retained separately
    as the live correction transaction, while the best candidate remains the
    rollback point until that transaction makes measurable progress.
    """
    try:
        parsed = _parse_module(code)
    except (TypeError, ValueError):
        return []
    statement_fps = getattr(ctx, "stmt_fps", {})
    requested = [
        label for label in labels if label in ctx.nodes and statement_fps.get(label)
    ]
    all_label_list = [
        label
        for label in (all_labels if all_labels is not None else requested)
        if label in ctx.nodes
    ]
    target_names = {_lean_name(label) for label in all_label_list}
    label_by_name = {_lean_name(label): label for label in all_label_list}
    helper_owners = _planned_helper_owner_by_name(ctx, all_label_list)
    components = _target_components_from_helpers(
        parsed, label_by_name, helper_owners
    )
    component_for = {
        label: component
        for component in components
        for label in component
    }
    stored: list[str] = []
    handled: set[str] = set()
    requested_set = set(requested)
    for label in requested:
        if label in handled:
            continue
        component = component_for.get(label, {label})
        # A shared helper makes the complete component the unit of persistence.
        # Never save a fragment that cannot later be imported independently.
        if not component <= requested_set:
            continue
        component_labels = [item for item in all_label_list if item in component]
        pieces = _delivered_decl_texts(
            parsed, component_labels, target_names, helper_owners
        )
        if not pieces:
            continue
        candidate = "\n\n".join(pieces).strip()
        if not candidate:
            continue
        candidate_code, _ = _compose_module(
            parsed.imports, parsed.preamble, pieces
        )
        obligations, violations, findings = _evaluate_phase1_candidate(
            ctx, component_labels, candidate_code
        )
        candidate_hash = _candidate_hash(candidate)
        proposed = {
            "candidate_state_version": 1,
            "statement_fp": statement_fps[component_labels[0]],
            "plan_fp": _candidate_plan_fingerprint(ctx, component_labels[0]),
            "code": candidate[:45000],
            "candidate_hash": candidate_hash,
            "source": source,
            "reusable_uncompiled": bool(reusable_uncompiled),
            "generation_tier": (
                generation_tier
                if generation_tier in {"base", "escalation"}
                else "base"
            ),
            "repair_stage": repair_stage,
            "imports": list(parsed.imports),
            "preamble": list(parsed.preamble),
            "component_labels": list(component_labels),
            "required_dependencies": [],
            "deterministic_obligations": sorted(obligations),
            "satisfied_obligations": sorted(obligations - violations),
            "deterministic_violations": sorted(violations),
            "deterministic_findings": [
                finding.message[-4000:] for finding in findings
            ],
            "lean_status": lean_status,
            "lean_output": lean_output[-12000:],
            "lean_output_sha256": (
                hashlib.sha256(lean_output.encode("utf-8")).hexdigest()
                if lean_output
                else ""
            ),
            "lean_error_count": (
                _lean_error_count(lean_output) if lean_status == "failed" else 0
            ),
            "semantic_status": semantic_status,
            "semantic_evidence": semantic_evidence[-12000:],
            "semantic_evidence_sha256": (
                hashlib.sha256(semantic_evidence.encode("utf-8")).hexdigest()
                if semantic_evidence
                else ""
            ),
            "base_attempted": generation_tier == "base",
            "escalation_attempted": generation_tier == "escalation",
            "revision": 1,
        }
        with _STATE_LOCK:
            candidates = getattr(ctx, "generation_candidates", None)
            if candidates is None:
                candidates = {}
                ctx.generation_candidates = candidates
            previous_entries = [
                (
                    _upgrade_candidate_entry(
                        ctx,
                        list(
                            (candidates.get(component_label) or {}).get(
                                "component_labels"
                            )
                            or [component_label]
                        ),
                        candidates[component_label],
                    )
                    if isinstance(candidates.get(component_label), dict)
                    else None
                )
                for component_label in component_labels
            ]
            decisions = [
                _candidate_transition_decision(previous, proposed)
                for previous in previous_entries
            ]
            accepted = all(decision[0] for decision in decisions)
            reasons = sorted({decision[1] for decision in decisions})
            regressed = set().union(*(decision[2] for decision in decisions))
            improved = set().union(*(decision[3] for decision in decisions))
            parent_hashes = sorted(
                {
                    str(entry.get("candidate_hash") or _candidate_hash(str(entry.get("code") or "")))
                    for entry in previous_entries
                    if isinstance(entry, dict) and str(entry.get("code") or "").strip()
                }
            )
            accepted_as_working = _may_retain_working_candidate(
                source=source,
                proposed=proposed,
                accepted_as_best=accepted,
                regressed=regressed,
            )
            if accepted:
                revision = max(
                    [int(entry.get("revision") or 0) for entry in previous_entries if isinstance(entry, dict)]
                    or [0]
                ) + (0 if reasons == ["same_candidate_evidence"] else 1)
                for component_label in component_labels:
                    previous = candidates.get(component_label) or {}
                    entry = dict(proposed)
                    entry.update(
                        {
                            "statement_fp": statement_fps[component_label],
                            "plan_fp": _candidate_plan_fingerprint(
                                ctx, component_label
                            ),
                            "required_dependencies": sorted(
                                set(
                                    (required_dependencies or {}).get(
                                        component_label, set()
                                    )
                                )
                            ),
                            "base_attempted": bool(previous.get("base_attempted"))
                            or generation_tier == "base",
                            "escalation_attempted": bool(
                                previous.get("escalation_attempted")
                            )
                            or generation_tier == "escalation",
                            "revision": revision,
                        }
                    )
                    if reasons == ["same_candidate_evidence"]:
                        entry["reusable_uncompiled"] = bool(
                            previous.get("reusable_uncompiled")
                        ) or bool(reusable_uncompiled)
                        entry["lean_status"] = (
                            lean_status
                            if lean_status != "unknown"
                            else str(previous.get("lean_status") or "unknown")
                        )
                        entry["lean_output"] = (
                            lean_output[-12000:]
                            if lean_output
                            else str(previous.get("lean_output") or "")
                        )
                        entry["lean_output_sha256"] = (
                            proposed["lean_output_sha256"]
                            or str(previous.get("lean_output_sha256") or "")
                        )
                        entry["lean_error_count"] = (
                            proposed["lean_error_count"]
                            or int(previous.get("lean_error_count") or 0)
                        )
                        # A deterministic-clean candidate is reusable only up
                        # to its first Lean check. Preserve failed code and
                        # diagnostics as the next revision seed, but never let
                        # the same bytes bypass model correction indefinitely.
                        if entry["lean_status"] == "failed":
                            entry["reusable_uncompiled"] = False
                        entry["semantic_status"] = (
                            semantic_status
                            if semantic_status != "unknown"
                            else str(previous.get("semantic_status") or "unknown")
                        )
                        entry["semantic_evidence"] = (
                            semantic_evidence[-12000:]
                            if semantic_evidence
                            else str(previous.get("semantic_evidence") or "")
                        )
                        entry["semantic_evidence_sha256"] = (
                            proposed["semantic_evidence_sha256"]
                            or str(
                                previous.get("semantic_evidence_sha256") or ""
                            )
                        )
                    # Promotion completes the local correction transaction.
                    # Any older intermediate must not survive beside the new
                    # monotonic best.
                    entry["working_candidate"] = {}
                    candidates[component_label] = entry
                    stored.append(component_label)
                    handled.add(component_label)
            else:
                # A deterministic regression remains evidence only. A clean
                # compiler intermediate may be the next transaction seed, but
                # it stays separate from the monotonic best and cannot freeze.
                for component_label in component_labels:
                    previous = candidates.get(component_label)
                    if not isinstance(previous, dict):
                        continue
                    previous["base_attempted"] = bool(previous.get("base_attempted")) or generation_tier == "base"
                    previous["escalation_attempted"] = bool(previous.get("escalation_attempted")) or generation_tier == "escalation"
                    history = list(previous.get("rejected_transitions") or [])
                    history.append(
                        {
                            "candidate_hash": candidate_hash,
                            "source": source,
                            "reason": ",".join(reasons),
                            "regressed": sorted(regressed),
                            "improved": sorted(improved),
                            "lean_status": lean_status,
                            "lean_output_sha256": proposed["lean_output_sha256"],
                            "semantic_status": semantic_status,
                            "semantic_evidence_sha256": proposed[
                                "semantic_evidence_sha256"
                            ],
                        }
                    )
                    previous["rejected_transitions"] = history[-12:]
                    if accepted_as_working:
                        previous["working_candidate"] = (
                            _working_candidate_payload(proposed)
                        )
                    stored.append(component_label)
                    handled.add(component_label)
                if not accepted_as_working:
                    regression_evidence = (
                        "A proposed Phase 1 candidate was not installed because it did "
                        "not improve the retained candidate. Continue by editing the "
                        "retained candidate and preserve all of its satisfied "
                        "obligations.\n"
                        f"Decision: {', '.join(reasons)}\n"
                        "Regressed obligations: "
                        + (", ".join(sorted(regressed)) or "none")
                        + "\nRemaining proposed violations:\n"
                        + (_format_skeleton_findings(findings) or "none")
                    )
                    # Keep the retained candidate and the reason it was
                    # retained in one state transaction. A parallel worker may
                    # not observe the new candidate epoch without its feedback.
                    _store_generation_feedback(
                        ctx,
                        component_labels,
                        regression_evidence[-12000:],
                        source="candidate_regression",
                    )

        _record(
            ctx.telemetry,
            "phase1_candidate_transition",
            labels=component_labels,
            statement_fps={
                label: statement_fps[label] for label in component_labels
            },
            plan_fps={
                label: _candidate_plan_fingerprint(ctx, label)
                for label in component_labels
            },
            candidate_hash=candidate_hash,
            parent_candidate_hashes=parent_hashes,
            source=source,
            generation_tier=generation_tier,
            accepted_as_best=accepted,
            accepted_as_working=accepted_as_working,
            decision_reasons=reasons,
            deterministic_obligations=sorted(obligations),
            satisfied_obligations=sorted(obligations - violations),
            remaining_obligations=sorted(violations),
            newly_satisfied=sorted(improved),
            regressed_obligations=sorted(regressed),
            lean_status=lean_status,
            semantic_status=semantic_status,
        )
    if stored:
        with _STATE_LOCK:
            saved_code_chars = sum(
                len((getattr(ctx, "generation_candidates", {}).get(label) or {}).get("code", ""))
                for label in stored
            )
        _record(
            ctx.telemetry,
            "phase1_retry_candidate_saved",
            labels=stored,
            source=source,
            code_chars=saved_code_chars,
            statement_fps={label: statement_fps[label] for label in stored},
        )
    return stored


def _reusable_uncompiled_candidate(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    *,
    require_reusable: bool = True,
) -> Phase1LayerCandidate | None:
    """Rehydrate a complete pre-audit candidate without another model call.

    This path is deliberately stricter than ``_generation_candidates_for``:
    every requested statement must have passed deterministic validation for
    its current blueprint fingerprint, and its imports/preamble must have been
    persisted. Older state and rejected candidates fall back to generation.
    """
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
        entries = [candidates.get(label) for label in labels]
    if not entries or any(
        not isinstance(entry, dict)
        or (require_reusable and not _candidate_is_reusable_uncompiled(entry))
        or not str(entry.get("code") or "").strip()
        for entry in entries
    ):
        return None

    imports = list(
        dict.fromkeys(
            str(item)
            for entry in entries
            for item in (entry.get("imports") or [])
            if str(item).strip()
        )
    )
    preamble = list(
        dict.fromkeys(
            str(item)
            for entry in entries
            for item in (entry.get("preamble") or [])
            if str(item).strip()
        )
    )
    blocks: list[str] = []
    seen: set[str] = set()
    for entry in entries:
        code = str(entry.get("code") or "").strip()
        if code not in seen:
            seen.add(code)
            blocks.append(code)
    try:
        parsed = _parse_module(_compose_module(imports, preamble, blocks)[0])
    except (TypeError, ValueError):
        return None
    parsed = _namespace_owned_helpers(ctx, labels, parsed)

    target_names = {_lean_name(label) for label in labels}
    delivered = [decl.name for decl in parsed.decls if decl.name in target_names]
    if len(delivered) != len(labels) or set(delivered) != target_names:
        return None

    missing_imports = _missing_olean_imports(parsed.imports)
    if missing_imports:
        ctx.unavailable_imports.update(missing_imports)
        parsed.imports = [
            item for item in parsed.imports if item not in set(missing_imports)
        ]
    tier = (
        "escalation"
        if any(entry.get("generation_tier") == "escalation" for entry in entries)
        else "base"
    )
    candidate = Phase1LayerCandidate(
        labels=list(labels),
        parsed=parsed,
        import_modules=_sections_for_deps(ctx, labels, sections),
        generation_tier=tier,
        sessions={},
    )
    target_kinds = {_lean_name(label): ctx.nodes[label].kind for label in labels}
    label_by_name = {_lean_name(label): label for label in labels}
    for decl in candidate.parsed.decls:
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    code = _phase1_layer_candidate_code(candidate)
    findings = _skeleton_code_findings(
        code,
        target_kinds,
        label_by_name,
        _planned_helper_owner_by_name(ctx, labels),
    )
    findings += _skeleton_deterministic_findings(code, ctx, labels)
    if findings:
        return None
    _record(
        ctx.telemetry,
        (
            "phase1_uncompiled_candidate_reused"
            if require_reusable
            else "phase1_semantic_candidate_rehydrated"
        ),
        labels=labels,
        count=len(labels),
        generation_tier=tier,
    )
    return candidate


def _retained_generation_candidate_code(
    ctx: Ctx, labels: Iterable[str]
) -> str:
    """Compose the exact best stored candidate for the current plan epoch.

    Unlike ``_reusable_uncompiled_candidate``, this also returns candidates that
    still have deterministic or Lean failures. Correction loops need that exact
    text so a rejected patch cannot become their next editing baseline.
    """
    label_list = list(labels)
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
        entries = [candidates.get(label) for label in label_list]
    if not entries or any(
        not isinstance(entry, dict) or not str(entry.get("code") or "").strip()
        for entry in entries
    ):
        return ""
    imports = list(
        dict.fromkeys(
            str(item)
            for entry in entries
            for item in (entry.get("imports") or [])
            if str(item).strip()
        )
    )
    preamble = list(
        dict.fromkeys(
            str(item)
            for entry in entries
            for item in (entry.get("preamble") or [])
            if str(item).strip()
        )
    )
    blocks: list[str] = []
    seen: set[str] = set()
    for entry in entries:
        block = str(entry.get("code") or "").strip()
        if block and block not in seen:
            seen.add(block)
            blocks.append(block)
    return _compose_module(imports, preamble, blocks)[0] if blocks else ""


def _salvage_partial_phase1_response(
    ctx: Ctx,
    labels: list[str],
    parsed: ParsedModule,
    sections: list[Section],
    *,
    generation_tier: str,
) -> list[str]:
    """Persist independently valid declarations from an incomplete response.

    A missing target is evidence about that target, not about every declaration
    returned beside it.  Shared local helpers still define atomic components:
    a component is reusable only when all of its targets were delivered and the
    complete component passes the ordinary deterministic Phase-1 gates.
    Compilation and semantic auditing remain mandatory in the next transaction.
    """
    target_names = {_lean_name(label): label for label in labels}
    delivered = [
        target_names[decl.name]
        for decl in parsed.decls
        if decl.name in target_names
    ]
    if not delivered:
        return []
    code, _ = _compose_module(
        parsed.imports,
        parsed.preamble,
        [decl.text for decl in parsed.decls],
    )
    stored = _store_generation_candidates(
        ctx,
        delivered,
        code,
        source="phase1_partial_response",
        all_labels=labels,
        generation_tier=generation_tier,
        repair_stage="partial_delivered",
    )
    salvaged: list[str] = []
    handled: set[str] = set()
    with _STATE_LOCK:
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
    for label in stored:
        if label in handled:
            continue
        entry = candidates.get(label) or {}
        component = [
            item
            for item in entry.get("component_labels") or [label]
            if item in stored
        ]
        if not component or any(item in handled for item in component):
            continue
        candidate = _reusable_uncompiled_candidate(
            ctx, component, sections, require_reusable=False
        )
        if candidate is None:
            continue
        candidate_code = _phase1_layer_candidate_code(candidate)
        reusable = _store_generation_candidates(
            ctx,
            component,
            candidate_code,
            source="phase1_partial_response_validated",
            all_labels=component,
            reusable_uncompiled=True,
            generation_tier=generation_tier,
            repair_stage="deterministic_valid",
        )
        salvaged.extend(reusable)
        handled.update(component)
    salvaged = list(dict.fromkeys(salvaged))
    _record(
        ctx.telemetry,
        "phase1_partial_response_salvaged",
        requested_labels=labels,
        delivered_labels=delivered,
        salvaged_labels=salvaged,
        unresolved_labels=[label for label in labels if label not in salvaged],
        generation_tier=generation_tier,
    )
    if salvaged:
        _log(
            "  preserved "
            f"{len(salvaged)} deterministically valid declaration(s) from an "
            "incomplete model response"
        )
    return salvaged


def _semantic_repair_candidate(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
) -> Phase1LayerCandidate | None:
    """Revise the exact compiling candidate rejected by statement alignment.

    This is the mandatory continuation of a semantic rejection. It deliberately
    runs before ordinary generation so an outer retry cannot turn precise
    critic evidence into a cold restart. A failed direct correction is marked
    explicitly; only that state may fall back to generation of an alternative.
    """
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        entries = [
            copy.deepcopy(getattr(ctx, "generation_candidates", {}).get(label))
            for label in labels
        ]
    if not entries or any(
        not isinstance(entry, dict)
        or entry.get("repair_stage") != "semantic_rejected"
        for entry in entries
    ):
        return None
    evidence = _generation_feedback_for(ctx, labels)
    if not evidence:
        return None
    seed = _reusable_uncompiled_candidate(
        ctx, labels, sections, require_reusable=False
    )
    if seed is None:
        return None
    if len(labels) == 1:
        seed.generation_tier = _retry_next_tier(
            ctx, labels[0], "phase1_statement"
        )
    required_dependencies = {
        label: {
            str(dep)
            for dep in entry.get("required_dependencies") or []
            if str(dep) in ctx.nodes and str(dep) != label
        }
        for label, entry in zip(labels, entries)
        if isinstance(entry, dict)
    }
    try:
        revised = _revise_semantic_candidates(
            ctx,
            [seed],
            set(labels),
            evidence,
            sections,
            required_dependencies=required_dependencies,
        )
    except RepairRequest:
        for entry in entries:
            entry["repair_stage"] = "semantic_correction_failed"
        _record(
            ctx.telemetry,
            "phase1_semantic_candidate_transition",
            labels=labels,
            previous="semantic_rejected",
            current="semantic_correction_failed",
        )
        raise
    if len(revised) != 1 or set(revised[0].labels) != set(labels):
        return None
    candidate = revised[0]
    code = _phase1_layer_candidate_code(candidate)
    _store_generation_candidates(
        ctx,
        labels,
        code,
        source="semantic_repair",
        all_labels=labels,
        reusable_uncompiled=True,
        generation_tier=candidate.generation_tier,
        repair_stage="semantic_corrected",
        semantic_status="correction_pending",
        semantic_evidence=evidence,
    )
    _record(
        ctx.telemetry,
        "phase1_semantic_candidate_transition",
        labels=labels,
        previous="semantic_rejected",
        current="semantic_corrected",
    )
    return candidate


def _generation_candidates_for(ctx: Ctx, labels: Iterable[str]) -> str:
    """Return the latest usable declarations as one compact revision input.

    A deterministic-clean compiler intermediate takes precedence over the
    monotonic best because it carries the newest exact diagnostics. The best
    remains stored separately as the rollback point until the working code
    actually compiles or makes measurable deterministic progress.
    """
    label_list = list(labels)
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
    blocks: list[str] = []
    included: list[str] = []
    seen: set[str] = set()
    for label in label_list:
        entry = candidates.get(label)
        working = (
            (entry or {}).get("working_candidate")
            if isinstance((entry or {}).get("working_candidate"), dict)
            else {}
        )
        code = str(
            working.get("code") or (entry or {}).get("code") or ""
        ).strip()
        if not code or code in seen:
            continue
        seen.add(code)
        included.append(label)
        blocks.append(f"-- Rejected candidate for {label}\n{code}")
    text = "\n\n".join(blocks)
    if included:
        _record(
            ctx.telemetry,
            "phase1_retry_candidate_injected",
            labels=included,
            code_chars=len(text),
        )
    return text


def _clear_generation_candidates(ctx: Ctx, labels: Iterable[str]) -> None:
    """Forget candidate Lean only after acceptance of the exact statement."""
    cleared: list[str] = []
    with _STATE_LOCK:
        candidates = getattr(ctx, "generation_candidates", {})
        for label in labels:
            if candidates.pop(label, None) is not None:
                cleared.append(label)
    telemetry = getattr(ctx, "telemetry", None)
    if cleared and telemetry is not None:
        _record(
            telemetry,
            "phase1_retry_candidate_cleared",
            labels=cleared,
            reason="statement_accepted",
        )


def _retry_lifecycle_key(stage: str, label: str) -> str:
    return f"{stage}:{label}"


def _retry_next_tier(ctx: Ctx, label: str, stage: str) -> str:
    """Return the next model tier without letting batching reset provenance."""
    statement_fps = getattr(ctx, "stmt_fps", {})
    entry = getattr(ctx, "retry_lifecycle", {}).get(
        _retry_lifecycle_key(stage, label), {}
    )
    if entry.get("statement_fp") != statement_fps.get(label):
        return "base"
    return "escalation" if entry.get("state") in {"escalation", "exhausted"} else "base"


def _record_retry_failure(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    stage: str,
    attempted_tier: str,
    evidence: str,
    source: str,
) -> set[str]:
    """Advance exact statement versions through base, escalation, exhausted.

    The transition is monotone.  A later batched audit reporting a base-tier
    candidate cannot reset a node that already reached escalation.
    """
    lifecycle = getattr(ctx, "retry_lifecycle", None)
    if lifecycle is None:
        lifecycle = {}
        ctx.retry_lifecycle = lifecycle
    exhausted: set[str] = set()
    evidence_hash = hashlib.sha256(evidence.encode("utf-8")).hexdigest()
    for label in labels:
        statement_fp = ctx.stmt_fps.get(label, "")
        if not statement_fp:
            continue
        key = _retry_lifecycle_key(stage, label)
        previous = lifecycle.get(key, {})
        previous_state = (
            str(previous.get("state") or "base")
            if previous.get("statement_fp") == statement_fp
            else "base"
        )
        state = (
            "exhausted"
            if attempted_tier == "escalation" or previous_state == "exhausted"
            else "escalation"
        )
        failures = int(previous.get("failures") or 0) + 1
        lifecycle[key] = {
            "label": label,
            "stage": stage,
            "statement_fp": statement_fp,
            "state": state,
            "last_tier": attempted_tier,
            "failures": failures,
            "source": source,
            "evidence_sha256": evidence_hash,
        }
        if state == "exhausted":
            exhausted.add(label)
        telemetry = getattr(ctx, "telemetry", None)
        if telemetry is not None:
            _record(
                telemetry,
                "node_retry_lifecycle",
                label=label,
                stage=stage,
                statement_fp=statement_fp,
                previous_state=previous_state,
                attempted_tier=attempted_tier,
                next_state=state,
                failures=failures,
                source=source,
                evidence_sha256=evidence_hash,
            )
    return exhausted


def _clear_retry_lifecycle(
    ctx: Ctx, labels: Iterable[str], *, stage: str | None = None
) -> None:
    lifecycle = getattr(ctx, "retry_lifecycle", {})
    wanted = set(labels)
    for key, entry in list(lifecycle.items()):
        if entry.get("label") in wanted and (stage is None or entry.get("stage") == stage):
            lifecycle.pop(key, None)


def _prune_stale_retry_lifecycle(ctx: Ctx) -> set[str]:
    """Discard retry history when the corresponding blueprint statement changes."""
    lifecycle = getattr(ctx, "retry_lifecycle", {})
    stale = {
        key
        for key, entry in lifecycle.items()
        if entry.get("label") not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(str(entry.get("label") or ""))
    }
    for key in stale:
        lifecycle.pop(key, None)
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
            status=_runner_failure_status(exc),
            duration_s=0.0,
            timeout_s=timeout,
            effort=effort or "",
            backend=runner_spec.partition(":")[0],
            model=runner_spec.partition(":")[2],
            resumed_session=bool(resume_session_id),
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
            transport_error=is_transient_error(exc),
        )
        if is_environment_error(exc) or is_transient_error(exc):
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
    stage = (
        f"model_call purpose={purpose} labels={labels[:8]}"
        + ("..." if len(labels) > 8 else "")
        + f" timeout={timeout}s runner={runner_spec}"
        + (" escalated" if escalated else "")
        + (" resumed" if resume_session_id else "")
    )
    started = time.monotonic()
    try:
        with _stage(stage):
            result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        duration = time.monotonic() - started
        status = _runner_failure_status(exc)
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
        if status == "transport_exhausted":
            if sessions is not None:
                sessions.pop(runner_spec, None)
            _record(
                ctx.telemetry,
                "model_call",
                purpose=purpose,
                labels=labels,
                status="transport_exhausted",
                duration_s=duration,
                timeout_s=timeout,
                effort=effort or "",
                backend=runner.backend_name,
                model=runner.model,
                resumed_session=bool(resume_session_id),
                prompt=prompt_artifact.to_event(REPO_ROOT),
                error=str(exc),
                environment_error=False,
                transport_error=True,
            )
            _log(
                f"model call ({purpose}) transport retries exhausted; "
                "saving run state without consuming a mathematical repair trial: "
                f"{str(exc)[:160]}",
                tag=tag,
            )
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
    # ``None`` is the backward-compatible representation for an old section
    # whose every label already passed the Phase-1 statement gates.  The
    # initial declaration pass stores an explicit (initially empty) set and
    # Phase 1 adds labels as their contracts are refined root-first.
    refined_labels: set[str] | None = None
    # The one whole-blueprint file emitted by the initial pass is permanent
    # scaffolding, not an accepted section. Phase-1 repairs keep this file,
    # mark affected contracts unrefined, and add new helper names in place;
    # they must never route back through the model-backed initial pass.
    provisional_environment: bool = False
    # Tier that produced the current Phase-1 candidate. This is provenance,
    # not acceptance state; layer-wide audits may combine candidates while
    # still advancing each rejected node from its own originating tier.
    generation_tier: str = "unknown"

    @property
    def file_name(self) -> str:
        return self.path.name


@dataclass
class Phase1LayerCandidate:
    """Uncompiled Phase-1 statements owned by one generation transaction.

    Bottom-up Phase 1 keeps these candidates in memory until the whole
    dependency layer has received one semantic judgment.  ``generation_tier``
    and ``sessions`` preserve producer provenance for a focused correction;
    neither field implies that the candidate has compiled or been accepted.
    """

    labels: list[str]
    parsed: ParsedModule
    import_modules: list[str]
    generation_tier: str
    sessions: dict[str, str] = field(default_factory=dict)


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


def _generated_lake_module_dir(name: str) -> Path:
    return (
        REPO_ROOT
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / "AutoBlueprint"
        / "Generated"
        / _module_safe_name(name)
    )


def _discard_section_objects(path: Path) -> None:
    """Remove every compiled object for a generated source, retaining source."""
    with contextlib.suppress(OSError, ValueError):
        _lake_olean_path(path).unlink(missing_ok=True)
    with contextlib.suppress(OSError):
        path.with_suffix(".olean").unlink(missing_ok=True)


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
    _discard_section_objects(path)


def _save_state(
    name: str,
    sections: list[Section],
    stmt_fps: dict[str, str],
    contract_fps: dict[str, str],
    *,
    quarantined_labels: set[str] | None = None,
    quarantine: dict[str, dict[str, str]] | None = None,
    local_group_partitions: dict[str, dict[str, Any]] | None = None,
    generation_feedback: dict[str, dict[str, str]] | None = None,
    generation_candidates: dict[str, dict[str, Any]] | None = None,
    retry_lifecycle: dict[str, dict[str, Any]] | None = None,
    design_plan_entries: dict[str, dict[str, Any]] | None = None,
    semantic_plan_entries: dict[str, dict[str, Any]] | None = None,
    design_plan_alternates: dict[str, dict[str, Any]] | None = None,
    blueprint_direct_generation: dict[str, dict[str, Any]] | None = None,
    repair_boundary_pending: dict[str, Any] | None = None,
    effective_section_size: int = 0,
    refinement_order: str = PHASE1_STATEMENT_ORDER,
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
                "refined_labels": (
                    None
                    if sec.refined_labels is None
                    else sorted(sec.refined_labels)
                ),
                "provisional_environment": sec.provisional_environment,
                "generation_tier": sec.generation_tier,
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

    local_partition_payload = {
        str(label): {
            "partition_id": str(entry.get("partition_id") or ""),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "statement_fps": {
                str(item): str(fp)
                for item, fp in (entry.get("statement_fps") or {}).items()
                if str(item) in stmt_fps and str(fp) == stmt_fps.get(str(item))
            },
            "group": [
                str(item)
                for item in entry.get("group") or []
                if str(item) in stmt_fps
            ],
        }
        for label, entry in (local_group_partitions or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and str(entry.get("partition_id") or "")
        and entry.get("group")
    }

    feedback_payload = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "source": str(entry.get("source") or "unknown"),
        }
        for label, entry in (generation_feedback or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and str(entry.get("evidence") or "").strip()
    }
    candidate_payload = {
        str(label): {
            "candidate_state_version": int(
                entry.get("candidate_state_version") or 0
            ),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "plan_fp": str(entry.get("plan_fp") or ""),
            "code": str(entry.get("code") or "")[:45000],
            "source": str(entry.get("source") or "unknown"),
            "reusable_uncompiled": _candidate_is_reusable_uncompiled(entry),
            "generation_tier": str(entry.get("generation_tier") or "base"),
            "repair_stage": str(entry.get("repair_stage") or "generated"),
            "imports": [str(item) for item in entry.get("imports") or []],
            "preamble": [str(item) for item in entry.get("preamble") or []],
            "component_labels": [
                str(item) for item in entry.get("component_labels") or [label]
            ],
            "required_dependencies": [
                str(item) for item in entry.get("required_dependencies") or []
            ],
            "candidate_hash": str(
                entry.get("candidate_hash")
                or _candidate_hash(str(entry.get("code") or ""))
            ),
            "deterministic_obligations": [
                str(item) for item in entry.get("deterministic_obligations") or []
            ],
            "satisfied_obligations": [
                str(item) for item in entry.get("satisfied_obligations") or []
            ],
            "deterministic_violations": [
                str(item) for item in entry.get("deterministic_violations") or []
            ],
            "deterministic_findings": [
                str(item)[-4000:]
                for item in entry.get("deterministic_findings") or []
            ],
            "lean_status": str(entry.get("lean_status") or "unknown"),
            "lean_output": str(entry.get("lean_output") or "")[-12000:],
            "lean_output_sha256": str(
                entry.get("lean_output_sha256") or ""
            ),
            "lean_error_count": int(entry.get("lean_error_count") or 0),
            "semantic_status": str(
                entry.get("semantic_status") or "unknown"
            ),
            "semantic_evidence": str(
                entry.get("semantic_evidence") or ""
            )[-12000:],
            "semantic_evidence_sha256": str(
                entry.get("semantic_evidence_sha256") or ""
            ),
            "base_attempted": bool(entry.get("base_attempted")),
            "escalation_attempted": bool(entry.get("escalation_attempted")),
            "revision": int(entry.get("revision") or 1),
            "rejected_transitions": [
                {
                    "candidate_hash": str(item.get("candidate_hash") or ""),
                    "source": str(item.get("source") or "unknown"),
                    "reason": str(item.get("reason") or "unknown"),
                    "regressed": [str(value) for value in item.get("regressed") or []],
                    "improved": [str(value) for value in item.get("improved") or []],
                    "lean_status": str(item.get("lean_status") or "unknown"),
                    "lean_output_sha256": str(
                        item.get("lean_output_sha256") or ""
                    ),
                    "semantic_status": str(
                        item.get("semantic_status") or "unknown"
                    ),
                    "semantic_evidence_sha256": str(
                        item.get("semantic_evidence_sha256") or ""
                    ),
                }
                for item in (entry.get("rejected_transitions") or [])[-12:]
                if isinstance(item, dict)
            ],
            "working_candidate": (
                _working_candidate_payload(entry["working_candidate"])
                if isinstance(entry.get("working_candidate"), dict)
                and str(entry["working_candidate"].get("code") or "").strip()
                else {}
            ),
        }
        for label, entry in (generation_candidates or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and str(entry.get("code") or "").strip()
    }
    lifecycle_payload = {
        str(key): {
            "label": str(entry.get("label") or ""),
            "stage": str(entry.get("stage") or ""),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "state": str(entry.get("state") or "base"),
            "last_tier": str(entry.get("last_tier") or "base"),
            "failures": int(entry.get("failures") or 0),
            "source": str(entry.get("source") or "unknown"),
            "evidence_sha256": str(entry.get("evidence_sha256") or ""),
        }
        for key, entry in (retry_lifecycle or {}).items()
        if str(entry.get("label") or "") in stmt_fps
        and str(entry.get("statement_fp") or "")
        == stmt_fps.get(str(entry.get("label") or ""))
    }
    plan_payload = {}
    for label, entry in (design_plan_entries or {}).items():
        if (
            label not in stmt_fps
            or str(entry.get("statement_fp") or "") != stmt_fps.get(label)
            or int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
            or not str(entry.get("target_signature") or "").strip()
        ):
            continue
        plan_payload[str(label)] = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "target_signature": str(entry.get("target_signature") or "")[:12000],
            "helpers": [
                {
                    "name": str(helper.get("name") or "")[:500],
                    "kind": str(helper.get("kind") or "")[:40],
                    "declaration": str(helper.get("declaration") or "")[:12000],
                    "members": [
                        {
                            "name": str(member.get("name") or "")[:500],
                            "type": str(member.get("type") or "")[:4000],
                        }
                        for member in helper.get("members") or []
                        if isinstance(member, dict)
                        and str(member.get("name") or "").strip()
                        and str(member.get("type") or "").strip()
                    ],
                    "required_members": [
                        str(item)[:500]
                        for item in helper.get("required_members") or []
                    ],
                    "purpose": str(helper.get("purpose") or "")[:2000],
                }
                for helper in entry.get("helpers") or []
                if isinstance(helper, dict)
                and str(helper.get("name") or "").strip()
                and str(helper.get("kind") or "").strip()
            ],
            "decisions": [
                str(item)[:4000]
                for item in entry.get("decisions") or []
                if str(item).strip()
            ],
            "audit_fp": str(entry.get("audit_fp") or ""),
            "rejected_audit_fp": str(entry.get("rejected_audit_fp") or ""),
            "rejected_kind": str(entry.get("rejected_kind") or ""),
            "rejected_reason": str(entry.get("rejected_reason") or "")[-12000:],
            "rejected_helpers": [
                str(item)[:2000] for item in entry.get("rejected_helpers") or []
            ],
            "correction_base_fp": str(entry.get("correction_base_fp") or ""),
            "correction_escalation_fp": str(
                entry.get("correction_escalation_fp") or ""
            ),
            "semantic_revision_count": int(
                entry.get("semantic_revision_count") or 0
            ),
            "closure_fp": str(entry.get("closure_fp") or ""),
            "closure_wave_id": str(entry.get("closure_wave_id") or ""),
            "origin": str(entry.get("origin") or ""),
        }
    semantic_plan_payload = {
        str(label): {
            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "representation": str(entry.get("representation") or "")[:600],
            "vocabulary": copy.deepcopy(entry.get("vocabulary") or [])[:8],
            "obligations": [
                str(item)[:320] for item in entry.get("obligations") or []
            ][:6],
            "provider_requirements": copy.deepcopy(
                entry.get("provider_requirements") or []
            ),
            "fallback": bool(entry.get("fallback")),
        }
        for label, entry in (semantic_plan_entries or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and int(entry.get("schema_version") or 0)
        == SEMANTIC_PLAN_SCHEMA_VERSION
    }
    alternate_plan_payload = {
        str(label): {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "target_signature": str(entry.get("target_signature") or "")[:12000],
            "helpers": copy.deepcopy(entry.get("helpers") or []),
            "decisions": [
                str(item)[:4000]
                for item in entry.get("decisions") or []
                if str(item).strip()
            ],
        }
        for label, entry in (design_plan_alternates or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and int(entry.get("schema_version") or 0) == DESIGN_PLAN_SCHEMA_VERSION
        and str(entry.get("target_signature") or "").strip()
    }
    direct_generation_payload = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "source": str(entry.get("source") or "unknown")[:200],
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "activations": max(1, int(entry.get("activations") or 1)),
        }
        for label, entry in (blueprint_direct_generation or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
    }
    boundary = repair_boundary_pending or {}
    boundary_labels = [
        str(label)
        for label in boundary.get("labels") or []
        if str(label) in stmt_fps
        and str((boundary.get("statement_fps") or {}).get(str(label)) or "")
        == stmt_fps.get(str(label))
    ]
    boundary_payload = (
        {
            "mode": str(boundary.get("mode") or "audit"),
            "labels": boundary_labels,
            "statement_fps": {
                label: stmt_fps[label] for label in boundary_labels
            },
            "previous_statements": {
                label: str((boundary.get("previous_statements") or {}).get(label) or "")[:6000]
                for label in boundary_labels
            },
            "evidence": str(boundary.get("evidence") or "")[-12000:],
            "repair_labels": [
                str(label)
                for label in boundary.get("repair_labels") or []
                if str(label) in stmt_fps
            ],
            "required_dependencies": {
                str(label): [
                    str(dep)
                    for dep in dependencies
                    if str(dep) in stmt_fps and str(dep) != str(label)
                ]
                for label, dependencies in (
                    boundary.get("required_dependencies") or {}
                ).items()
                if str(label) in stmt_fps
            },
            "decomposition_helpers": [
                str(item)[:2000]
                for item in boundary.get("decomposition_helpers") or []
                if str(item).strip()
            ],
        }
        if boundary_labels
        else {}
    )

    path = _state_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "version": 20,
                "refinement_order": refinement_order,
                "sections": entries,
                "scheduler": {
                    "quarantine": {
                        label: quarantine_payload[label]
                        for label in sorted(quarantine_payload)
                    },
                    "local_group_partitions": {
                        label: local_partition_payload[label]
                        for label in sorted(local_partition_payload)
                    },
                    "effective_section_size": effective_section_size,
                    "generation_feedback": {
                        label: feedback_payload[label]
                        for label in sorted(feedback_payload)
                    },
                    "generation_candidates": {
                        label: candidate_payload[label]
                        for label in sorted(candidate_payload)
                    },
                    "retry_lifecycle": {
                        key: lifecycle_payload[key]
                        for key in sorted(lifecycle_payload)
                    },
                    "design_plan_entries": {
                        label: plan_payload[label]
                        for label in sorted(plan_payload)
                    },
                    "semantic_plan_entries": {
                        label: semantic_plan_payload[label]
                        for label in sorted(semantic_plan_payload)
                    },
                    "design_plan_alternates": {
                        label: alternate_plan_payload[label]
                        for label in sorted(alternate_plan_payload)
                    },
                    "blueprint_direct_generation": {
                        label: direct_generation_payload[label]
                        for label in sorted(direct_generation_payload)
                    },
                    "repair_boundary_pending": boundary_payload,
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def _save_ctx_state(ctx: Ctx, sections: list[Section]) -> None:
    # A UI stop or outer retry may save while Phase 1 workers are completing.
    # Persist one coherent scheduler snapshot rather than references to mutable
    # dictionaries that can change while JSON payloads are being assembled.
    with _STATE_LOCK:
        generation_feedback = copy.deepcopy(
            getattr(ctx, "generation_feedback", {})
        )
        generation_candidates = copy.deepcopy(
            getattr(ctx, "generation_candidates", {})
        )
    _save_state(
        ctx.name,
        sections,
        ctx.stmt_fps,
        ctx.contract_fps,
        quarantined_labels=ctx.quarantined_labels,
        quarantine=ctx.quarantine,
        local_group_partitions=getattr(ctx, "local_group_partitions", {}),
        generation_feedback=generation_feedback,
        generation_candidates=generation_candidates,
        retry_lifecycle=getattr(ctx, "retry_lifecycle", {}),
        design_plan_entries=getattr(ctx, "design_plan_entries", {}),
        semantic_plan_entries=getattr(ctx, "semantic_plan_entries", {}),
        design_plan_alternates=getattr(ctx, "design_plan_alternates", {}),
        blueprint_direct_generation=getattr(
            ctx, "blueprint_direct_generation", {}
        ),
        repair_boundary_pending=getattr(ctx, "repair_boundary_pending", {}),
        effective_section_size=ctx.effective_section_size,
        refinement_order=ctx.refinement_order,
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
    saved_order = str(payload.get("refinement_order") or "top-down")
    if saved_order != ctx.refinement_order:
        _log(
            "resume: discarded generated state because refinement order changed "
            f"from {saved_order} to {ctx.refinement_order}"
        )
        _record(
            ctx.telemetry,
            "resume_state_rejected",
            reason="refinement_order_changed",
            saved_order=saved_order,
            requested_order=ctx.refinement_order,
        )
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
    raw_local_partitions = scheduler.get("local_group_partitions") or {}
    ctx.local_group_partitions = {
        str(label): {
            "partition_id": str(entry.get("partition_id") or ""),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "statement_fps": {
                str(item): str(fp)
                for item, fp in (entry.get("statement_fps") or {}).items()
            },
            "group": [str(item) for item in entry.get("group") or []],
        }
        for label, entry in raw_local_partitions.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and all(
            ctx.stmt_fps.get(str(item)) == str(fp)
            for item, fp in (entry.get("statement_fps") or {}).items()
        )
    }
    raw_feedback = scheduler.get("generation_feedback") or {}
    ctx.generation_feedback = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "source": str(entry.get("source") or "unknown"),
        }
        for label, entry in raw_feedback.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and str(entry.get("evidence") or "").strip()
    }
    raw_candidates = scheduler.get("generation_candidates") or {}
    ctx.generation_candidates = {
        str(label): {
            "candidate_state_version": int(
                entry.get("candidate_state_version") or 0
            ),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "plan_fp": str(entry.get("plan_fp") or ""),
            "code": str(entry.get("code") or "")[:45000],
            "source": str(entry.get("source") or "unknown"),
            "reusable_uncompiled": _candidate_is_reusable_uncompiled(entry),
            "generation_tier": str(entry.get("generation_tier") or "base"),
            "repair_stage": str(entry.get("repair_stage") or "generated"),
            "imports": [str(item) for item in entry.get("imports") or []],
            "preamble": [str(item) for item in entry.get("preamble") or []],
            "component_labels": [
                str(item) for item in entry.get("component_labels") or [label]
            ],
            "required_dependencies": [
                str(item) for item in entry.get("required_dependencies") or []
            ],
            "candidate_hash": str(entry.get("candidate_hash") or ""),
            "deterministic_obligations": [
                str(item) for item in entry.get("deterministic_obligations") or []
            ],
            "satisfied_obligations": [
                str(item) for item in entry.get("satisfied_obligations") or []
            ],
            "deterministic_violations": [
                str(item) for item in entry.get("deterministic_violations") or []
            ],
            "deterministic_findings": [
                str(item)[-4000:]
                for item in entry.get("deterministic_findings") or []
            ],
            "lean_status": str(entry.get("lean_status") or "unknown"),
            "lean_output": str(entry.get("lean_output") or "")[-12000:],
            "lean_output_sha256": str(
                entry.get("lean_output_sha256") or ""
            ),
            "lean_error_count": int(entry.get("lean_error_count") or 0),
            "semantic_status": str(
                entry.get("semantic_status") or "unknown"
            ),
            "semantic_evidence": str(
                entry.get("semantic_evidence") or ""
            )[-12000:],
            "semantic_evidence_sha256": str(
                entry.get("semantic_evidence_sha256") or ""
            ),
            "base_attempted": bool(entry.get("base_attempted")),
            "escalation_attempted": bool(entry.get("escalation_attempted")),
            "revision": int(entry.get("revision") or 1),
            "rejected_transitions": [
                dict(item)
                for item in (entry.get("rejected_transitions") or [])[-12:]
                if isinstance(item, dict)
            ],
            "working_candidate": (
                _working_candidate_payload(entry["working_candidate"])
                if isinstance(entry.get("working_candidate"), dict)
                and str(entry["working_candidate"].get("code") or "").strip()
                else {}
            ),
        }
        for label, entry in raw_candidates.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and str(entry.get("code") or "").strip()
    }
    raw_lifecycle = scheduler.get("retry_lifecycle") or {}
    ctx.retry_lifecycle = {
        str(key): {
            "label": str(entry.get("label") or ""),
            "stage": str(entry.get("stage") or ""),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "state": str(entry.get("state") or "base"),
            "last_tier": str(entry.get("last_tier") or "base"),
            "failures": int(entry.get("failures") or 0),
            "source": str(entry.get("source") or "unknown"),
            "evidence_sha256": str(entry.get("evidence_sha256") or ""),
        }
        for key, entry in raw_lifecycle.items()
        if isinstance(entry, dict)
        and str(entry.get("label") or "") in ctx.nodes
        and str(entry.get("statement_fp") or "")
        == ctx.stmt_fps.get(str(entry.get("label") or ""))
    }
    raw_boundary = scheduler.get("repair_boundary_pending") or {}
    boundary_labels = [
        str(label)
        for label in raw_boundary.get("labels") or []
        if str(label) in ctx.nodes
        and str((raw_boundary.get("statement_fps") or {}).get(str(label)) or "")
        == ctx.stmt_fps.get(str(label))
    ]
    ctx.repair_boundary_pending = (
        {
            "mode": str(raw_boundary.get("mode") or "audit"),
            "labels": boundary_labels,
            "statement_fps": {
                label: ctx.stmt_fps[label] for label in boundary_labels
            },
            "previous_statements": {
                label: str((raw_boundary.get("previous_statements") or {}).get(label) or "")[:6000]
                for label in boundary_labels
            },
            "evidence": str(raw_boundary.get("evidence") or "")[-12000:],
            "repair_labels": [
                str(label)
                for label in raw_boundary.get("repair_labels") or []
                if str(label) in ctx.nodes
            ],
            "required_dependencies": {
                str(label): {
                    str(dep)
                    for dep in dependencies
                    if str(dep) in ctx.nodes and str(dep) != str(label)
                }
                for label, dependencies in (
                    raw_boundary.get("required_dependencies") or {}
                ).items()
                if str(label) in ctx.nodes
            },
            "decomposition_helpers": [
                str(item)[:2000]
                for item in raw_boundary.get("decomposition_helpers") or []
                if str(item).strip()
            ],
        }
        if boundary_labels
        else {}
    )
    raw_plan = scheduler.get("design_plan_entries") or {}
    ctx.design_plan_entries = {
        str(label): {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "target_signature": str(entry.get("target_signature") or "")[:12000],
            "helpers": [
                {
                    "name": str(helper.get("name") or "")[:500],
                    "kind": str(helper.get("kind") or "")[:40],
                    "declaration": str(helper.get("declaration") or "")[:12000],
                    "members": [
                        {
                            "name": str(member.get("name") or "")[:500],
                            "type": str(member.get("type") or "")[:4000],
                        }
                        for member in helper.get("members") or []
                        if isinstance(member, dict)
                        and str(member.get("name") or "").strip()
                        and str(member.get("type") or "").strip()
                    ],
                    "required_members": [
                        str(item)[:500]
                        for item in helper.get("required_members") or []
                    ],
                    "purpose": str(helper.get("purpose") or "")[:2000],
                }
                for helper in entry.get("helpers") or []
                if isinstance(helper, dict)
                and str(helper.get("name") or "").strip()
                and str(helper.get("kind") or "").strip()
            ],
            "decisions": [
                str(item)[:4000]
                for item in entry.get("decisions") or []
                if str(item).strip()
            ],
            "audit_fp": str(entry.get("audit_fp") or ""),
            "rejected_audit_fp": str(entry.get("rejected_audit_fp") or ""),
            "rejected_kind": str(entry.get("rejected_kind") or ""),
            "rejected_reason": str(entry.get("rejected_reason") or "")[-12000:],
            "rejected_helpers": [
                str(item)[:2000] for item in entry.get("rejected_helpers") or []
            ],
            "correction_base_fp": str(entry.get("correction_base_fp") or ""),
            "correction_escalation_fp": str(
                entry.get("correction_escalation_fp") or ""
            ),
            "semantic_revision_count": int(
                entry.get("semantic_revision_count") or 0
            ),
            "closure_fp": str(entry.get("closure_fp") or ""),
            "closure_wave_id": str(entry.get("closure_wave_id") or ""),
            "origin": str(entry.get("origin") or ""),
        }
        for label, entry in raw_plan.items()
        if isinstance(entry, dict)
        and int(entry.get("schema_version") or 0) == DESIGN_PLAN_SCHEMA_VERSION
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and str(entry.get("target_signature") or "").strip()
    }
    raw_semantic_plan = scheduler.get("semantic_plan_entries") or {}
    ctx.semantic_plan_entries = {
        str(label): {
            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "representation": str(entry.get("representation") or "")[:600],
            "vocabulary": [
                {
                    "name": str(item.get("name") or "")[:500],
                    "purpose": str(item.get("purpose") or "")[:240],
                }
                for item in entry.get("vocabulary") or []
                if isinstance(item, dict)
                and str(item.get("name") or "").strip()
            ][:8],
            "obligations": [
                str(item)[:320]
                for item in entry.get("obligations") or []
                if str(item).strip()
            ][:6],
            "provider_requirements": [
                {
                    "provider": str(item.get("provider") or ""),
                    "capabilities": [
                        str(value)[:240]
                        for value in item.get("capabilities") or []
                        if str(value).strip()
                    ][:8],
                }
                for item in entry.get("provider_requirements") or []
                if isinstance(item, dict)
                and str(item.get("provider") or "")
                in _statement_uses(ctx.nodes[str(label)])
            ],
            "fallback": bool(entry.get("fallback")),
        }
        for label, entry in raw_semantic_plan.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and int(entry.get("schema_version") or 0)
        == SEMANTIC_PLAN_SCHEMA_VERSION
        and str(entry.get("statement_fp") or "")
        == ctx.stmt_fps.get(str(label))
    }
    raw_alternates = scheduler.get("design_plan_alternates") or {}
    ctx.design_plan_alternates = _parse_design_plan_entries(
        ctx,
        raw_alternates,
        json.dumps(
            {
                "contracts": [
                    {
                        "label": str(label),
                        "target_signature": str(entry.get("target_signature") or ""),
                        "helpers": entry.get("helpers") or [],
                        "decisions": entry.get("decisions") or [],
                    }
                    for label, entry in raw_alternates.items()
                    if isinstance(entry, dict)
                    and int(entry.get("schema_version") or 0)
                    == DESIGN_PLAN_SCHEMA_VERSION
                    and str(entry.get("statement_fp") or "")
                    == ctx.stmt_fps.get(str(label))
                ]
            }
        ),
    )
    raw_direct_generation = scheduler.get("blueprint_direct_generation") or {}
    ctx.blueprint_direct_generation = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "source": str(entry.get("source") or "unknown")[:200],
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "activations": max(1, int(entry.get("activations") or 1)),
        }
        for label, entry in raw_direct_generation.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "")
        == ctx.stmt_fps.get(str(label))
    }
    _sync_design_plan(ctx)
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
        entry_provisional = bool(entry.get("provisional_environment", False))
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
            if ok and not entry_provisional:
                ok, _output = _check_lean(path, lean_command)
            if ok:
                detail = (
                    "name-complete provisional boilerplate"
                    if entry_provisional
                    else "recompiled clean"
                )
                _log(f"resume: salvaged modified section {path.name} ({detail})")
        if not ok:
            dropped_labels.update(labels)
            dropped_modules.add(str(entry.get("module") or ""))
            _discard_section_artifacts(path)
            continue
        sec = Section(
            number=int(entry.get("number") or 0),
            labels=labels,
            path=path,
            module=str(entry.get("module") or ""),
            import_modules=[str(m) for m in entry.get("import_modules") or []],
            deferred=entry_deferred,
            refined_labels=(
                {str(label) for label in entry.get("refined_labels") or []}
                if "refined_labels" in entry
                and entry.get("refined_labels") is not None
                else None
            ),
            provisional_environment=entry_provisional,
            generation_tier=str(entry.get("generation_tier") or "unknown"),
        )
        if sec.deferred:
            _discard_section_objects(path)
        elif (
            not sec.provisional_environment
            and (
                not path.with_suffix(".olean").is_file()
                or not _lake_olean_path(path).is_file()
            )
        ):
            attempt = _compile_module_olean(path, lean_command)
            if not attempt.ok:
                dropped_labels.update(labels)
                dropped_modules.add(sec.module)
                _discard_section_artifacts(path)
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
    owned = {sec.path.resolve() for sec in kept}
    owned |= {sec.path.with_suffix(".olean").resolve() for sec in kept}
    owned_lake = {_lake_olean_path(sec.path).resolve() for sec in kept}
    removed: list[str] = []
    if generated_dir.is_dir():
        for pattern in ("Chunk*.lean", "Chunk*.olean", "Skeleton*.lean", "Skeleton*.olean"):
            for artifact in sorted(generated_dir.glob(pattern)):
                if artifact.resolve() in owned:
                    continue
                if artifact.suffix == ".lean":
                    _discard_section_artifacts(artifact)
                else:
                    with contextlib.suppress(FileNotFoundError, OSError):
                        artifact.unlink()
                removed.append(artifact.name)
    lake_dir = _generated_lake_module_dir(ctx.name)
    if lake_dir.is_dir():
        for pattern in ("Chunk*.olean", "Skeleton*.olean"):
            for artifact in sorted(lake_dir.glob(pattern)):
                if artifact.resolve() in owned_lake:
                    continue
                with contextlib.suppress(FileNotFoundError, OSError):
                    artifact.unlink()
                    removed.append(f"lake-build/{artifact.name}")
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
        label
        for sec in sections
        if not sec.deferred
        for label in (
            sec.labels if sec.refined_labels is None else sec.refined_labels
        )
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
        refined = set(sec.labels) if sec.refined_labels is None else sec.refined_labels
        for label in refined:
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
        statement_dependencies = _statement_uses(ctx.nodes[label])
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
            scope = "statement interface" if dep in statement_dependencies else "proof only"
            lines.append(f"- {label} -> {dep} ({scope}): {ownership}")
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


def _statement_uses(node: Node) -> set[str]:
    """Dependencies that belong in the node's public declaration.

    Older tests and persisted in-memory callers construct ``Node`` with only
    ``uses``.  Fall back to that union only when no scoped information exists.
    """
    statement = set(getattr(node, "statement_uses", set()))
    proof = set(getattr(node, "proof_uses", set()))
    if statement or proof:
        return statement
    return set(node.uses)


def _proof_uses(node: Node) -> set[str]:
    return set(getattr(node, "proof_uses", set()))


def _transitive_statement_dependencies(
    nodes: dict[str, Node], label: str
) -> set[str]:
    """Public-interface dependency closure, excluding proof-only edges."""
    found: set[str] = set()
    node = nodes.get(label)
    stack = list(_statement_uses(node)) if node is not None else []
    while stack:
        dep = stack.pop()
        if dep in found:
            continue
        found.add(dep)
        if dep in nodes:
            stack.extend(_statement_uses(nodes[dep]))
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
    """Changed contracts outside a target's dependency/decomposition scope.

    Existing downstream consumers remain immutable during a Phase 1 repair.
    This general scope check permits connected additions so ordinary repairs
    can be validated transactionally. Confirmed decomposition receives the
    stricter ``_decomposition_orientation_findings`` check as well: every new
    helper must be an actual dependency of the rejected target.
    """
    allowed = _upstream_contract_closure(before, targets) | _upstream_contract_closure(
        after, targets
    )
    added = set(after) - set(before)
    connected = set(targets)
    pending = set(added)
    while pending:
        newly_connected = {
            label
            for label in pending
            if set(after[label].uses) & connected
        }
        if not newly_connected:
            break
        allowed.update(newly_connected)
        connected.update(newly_connected)
        pending -= newly_connected
    return {label for label in changed if label not in allowed}


def _decomposition_orientation_findings(
    before: dict[str, Node],
    after: dict[str, Node],
    roots: Iterable[str],
) -> list[str]:
    """Reject new decomposition helpers placed on the consumer side.

    A helper introduced to state or prove a rejected contract must be in that
    contract's dependency closure. Otherwise the original node cannot use it;
    adding the reverse edge later either leaves dead scaffolding or creates the
    cycle observed in the Simplex run.
    """
    root_set = {label for label in roots if label in after}
    added = set(after) - set(before)
    if not root_set or not added:
        return []
    root_closures = {
        root: _transitive_dependencies(after, root) for root in root_set
    }
    findings: list[str] = []
    for helper in sorted(added):
        owners = sorted(
            root for root, closure in root_closures.items() if helper in closure
        )
        if owners:
            continue
        reverse = sorted(
            root
            for root in root_set
            if root in _transitive_dependencies(after, helper)
        )
        if reverse:
            findings.append(
                f"new helper `{helper}` depends on repaired target(s) "
                f"{', '.join(reverse)} instead of being their dependency"
            )
        else:
            findings.append(
                f"new helper `{helper}` is not in the dependency closure of "
                f"any repaired target ({', '.join(sorted(root_set))})"
            )
    return findings


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


# Terminal tactic/sorry body on a declaration; everything before it is the
# frozen public type. Phase 1 may defer theorem proofs and typed def/abbrev
# implementations using this exact shape.
_TERMINAL_PROOF_RE = re.compile(r":=\s*(?:by\b[\s\S]*|sorry\s*)\Z")
# Per-declaration cap for definition-kind interface text. Generated skeleton
# bodies are one-node-sized, so this triggers rarely; it exists so one huge
# body cannot evict whole modules from the digest budget.
_INTERFACE_DECL_CAP = 2400

FROZEN_INTERFACE_NOTE = """\
This interface listing is generated deterministically from the frozen skeleton
files and is COMPLETE for the modules it covers — including structure fields,
declaration headers, and completed definition bodies when available. Do NOT
spend budget re-reading Skeleton*.lean or any
generated Lean files to rediscover names, signatures, or fields: everything
referenceable is below. It is an interface reference ONLY. The blueprint TeX
is the sole mathematical source of truth, and the Lean you write exists to
certify the blueprint — not to be self-consistent Lean on its own terms.
Derive every statement 1-1 from the blueprint node text; use this interface
solely to spell frozen dependencies with their exact names, types, and fields.
If this interface ever seems to conflict with the blueprint, follow the
blueprint and surface the mismatch — never adapt the mathematics to the Lean."""


def _decl_interface_text(decl) -> str:
    """Return the useful frozen interface for one declaration.

    Theorem proofs and deferred def/abbrev bodies are omitted. Completed
    definition bodies remain visible because they carry definitional meaning.
    """
    text = decl.text.strip()
    if decl.kind in {"theorem", "lemma"} or (
        decl.kind in {"def", "abbrev"} and _has_terminal_sorry(text)
    ):
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


PHASE1_DEPENDENCY_CONTEXT_BUDGET = 10000


def _minimal_dependency_interface(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    modules: list[str],
    *,
    local_code: str = "",
    budget: int | None = PHASE1_DEPENDENCY_CONTEXT_BUDGET,
) -> str:
    """Return the smallest complete generated interface needed by ``labels``.

    Start from direct non-Mathlib ``uses`` dependencies outside the target
    group. Include their exact frozen declarations, then include only generated
    declarations referenced by those interfaces. The final name-set comparison
    is the deterministic completeness gate: a model call is never launched
    with an advertised generated dependency silently absent from its context.

    ``budget`` is a soft batching target, not a correctness limit. The Phase-1
    scheduler partitions ordinary multi-node groups before prompt construction.
    An atomic component or singleton whose genuinely minimal interface is still
    larger must receive that complete interface; omitting it or terminating the
    autonomous run would both be incorrect.
    """
    target_set = set(labels)
    required = {
        dep
        for label in labels
        for dep in ctx.nodes.get(label, Node(label, "", Path("."), 0)).uses
        if dep in ctx.nodes and not ctx.nodes[dep].mathlibok and dep not in target_set
    }
    if not required:
        return ""

    local_names = set(_lean_declarations(local_code)) if local_code.strip() else set()
    sources: list[str] = []
    seen_paths: set[Path] = set()
    for sec in sections:
        if sec.module not in modules or sec.path in seen_paths or not sec.path.is_file():
            continue
        seen_paths.add(sec.path)
        sources.append(sec.path.read_text(encoding="utf-8"))
    # A section list can represent only the current scheduling frontier. Module
    # names still map deterministically to generated source paths, so recover
    # their interfaces without asking the model to inspect the repository.
    for module in modules:
        path = REPO_ROOT / (module.replace(".", "/") + ".lean")
        if path in seen_paths or not path.is_file():
            continue
        seen_paths.add(path)
        sources.append(path.read_text(encoding="utf-8"))

    declarations = {}
    for source in sources:
        declarations.update(_lean_declarations(source))
    label_by_name = {
        _lean_name(label): label
        for label, node in ctx.nodes.items()
        if not node.mathlibok
    }

    queue = list(sorted(required))
    included: dict[str, str] = {}
    missing: set[str] = set()
    while queue:
        label = queue.pop(0)
        if label in included or _lean_name(label) in local_names:
            continue
        lean_name = _lean_name(label)
        decl = declarations.get(lean_name)
        if decl is None:
            missing.add(label)
            continue
        text = _decl_interface_text(decl)
        included[label] = text
        for referenced_name, referenced_label in label_by_name.items():
            if (
                referenced_label not in target_set
                and referenced_label not in included
                and re.search(rf"(?<![A-Za-z0-9_']){re.escape(referenced_name)}(?![A-Za-z0-9_'])", text)
            ):
                queue.append(referenced_label)

    unresolved = sorted(
        label for label in required if label not in included and _lean_name(label) not in local_names
    )
    unresolved.extend(sorted(missing - set(unresolved)))
    if unresolved:
        raise ValueError(
            "generated dependency context is incomplete for "
            + ", ".join(labels)
            + ": missing "
            + ", ".join(dict.fromkeys(unresolved))
        )

    blocks: list[str] = []
    for label in sorted(included):
        block = f"-- {label}\n{included[label]}"
        blocks.append(block)
    return "\n\n".join(blocks)


def _phase1_dependency_interface_chars(
    ctx: Ctx, labels: list[str], sections: list[Section]
) -> int:
    """Measure the complete frozen dependency interface for one candidate group."""
    modules = _sections_for_deps(ctx, labels, sections)
    return len(
        _minimal_dependency_interface(
            ctx,
            labels,
            sections,
            modules,
            budget=None,
        )
    )


def _phase1_context_atomic_units(ctx: Ctx, group: list[str]) -> list[list[str]]:
    """Keep persisted shared-helper candidate components indivisible."""
    available = set(group)
    emitted: set[str] = set()
    units: list[list[str]] = []
    for label in group:
        if label in emitted:
            continue
        component = set(_candidate_component_labels(ctx, label, available))
        unit = [item for item in group if item in component and item not in emitted]
        if not unit:
            unit = [label]
        units.append(unit)
        emitted.update(unit)
    return units


def _partition_phase1_groups_by_dependency_context(
    ctx: Ctx,
    groups: list[list[str]],
    sections: list[Section],
    *,
    budget: int = PHASE1_DEPENDENCY_CONTEXT_BUDGET,
) -> list[list[str]]:
    """Split candidate groups at the complete dependency-context boundary.

    The operation is deterministic and model-free. It greedily preserves the
    largest prefix whose exact generated dependency interface fits the soft
    budget. Persisted shared-helper components remain atomic; if such a unit or
    a singleton exceeds the budget, prompt construction receives its complete
    interface and telemetry records the unavoidable overage.
    """
    partitioned: list[list[str]] = []
    for original in groups:
        if not original:
            continue
        try:
            parts: list[list[str]] = []
            current: list[str] = []
            for unit in _phase1_context_atomic_units(ctx, original):
                trial = current + unit
                trial_chars = _phase1_dependency_interface_chars(
                    ctx, trial, sections
                )
                if current and trial_chars > budget:
                    parts.append(current)
                    current = list(unit)
                else:
                    current = trial
            if current:
                parts.append(current)

            sizes = [
                _phase1_dependency_interface_chars(ctx, part, sections)
                for part in parts
            ]
        except ValueError as exc:
            # This pre-dispatch pass is only a batching optimization. Synthetic
            # replay states and a temporarily deferred section may not expose a
            # readable interface yet. Preserve the original group and let the
            # existing prompt-construction completeness gate make the
            # authoritative decision when generation actually starts.
            _record(
                ctx.telemetry,
                "phase1_dependency_context_partition_deferred",
                labels=original,
                soft_budget=budget,
                reason=str(exc),
            )
            partitioned.append(original)
            continue
        if len(parts) > 1:
            _log(
                "  dependency context partitioned "
                f"{len(original)} node(s) into "
                + " + ".join(str(len(part)) for part in parts)
                + f" (soft limit {budget} chars)"
            )
            _record(
                ctx.telemetry,
                "phase1_dependency_context_partitioned",
                labels=original,
                groups=parts,
                interface_chars=sizes,
                soft_budget=budget,
            )
        for part, size in zip(parts, sizes):
            if size > budget:
                _record(
                    ctx.telemetry,
                    "phase1_dependency_context_soft_overflow",
                    labels=part,
                    interface_chars=size,
                    soft_budget=budget,
                    reason="atomic_component_or_singleton",
                )
        partitioned.extend(parts)
    return partitioned


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


def _design_plan_rules(ctx: Ctx, labels: list[str]) -> str:
    """Rules for JSON interface planning, without generation-only output modes."""
    unavailable = ""
    if ctx.unavailable_imports:
        unavailable = (
            "\nUnavailable imports (do not reference declarations from these):\n"
            + "\n".join(f"- {item}" for item in sorted(ctx.unavailable_imports))
        )
    library_block = _library_context_for(ctx, labels)
    return f"""Plan constraints:
- Return JSON only and include exactly one contract for every requested label.
- The blueprint TeX is the only mathematical source of truth. Preserve the
  same objects, parameters, hypotheses, and claim without weakening or
  strengthening it.
- Use each node's required generated Lean name. Mathlib-owned dependencies use
  their settled external declarations from the dependency table.
- `target_signature` describes one top-level public declaration but contains
  no body, proof, `sorry`, `axiom`, `constant`, or `opaque` declaration.
- Helpers may only be structure, inductive, or class type interfaces owned by
  that contract. Do not invent helper definitions or theorem declarations.
- Do not return Lean code blocks, prose outside the JSON object, or any
  alternate output format. Missing interface structure must be represented in
  the contract's helper surface and decisions; later deterministic and semantic
  gates decide whether blueprint decomposition is required.
{unavailable}

Local Lean library candidates (module paths verified by deterministic search):
{library_block or "- none found"}

Lean API idioms:
{LEAN_IDIOM_CHEATSHEET}"""


def _initial_declaration_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    timeout_s: int,
    feedback: str = "",
    previous_code: str = "",
) -> str:
    """Ask only for the provisional environment needed to start Phase 1.

    This is deliberately not a statement-acceptance prompt. Signatures must be
    faithful enough for consumers to elaborate, but every body and proof stays
    provisional until root-first Phase 1 validates and replaces it.
    """
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:3500]}\n```"
        for label in labels
    )
    signatures = _frozen_interface_digest(
        sections, import_modules, budget=14000
    )
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    feedback_block = ""
    if feedback:
        feedback_block = f"""

The previous provisional file did not compile. Correct only its declaration
syntax/types using this compiler output; do not start mathematical refinement:
```text
{feedback[-10000:]}
```

Previous provisional file:
```lean
{previous_code[:160000] or '-- unavailable'}
```
"""
    unavailable = ""
    if ctx.unavailable_imports:
        unavailable = (
            "\nDo not import these unavailable modules:\n"
            + "\n".join(f"- {item}" for item in sorted(ctx.unavailable_imports))
        )
    return f"""TASK: INITIAL-LEAN-DECLARATION-ENVIRONMENT

Return exactly one Lean 4 file in one code block. No commentary.

This is compilation scaffolding before mathematical statement refinement.
Create every requested Lean name with a faithful provisional type/signature so
that declarations which consume it can elaborate later. Do not prove or fully
implement anything in this call:
- theorem-like nodes must end in `:= by sorry`;
- use the Lean command `theorem` for every theorem-like node, including
  blueprint corollaries, claims, facts, and remarks; never emit `corollary`;
- definition-like nodes must expose the objects, fields, parameters, and result
  type described by the blueprint, but their body may also be `:= by sorry`;
- structures/inductives may be used when their named fields are required by
  consumers; otherwise prefer a typed `def ... := by sorry`;
- never use `axiom`, `constant`, `opaque`, `admit`, `True`, or a placeholder
  type that erases the node's parameters or mathematical role;
- use the exact generated name listed for every target and visibly use the
  supplied generated names for direct dependencies;
- emit every target. Never return NEEDS-DECOMPOSITION from this pass: missing
  helpers and exact contract corrections belong to Phase 1;
- do not attempt proofs, inspect the repository, run Lean, or search Mathlib.
  Use the verified imports and interfaces supplied below and spend the budget
  emitting complete code.

The blueprint remains the source of truth, but these declarations are
provisional: the pipeline will not count them as accepted or proved. Phase 1
will deterministically check, compile, audit, and freeze their exact contracts
from roots down toward dependencies.

This call has a wall-clock budget of about {timeout_s}s.
{unavailable}
{feedback_block}

Blueprint name: {ctx.name}

Available imports for declarations already emitted:
```lean
{chr(10).join(f'import {m}' for m in import_modules) or '-- none'}
```

Available provisional interfaces (use these names; do not redefine them):
```lean
{signatures or '-- none'}
```

Resolved direct dependency ownership:
```text
{dependency_contracts}
```

Target nodes for this provisional file, in dependency order:
{target_text}
"""


def _skeleton_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    feedback: str = "",
    previous_code: str = "",
    timeout_s: int = 0,
    initial_only: bool = False,
) -> str:
    if initial_only:
        return _initial_declaration_prompt(
            ctx,
            labels,
            sections,
            import_modules,
            timeout_s=timeout_s,
            feedback=feedback,
            previous_code=previous_code,
        )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
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
    signatures = _minimal_dependency_interface(
        ctx,
        labels,
        sections,
        import_modules,
        local_code=previous_code,
        budget=10000,
    )
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    return f"""TASK: BLUEPRINT-SKELETON-SECTION

Return exactly one Lean 4 file (one code block). No commentary.

Generate ONE declaration per target node listed below — statements only:
- definition-kind nodes (definition/defn/construction/notation/convention):
  emit the exact public type/interface. A `def` or `abbrev` body must end in
  `:= sorry`; Phase 2 implements it. A `structure`/`inductive` interface must
  list its real fields/constructors and cannot use `sorry`. The one narrow
  exception is a type-valued target whose complete contract is a plan-owned
  structure/class/inductive: emit that helper completely and make the target a
  transparent alias such as `def target (n) : Type := OwnedInterface n`;
- theorem-like nodes (lemma/proposition/theorem/corollary and EVERY other
  environment kind, e.g. claim/fact/remark): the exact statement as a
  `theorem` ending in `:= sorry`. Do NOT attempt proofs at this phase: a
  partial or failing tactic block is rejected deterministically and wastes
  the whole call. The ONLY exception is a complete single-tactic closer you
  are certain of (e.g. `:= rfl`); when in any doubt, use `:= sorry`. If a
  proof attempt is unfinished when your budget runs short, replace it with
  `:= sorry` before replying. Never encode a theorem-like node as a bare
  `def : Prop`.
- Emit no auxiliary `def`, `abbrev`, theorem, lemma, or instance declarations.
  A structural helper may be emitted only when needed to state a requested
  target. Return its complete typed declaration together with that target;
  this same Lean response becomes the persisted typed contract. A genuinely
  separate mathematical obligation requires `NEEDS-DECOMPOSITION`.
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

Minimal generated dependency interface (deterministically complete for the
target nodes; use these exact names and do not inspect generated files):
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

{_design_plan_block(ctx, labels)}

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
    provisional_only: bool = False,
) -> str:
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:5000]}\n```"
        for label in patch_labels
    )
    relevant = [
        finding
        for finding in findings
        if finding.label in set(patch_labels) or finding.lean_name in {_lean_name(label) for label in patch_labels}
    ]
    signatures = _minimal_dependency_interface(
        ctx,
        patch_labels,
        sections,
        import_modules,
        local_code=module_code,
        budget=8000,
    )
    provisional_rule = (
        "Repair the signature/type only. The body of a target `def`/`abbrev` "
        "and the proof of a target theorem must end in `:= sorry`; Phase 2 "
        "implements them. Structure/inductive fields and constructors must be exact. "
        "A type-valued target may instead be a transparent alias directly to its "
        "same-node plan-owned structural interface; that alias is the public type "
        "contract, not a Phase-2 implementation."
    )
    planned_helpers = _planned_helper_specs(ctx, patch_labels)
    helper_rule = (
        "No plan-owned auxiliary type interface is required for these targets."
        if not planned_helpers
        else
        "The only permitted auxiliary declarations are these exact plan-owned "
        "type interfaces; emit a complete replacement for any one named by a "
        "finding:\n"
        + "\n".join(
            f"  - {helper.get('kind')} {helper.get('name')} (owner {label}):\n"
            + "\n".join(
                f"      {member.get('name')} : {member.get('type')}"
                for member in helper.get("members") or []
            )
            for label, helper in planned_helpers
        )
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
- {provisional_rule}
- Target theorem-like nodes and ordinary target `def`/`abbrev` bodies must end
  with terminal `:= sorry`; retain the transparent structural-alias exception
  described above.
- Use the Lean command `theorem` for theorem-like nodes; never use `corollary`.
- If a finding concerns a partial or failing proof on a theorem-like node,
  replace that proof with terminal `:= sorry` — do not try to complete it;
  proofs are a later phase.
- The replacement statement must still encode the same blueprint node. Do not
  weaken, abstract away, or replace it with `True`.
- If a replacement must use another blueprint node listed in `uses`, visibly
  mention that node's generated Lean name.
- {helper_rule}
- Do not emit any helper `def`, `abbrev`, theorem, lemma, or instance beyond
  the exact plan-owned interfaces named above.
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

Minimal generated dependency interface (deterministically complete for the
target declarations; do not inspect generated files):
```lean
{signatures or '-- none'}
```

{_design_plan_block(ctx, patch_labels, budget=4000)}

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


def _isolated_deterministic_failure_labels(
    findings: list[SkeletonFinding], labels: list[str]
) -> list[str]:
    """Return an attributable proper subset, or empty for section-wide failures."""
    if any(finding.label is None for finding in findings):
        return []
    label_set = set(labels)
    failed = {finding.label for finding in findings if finding.label in label_set}
    if not failed or failed == label_set:
        return []
    return [label for label in labels if label in failed]


def _apply_skeleton_replacements(
    parsed: ParsedModule,
    labels: list[str],
    patch_labels: list[str],
    replacement_code: str,
    explicit_owner_by_name: dict[str, str] | None = None,
    required_helper_replacements: set[str] | None = None,
    unavailable_imports: set[str] | None = None,
) -> ParsedModule | None:
    """Merge replacement declarations into a generated section.

    The section remains a section: this only swaps or inserts declarations for
    the listed target labels. Accepted plan-owned helper interfaces are stable
    state: a target-only correction preserves them unless the response replaces
    them explicitly. Unplanned helpers still belong to the target replacement
    transaction and are discarded when omitted. The caller re-runs the
    deterministic audit on the whole module before freezing.
    """
    patch_parsed = _parse_module(replacement_code)
    target_names = {_lean_name(label) for label in labels}
    patch_names = {_lean_name(label) for label in patch_labels}
    replacements = {decl.name: decl for decl in patch_parsed.decls if decl.name in patch_names}
    if set(replacements) != patch_names:
        return None

    original = list(parsed.decls)
    original_names = {decl.name for decl in original if decl.name}
    label_by_name = {_lean_name(label): label for label in labels}
    original_consumers = _declaration_target_consumers(
        parsed, label_by_name, explicit_owner_by_name
    )
    patch_label_set = set(patch_labels)
    replaceable_helper_names = {
        decl.name
        for index, decl in enumerate(original)
        if decl.name
        and decl.name not in target_names
        and original_consumers.get(index, set())
        and original_consumers[index] <= patch_label_set
    }
    planned_helper_names = set(explicit_owner_by_name or {})
    returned_helper_names = {
        decl.name
        for decl in patch_parsed.decls
        if decl.name and decl.name not in patch_names and decl.name not in target_names
    }
    if not set(required_helper_replacements or {}) <= returned_helper_names:
        return None
    helper_decls = [
        decl
        for decl in patch_parsed.decls
        if decl.name
        and decl.name not in patch_names
        and decl.name not in target_names
        and (
            decl.name not in original_names
            or decl.name in replaceable_helper_names
        )
    ]

    helper_inserted = False
    used_replacements: set[str] = set()
    new_decls: list[DeclBlock] = []
    for index, decl in enumerate(original):
        # Unplanned local helpers belong to the target replacement transaction.
        # Plan-owned interfaces are different: once accepted, correcting only
        # the target must not silently delete them. An explicitly returned
        # replacement still supersedes the old interface below.
        if (
            decl.name not in patch_names
            and decl.name not in target_names
            and original_consumers.get(index, set())
            and original_consumers[index] <= patch_label_set
        ):
            if (
                decl.name in planned_helper_names
                and decl.name not in returned_helper_names
            ):
                new_decls.append(decl)
            continue
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

    # Lean declaration names are module-global. Keep the first declaration for
    # every name, not just current targets: a model may repeat an existing
    # dependency as a "helper", and retaining it poisons every later retry.
    seen_names: set[str] = set()
    deduped: list[DeclBlock] = []
    for decl in new_decls:
        if decl.name:
            if decl.name in seen_names:
                continue
            seen_names.add(decl.name)
        deduped.append(decl)
    merged_imports = list(dict.fromkeys(parsed.imports + patch_parsed.imports))
    missing_imports = set(_missing_olean_imports(merged_imports))
    if unavailable_imports is not None:
        unavailable_imports.update(missing_imports)
    return ParsedModule(
        # Import validation belongs after the merge. Validating only the patch
        # response is too late: the merge has already copied those imports into
        # the persistent skeleton, where they poison every subsequent retry.
        imports=[item for item in merged_imports if item not in missing_imports],
        preamble=list(dict.fromkeys(parsed.preamble + patch_parsed.preamble)),
        decls=deduped,
    )


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
    provisional_only: bool = False,
    escalate_timeout: bool = True,
) -> tuple[ParsedModule | None, str]:
    patch_labels = _patchable_skeleton_labels(findings, labels)
    if not patch_labels:
        return None, "not patchable"
    _log(
        "  targeted check isolated "
        + f"{len(patch_labels)} declaration(s); patching: "
        + ", ".join(patch_labels)
    )
    try:
        prompt = _targeted_skeleton_patch_prompt(
            ctx,
            patch_labels,
            sections,
            import_modules,
            module_code,
            findings,
            timeout_s=timeout,
            provisional_only=provisional_only,
        )
    except ValueError as exc:
        return None, f"targeted declaration context check failed: {exc}"
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
    if (
        result.status == "timeout"
        and not escalated
        and escalate_timeout
        and len(patch_labels) == 1
    ):
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
        canonical = _ingest_model_lean(ctx, patch_labels, result.text)
    except ValueError as exc:
        return None, f"targeted declaration patch did not return Lean code: {exc}"
    replacement_parsed = canonical.parsed
    replacement_code, _ = _compose_module(
        replacement_parsed.imports,
        replacement_parsed.preamble,
        [decl.text for decl in replacement_parsed.decls],
    )
    planned_helper_owners = _planned_helper_owner_by_name(ctx, labels)
    required_helper_replacements = {
        finding.lean_name
        for finding in findings
        if finding.lean_name in planned_helper_owners
        and planned_helper_owners[finding.lean_name] in set(patch_labels)
    }
    patched = _apply_skeleton_replacements(
        parsed,
        labels,
        patch_labels,
        replacement_code,
        planned_helper_owners,
        required_helper_replacements,
        ctx.unavailable_imports,
    )
    if patched is None:
        return None, (
            "targeted declaration patch omitted one or more required target/helper "
            "replacement declarations"
        )
    _record(
        ctx.telemetry,
        "skeleton_declaration_patch_result",
        labels=patch_labels,
        status="applied",
    )
    return patched, "patched"


def _retry_statement_patch_compile_once(
    ctx: Ctx,
    owner_labels: list[str],
    allowed_labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    parsed: ParsedModule,
    module_code: str,
    lean_output: str,
    path: Path,
    *,
    sessions: dict[str, str] | None = None,
) -> tuple[ParsedModule | None, str, str]:
    """Give one failed statement correction its exact Lean errors.

    This is an exceptional, base-tier retry after a semantic correction has
    already been produced. It never expands into the hard-timeout ladder: if
    the precise compiler feedback is insufficient, the caller resumes the
    existing repair/decomposition routing instead of spending another long
    agent call.
    """
    _code, ranges = _compose_module(
        parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
    )
    findings = _lean_compile_findings(
        parsed,
        owner_labels,
        ranges,
        lean_output,
        path.name,
        _planned_helper_owner_by_name(ctx, owner_labels),
    )
    allowed = set(allowed_labels)
    findings = [finding for finding in findings if finding.label in allowed]
    patch_labels = _patchable_skeleton_labels(findings, allowed_labels)
    if not patch_labels and len(allowed_labels) == 1:
        patch_labels = list(allowed_labels)
        findings = [
            SkeletonFinding(
                "Lean rejected the corrected declaration:\n" + lean_output[-8000:],
                label=allowed_labels[0],
                lean_name=_lean_name(allowed_labels[0]),
            )
        ]
    if not patch_labels:
        return None, module_code, "compiler error could not be assigned to a corrected declaration"

    _log(
        "  corrected statement failed Lean; giving exact compiler feedback once: "
        + ", ".join(patch_labels)
    )
    patched, note = _targeted_patch_skeleton_decls(
        ctx,
        owner_labels,
        sections,
        import_modules,
        parsed,
        module_code,
        findings,
        timeout=ctx.base_timeout,
        sessions=sessions,
        escalated=False,
        escalate_timeout=False,
    )
    if patched is None:
        return None, module_code, note

    target_kinds = {
        _lean_name(label): ctx.nodes[label].kind for label in allowed_labels
    }
    label_by_name = {_lean_name(label): label for label in allowed_labels}
    for decl in patched.decls:
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    corrected_code, _ranges = _compose_module(
        patched.imports, patched.preamble, [decl.text for decl in patched.decls]
    )
    deterministic = _skeleton_code_findings(
        corrected_code,
        target_kinds,
        label_by_name,
        _planned_helper_owner_by_name(ctx, allowed_labels),
    )
    deterministic += _skeleton_deterministic_findings(
        corrected_code, ctx, allowed_labels
    )
    if deterministic:
        return None, module_code, _format_skeleton_findings(deterministic)
    path.write_text(corrected_code, encoding="utf-8")
    ok, output = _check_lean(path, ctx.lean_command)
    if not ok:
        return None, module_code, output[-8000:]
    _record(
        ctx.telemetry,
        "statement_patch_compile_retry",
        labels=patch_labels,
        status="accepted",
    )
    return patched, corrected_code, "patched from exact compiler feedback"


def _proof_prompt(
    ctx: Ctx,
    targets: list[tuple[str, str]],  # (label, frozen declaration text)
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
            f"Blueprint kind: {node.kind}\n"
            f"Frozen declaration (header/interface is IMMUTABLE):\n```lean\n{decl_text[:6000]}\n```\n"
            f"Required dependency mentions in the implementation or statement: "
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
    return f"""TASK: IMPLEMENT-FROZEN-DECLARATION-BODIES

Return exactly one Lean 4 code block. No commentary.

For EACH target declaration below, return that declaration with its terminal
`sorry` replaced by a real `:= by ...` body:
- Copy the frozen declaration header EXACTLY. Only the tactic body after
  `:= by` is used; any header or statement change is discarded.
- For theorem-like targets, produce a proof. For `def`/`abbrev` targets,
  construct the exact value/function/predicate described by the blueprint.
- Bodies must be self-contained tactic blocks (`have`/`let`/`calc` inside are
  fine). Do NOT add new top-level declarations; if an implementation genuinely
  needs a helper node, reply with NEEDS-DECOMPOSITION for that label instead.
- The implementation must certify or realize the blueprint obligations for
  this node. It does
  not need to mirror the prose line by line, but it must not bypass the
  blueprint argument by using an abstract theorem/tag/witness that erases the
  construction, case split, reduction, invariant, or intermediate claim the
  blueprint proof relies on.
- If a node's blueprint entry lists dependencies, the body (or statement)
  must visibly use their generated Lean names; a proof that re-derives a
  dependency inline will be rejected.
- You may add `import` lines for tactic modules you need.
- Dependency declarations may still have deferred bodies in the skeleton;
  using their frozen interfaces is exactly how the blueprint dependency graph
  is supposed to work.
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


def _plan_owned_declaration_cycle_findings(
    code: str, ctx: Ctx, labels: Iterable[str]
) -> list[SkeletonFinding]:
    """Detect impossible owner/helper cycles in emitted Phase-1 declarations."""
    decls = _lean_declarations(code)
    entries = getattr(ctx, "design_plan_entries", {})
    findings: list[SkeletonFinding] = []
    for label in labels:
        target_name = _lean_name(label)
        if target_name not in decls:
            continue
        helper_names: list[str] = []
        for helper in (entries.get(label) or {}).get("helpers") or []:
            raw_name = str(helper.get("name") or "").strip()
            canonical = _owned_helper_name(ctx, raw_name, [label])
            emitted = canonical if canonical in decls else raw_name
            if emitted in decls:
                helper_names.append(emitted)
        local_names = [target_name, *helper_names]
        graph = {
            source: {
                target
                for target in local_names
                if target != source
                and _mentions_lean_symbol(decls[source].text, target)
            }
            for source in local_names
        }

        def reaches(source: str, target: str) -> bool:
            todo = list(graph.get(source, set()))
            seen: set[str] = set()
            while todo:
                current = todo.pop()
                if current == target:
                    return True
                if current in seen:
                    continue
                seen.add(current)
                todo.extend(graph.get(current, set()) - seen)
            return False

        cyclic_helpers = sorted(
            helper
            for helper in helper_names
            if reaches(target_name, helper) and reaches(helper, target_name)
        )
        if cyclic_helpers:
            findings.append(
                SkeletonFinding(
                    f"{label} interface plan creates an impossible declaration "
                    f"cycle between `{target_name}` and plan-owned helper(s): "
                    + ", ".join(f"`{name}`" for name in cyclic_helpers),
                    label=label,
                    lean_name=target_name,
                    category="plan_contract_closure",
                )
            )
    return findings


def _skeleton_deterministic_findings(code: str, ctx: Ctx, labels: list[str]) -> list[SkeletonFinding]:
    """Coverage/kind checks for a section. Dependency-mention checks are only
    applied to declarations whose bodies are already complete; deferred theorem
    proofs and def/abbrev bodies get theirs during Phase 2."""
    # The complete merged candidate, not a partial patch response, owns the
    # exact typed contract on fresh runs. Refreshing here keeps compiler and
    # semantic repairs atomic with the code they changed.
    if getattr(ctx, "semantic_plan_entries", {}):
        parsed_for_contract = _parse_module(code)
        label_by_name_for_contract = {
            _lean_name(label): label for label in labels
        }
        owner_by_index = _declaration_owner_map(
            parsed_for_contract,
            label_by_name_for_contract,
            _planned_helper_owner_by_name(ctx, labels),
        )
        _realize_typed_contracts_from_candidate(
            ctx,
            labels,
            CanonicalModelModule(parsed_for_contract, owner_by_index),
        )
    findings: list[SkeletonFinding] = []
    decls = _lean_declarations(code)
    generated_by_name = {
        _lean_name(other_label): other_label
        for other_label, other_node in ctx.nodes.items()
        if not other_node.mathlibok
    }
    plan_entries = getattr(ctx, "design_plan_entries", {})
    for label in labels:
        entry = plan_entries.get(label) or {}
        if int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION:
            continue
        for helper in entry.get("helpers") or []:
            helper_name = str(helper.get("name") or "").strip()
            canonical_helper_name = _owned_helper_name(ctx, helper_name, [label])
            helper_decl = decls.get(helper_name) or decls.get(canonical_helper_name)
            if helper_name and helper_decl is None:
                findings.append(
                    SkeletonFinding(
                        f"{label} omitted helper `{helper_name}` required by its "
                        "accepted interface contract",
                        label=label,
                        lean_name=canonical_helper_name,
                    )
                )
                continue
            if helper_decl is None:
                continue
            expected_kind = str(helper.get("kind") or "").strip()
            actual_kind = helper_decl.kind
            kind_matches = expected_kind == actual_kind or {
                expected_kind, actual_kind
            } <= {"theorem", "lemma"}
            if expected_kind and not kind_matches:
                findings.append(
                    SkeletonFinding(
                        f"{label} helper `{helper_name}` must be a {expected_kind}, "
                        f"but generation emitted a {actual_kind}",
                        label=label,
                        lean_name=canonical_helper_name,
                    )
                )
            missing_members = [
                member
                for member in helper.get("required_members") or []
                if not re.search(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(str(member))}"
                    rf"(?![A-Za-z0-9_'.])",
                    helper_decl.text,
                )
            ]
            if missing_members:
                findings.append(
                    SkeletonFinding(
                        f"{label} helper `{helper_name}` omits required member(s): "
                        + ", ".join(f"`{item}`" for item in missing_members),
                        label=label,
                        lean_name=canonical_helper_name,
                    )
                )
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
        # A deferred Phase-1 declaration contains only its public type. Once a
        # body/proof is present, proof-scoped graph edges are authorized too.
        allowed_dependencies = (
            _transitive_statement_dependencies(ctx.nodes, label)
            if _has_terminal_sorry(decl.text)
            else _transitive_dependencies(ctx.nodes, label)
        )
        unexpected = sorted(
            other_label
            for lean_name, other_label in generated_by_name.items()
            if other_label != label
            and other_label not in allowed_dependencies
            and _mentions_lean_symbol(decl.text, lean_name)
        )
        if unexpected:
            findings.append(
                SkeletonFinding(
                    f"{label} references generated declaration(s) outside its "
                    "blueprint dependency closure: "
                    + ", ".join(
                        f"{dep} -> `{_lean_name(dep)}`" for dep in unexpected[:12]
                    ),
                    label=label,
                    lean_name=lean_name,
                    category="outside_dependency_closure",
                    dependencies=tuple(unexpected),
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
    findings.extend(_plan_owned_declaration_cycle_findings(code, ctx, labels))
    return findings


def _skeleton_deterministic_audit(code: str, ctx: Ctx, labels: list[str]) -> list[str]:
    return [finding.message for finding in _skeleton_deterministic_findings(code, ctx, labels)]


def _model_alignment_audit(
    ctx: Ctx,
    labels: list[str],
    code: str,
    *,
    tag: str = "",
) -> AlignmentAuditResult | None:
    """Batched blueprint-contract audit. None means accepted.

    Rejections remain four-value iterable for existing callers. Structured
    statement-dependency evidence is available on ``required_dependencies``.
    Phase-1 issues also identify whether the rejected plan, emitted Lean, or
    both introduced the mismatch. ``kind`` remains ``blueprint``,
    ``decomposition``, or ``lean-generation`` for compatibility.
    """
    decls = _lean_declarations(code)
    parsed = _parse_module(code)
    label_by_name = {_lean_name(label): label for label in labels}
    consumers_by_index = _declaration_target_consumers(parsed, label_by_name)
    owned_material: dict[str, list[str]] = {label: [] for label in labels}
    for index, decl in enumerate(parsed.decls):
        for owner in consumers_by_index.get(index, set()):
            if owner in owned_material:
                owned_material[owner].append(decl.text)
    cache = getattr(ctx, "statement_audit_cache", None)
    if cache is None:
        cache = set()
        setattr(ctx, "statement_audit_cache", cache)

    def cache_key(label: str) -> str:
        decl = decls.get(_lean_name(label))
        material = {
            "label": label,
            "blueprint": ctx.tex_blocks.get(label, ""),
            # Origin routing compares blueprint, plan, and Lean. A plan change
            # must therefore invalidate a cached verdict even when the emitted
            # declaration has not changed yet.
            "design_plan": (getattr(ctx, "design_plan_entries", {}) or {}).get(
                label
            ),
            # Include local helpers owned by this target as well as the public
            # declaration. A compiler patch that changes a helper can change
            # the meaning of an otherwise byte-identical target statement and
            # must therefore invalidate the semantic verdict.
            "lean": "\n\n".join(owned_material.get(label) or [])
            or (decl.text if decl else "(missing)"),
            "paper": hashlib.sha256(ctx.paper_text.encode("utf-8")).hexdigest(),
        }
        return hashlib.sha256(
            json.dumps(material, sort_keys=True).encode("utf-8")
        ).hexdigest()

    keys = {label: cache_key(label) for label in labels}
    cached_labels = [label for label in labels if keys[label] in cache]
    audit_labels = [label for label in labels if keys[label] not in cache]
    if cached_labels:
        _log(
            f"  statement audit reused {len(cached_labels)} unchanged "
            "declaration verdict(s)"
        )
        _record(
            ctx.telemetry,
            "statement_audit_cache_hit",
            labels=cached_labels,
            count=len(cached_labels),
        )
    if not audit_labels:
        return None

    nodes = {label: ctx.nodes[label] for label in audit_labels}
    prompt = _statement_audit_prompt(
        ctx.name,
        nodes,
        ctx.tex_blocks,
        decls,
        ctx.paper_text,
        skeleton_phase=True,
        design_plan_entries={
            label: (getattr(ctx, "design_plan_entries", {}) or {}).get(label)
            for label in audit_labels
        },
    )
    prompt += (
        "\nExisting blueprint labels available for `required_dependencies` "
        "(use only when the public statement truly requires one):\n"
        + "\n".join(
            f"- {label} ({node.kind})"
            for label, node in sorted(
                ctx.nodes.items(), key=lambda item: (item[1].file, item[1].line, item[0])
            )
        )
        + "\n"
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
        labels=audit_labels,
        tag=tag,
    )
    if result.status != "ok" and len(audit_labels) == 1:
        # An unavailable auditor must not silently pass statements; retry once
        # via the escalation budget for a singleton. Multi-node audit failures
        # return to the shared scope router instead of repeating the whole call.
        result = _call_model(
            ctx,
            prompt,
            purpose="statement_audit",
            timeout=ctx.hard_timeout,
            effort=ctx.escalation_effort,
            labels=audit_labels,
            escalated=True,
            tag=tag,
        )
    if result.status != "ok":
        return AlignmentAuditResult(
            "lean-generation",
            f"blueprint contract audit call failed: {result.error}",
            set(audit_labels),
            [],
        )
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        return AlignmentAuditResult(
            "lean-generation",
            f"blueprint contract audit returned invalid JSON: {exc}",
            set(audit_labels),
            [],
        )
    issues = payload.get("issues") or []
    accepted = bool(payload.get("accepted")) and not any(
        str(issue.get("severity", "")).lower() == "reject"
        for issue in issues
        if isinstance(issue, dict)
    )
    _record(
        ctx.telemetry,
        "statement_audit",
        labels=audit_labels,
        source="model",
        accepted=accepted,
        classification=str(payload.get("classification") or ""),
    )
    if accepted:
        cache.update(keys[label] for label in audit_labels)
        return None
    formatted: list[str] = []
    rejected: set[str] = set()
    required_dependencies: dict[str, set[str]] = {}
    kinds_by_label: dict[str, str] = {}
    helpers_by_label: dict[str, list[str]] = {}
    reasons_by_label: dict[str, str] = {}
    missing_info_by_label: dict[str, list[str]] = {}
    origins_by_label: dict[str, str] = {}
    plan_requirements_by_label: dict[str, list[str]] = {}
    global_classification = str(payload.get("classification") or "")
    for issue in issues if isinstance(issues, list) else []:
        if not isinstance(issue, dict):
            continue
        node = str(issue.get("node") or "(unknown)")
        issue_line = (
            f"{node} [{issue.get('severity', 'reject')}]: "
            f"{issue.get('reason', '')}"
        )
        formatted.append(issue_line)
        if str(issue.get("severity", "reject")).lower() == "reject" and node in nodes:
            rejected.add(node)
            issue_classification = str(
                issue.get("classification") or global_classification
            )
            if issue_classification == "needs_decomposition":
                issue_kind = "decomposition"
                missing_info: list[str] = []
            else:
                issue_kind, missing_info = _authorized_alignment_failure_kind(
                    issue_classification, [issue_line], [issue]
                )
            # More specific blueprint/decomposition evidence must not be lost
            # when a critic reports several findings for the same node.
            priority = {"lean-generation": 0, "decomposition": 1, "blueprint": 2}
            if priority.get(issue_kind, 0) >= priority.get(
                kinds_by_label.get(node, "lean-generation"), 0
            ):
                kinds_by_label[node] = issue_kind
            reasons_by_label.setdefault(node, issue_line)
            missing_info_by_label.setdefault(node, []).extend(missing_info)
            raw_origin = str(issue.get("failure_origin") or "lean").strip().lower()
            plan_requirements = [
                str(item).strip()
                for item in issue.get("missing_plan_requirements") or []
                if str(item).strip()
            ]
            # Plan routing is useful only for ordinary translation failures and
            # only when the independent critic names concrete blueprint content
            # absent from the plan. Unsupported labels fall back to the existing
            # Lean retry lifecycle rather than trusting a bare model category.
            origin = (
                raw_origin
                if issue_kind == "lean-generation"
                and raw_origin in {"plan", "both"}
                and plan_requirements
                else "lean"
            )
            origin_priority = {"lean": 0, "plan": 1, "both": 2}
            if origin_priority[origin] >= origin_priority.get(
                origins_by_label.get(node, "lean"), 0
            ):
                origins_by_label[node] = origin
            if origin in {"plan", "both"}:
                plan_requirements_by_label.setdefault(node, []).extend(
                    plan_requirements
                )
            helpers_by_label.setdefault(node, []).extend(
                str(helper).strip()
                for helper in issue.get("missing_helpers") or []
                if str(helper).strip()
            )
            certified = {
                str(dep).strip()
                for dep in issue.get("required_dependencies") or []
                if str(dep).strip() in ctx.nodes and str(dep).strip() != node
            }
            if certified:
                required_dependencies[node] = certified
    if not rejected:
        rejected = set(audit_labels)
        for label in rejected:
            kinds_by_label[label] = "lean-generation"
            origins_by_label[label] = "lean"
            reasons_by_label[label] = (
                "The critic rejected the declaration without attributable "
                "per-node routing evidence."
            )
    # The critic reports issues per node. Non-rejected nodes in the same
    # response have received a positive judgment and remain reusable even if a
    # sibling is routed to correction or blueprint repair.
    cache.update(keys[label] for label in audit_labels if label not in rejected)
    classification = global_classification
    routed_kinds = set(kinds_by_label.values())
    kind = next(iter(routed_kinds)) if len(routed_kinds) == 1 else "mixed"
    missing_blueprint_information = list(
        dict.fromkeys(
            item
            for label in sorted(rejected)
            for item in missing_info_by_label.get(label, [])
        )
    )
    _record(
        ctx.telemetry,
        "statement_audit_routing",
        labels=sorted(rejected),
        reported_classification=classification,
        routed_kind=kind,
        routed_kinds={
            label: kinds_by_label.get(label, "lean-generation")
            for label in sorted(rejected)
        },
        blueprint_repair_authorized=any(
            value in {"blueprint", "decomposition"}
            for value in kinds_by_label.values()
        ),
        missing_blueprint_information=missing_blueprint_information,
        required_dependencies={
            label: sorted(dependencies)
            for label, dependencies in required_dependencies.items()
        },
        failure_origins={
            label: origins_by_label.get(label, "lean")
            for label in sorted(rejected)
        },
        missing_plan_requirements={
            label: list(dict.fromkeys(requirements))
            for label, requirements in sorted(plan_requirements_by_label.items())
        },
    )
    decomposition_helpers = list(
        dict.fromkeys(
            helper
            for label in sorted(rejected)
            if kinds_by_label.get(label) == "decomposition"
            for helper in helpers_by_label.get(label, [])
        )
    )
    reason = "Blueprint contract audit rejected:\n- " + "\n- ".join(formatted)
    if required_dependencies:
        reason += "\nRequired existing blueprint statement dependencies:\n- " + "\n- ".join(
            f"{label} -> {', '.join(sorted(dependencies))}"
            for label, dependencies in sorted(required_dependencies.items())
        )
    if kind == "lean-generation" and classification == "blueprint_issue":
        reason += (
            "\nBlueprint repair was not authorized because the audit named no "
            "mathematical information absent from the blueprint."
        )
    decomposition_labels = {
        label for label, routed in kinds_by_label.items()
        if routed == "decomposition"
    }
    if decomposition_labels:
        if not decomposition_helpers:
            decomposition_helpers = [
                "split each decomposition-routed node's bundled declaration-level obligations "
                "into explicit helper nodes without weakening or dropping any claim"
            ]
        reason += "\nMissing helper statements:\n- " + "\n- ".join(
            dict.fromkeys(decomposition_helpers)
        )
    return AlignmentAuditResult(
        kind,
        reason,
        rejected,
        list(dict.fromkeys(decomposition_helpers)),
        required_dependencies,
        kinds_by_label,
        {
            label: list(dict.fromkeys(values))
            for label, values in helpers_by_label.items()
        },
        reasons_by_label,
        origins_by_label,
        {
            label: list(dict.fromkeys(values))
            for label, values in plan_requirements_by_label.items()
        },
    )


# ---------------------------------------------------------------------------
# Initial declarations and Phase-1 statement machinery


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


def _design_plan_order(ctx: Ctx, labels: Iterable[str]) -> list[str]:
    """Return labels in root-first planning order, independent of traversal."""
    requested = set(labels)
    ordered = [
        label
        for layer in _top_down_statement_layers(ctx.nodes)
        for label in layer
        if label in requested
    ]
    return ordered + sorted(requested - set(ordered))


def _sync_design_plan(ctx: Ctx) -> None:
    """Rebuild the compatibility text view from structured contracts."""
    entries = getattr(ctx, "design_plan_entries", {})
    ctx.design_plan = "\n".join(
        _render_design_plan_entry(label, entries[label])
        for label in _design_plan_order(ctx, entries)
        if not _uses_blueprint_direct_generation(ctx, label)
        if str(entries[label].get("target_signature") or "").strip()
    )


_PLAN_ENTRY_PROGRESS_KEYS = ("semantic_revision_count",)


def _uses_blueprint_direct_generation(ctx: Ctx, label: str) -> bool:
    """Return whether this exact statement has stopped trusting its plan."""
    entry = (getattr(ctx, "blueprint_direct_generation", {}) or {}).get(label)
    return bool(
        isinstance(entry, dict)
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(label, "")
    )


def _activate_blueprint_direct_generation(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    source: str,
) -> set[str]:
    """Bound the damage from an unusable global-plan component.

    The plan remains available for healthy contracts, but these exact
    statement versions are generated from the blueprint and accumulated
    failure evidence instead. This transition costs no model call and is
    monotonic until the blueprint statement changes.
    """
    direct = getattr(ctx, "blueprint_direct_generation", {})
    ctx.blueprint_direct_generation = direct
    activated: set[str] = set()
    for label in dict.fromkeys(labels):
        statement_fp = ctx.stmt_fps.get(label, "")
        if not statement_fp:
            continue
        previous = direct.get(label) or {}
        previous_evidence = (
            str(previous.get("evidence") or "")
            if str(previous.get("statement_fp") or "") == statement_fp
            else ""
        )
        combined = previous_evidence
        if evidence and evidence not in combined:
            combined = (
                (combined + f"\n\nLater evidence ({source}):\n" if combined else "")
                + evidence
            )[-12000:]
        direct[label] = {
            "statement_fp": statement_fp,
            "source": source,
            "evidence": combined,
            "activations": int(previous.get("activations") or 0) + 1,
        }
        activated.add(label)
    if not activated:
        return set()

    for label in activated:
        getattr(ctx, "design_plan_alternates", {}).pop(label, None)
        entry = getattr(ctx, "design_plan_entries", {}).get(label)
        if isinstance(entry, dict):
            for key in (
                "audit_fp",
                "rejected_audit_fp",
                "rejected_kind",
                "rejected_reason",
                "rejected_helpers",
                "correction_base_fp",
                "correction_escalation_fp",
                "closure_fp",
                "closure_wave_id",
            ):
                entry.pop(key, None)
    _store_generation_feedback(ctx, activated, evidence, source=source)
    _clear_retry_lifecycle(ctx, activated, stage="phase1_statement")
    _prune_stale_generation_candidates(ctx)
    _sync_design_plan(ctx)
    _record(
        ctx.telemetry,
        "phase1_blueprint_direct_generation_activated",
        labels=sorted(activated),
        source=source,
        avoided_route="repeated_interface_plan_correction",
        evidence=evidence[-4000:],
    )
    _log(
        "  interface plan circuit breaker activated; generating directly from "
        "the blueprint for: " + ", ".join(sorted(activated))
    )
    return activated


def _prune_stale_blueprint_direct_generation(ctx: Ctx) -> set[str]:
    """Discard circuit-breaker state when the blueprint statement changes."""
    direct = getattr(ctx, "blueprint_direct_generation", {})
    stale = {
        label
        for label, entry in direct.items()
        if label not in ctx.nodes
        or str(entry.get("statement_fp") or "") != ctx.stmt_fps.get(label, "")
    }
    for label in stale:
        direct.pop(label, None)
    return stale


def _preserve_plan_entry_progress(
    previous: dict[str, Any] | None,
    replacement: dict[str, Any],
) -> dict[str, Any]:
    """Carry retry progress across a replacement of the same statement plan.

    Model corrections replace the contract's mathematical payload, but the
    blueprint statement has not changed.  Counters that bound correction
    strategies therefore belong to the statement lifecycle, not to one model
    response.  Dropping them lets closure or alternate-plan correction reset a
    repeatedly rejected node to revision zero and creates an unbounded logical
    retry loop under the global repair budget.
    """
    previous = previous or {}
    for key in _PLAN_ENTRY_PROGRESS_KEYS:
        prior = int(previous.get(key) or 0)
        current = int(replacement.get(key) or 0)
        if prior or current:
            replacement[key] = max(prior, current)
    return replacement


def _prune_stale_design_plan(ctx: Ctx) -> set[str]:
    """Invalidate only plan entries whose blueprint statement changed."""
    stale_direct = _prune_stale_blueprint_direct_generation(ctx)
    entries = getattr(ctx, "design_plan_entries", {})
    stale = {
        label
        for label, entry in entries.items()
        if label not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        or int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
        or not str(entry.get("target_signature") or "").strip()
    }
    for label in stale:
        entries.pop(label, None)
    alternates = getattr(ctx, "design_plan_alternates", {})
    stale_alternates = {
        label
        for label, entry in alternates.items()
        if label not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        or int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
        or not str(entry.get("target_signature") or "").strip()
    }
    for label in stale_alternates:
        alternates.pop(label, None)
    semantic_entries = getattr(ctx, "semantic_plan_entries", {})
    stale_semantic = {
        label
        for label, entry in semantic_entries.items()
        if label not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        or int(entry.get("schema_version") or 0)
        != SEMANTIC_PLAN_SCHEMA_VERSION
    }
    for label in stale_semantic:
        semantic_entries.pop(label, None)
    _sync_design_plan(ctx)
    telemetry = getattr(ctx, "telemetry", None)
    if stale and telemetry is not None:
        _record(
            telemetry,
            "phase1_design_plan_invalidated",
            labels=sorted(stale),
            reason="statement_fingerprint_changed",
        )
    return stale | stale_alternates | stale_semantic | stale_direct


DESIGN_PLAN_SCHEMA_VERSION = 6
DESIGN_PLAN_CLOSURE_VERSION = 4
SEMANTIC_PLAN_SCHEMA_VERSION = 1

# Phase 1 may introduce only declaration-only type interfaces. Ordinary helper
# definitions and theorems would need bodies/proofs, but Phase 2 implements only
# blueprint targets; accepting them here either forces proof work into Phase 1
# or leaves an untracked ``sorry`` in the final module.
DESIGN_PLAN_HELPER_KINDS = {"structure", "inductive", "class"}


def _render_semantic_plan_entry(label: str, entry: dict[str, Any]) -> str:
    """Compact advisory guidance for one Phase-1 declaration.

    Unlike ``_render_design_plan_entry``, this is intentionally not Lean. The
    blueprint and deterministic dependency graph remain authoritative; these
    notes only keep independently generated frontiers semantically coherent.
    """
    lines = [
        f"NODE {label}",
        f"REPRESENTATION: {str(entry.get('representation') or '').strip()}",
    ]
    vocabulary = entry.get("vocabulary") or []
    if vocabulary:
        lines.append("STABLE VOCABULARY:")
        lines.extend(
            f"- {str(item.get('name') or '').strip()}: "
            f"{str(item.get('purpose') or '').strip()}"
            for item in vocabulary
            if isinstance(item, dict)
        )
    obligations = [
        str(item).strip()
        for item in entry.get("obligations") or []
        if str(item).strip()
    ]
    if obligations:
        lines.append("MUST PRESERVE:")
        lines.extend(f"- {item}" for item in obligations)
    requirements = entry.get("provider_requirements") or []
    if requirements:
        lines.append("PROVIDER CAPABILITIES:")
        for requirement in requirements:
            if not isinstance(requirement, dict):
                continue
            capabilities = ", ".join(
                str(item).strip()
                for item in requirement.get("capabilities") or []
                if str(item).strip()
            )
            lines.append(
                f"- {str(requirement.get('provider') or '').strip()}: "
                f"{capabilities or '(none specified)'}"
            )
    return "\n".join(lines)


def _parse_semantic_plan_entries(
    ctx: Ctx, labels: Iterable[str], text: str
) -> tuple[dict[str, dict[str, Any]], dict[str, list[str]]]:
    """Parse and mechanically sanitize the compact global semantic plan.

    Invalid graph edges are removed and reported rather than repaired by a
    model. The plan is advisory, so a malformed entry can never block Phase 1;
    callers fill missing entries with deterministic blueprint-only guidance.
    """
    requested = {
        label
        for label in labels
        if label in ctx.nodes and ctx.stmt_fps.get(label)
    }
    try:
        payload = _extract_json(text)
    except ValueError:
        return {}, {"<response>": ["response was not valid JSON"]}
    contracts = payload.get("contracts") if isinstance(payload, dict) else None
    if not isinstance(contracts, list):
        return {}, {"<response>": ["JSON object omitted contracts array"]}

    parsed: dict[str, dict[str, Any]] = {}
    findings: dict[str, list[str]] = {}
    vocabulary_owners: dict[str, set[str]] = {}
    for raw in contracts:
        if not isinstance(raw, dict):
            continue
        label = str(raw.get("label") or "").strip()
        if label not in requested or label in parsed:
            continue
        representation = str(raw.get("representation") or "").strip()[:600]
        vocabulary: list[dict[str, str]] = []
        seen_names: set[str] = set()
        for item in raw.get("vocabulary") or []:
            if not isinstance(item, dict):
                continue
            name = str(item.get("name") or "").strip()
            purpose = str(item.get("purpose") or "").strip()[:240]
            if (
                not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name)
                or name in seen_names
            ):
                findings.setdefault(label, []).append(
                    f"discarded invalid or duplicate vocabulary name {name!r}"
                )
                continue
            seen_names.add(name)
            vocabulary.append({"name": name, "purpose": purpose})
            vocabulary_owners.setdefault(name, set()).add(label)
            if len(vocabulary) >= 8:
                break

        obligations = [
            str(item).strip()[:320]
            for item in raw.get("obligations") or []
            if str(item).strip()
        ][:6]
        allowed_providers = _statement_uses(ctx.nodes[label])
        provider_requirements: list[dict[str, Any]] = []
        seen_providers: set[str] = set()
        for item in raw.get("provider_requirements") or []:
            if not isinstance(item, dict):
                continue
            provider = str(item.get("provider") or "").strip()
            if provider not in allowed_providers:
                findings.setdefault(label, []).append(
                    f"discarded unauthorized provider {provider!r}"
                )
                continue
            if provider in seen_providers:
                continue
            seen_providers.add(provider)
            capabilities = [
                str(value).strip()[:240]
                for value in item.get("capabilities") or []
                if str(value).strip()
            ][:8]
            provider_requirements.append(
                {"provider": provider, "capabilities": capabilities}
            )
        parsed[label] = {
            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
            "statement_fp": ctx.stmt_fps[label],
            "representation": representation,
            "vocabulary": vocabulary,
            "obligations": obligations,
            "provider_requirements": provider_requirements,
        }

    # A stable helper spelling cannot be owned by two unrelated nodes. Drop
    # only the ambiguous hint; the actual Lean candidate remains free to use a
    # pipeline-namespaced helper and still goes through every normal gate.
    ambiguous = {
        name for name, owners in vocabulary_owners.items() if len(owners) > 1
    }
    if ambiguous:
        for label, entry in parsed.items():
            before = entry["vocabulary"]
            entry["vocabulary"] = [
                item for item in before if item["name"] not in ambiguous
            ]
            removed = sorted(
                item["name"] for item in before if item["name"] in ambiguous
            )
            if removed:
                findings.setdefault(label, []).append(
                    "discarded vocabulary name(s) with multiple owners: "
                    + ", ".join(removed)
                )
    return parsed, findings


def _semantic_plan_fallback_entry(ctx: Ctx, label: str) -> dict[str, Any]:
    """Deterministic advisory entry used when planning output is incomplete."""
    return {
        "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
        "statement_fp": getattr(ctx, "stmt_fps", {}).get(label, ""),
        "representation": (
            "Use the exact mathematical objects and claim in this blueprint node."
        ),
        "vocabulary": [],
        "obligations": [],
        "provider_requirements": [
            {"provider": dep, "capabilities": []}
            for dep in sorted(_statement_uses(ctx.nodes[label]))
        ],
        "fallback": True,
    }


def _render_design_plan_entry(label: str, entry: dict[str, Any]) -> str:
    """Canonical prompt rendering of one complete structured contract."""
    lines = [
        f"NODE {label}",
        f"TARGET: {str(entry.get('target_signature') or '').strip()}",
    ]
    helpers = entry.get("helpers") or []
    if helpers:
        lines.append("OWNED HELPERS:")
        for helper in helpers:
            purpose = str(helper.get("purpose") or "").strip()
            suffix = f" -- {purpose}" if purpose else ""
            kind = str(helper.get("kind") or "def").strip()
            name = str(helper.get("name") or "").strip()
            lines.append(f"- {kind} {name}{suffix}")
            declaration = str(helper.get("declaration") or "").strip()
            if declaration:
                lines.append("  EXACT DECLARATION:")
                lines.extend(f"    {line}" for line in declaration.splitlines())
                continue
            typed_members = helper.get("members") or []
            if typed_members:
                lines.extend(
                    f"  - {str(member.get('name') or '').strip()} : "
                    f"{str(member.get('type') or '').strip()}"
                    for member in typed_members
                )
            else:
                # Compatibility for hand-built test contexts. Parsed and
                # persisted schema-v6 plans always contain typed members.
                lines.extend(
                    f"  - {str(member).strip()} : <missing type>"
                    for member in helper.get("required_members") or []
                    if str(member).strip()
                )
    decisions = [str(item).strip() for item in entry.get("decisions") or [] if str(item).strip()]
    if decisions:
        lines.append("DECISIONS:")
        lines.extend(f"- {item}" for item in decisions)
    return "\n".join(lines)


def _normalize_plan_helper(raw: Any) -> dict[str, Any] | None:
    """Normalize an auxiliary type interface owned by one blueprint target.

    Helpers requiring executable bodies or proofs are deliberately rejected.
    Their semantic content must be represented by the target declaration and
    implemented in Phase 2, where it remains covered by blueprint alignment.
    """
    if not isinstance(raw, dict):
        return None
    name = str(raw.get("name") or "").strip()
    kind = str(raw.get("kind") or "").strip().lower()
    purpose = str(raw.get("purpose") or "").strip()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
        return None
    if kind not in DESIGN_PLAN_HELPER_KINDS:
        return None
    raw_members = raw.get("members")
    if not isinstance(raw_members, list) or not raw_members:
        return None
    members: list[dict[str, str]] = []
    for item in raw_members:
        if not isinstance(item, dict):
            return None
        member_name = str(item.get("name") or "").strip()
        member_type = str(item.get("type") or "").strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", member_name):
            return None
        if not member_type or len(member_type) > 4000:
            return None
        members.append({"name": member_name, "type": member_type})
    member_names = [member["name"] for member in members]
    if (
        len(members) > 32
        or len(member_names) != len(set(member_names))
        or sum(len(member["type"]) for member in members) > 24000
    ):
        return None
    return {
        "name": name[:500],
        "kind": kind,
        "members": members,
        "required_members": member_names,
        "purpose": purpose[:2000],
    }


def _normalize_plan_mathlib_aliases(ctx: Ctx, text: str) -> str:
    r"""Resolve generated spellings for nodes already settled by Mathlib.

    The planner sees both a blueprint label and its authoritative ``\lean``
    declaration. Models nevertheless sometimes derive a generated name from
    the label (for example ``def_affine_map`` instead of ``AffineMap``). That
    translation is exact and deterministic, so it belongs at ingestion rather
    than in a paid contract-correction call.
    """
    normalized = text
    mappings = sorted(
        (
            (_lean_name(label), str(node.lean_decl).strip())
            for label, node in ctx.nodes.items()
            if node.mathlibok
            and str(node.lean_decl or "").strip()
            and _lean_name(label) != str(node.lean_decl).strip()
        ),
        key=lambda item: len(item[0]),
        reverse=True,
    )
    for generated, settled in mappings:
        normalized = _lean_identifier_replace(normalized, generated, settled)
    return normalized


def _parse_design_plan_entries(
    ctx: Ctx, labels: Iterable[str], text: str
) -> dict[str, dict[str, Any]]:
    """Parse a lossless, versioned contract-plan response.

    Free-form signature text is intentionally not accepted: it cannot preserve
    helper ownership and design decisions through persistence and generation.
    """
    requested = {label for label in labels if label in ctx.nodes and ctx.stmt_fps.get(label)}
    try:
        payload = _extract_json(text)
    except ValueError:
        return {}
    contracts = payload.get("contracts") if isinstance(payload, dict) else None
    if not isinstance(contracts, list):
        return {}
    parsed: dict[str, dict[str, Any]] = {}
    for raw in contracts:
        if not isinstance(raw, dict):
            continue
        label = str(raw.get("label") or "").strip()
        signature = _normalize_plan_mathlib_aliases(
            ctx, str(raw.get("target_signature") or "").strip()
        )
        if label not in requested or not signature:
            continue
        expected_name = _lean_name(label)
        if not re.search(
            rf"(?<![A-Za-z0-9_'.]){re.escape(expected_name)}(?![A-Za-z0-9_'.])",
            signature,
        ):
            continue
        raw_helpers = raw.get("helpers") or []
        if not isinstance(raw_helpers, list):
            continue
        helpers = [
            helper
            for helper in (_normalize_plan_helper(item) for item in raw_helpers)
            if helper is not None
        ]
        if len(helpers) != len(raw_helpers):
            continue
        helper_names = [helper["name"] for helper in helpers]
        if len(helper_names) != len(set(helper_names)):
            continue
        for helper in helpers:
            for member in helper["members"]:
                member["type"] = _normalize_plan_mathlib_aliases(
                    ctx, member["type"]
                )
        parsed[label] = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": ctx.stmt_fps[label],
            "target_signature": signature[:12000],
            "helpers": helpers,
            "decisions": [
                str(item).strip()[:4000]
                for item in raw.get("decisions") or []
                if str(item).strip()
            ],
        }
    target_names = {
        _lean_name(label)
        for label, node in ctx.nodes.items()
        if not node.mathlibok
    }
    helper_owners: dict[str, set[str]] = {}
    for label, entry in parsed.items():
        for helper in entry["helpers"]:
            helper_owners.setdefault(helper["name"], set()).add(label)
    invalid_owners = {
        label
        for helper_name, owners in helper_owners.items()
        if len(owners) != 1 or helper_name in target_names
        for label in owners
    }
    for label in invalid_owners:
        parsed.pop(label, None)
    return parsed


def _design_plan_audit_fingerprint(ctx: Ctx, label: str) -> str:
    """Identity of one blueprint contract and its proposed Lean interface."""
    entry = getattr(ctx, "design_plan_entries", {}).get(label) or {}
    material = {
        "label": label,
        "statement_fp": getattr(ctx, "stmt_fps", {}).get(label, ""),
        "contract": {
            "schema_version": int(entry.get("schema_version") or 0),
            "target_signature": str(entry.get("target_signature") or ""),
            "helpers": entry.get("helpers") or [],
            "decisions": entry.get("decisions") or [],
        },
        "paper": hashlib.sha256(
            str(getattr(ctx, "paper_text", "")).encode("utf-8")
        ).hexdigest(),
    }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True).encode("utf-8")
    ).hexdigest()


_PLAN_REVISION_FINDING_CATEGORIES = {
    "plan_contract_closure",
}


def _findings_require_plan_revision(
    ctx: Ctx | Iterable[SkeletonFinding],
    findings: Iterable[SkeletonFinding] | None = None,
) -> bool:
    """Return whether candidate errors originate in the interface plan.

    Only mechanically invalid accepted contracts belong here. An unplanned
    helper invented by statement generation is a generation error when the
    accepted contract never requested that declaration; routing it back to
    plan correction repeatedly edits an already valid plan without addressing
    the bad output. Every Phase-1 path uses this predicate so actual contract
    closure failures do not fall through to compiler patching.
    """
    if findings is None:
        findings = ctx  # compatibility for direct predicate callers
        entries: dict[str, dict[str, Any]] = {}
    else:
        entries = getattr(ctx, "design_plan_entries", {}) or {}
    return any(
        finding.category in _PLAN_REVISION_FINDING_CATEGORIES
        and (
            finding.label is None
            or (entries.get(finding.label) or {}).get("origin")
            != "phase1_candidate"
        )
        for finding in findings
    )


def _mentions_lean_symbol(text: str, name: str) -> bool:
    """Match a generated Lean name, including its use as a namespace prefix."""
    return bool(
        name
        and re.search(
            rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'])",
            text,
        )
    )


def _design_plan_public_interface_fragments(entry: dict[str, Any]) -> list[str]:
    """Lean-aware text fragments that constitute one planned public interface.

    Target declarations go through the same declaration parser used at the
    model-output boundary. Helper fields and inductive constructors are already
    normalized as typed members by the versioned plan parser. Purposes and
    free-form decisions are intentionally excluded: prose cannot satisfy a
    declaration-level blueprint dependency.
    """
    signature = str(entry.get("target_signature") or "")
    parsed = _parse_module(signature)
    fragments = [decl.text for decl in parsed.decls]
    if not fragments and signature.strip():
        # Preserve useful closure evidence for a malformed declaration; the
        # canonical-target check reports the syntax defect separately.
        fragments.append(signature)
    fragments.extend(
        str(helper.get("declaration") or "")
        for helper in entry.get("helpers") or []
        if str(helper.get("declaration") or "").strip()
    )
    fragments.extend(
        str(member.get("type") or "")
        for helper in entry.get("helpers") or []
        for member in helper.get("members") or []
        if isinstance(member, dict) and str(member.get("type") or "").strip()
    )
    return fragments


def _design_plan_dependency_closure_details(
    ctx: Ctx, label: str
) -> dict[str, list[str]]:
    """Observe every statement dependency on the typed plan surface."""
    entry = getattr(ctx, "design_plan_entries", {}).get(label) or {}
    fragments = _design_plan_public_interface_fragments(entry)
    required: list[str] = []
    represented: list[str] = []
    missing: list[str] = []
    generated_providers: list[str] = []
    node = ctx.nodes.get(label)
    for dependency in sorted(_statement_uses(node) if node is not None else set()):
        dependency_node = ctx.nodes.get(dependency)
        if dependency_node is None:
            continue
        lean_name = (
            str(dependency_node.lean_decl or "").strip()
            if dependency_node.mathlibok
            else _lean_name(dependency)
        )
        rendered = f"{dependency} -> `{lean_name or '<missing Lean mapping>'}`"
        required.append(rendered)
        if lean_name and any(
            _mentions_lean_symbol(fragment, lean_name) for fragment in fragments
        ):
            represented.append(rendered)
            continue
        missing.append(rendered)
        if not dependency_node.mathlibok:
            generated_providers.append(dependency)
    return {
        "required": required,
        "represented": represented,
        "missing": missing,
        "generated_providers": generated_providers,
    }


def _design_plan_owner_helper_cycle_paths(ctx: Ctx, label: str) -> list[str]:
    """Find declaration-order cycles already forced by a target/helper plan."""
    entry = getattr(ctx, "design_plan_entries", {}).get(label) or {}
    target = _lean_name(label)
    helpers = {
        str(helper.get("name") or "").strip(): helper
        for helper in entry.get("helpers") or []
        if str(helper.get("name") or "").strip()
    }
    names = [target, *helpers]
    texts = {target: str(entry.get("target_signature") or "")}
    texts.update(
        {
            name: "\n".join(
                str(member.get("type") or "")
                for member in helper.get("members") or []
                if isinstance(member, dict)
            )
            for name, helper in helpers.items()
        }
    )
    graph = {
        source: {
            destination
            for destination in names
            if destination != source
            and _mentions_lean_symbol(texts.get(source, ""), destination)
        }
        for source in names
    }

    def path(source: str, destination: str) -> list[str] | None:
        todo = [[source]]
        while todo:
            candidate = todo.pop(0)
            current = candidate[-1]
            for neighbor in sorted(graph.get(current, set())):
                if neighbor == destination:
                    return [*candidate, neighbor]
                if neighbor not in candidate:
                    todo.append([*candidate, neighbor])
        return None

    cycles: list[str] = []
    for helper in sorted(helpers):
        outward = path(target, helper)
        returning = path(helper, target)
        if outward and returning:
            cycles.append(" -> ".join([*outward, *returning[1:]]))
    return list(dict.fromkeys(cycles))


def _planned_target_members(signature: str, target_name: str) -> set[str]:
    """Extract the member surface exposed by a planned target declaration.

    This intentionally recognizes only declaration syntax whose dotted public
    surface Lean creates deterministically: structure/class fields and
    inductive constructors. It does not guess methods from prose or decisions.
    """
    match = re.search(
        rf"\b(structure|class|inductive)\s+{re.escape(target_name)}"
        rf"(?![A-Za-z0-9_'])[\s\S]*?\bwhere\b([\s\S]*)",
        signature,
    )
    if not match:
        return set()
    kind, body = match.group(1), match.group(2)
    if kind == "inductive":
        return set(
            re.findall(
                r"(?:^|[;\n])\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)",
                body,
            )
        )
    return set(
        re.findall(
            r"(?:^|[;\n])\s*([A-Za-z_][A-Za-z0-9_']*)\s*:",
            body,
        )
    )


def _planned_target_result_type(signature: str, target_name: str) -> str:
    """Return the top-level result type of a planned target declaration.

    Binder annotations may contain their own colons, so this scans the parsed
    declaration and accepts only a colon outside parentheses, brackets, and
    braces. The result is used only to connect a target value to an interface
    helper already owned by the same plan entry.
    """
    declaration = next(
        (
            decl.text
            for decl in _parse_module(signature).decls
            if decl.name == target_name
        ),
        "",
    )
    name_match = re.search(
        rf"\b{re.escape(target_name)}(?![A-Za-z0-9_'])",
        declaration,
    )
    if not name_match:
        return ""

    tail = declaration[name_match.end():]
    depths = {"(": 0, "[": 0, "{": 0}
    closing = {")": "(", "]": "[", "}": "{"}
    for index, char in enumerate(tail):
        if char in depths:
            depths[char] += 1
        elif char in closing:
            opener = closing[char]
            depths[opener] = max(0, depths[opener] - 1)
        elif char == ":" and not any(depths.values()):
            return tail[index + 1:].split(":=", 1)[0].strip()
    return ""


def _lean_surface_tokens(text: str) -> tuple[str, ...]:
    """Tokenize a declaration surface for conservative exact comparison.

    This is deliberately stricter than Lean equivalence. It ignores formatting
    and comments, but it does not treat alternative types or formulations as
    equal. A false negative merely keeps the ordinary generation-retry route;
    a positive result proves regeneration under the unchanged plan cannot
    repair a semantic omission in that plan.
    """
    without_block_comments = re.sub(r"/-[\s\S]*?-/", " ", text)
    without_comments = re.sub(r"--[^\n]*", " ", without_block_comments)
    return tuple(
        re.findall(
            r"[A-Za-z_][A-Za-z0-9_'.]*|\d+(?:\.\d+)?|:=|=>|->|[^\s]",
            without_comments,
        )
    )


def _contains_token_sequence(
    haystack: tuple[str, ...], needle: tuple[str, ...]
) -> bool:
    """Return whether one exact Lean token sequence occurs contiguously."""
    if not needle or len(needle) > len(haystack):
        return False
    width = len(needle)
    return any(
        haystack[index:index + width] == needle
        for index in range(len(haystack) - width + 1)
    )


def _candidate_exactly_realizes_plan(
    ctx: Ctx,
    label: str,
    code: str,
    *,
    allow_revised_plan: bool = False,
) -> bool:
    """Prove that a compiled Phase-1 interface copied its accepted plan.

    The check covers the target declaration header plus every plan-owned
    helper's kind, complete member set, and typed member declarations. Plan
    prose is intentionally irrelevant: if blueprint content appears only in a
    decision but not in this complete public interface, the plan itself is the
    artifact that must change.
    """
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label) or {}
    if (
        _uses_blueprint_direct_generation(ctx, label)
        or
        int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
        or (
            not allow_revised_plan
            and int(entry.get("semantic_revision_count") or 0) >= 1
        )
    ):
        return False

    target_name = _lean_name(label)
    parsed = _parse_module(code)
    actual_by_name = {decl.name: decl for decl in parsed.decls if decl.name}
    actual_target = actual_by_name.get(target_name)
    planned_target = next(
        (
            decl
            for decl in _parse_module(
                str(entry.get("target_signature") or "")
            ).decls
            if decl.name == target_name
        ),
        None,
    )
    if actual_target is None or planned_target is None:
        return False

    helper_aliases = {
        str(helper.get("name") or "").strip(): _owned_helper_name(
            ctx, str(helper.get("name") or "").strip(), [label]
        )
        for helper in entry.get("helpers") or []
        if str(helper.get("name") or "").strip()
    }

    def canonical_planned_text(text: str) -> str:
        result = text
        for original, canonical in sorted(
            helper_aliases.items(), key=lambda item: len(item[0]), reverse=True
        ):
            result = _lean_identifier_replace(result, original, canonical)
        return result

    expected_target = canonical_planned_text(_decl_interface_text(planned_target))
    actual_target_surface = _decl_interface_text(actual_target)
    if _lean_surface_tokens(expected_target) != _lean_surface_tokens(
        actual_target_surface
    ):
        return False

    for helper in entry.get("helpers") or []:
        helper_name = str(helper.get("name") or "").strip()
        canonical_name = helper_aliases.get(helper_name, helper_name)
        actual_helper = actual_by_name.get(canonical_name) or actual_by_name.get(
            helper_name
        )
        if actual_helper is None:
            return False
        expected_kind = str(helper.get("kind") or "").strip()
        if actual_helper.kind != expected_kind:
            return False
        exact_declaration = str(helper.get("declaration") or "").strip()
        if exact_declaration and _lean_surface_tokens(
            exact_declaration
        ) != _lean_surface_tokens(_decl_interface_text(actual_helper)):
            return False
        expected_members = {
            str(member.get("name") or "").strip()
            for member in helper.get("members") or []
            if isinstance(member, dict)
            and str(member.get("name") or "").strip()
        }
        if exact_declaration and not expected_members:
            expected_members = {
                str(member).strip()
                for member in helper.get("required_members") or []
                if str(member).strip()
            }
        if _planned_target_members(
            actual_helper.text, actual_helper.name or canonical_name
        ) != expected_members:
            return False
        helper_tokens = _lean_surface_tokens(actual_helper.text)
        for member in helper.get("members") or []:
            if not isinstance(member, dict):
                return False
            member_name = str(member.get("name") or "").strip()
            member_type = canonical_planned_text(
                str(member.get("type") or "").strip()
            )
            if not _contains_token_sequence(
                helper_tokens,
                _lean_surface_tokens(f"{member_name} : {member_type}"),
            ):
                return False
    return True


def _candidate_target_exactly_realizes_plan(
    ctx: Ctx, label: str, code: str
) -> bool:
    """Return whether the emitted target header exactly copies its plan.

    A compiler can reject an identifier in the target signature before the
    complete helper surface is usable. Matching only the target is sufficient
    for that narrow diagnosis: if the rejected identifier occurs in the
    accepted target signature too, statement regeneration cannot remove it
    without violating the plan.
    """
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label) or {}
    if (
        _uses_blueprint_direct_generation(ctx, label)
        or int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
    ):
        return False

    target_name = _lean_name(label)
    actual = next(
        (decl for decl in _parse_module(code).decls if decl.name == target_name),
        None,
    )
    planned = next(
        (
            decl
            for decl in _parse_module(
                str(entry.get("target_signature") or "")
            ).decls
            if decl.name == target_name
        ),
        None,
    )
    if actual is None or planned is None:
        return False

    expected = _decl_interface_text(planned)
    for helper in entry.get("helpers") or []:
        helper_name = str(helper.get("name") or "").strip()
        if helper_name:
            expected = _lean_identifier_replace(
                expected,
                helper_name,
                _owned_helper_name(ctx, helper_name, [label]),
            )
    return _lean_surface_tokens(expected) == _lean_surface_tokens(
        _decl_interface_text(actual)
    )


_UNKNOWN_LEAN_NAME_RE = re.compile(
    r"unknown\s+(?:constant|identifier|namespace)\s+[`']([^`']+)[`']",
    re.IGNORECASE,
)


def _plan_owned_unknown_lean_names(
    ctx: Ctx, label: str, output: str
) -> tuple[set[str], set[str]]:
    """Return compiler-unknown names in the target and complete plan surface."""
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label) or {}
    target_tokens = set(
        _lean_surface_tokens(str(entry.get("target_signature") or ""))
    )
    planned_text = "\n".join(
        [str(entry.get("target_signature") or "")]
        + [
            str(member.get("type") or "")
            for helper in entry.get("helpers") or []
            for member in helper.get("members") or []
            if isinstance(member, dict)
        ]
    )
    planned_tokens = set(_lean_surface_tokens(planned_text))
    unknown = {
        name
        for name in _UNKNOWN_LEAN_NAME_RE.findall(output)
        if name in planned_tokens
    }
    return unknown & target_tokens, unknown


def _phase1_compile_plan_defects(
    ctx: Ctx,
    labels: Iterable[str],
    code: str,
    output: str,
) -> dict[str, str]:
    """Classify compile failures that regeneration cannot fix under the plan.

    The direct case requires an unknown Lean name copied by an exact target
    header. Ambiguous failures receive one normal compiler correction; only an
    identical error shape under the same plan fingerprint and an exact full
    public interface is routed to plan correction on recurrence.
    """
    defects: dict[str, str] = {}
    current_shape = _lean_error_shape(output)
    with _STATE_LOCK:
        candidates = copy.deepcopy(
            getattr(ctx, "generation_candidates", {}) or {}
        )
    for label in labels:
        if label not in getattr(ctx, "nodes", {}):
            continue
        if (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            == "phase1_candidate"
        ):
            # The typed contract came from this same candidate. Compiler
            # feedback must revise the candidate and contract together, not
            # invoke the legacy independent plan-correction path.
            continue
        target_unknown, plan_unknown = _plan_owned_unknown_lean_names(
            ctx, label, output
        )
        exact_target = _candidate_target_exactly_realizes_plan(
            ctx, label, code
        )
        exact_interface = _candidate_exactly_realizes_plan(
            ctx, label, code, allow_revised_plan=True
        )
        actionable_unknown = (
            target_unknown if exact_target else set()
        ) | (plan_unknown if exact_interface else set())
        if actionable_unknown:
            defects[label] = (
                "accepted plan contains compiler-unknown Lean name(s): "
                + ", ".join(sorted(actionable_unknown))
            )
            continue

        previous = candidates.get(label) or {}
        if (
            str(previous.get("plan_fp") or "")
            == _candidate_plan_fingerprint(ctx, label)
            and str(previous.get("lean_status") or "") == "failed"
            and str(previous.get("lean_output") or "")
            and _lean_error_shape(str(previous.get("lean_output") or ""))
            == current_shape
            and exact_interface
        ):
            defects[label] = (
                "exact plan realization repeated the same Lean compiler "
                "failure under the unchanged plan"
            )
    return defects


def _plan_realized_semantic_rejections(
    ctx: Ctx, labels: Iterable[str], code: str
) -> set[str]:
    """Return rejected labels that regeneration cannot fix under this plan."""
    return {
        label
        for label in labels
        if label in getattr(ctx, "nodes", {})
        and (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            != "phase1_candidate"
        )
        and _candidate_exactly_realizes_plan(ctx, label, code)
    }


def _revise_audit_reported_plan_defects(
    ctx: Ctx,
    audit: AlignmentAuditResult,
    *,
    layer_no: int,
    source: str,
) -> set[str]:
    """Correct plan-owned semantic defects before retrying stale-plan Lean.

    The independent statement critic sees the blueprint, current plan, and
    emitted Lean together. A ``plan`` or ``both`` origin is actionable only
    when the critic also names concrete blueprint obligations absent from the
    plan; ``_model_alignment_audit`` enforces that evidence requirement. The
    existing plan-correction transaction remains responsible for mechanical
    closure validation, candidate provenance, and the later semantic re-audit.
    """
    eligible = (
        audit.labels_for("lean-generation")
        & audit.labels_for_origin("plan", "both")
    )
    eligible = {
        label
        for label in eligible
        if (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            != "phase1_candidate"
        )
    }
    if not eligible:
        return set()
    requirements = audit.plan_requirements_for(sorted(eligible))
    evidence = audit.reason_for(sorted(eligible))
    if requirements:
        evidence += "\nBlueprint requirements absent from the current plan:\n- "
        evidence += "\n- ".join(requirements)
    revised = _revise_exhausted_phase1_contracts(
        ctx,
        eligible,
        evidence,
        policy="audit_origin_plan_defect",
    )
    if revised:
        origins = {
            label: audit.origins_by_label.get(label, "lean")
            for label in sorted(revised)
        }
        _record(
            ctx.telemetry,
            "phase1_audit_origin_plan_revision",
            layer=layer_no,
            source=source,
            labels=sorted(revised),
            failure_origins=origins,
            missing_plan_requirements={
                label: audit.plan_requirements_by_label.get(label, [])
                for label in sorted(revised)
            },
            avoided_route="stale_plan_generation_retry",
        )
        _log(
            "  statement audit located the mismatch in the current plan; "
            "revised it before another Lean generation attempt: "
            + ", ".join(sorted(revised))
        )
    return revised


def _audit_plan_revision_request(
    ctx: Ctx,
    audit: AlignmentAuditResult,
    *,
    layer_no: int,
    source: str,
) -> RepairRequest | None:
    """Build the common retry request after an audit-driven plan revision."""
    revised = _revise_audit_reported_plan_defects(
        ctx, audit, layer_no=layer_no, source=source
    )
    if not revised:
        return None
    ordered = sorted(revised)
    return RepairRequest(
        audit.reason_for(ordered),
        ordered,
        section_labels=ordered,
        authorizes_blueprint_repair=False,
        failure_route=FailureScopeDecision(
            action="independent",
            parts=tuple((label,) for label in ordered),
            failed_labels=tuple(ordered),
            accepted_labels=(),
        ),
        plan_revision_required=True,
    )


def _design_plan_symbol_surfaces(
    ctx: Ctx,
) -> tuple[dict[str, set[str]], dict[str, str]]:
    """Return planned generated symbols and the blueprint node owning each."""
    entries = getattr(ctx, "design_plan_entries", {})
    surfaces: dict[str, set[str]] = {}
    owners: dict[str, str] = {}
    for label, entry in entries.items():
        if label not in ctx.nodes or _uses_blueprint_direct_generation(ctx, label):
            continue
        target_name = _lean_name(label)
        signature = str(entry.get("target_signature") or "")
        target_members = _planned_target_members(signature, target_name)
        result_type = _planned_target_result_type(signature, target_name)
        owners[target_name] = label
        for helper in entry.get("helpers") or []:
            helper_name = str(helper.get("name") or "").strip()
            if not helper_name:
                continue
            members = {
                str(member).strip()
                for member in helper.get("required_members") or []
                if str(member).strip()
            }
            canonical = _owned_helper_name(ctx, helper_name, [label])
            if any(
                _mentions_lean_symbol(result_type, spelling)
                for spelling in (helper_name, canonical)
            ):
                target_members.update(members)
            for spelling in (helper_name, canonical):
                surfaces[spelling] = set(members)
                owners[spelling] = label
        surfaces[target_name] = target_members
    return surfaces, owners


def _design_plan_closure_fingerprint(ctx: Ctx, label: str) -> str:
    """Fingerprint one contract against the complete planned symbol surface."""
    surfaces, owners = _design_plan_symbol_surfaces(ctx)
    material = {
        "closure_version": DESIGN_PLAN_CLOSURE_VERSION,
        "contract": _design_plan_audit_fingerprint(ctx, label),
        "symbols": {
            name: {"owner": owners[name], "members": sorted(members)}
            for name, members in sorted(surfaces.items())
        },
    }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _design_plan_contract_closure_issues(
    ctx: Ctx, labels: Iterable[str]
) -> list[PlanClosureFinding]:
    """Reject mechanically unrealizable plan references before generation.

    This is a symbol-table check, not a semantic audit. In particular, every
    dotted reference to a generated target/helper must name a member exposed by
    that planned declaration, and a helper reference must remain inside the
    consumer's statement dependency closure.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    surfaces, owners = _design_plan_symbol_surfaces(ctx)
    findings: list[PlanClosureFinding] = []
    for label in labels:
        if _uses_blueprint_direct_generation(ctx, label):
            continue
        entry = entries.get(label) or {}
        signature = str(entry.get("target_signature") or "")
        interface_fragments = _design_plan_public_interface_fragments(entry)
        interface_text = "\n".join(interface_fragments)
        allowed = _transitive_statement_dependencies(ctx.nodes, label)
        local: list[PlanClosureFinding] = []
        target_name = _lean_name(label)
        declared = [
            (decl.kind, decl.name or "<anonymous>")
            for decl in _parse_module(signature).decls
        ]
        target_declarations = [
            (kind, name) for kind, name in declared if name == target_name
        ]
        extra_declarations = [
            (kind, name) for kind, name in declared if name != target_name
        ]
        if len(target_declarations) != 1:
            local.append(
                PlanClosureFinding(
                    label,
                    f"{label}: target signature must declare exactly one canonical "
                    f"target named `{target_name}`; found "
                    + (
                        str(len(target_declarations))
                        if declared
                        else "no declarations"
                    ),
                )
            )
        if extra_declarations:
            rendered = ", ".join(
                f"`{kind} {name}`" for kind, name in extra_declarations
            )
            local.append(
                PlanClosureFinding(
                    label,
                    f"{label}: target signature declares additional public target(s): "
                    f"{rendered}. One blueprint node owns exactly one canonical public "
                    f"declaration, `{target_name}`. If the node defines several "
                    "mathematical operations, package them as fields of one "
                    "plan-owned structure/class interface and make the canonical "
                    "target return that interface",
                )
            )
        generated = {
            _lean_name(other): other
            for other, other_node in ctx.nodes.items()
            if not other_node.mathlibok
        }
        unexpected_dependencies = sorted(
            other
            for lean_name, other in generated.items()
            if other != label
            and other not in allowed
            and _mentions_lean_symbol(interface_text, lean_name)
        )
        if unexpected_dependencies:
            local.append(
                PlanClosureFinding(
                    label,
                    f"{label}: public interface references dependency/dependencies "
                    "outside its statement dependency closure: "
                    + ", ".join(
                        f"{dependency} -> `{_lean_name(dependency)}`"
                        for dependency in unexpected_dependencies
                    ),
                    unauthorized_dependencies=tuple(unexpected_dependencies),
                )
            )
        for symbol, members in surfaces.items():
            owner = owners.get(symbol)
            mentions_symbol = _mentions_lean_symbol(interface_text, symbol)
            unauthorized_owner = bool(
                owner
                and owner != label
                and owner not in allowed
                and mentions_symbol
            )
            if unauthorized_owner:
                # The consumer invented an out-of-closure reference. Do not
                # also claim that the healthy provider is missing the invented
                # member: that would block and rewrite the provider for a
                # defect owned entirely by this consumer.
                if symbol != _lean_name(owner):
                    local.append(
                        PlanClosureFinding(
                            label,
                            f"{label}: public interface references helper `{symbol}` "
                            f"owned by {owner}, outside its statement dependency closure",
                            unauthorized_dependencies=(owner,),
                        )
                    )
                continue
            dotted_members = set(
                re.findall(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(symbol)}\."
                    r"([A-Za-z_][A-Za-z0-9_']*)",
                    interface_text,
                )
            )
            for member in sorted(dotted_members - members):
                local.append(
                    PlanClosureFinding(
                        label,
                        f"{label}: target signature requires `{symbol}.{member}`, "
                        f"but planned declaration `{symbol}` exposes no such member",
                        provider=owners.get(symbol),
                        missing_provider_members=(f"{symbol}.{member}",),
                    )
                )
        cycle_paths = _design_plan_owner_helper_cycle_paths(ctx, label)
        if cycle_paths:
            local.append(
                PlanClosureFinding(
                    label,
                    f"{label}: interface plan creates impossible target/helper "
                    "declaration cycle(s): " + "; ".join(cycle_paths),
                    cycle_paths=tuple(cycle_paths),
                )
            )
        findings.extend(local)
    return findings


def _design_plan_contract_closure_findings(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, list[str]]:
    """Compatibility view of structured closure issues grouped by consumer."""
    findings: dict[str, list[str]] = {}
    for issue in _design_plan_contract_closure_issues(ctx, labels):
        findings.setdefault(issue.consumer, []).append(issue.message)
    return {
        label: list(dict.fromkeys(messages))
        for label, messages in findings.items()
    }


def _design_plan_unauthorized_reference_findings(
    ctx: Ctx, labels: Iterable[str]
) -> list[str]:
    """Reject generated target references outside statement authorization."""
    return [
        issue.message
        for issue in _design_plan_contract_closure_issues(ctx, labels)
        if issue.unauthorized_dependencies
    ]


def _design_plan_invalid_mathlib_alias_findings(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, list[str]]:
    r"""Reject generated aliases for blueprint nodes already settled by Mathlib.

    A ``\mathlibok`` node is not generated by this pipeline: its ``\lean``
    mapping is the authoritative declaration name. The planner may omit a
    proof-only Mathlib dependency from a public contract, but if it mentions
    that dependency it must use the settled name rather than the generated
    spelling derived from the blueprint label.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    mappings = {
        _lean_name(dep): (dep, str(node.lean_decl).strip())
        for dep, node in ctx.nodes.items()
        if node.mathlibok
        and str(node.lean_decl or "").strip()
        and _lean_name(dep) != str(node.lean_decl).strip()
    }
    findings: dict[str, list[str]] = {}
    for label in labels:
        if _uses_blueprint_direct_generation(ctx, label):
            continue
        contract = "\n".join(
            _design_plan_public_interface_fragments(entries.get(label) or {})
        )
        invalid = [
            (generated, dep, settled)
            for generated, (dep, settled) in mappings.items()
            if _mentions_lean_symbol(contract, generated)
        ]
        if invalid:
            findings[label] = [
                f"{label}: contract uses generated alias `{generated}` for "
                f"Mathlib-owned {dep}; use its settled `\\lean` declaration "
                f"`{settled}` instead"
                for generated, dep, settled in sorted(invalid)
            ]
    return findings


def _design_plan_dependency_findings(ctx: Ctx, labels: Iterable[str]) -> list[str]:
    r"""Reject mechanically unauthorized references without semantic guessing.

    Missing ``\uses`` names remain observable in closure telemetry, but they
    are not mechanically conclusive. A theorem used by a proof normally must
    not occur in the theorem's public proposition, while a definition used in
    an equation often must. The mandatory statement-alignment audit decides
    whether the generated contract preserves the actual blueprint text.
    """
    return _design_plan_unauthorized_reference_findings(ctx, labels)


def _validate_design_plan_contract_closure(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, list[str]]:
    """Validate and fingerprint the deterministic plan-to-generation handoff."""
    entries = getattr(ctx, "design_plan_entries", {})
    ordered = [
        label
        for label in labels
        if label in entries and not _uses_blueprint_direct_generation(ctx, label)
    ]
    uncached = [
        label
        for label in ordered
        if str(entries[label].get("closure_fp") or "")
        != _design_plan_closure_fingerprint(ctx, label)
    ]
    if not uncached:
        if ordered:
            _record(
                ctx.telemetry,
                "phase1_design_plan_closure",
                labels=ordered,
                status="cache_hit",
            )
        return {}

    findings = _design_plan_contract_closure_findings(ctx, uncached)
    for label, messages in _design_plan_invalid_mathlib_alias_findings(
        ctx, uncached
    ).items():
        findings[label] = [*messages, *findings.get(label, [])]
    dependency_closure = {
        label: _design_plan_dependency_closure_details(ctx, label)
        for label in uncached
    }
    for label in uncached:
        if label not in findings:
            entries[label]["closure_fp"] = _design_plan_closure_fingerprint(
                ctx, label
            )
        else:
            entries[label].pop("closure_fp", None)
    _sync_design_plan(ctx)
    _record(
        ctx.telemetry,
        "phase1_design_plan_closure",
        labels=uncached,
        status="rejected" if findings else "accepted",
        rejected_labels=sorted(findings),
        statement_fingerprints={
            label: ctx.stmt_fps.get(label, "") for label in uncached
        },
        plan_fingerprints={
            label: _design_plan_audit_fingerprint(ctx, label)
            for label in uncached
        },
        dependency_closure=dependency_closure,
        findings=[
            finding
            for label in sorted(findings)
            for finding in findings[label]
        ],
    )
    return findings


def _design_plan_closure_repair_components(
    ctx: Ctx, findings: dict[str, list[str]]
) -> list[list[str]]:
    """Connected provider-consumer units that must be corrected atomically.

    Findings about a consumer's unauthorized dependency remain consumer-only.
    Missing member-surface findings join the consumer to the provider that
    owns that surface. Shared providers therefore combine all affected
    consumers into one coherent correction instead of letting independent
    calls invent mutually incompatible member names.
    """
    affected = set(findings)
    adjacency: dict[str, set[str]] = {label: set() for label in affected}
    for issue in _design_plan_contract_closure_issues(ctx, findings):
        if issue.consumer not in findings:
            continue
        # A consumer that omits a required dependency is the broken contract;
        # the dependency provider itself is not broken and must remain
        # schedulable. Only a missing member on a provider-owned surface makes
        # provider and consumer an atomic repair unit.
        providers = (
            {issue.provider}
            if issue.provider is not None and issue.missing_provider_members
            else set()
        )
        for provider in providers:
            if provider == issue.consumer or provider not in ctx.nodes:
                continue
            affected.add(provider)
            adjacency.setdefault(issue.consumer, set()).add(provider)
            adjacency.setdefault(provider, set()).add(issue.consumer)

    ordered = _design_plan_order(ctx, affected)
    position = {label: index for index, label in enumerate(ordered)}
    components: list[list[str]] = []
    unseen = set(affected)
    while unseen:
        seed = min(unseen, key=position.get)
        todo = [seed]
        component: set[str] = set()
        while todo:
            label = todo.pop()
            if label in component:
                continue
            component.add(label)
            todo.extend(adjacency.get(label, set()) - component)
        unseen.difference_update(component)
        components.append(
            sorted(component, key=position.get)
        )
    return components


def _closure_blocked_labels(
    ctx: Ctx, findings: dict[str, list[str]]
) -> set[str]:
    """Contracts that cannot freeze while the current closure findings remain."""
    return {
        label
        for component in _design_plan_closure_repair_components(ctx, findings)
        for label in component
    }


def _closure_findings_for_scope(
    ctx: Ctx,
    findings: dict[str, list[str]],
    scope: Iterable[str],
) -> dict[str, list[str]]:
    """Select complete closure components touching the requested labels."""
    requested = set(scope)
    selected_consumers: set[str] = set()
    for component in _design_plan_closure_repair_components(ctx, findings):
        if requested & set(component):
            selected_consumers.update(label for label in component if label in findings)
    return {
        label: findings[label]
        for label in findings
        if label in selected_consumers
    }


def _evaluate_design_plan_candidate(
    ctx: Ctx,
    ordered: list[str],
    entries: dict[str, dict[str, Any]],
    candidate_id: str,
) -> DesignPlanCandidate:
    """Score a plan with the existing closure rules without changing live state."""
    # A losing tournament lane may finish after an admissible sibling has
    # already allowed Phase 1 to continue. Score against an isolated shallow
    # context so that late deterministic evaluation can never swap candidate
    # entries into the live run, even briefly. Graph and statement data remain
    # shared read-only; only plan state is candidate-local.
    candidate_ctx = copy.copy(ctx)
    candidate_ctx.design_plan_entries = entries
    candidate_ctx.design_plan = ""
    missing = [label for label in ordered if label not in entries]
    findings = _design_plan_contract_closure_findings(candidate_ctx, ordered)
    for label, messages in _design_plan_invalid_mathlib_alias_findings(
        candidate_ctx, ordered
    ).items():
        findings.setdefault(label, []).extend(messages)
    findings = {
        label: list(dict.fromkeys(messages))
        for label, messages in findings.items()
    }
    components = _design_plan_closure_repair_components(candidate_ctx, findings)
    blocked = {label for component in components for label in component}
    return DesignPlanCandidate(
        candidate_id=candidate_id,
        entries=copy.deepcopy(entries),
        missing=missing,
        findings=findings,
        blocked=blocked,
        components=components,
    )


def _initial_plan_admission(
    ctx: Ctx,
    ordered: list[str],
    candidate: DesignPlanCandidate,
) -> tuple[bool, list[str], list[str]]:
    """Decide whether a complete plan is safe to start Phase 1 with.

    Requiring zero findings over every future consumer rejected every known
    fast historical plan and recreated the expensive global-correction path.
    The non-arbitrary admission boundary is therefore the same dependency
    boundary Phase 1 can actually execute now: the complete initial bottom-up
    frontier. Every requested contract must exist, and every initial provider
    must be mechanically closed. Future consumers retain their existing
    just-in-time frontier gate before they can generate Lean.
    """
    pending = set(ordered)
    generated = {
        label for label, node in ctx.nodes.items() if not node.mathlibok
    }
    frozen = generated - pending
    frontier = _bottom_up_ready_frontier(ctx.nodes, pending, frozen)
    blocked = sorted(set(frontier) & candidate.blocked)
    complete = not candidate.missing and all(
        label in candidate.entries for label in ordered
    )
    return complete and bool(frontier) and not blocked, frontier, blocked


def _initial_plan_repair_costs(
    candidate: DesignPlanCandidate,
    node_count: int,
) -> tuple[int, int]:
    """Estimate bounded local correction versus another full tournament.

    The estimate is deliberately expressed in contract-work units rather than
    model-specific seconds or prices. A closure repair may use the base and
    escalation tiers for each blocked contract, each finding adds validation
    work, and each disconnected component is a separate correction
    transaction. A fresh tournament asks two lanes to plan every contract.
    """
    finding_count = sum(len(items) for items in candidate.findings.values())
    repair_work = (
        2 * len(candidate.blocked)
        + finding_count
        + len(candidate.components)
    )
    tournament_work = 2 * max(1, node_count)
    return repair_work, tournament_work


def _initial_plan_repair_admission(
    ctx: Ctx,
    ordered: list[str],
    candidate: DesignPlanCandidate,
) -> tuple[bool, list[str], list[str], int, int]:
    """Admit a complete near-good plan only when scoped repair is cheaper.

    Clean initial frontiers are handled by ``_initial_plan_admission`` and may
    start as soon as either lane finishes. This fallback runs only after both
    lanes have settled, so it cannot preempt a clean sibling. The existing
    frontier closure gateway remains responsible for performing and validating
    the repair before statement generation.
    """
    _clean, frontier, blocked = _initial_plan_admission(ctx, ordered, candidate)
    complete = not candidate.missing and all(
        label in candidate.entries for label in ordered
    )
    repair_work, tournament_work = _initial_plan_repair_costs(
        candidate, len(ordered)
    )
    repairable = (
        complete
        and bool(frontier)
        and bool(blocked)
        and repair_work < tournament_work
    )
    return repairable, frontier, blocked, repair_work, tournament_work


def _merge_design_plan_candidates(
    ctx: Ctx,
    ordered: list[str],
    primary: DesignPlanCandidate,
    alternate: DesignPlanCandidate,
) -> tuple[DesignPlanCandidate, list[list[str]]]:
    """Replace defective closure components only when the full plan improves.

    Arbitrary per-node mixing is unsafe because consumers and providers share
    helper surfaces. Components come from the same closure graph used by plan
    repair, and every proposed replacement is rescored in the complete plan.
    """
    pending = set(ordered)
    generated = {
        label for label, node in ctx.nodes.items() if not node.mathlibok
    }
    frozen = generated - pending
    ready_frontier = set(
        _bottom_up_ready_frontier(ctx.nodes, pending, frozen)
    )

    def ready_count(candidate: DesignPlanCandidate) -> int:
        return len(ready_frontier - candidate.blocked)

    current = primary
    accepted_components: list[list[str]] = []
    attempted: set[tuple[str, ...]] = set()
    while current.findings:
        improved = False
        for component in current.components:
            key = tuple(sorted(component))
            if key in attempted:
                continue
            attempted.add(key)
            if any(label not in alternate.entries for label in component):
                continue
            trial_entries = copy.deepcopy(current.entries)
            for label in component:
                trial_entries[label] = copy.deepcopy(alternate.entries[label])
            trial = _evaluate_design_plan_candidate(
                ctx,
                ordered,
                trial_entries,
                f"merge:{primary.candidate_id}+{alternate.candidate_id}",
            )
            if (
                trial.score < current.score
                and ready_count(trial) >= ready_count(current)
            ):
                current = trial
                accepted_components.append(list(component))
                improved = True
                break
        if not improved:
            break
    return current, accepted_components


def _design_plan_audit_prompt(ctx: Ctx, labels: list[str]) -> str:
    """Ask an independent critic to validate contracts before Lean emission."""
    entries = getattr(ctx, "design_plan_entries", {})
    tex_blocks = getattr(ctx, "tex_blocks", {})
    pairs = []
    for label in labels:
        node = ctx.nodes[label]
        statement_uses = _statement_uses(node)
        proof_only_uses = _proof_uses(node) - statement_uses
        pairs.append(
            f"## Node {label}\n"
            f"- kind: {node.kind}\n"
            f"- expected Lean name: {_lean_name(label)}\n"
            f"- statement-interface dependencies: "
            f"{', '.join(sorted(statement_uses)) or '(none)'}\n"
            f"- proof-only dependencies: "
            f"{', '.join(sorted(proof_only_uses)) or '(none)'}\n"
            f"Blueprint text:\n```tex\n{tex_blocks.get(label, '')[:5000]}\n```\n"
            f"Proposed interface contract:\n```text\n"
            f"{_render_design_plan_entry(label, entries.get(label) or {})[:12000]}\n```"
        )
    nearby_labels = _design_plan_context_labels(ctx, labels)
    nearby_text = "\n".join(
        _render_design_plan_entry(label, entries.get(label) or {})
        for label in _design_plan_order(ctx, nearby_labels)
        if str((entries.get(label) or {}).get("target_signature") or "").strip()
    )[:12000]
    nearby = (
        "Related proposed contracts (also untrusted; use only to check local "
        "consistency):\n```text\n" + nearby_text + "\n```"
        if nearby_text
        else ""
    )
    paper = str(getattr(ctx, "paper_text", ""))
    paper_block = (
        f"Original paper context:\n<paper>\n{paper[:12000]}\n</paper>\n"
        if paper
        else ""
    )
    return f"""TASK: BLUEPRINT-INTERFACE-PLAN-AUDIT

You are an independent critic. The proposed contracts below have NOT been
accepted and no Lean has been generated from them yet. Compare each proposed
interface with its blueprint node.

Reject a contract if it drops an object, parameter, hypothesis, equation,
property, inverse/uniqueness requirement, or other declaration-level
obligation from the blueprint; bundles independent obligations that require
separate declarations; or makes a downstream theorem vacuous. Do not require
exact Lean syntax or proof bodies at this stage: judge the mathematical public
interface. Dependency authorization is checked deterministically before this
call. Do not reject a contract merely because a proof-only dependency is absent
from its public signature, and do not infer additional graph requirements.

Return exactly one JSON object. On success:
{{"accepted": true, "classification": "accepted", "issues": []}}

On failure:
{{
  "accepted": false,
  "classification": "lean_translation_issue" | "blueprint_issue" | "needs_decomposition",
  "issues": [
    {{
      "node": "blueprint label",
      "severity": "reject",
      "reason": "precise mismatch",
      "missing_helpers": ["exact helper obligation, only for decomposition"],
      "missing_blueprint_information": [
        "exact mathematical fact absent from the blueprint"
      ]
    }}
  ]
}}

Use `lean_translation_issue` when the blueprint is coherent but the proposed
interface mistranslates it. Use `blueprint_issue` only when the blueprint claim
itself is mathematically inconsistent or missing a necessary hypothesis. Use
`needs_decomposition` only when the blueprint is concrete but one node bundles
multiple declaration-level obligations that must become explicit blueprint
nodes. A model's difficulty expressing a contract is not a blueprint issue.
For every `blueprint_issue`, `missing_blueprint_information` MUST be nonempty and
name the absent mathematical fact. If another Lean representation could encode
the existing blueprint faithfully, this is a `lean_translation_issue`, not
permission to rewrite the blueprint.

{nearby}

Contracts under review:
{chr(10).join(pairs)}

{paper_block}"""


def _audit_phase1_design_plan(
    ctx: Ctx, labels: Iterable[str]
) -> AlignmentAuditResult | None:
    """Validate uncached plan entries before they can guide Lean generation."""
    entries = getattr(ctx, "design_plan_entries", {})
    ordered = [
        label
        for label in _design_plan_order(ctx, labels)
        if label in entries
        and not _uses_blueprint_direct_generation(ctx, label)
        and str(entries[label].get("audit_fp") or "")
        != _design_plan_audit_fingerprint(ctx, label)
    ]
    if not ordered:
        return None

    cached_rejected = [
        label
        for label in ordered
        if str(entries[label].get("rejected_audit_fp") or "")
        == _design_plan_audit_fingerprint(ctx, label)
    ]
    if cached_rejected:
        kinds_by_label = {
            label: str(entries[label].get("rejected_kind") or "lean-generation")
            for label in cached_rejected
        }
        kinds = set(kinds_by_label.values())
        kind = next(iter(kinds)) if len(kinds) == 1 else "mixed"
        reasons_by_label = {
            label: str(entries[label].get("rejected_reason") or "").strip()
            for label in cached_rejected
            if str(entries[label].get("rejected_reason") or "").strip()
        }
        helpers_by_label = {
            label: list(
                dict.fromkeys(
                    str(item)
                    for item in entries[label].get("rejected_helpers") or []
                )
            )
            for label in cached_rejected
        }
        reasons = list(dict.fromkeys(reasons_by_label.values()))
        helpers = list(
            dict.fromkeys(
                item
                for label in cached_rejected
                for item in helpers_by_label.get(label, [])
            )
        )
        cached_reason = "\n".join(reasons) or "Interface-plan audit previously rejected"
        if reasons and all(
            not item.startswith("Interface-plan ") for item in reasons
        ):
            cached_reason = "Interface-plan audit rejected:\n- " + "\n- ".join(
                reasons
            )
        _log(
            "  reusing unchanged interface-plan rejection for: "
            + ", ".join(cached_rejected)
        )
        _record(
            ctx.telemetry,
            "phase1_design_plan_rejection_reused",
            labels=cached_rejected,
            classification=kind,
            contract_fingerprints={
                label: _design_plan_audit_fingerprint(ctx, label)
                for label in cached_rejected
            },
        )
        return AlignmentAuditResult(
            kind,
            cached_reason,
            set(cached_rejected),
            helpers,
            kinds_by_label=kinds_by_label,
            helpers_by_label=helpers_by_label,
            reasons_by_label=reasons_by_label,
        )

    deterministic = _design_plan_dependency_findings(ctx, ordered)
    if deterministic:
        rejected = {
            label
            for label in ordered
            if any(item.startswith(f"{label}:") for item in deterministic)
        }
        reason = "Interface-plan deterministic checks rejected:\n- " + "\n- ".join(
            deterministic
        )
        for label in rejected:
            entries[label]["rejected_audit_fp"] = _design_plan_audit_fingerprint(
                ctx, label
            )
            entries[label]["rejected_kind"] = "lean-generation"
            entries[label]["rejected_reason"] = reason
            entries[label]["rejected_helpers"] = []
        _record(
            ctx.telemetry,
            "phase1_design_plan_audit",
            labels=sorted(rejected),
            accepted=False,
            classification="deterministic_dependency_rejection",
            findings=deterministic,
        )
        return AlignmentAuditResult(
            "lean-generation",
            reason,
            rejected,
            [],
            kinds_by_label={label: "lean-generation" for label in rejected},
            reasons_by_label={label: reason for label in rejected},
        )
    _log(
        f"==> Phase 1 contract-plan audit: checking {len(ordered)} proposed "
        "interface(s) before Lean generation"
    )
    result = _call_model(
        ctx,
        _design_plan_audit_prompt(ctx, ordered),
        purpose="phase1_design_plan_audit",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=ordered,
    )
    if result.status != "ok" and len(ordered) == 1:
        result = _call_model(
            ctx,
            _design_plan_audit_prompt(ctx, ordered),
            purpose="phase1_design_plan_audit",
            timeout=ctx.hard_timeout,
            effort=ctx.escalation_effort,
            labels=ordered,
            escalated=True,
        )
    if result.status != "ok":
        return AlignmentAuditResult(
            "lean-generation",
            f"interface-plan audit call failed: {result.error}",
            set(ordered),
            [],
            kinds_by_label={label: "lean-generation" for label in ordered},
        )
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        return AlignmentAuditResult(
            "lean-generation",
            f"interface-plan audit returned invalid JSON: {exc}",
            set(ordered),
            [],
            kinds_by_label={label: "lean-generation" for label in ordered},
        )
    issues = payload.get("issues") or []
    accepted = bool(payload.get("accepted")) and not any(
        isinstance(issue, dict)
        and str(issue.get("severity", "reject")).lower() == "reject"
        for issue in issues
    )
    _record(
        ctx.telemetry,
        "phase1_design_plan_audit",
        labels=ordered,
        accepted=accepted,
        classification=str(payload.get("classification") or ""),
    )
    if accepted:
        for label in ordered:
            entries[label]["audit_fp"] = _design_plan_audit_fingerprint(ctx, label)
            for key in (
                "rejected_audit_fp",
                "rejected_kind",
                "rejected_reason",
                "rejected_helpers",
                "correction_base_fp",
                "correction_escalation_fp",
            ):
                entries[label].pop(key, None)
        _sync_design_plan(ctx)
        return None

    rejected: set[str] = set()
    formatted: list[str] = []
    kinds_by_label: dict[str, str] = {}
    helpers_by_label: dict[str, list[str]] = {}
    reasons_by_label: dict[str, str] = {}
    missing_info_by_label: dict[str, list[str]] = {}
    global_classification = str(payload.get("classification") or "")
    for issue in issues if isinstance(issues, list) else []:
        if not isinstance(issue, dict):
            continue
        node = str(issue.get("node") or "(unknown)")
        severity = str(issue.get("severity") or "reject")
        issue_line = f"{node} [{severity}]: {issue.get('reason', '')}"
        formatted.append(issue_line)
        if severity.lower() == "reject" and node in ordered:
            rejected.add(node)
            issue_classification = str(
                issue.get("classification") or global_classification
            )
            if issue_classification == "needs_decomposition":
                issue_kind = "decomposition"
                missing_information: list[str] = []
            else:
                issue_kind, missing_information = _authorized_alignment_failure_kind(
                    issue_classification, [issue_line], [issue]
                )
            kinds_by_label[node] = issue_kind
            reasons_by_label[node] = issue_line
            missing_info_by_label[node] = missing_information
            helpers_by_label[node] = list(
                dict.fromkeys(
                    str(item).strip()
                    for item in issue.get("missing_helpers") or []
                    if str(item).strip()
                )
            )
    if not rejected:
        rejected = set(ordered)
        for label in rejected:
            kinds_by_label[label] = "lean-generation"
            reasons_by_label[label] = (
                "The interface-plan critic rejected without attributable "
                "per-node routing evidence."
            )
    for label in set(ordered) - rejected:
        entries[label]["audit_fp"] = _design_plan_audit_fingerprint(ctx, label)
    routed_kinds = set(kinds_by_label.values())
    kind = next(iter(routed_kinds)) if len(routed_kinds) == 1 else "mixed"
    missing_blueprint_information = list(
        dict.fromkeys(
            item
            for label in sorted(rejected)
            for item in missing_info_by_label.get(label, [])
        )
    )
    helpers = list(
        dict.fromkeys(
            helper
            for label in sorted(rejected)
            for helper in helpers_by_label.get(label, [])
        )
    )
    _record(
        ctx.telemetry,
        "phase1_design_plan_audit_routing",
        labels=sorted(rejected),
        reported_classification=global_classification,
        routed_kind=kind,
        routed_kinds={
            label: kinds_by_label.get(label, "lean-generation")
            for label in sorted(rejected)
        },
        blueprint_repair_authorized=any(
            routed in {"blueprint", "decomposition"}
            for routed in kinds_by_label.values()
        ),
        missing_blueprint_information=missing_blueprint_information,
    )
    reason = "Interface-plan audit rejected:\n- " + "\n- ".join(
        formatted or ["critic rejected the proposed interface without node details"]
    )
    if kind == "lean-generation" and global_classification == "blueprint_issue":
        reason += (
            "\nBlueprint repair was not authorized because the audit named no "
            "mathematical information absent from the blueprint."
        )
    for label in rejected:
        entries[label]["rejected_audit_fp"] = _design_plan_audit_fingerprint(ctx, label)
        entries[label]["rejected_kind"] = kinds_by_label.get(
            label, "lean-generation"
        )
        entries[label]["rejected_reason"] = reasons_by_label.get(label, reason)
        entries[label]["rejected_helpers"] = helpers_by_label.get(label, [])
    return AlignmentAuditResult(
        kind,
        reason,
        rejected,
        helpers,
        kinds_by_label=kinds_by_label,
        helpers_by_label=helpers_by_label,
        reasons_by_label=reasons_by_label,
    )


def _try_alternate_design_plan_component(
    ctx: Ctx, labels: list[str], evidence: str
) -> bool:
    """Try the retained candidate once before paying for plan correction."""
    entries = getattr(ctx, "design_plan_entries", {})
    alternates = getattr(ctx, "design_plan_alternates", {})
    if not labels or any(label not in alternates for label in labels):
        return False
    ordered = _design_plan_order(ctx, entries)
    current = _evaluate_design_plan_candidate(ctx, ordered, entries, "selected")
    trial_entries = copy.deepcopy(entries)
    changed = False
    for label in labels:
        replacement = _preserve_plan_entry_progress(
            entries.get(label), copy.deepcopy(alternates[label])
        )
        changed = changed or replacement != trial_entries.get(label)
        trial_entries[label] = replacement
    for label in labels:
        alternates.pop(label, None)
    if not changed:
        return False

    trial = _evaluate_design_plan_candidate(ctx, ordered, trial_entries, "alternate")
    acceptable = trial.score < current.score or (current.closed and trial.closed)
    _record(
        ctx.telemetry,
        "phase1_design_plan_alternate_component",
        labels=labels,
        status="applied" if acceptable else "rejected",
        previous_score=list(current.score),
        alternate_score=list(trial.score),
        evidence_sha256=hashlib.sha256(evidence.encode("utf-8")).hexdigest(),
    )
    if not acceptable:
        return False
    for label in labels:
        entries[label] = trial_entries[label]
    _sync_design_plan(ctx)
    _log(
        "  reused retained alternate plan component before model correction: "
        + ", ".join(labels)
    )
    return True


def _correct_phase1_design_plan(
    ctx: Ctx,
    labels: list[str],
    evidence: str,
    *,
    escalated: bool = False,
    try_alternate: bool = True,
    context_labels: Iterable[str] | None = None,
) -> bool:
    """Revise one connected set of interface contracts using exact evidence."""
    if try_alternate and _try_alternate_design_plan_component(ctx, labels, evidence):
        return True
    entries = getattr(ctx, "design_plan_entries", {})
    context_only = [
        label
        for label in dict.fromkeys(context_labels or [])
        if label not in labels and label in entries
    ]
    fingerprint = hashlib.sha256(
        json.dumps(
            {
                "targets": {
                    label: _design_plan_audit_fingerprint(ctx, label)
                    for label in sorted(labels)
                },
                "context": {
                    label: _design_plan_audit_fingerprint(ctx, label)
                    for label in sorted(context_only)
                },
                "evidence": hashlib.sha256(evidence.encode("utf-8")).hexdigest(),
            },
            sort_keys=True,
        ).encode("utf-8")
    ).hexdigest()
    attempt_key = "correction_escalation_fp" if escalated else "correction_base_fp"
    if labels and all(
        str((entries.get(label) or {}).get(attempt_key) or "") == fingerprint
        for label in labels
    ):
        _log(
            "  skipping unchanged interface-plan correction already attempted at "
            + ("escalation" if escalated else "base")
            + " tier"
        )
        _record(
            ctx.telemetry,
            "phase1_design_plan_correction",
            labels=labels,
            status="reused_unchanged_failure",
            tier="escalation" if escalated else "base",
            contract_fingerprint=fingerprint,
        )
        return False
    _log(
        "==> Phase 1 contract-plan correction "
        f"({'escalation' if escalated else 'base'}): "
        + ", ".join(labels[:8])
        + ("..." if len(labels) > 8 else "")
    )
    for label in labels:
        if label in entries:
            entries[label][attempt_key] = fingerprint
    tex_blocks = getattr(ctx, "tex_blocks", {})
    targets = "\n\n".join(
        f"## {label}\nBlueprint:\n```tex\n{tex_blocks.get(label, '')[:5000]}\n```\n"
        f"Current contract:\n{_render_design_plan_entry(label, entries.get(label) or {})}"
        for label in labels
    )
    context = "\n\n".join(
        f"## READ-ONLY CONTEXT {label}\n"
        f"{_render_design_plan_entry(label, entries.get(label) or {})}"
        for label in context_only
    )
    prompt = f"""TASK: CORRECT-BLUEPRINT-INTERFACE-PLAN

Correct only the connected interface contracts below. Some requested labels
may be provider contracts included because another requested contract refers
to a missing member on their public surface. Make the complete requested set
mutually consistent rather than merely renaming the consumer's missing member.
The blueprint is the source of truth. Preserve every object, parameter,
hypothesis, equation, and declaration-level property identified by the critic.
Do not edit the blueprint and do not emit Lean bodies or proofs.

Return exactly one JSON object using the same lossless schema as planning:
{{
  "contracts": [
    {{
      "label": "requested blueprint label",
      "target_signature": "complete Lean-ish target signature",
      "helpers": [
        {{"name": "stable helper name", "kind": "structure|inductive|class", "members": [{{"name": "stable_field_or_constructor", "type": "complete Lean-ish member type"}}], "purpose": "brief type-interface role"}}
      ],
      "decisions": ["semantic/interface decision generation must preserve"]
    }}
  ]
}}
Include every requested label and no others. Helpers may only be auxiliary
`structure`, `inductive`, or `class` interfaces needed to state the target.
Every helper member must include its complete Lean-ish type. A list of member
names without types is invalid because statement generation must not invent the
helper interface.
Never introduce a helper `def`, `abbrev`, `theorem`, or `lemma`: equations and
properties belong to the target contract/decisions and are implemented in
Phase 2. Each `target_signature` must contain exactly one top-level declaration,
whose name is the requested node's required Lean name. When one blueprint node
describes several operations, place those operations and their defining laws in
one plan-owned `structure` or `class` helper and make the single canonical
target return that interface. Preserve required type-interface helpers and
decisions; do not emit Lean bodies or proofs.

Contracts under READ-ONLY CONTEXT are supplied only so the requested contracts
can use their already-decided public surfaces consistently. Do not return or
rewrite those context contracts.

Critic evidence:
{evidence}

{targets}

{context}
"""
    result = _call_model(
        ctx,
        prompt,
        purpose="phase1_design_plan_correction",
        timeout=ctx.hard_timeout if escalated else ctx.base_timeout,
        effort=ctx.escalation_effort if escalated else ctx.base_effort,
        labels=labels,
        escalated=escalated,
    )
    if result.status != "ok" or not result.text.strip():
        return False
    corrected = _parse_design_plan_entries(ctx, labels, result.text)
    if set(corrected) != set(labels):
        return False
    old_fingerprints = {
        label: _design_plan_audit_fingerprint(ctx, label) for label in labels
    }
    old_rejection_metadata = {
        label: {
            key: entries[label].get(key)
            for key in (
                "rejected_audit_fp",
                "rejected_kind",
                "rejected_reason",
                "rejected_helpers",
                "correction_base_fp",
                "correction_escalation_fp",
            )
            if key in entries[label]
        }
        for label in labels
    }
    for label, entry in corrected.items():
        entry.pop("audit_fp", None)
        entries[label] = _preserve_plan_entry_progress(entries.get(label), entry)
    if all(
        _design_plan_audit_fingerprint(ctx, label) == old_fingerprints[label]
        for label in labels
    ):
        for label in labels:
            entries[label].update(old_rejection_metadata[label])
            entries[label][attempt_key] = fingerprint
        _record(
            ctx.telemetry,
            "phase1_design_plan_correction",
            labels=labels,
            status="unchanged",
            tier="escalation" if escalated else "base",
        )
        return False
    _sync_design_plan(ctx)
    _record(
        ctx.telemetry,
        "phase1_design_plan_correction",
        labels=labels,
        status="applied",
        tier="escalation" if escalated else "base",
    )
    return True


def _phase1_frontier_plan_gateway(
    ctx: Ctx,
    labels: Iterable[str],
    plan_order: list[str],
    closure_findings: dict[str, list[str]],
) -> dict[str, list[str]]:
    """Admit one dependency-ready plan slice to statement generation.

    The full plan is deliberately lightweight and untrusted.  Mechanical
    closure is computed globally, but paid semantic checking happens just in
    time for the next graph frontier.  A rejected contract is corrected with
    its direct provider/consumer slice as read-only context; unrelated plan
    entries are never rewritten.  The accepted audit fingerprint is persisted
    on each entry, so an unchanged frontier pays this gate only once.
    """
    ordered = [
        label
        for label in _design_plan_order(ctx, labels)
        if label in getattr(ctx, "design_plan_entries", {})
        and (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            != "phase1_candidate"
        )
        and not _uses_blueprint_direct_generation(ctx, label)
        and int(
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "schema_version"
            )
            or 0
        )
        == DESIGN_PLAN_SCHEMA_VERSION
    ]
    if not ordered:
        return closure_findings
    context_labels = sorted(
        _design_plan_context_labels(ctx, ordered) - set(ordered)
    )

    def invalidate_exhausted_entries(
        exhausted: Iterable[str], *, reason: str
    ) -> None:
        """Force fresh bounded planning after this contract cannot improve."""
        invalidated = [
            label
            for label in dict.fromkeys(exhausted)
            if label in getattr(ctx, "design_plan_entries", {})
        ]
        if not invalidated:
            return
        entries = ctx.design_plan_entries
        alternates = getattr(ctx, "design_plan_alternates", {})
        for label in invalidated:
            entries.pop(label, None)
            alternates.pop(label, None)
        _sync_design_plan(ctx)
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_invalidated",
            labels=invalidated,
            reason=reason,
            next_action="fresh_scoped_planning",
        )
    _record(
        ctx.telemetry,
        "phase1_frontier_plan_gateway",
        labels=ordered,
        context_labels=context_labels,
        status="started",
        contract_fingerprints={
            label: _design_plan_audit_fingerprint(ctx, label)
            for label in ordered
        },
    )

    def correct_direct_closure(
        current: dict[str, list[str]],
    ) -> dict[str, list[str]]:
        """Close defects owned by this frontier without editing future nodes."""
        direct = {
            label: list(current[label])
            for label in ordered
            if label in current
        }
        if not direct:
            return current
        affected = [label for label in ordered if label in direct]
        evidence = (
            "Phase 1 frontier contracts fail deterministic plan closure:\n- "
            + "\n- ".join(
                finding
                for label in affected
                for finding in direct[label]
            )
        )
        corrected = _correct_phase1_design_plan(
            ctx,
            affected,
            evidence,
            escalated=False,
            context_labels=context_labels,
        )
        correction_tier = "base"
        if not corrected:
            corrected = _correct_phase1_design_plan(
                ctx,
                affected,
                evidence,
                escalated=True,
                context_labels=context_labels,
            )
            correction_tier = "escalation"
        if corrected:
            current = _validate_design_plan_contract_closure(ctx, plan_order)
        remaining = {
            label: list(current[label])
            for label in affected
            if label in current
        }
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_closure",
            labels=affected,
            context_labels=context_labels,
            status="accepted" if corrected and not remaining else "rejected",
            correction_tier=correction_tier,
            findings=remaining,
        )
        if corrected and not remaining:
            return current
        invalidate_exhausted_entries(
            affected, reason="frontier_contract_closure_correction_exhausted"
        )
        route = _route_lean_generation_failure(affected)
        raise RepairRequest(
            evidence,
            list(route.failed_labels),
            section_labels=affected,
            context_labels=context_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            plan_revision_required=True,
        )

    # Global closure findings remain useful for future scheduling, but a
    # consumer that is not dependency-ready cannot block or rewrite today's
    # provider. Only defects whose consumer is in this frontier are repaired
    # here; direct providers/consumers are immutable correction context.
    closure_findings = correct_direct_closure(closure_findings)

    audit = _audit_phase1_design_plan(ctx, ordered)
    if audit is None:
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_gateway",
            labels=ordered,
            context_labels=context_labels,
            status="accepted",
            corrected_labels=[],
        )
        return closure_findings

    audit = _coerce_alignment_audit_result(audit)
    kind, reason, rejected, helpers = audit
    rejected_ordered = [label for label in ordered if label in rejected]
    if not rejected_ordered:
        rejected_ordered = list(ordered)

    blueprint_rejected = audit.labels_for("blueprint")
    decomposition_rejected = audit.labels_for("decomposition")
    repair_rejected = blueprint_rejected | decomposition_rejected
    if repair_rejected:
        repair_ordered = [
            label for label in rejected_ordered if label in repair_rejected
        ]
        deferred_plan_labels = [
            label for label in rejected_ordered if label not in repair_rejected
        ]
        repair_kind = "decomposition" if decomposition_rejected else "blueprint"
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_audit_routed",
            labels=rejected_ordered,
            blueprint_repair_labels=repair_ordered,
            deferred_plan_correction_labels=deferred_plan_labels,
            routed_kinds={
                label: audit.kinds_by_label.get(label, "lean-generation")
                for label in rejected_ordered
            },
        )
        raise RepairRequest(
            audit.reason_for(repair_ordered),
            repair_ordered,
            decomposition_helpers=(
                audit.helpers_for(decomposition_rejected)
                if repair_kind == "decomposition"
                else []
            ),
            section_labels=repair_ordered,
            context_labels=context_labels,
            authorizes_blueprint_repair=True,
            model_repair_labels=repair_ordered,
        )

    # An unavailable critic supplies no evidence that the plan is wrong. Route
    # it as infrastructure/generation retry rather than spending a correction
    # call on an arbitrary plan edit.
    if reason.startswith("interface-plan audit call failed:") or reason.startswith(
        "interface-plan audit returned invalid JSON:"
    ):
        route = _route_lean_generation_failure(rejected_ordered)
        raise RepairRequest(
            reason,
            list(route.failed_labels),
            section_labels=rejected_ordered,
            context_labels=context_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
        )

    corrected = _correct_phase1_design_plan(
        ctx,
        rejected_ordered,
        reason,
        escalated=False,
        context_labels=context_labels,
    )
    correction_tier = "base"
    if not corrected:
        corrected = _correct_phase1_design_plan(
            ctx,
            rejected_ordered,
            reason,
            escalated=True,
            context_labels=context_labels,
        )
        correction_tier = "escalation"
    if not corrected:
        route = _route_lean_generation_failure(rejected_ordered)
        invalidate_exhausted_entries(
            rejected_ordered, reason="frontier_semantic_correction_exhausted"
        )
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_gateway",
            labels=ordered,
            context_labels=context_labels,
            status="correction_exhausted",
            rejected_labels=rejected_ordered,
        )
        raise RepairRequest(
            reason,
            list(route.failed_labels),
            section_labels=rejected_ordered,
            context_labels=context_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            plan_revision_required=True,
        )

    # A semantic correction can introduce a mechanically invalid target
    # contract. Re-run closure globally for observability, but repair only the
    # changed frontier; future consumers remain queued for their own gateway.
    closure_findings = _validate_design_plan_contract_closure(ctx, plan_order)
    closure_findings = correct_direct_closure(closure_findings)

    repeated = _audit_phase1_design_plan(ctx, rejected_ordered)
    if repeated is not None:
        repeated = _coerce_alignment_audit_result(repeated)
        repeated_kind, repeated_reason, repeated_rejected, repeated_helpers = repeated
        retry_labels = [
            label for label in rejected_ordered if label in repeated_rejected
        ] or rejected_ordered
        repeated_blueprint = repeated.labels_for("blueprint")
        repeated_decomposition = repeated.labels_for("decomposition")
        repeated_repair = repeated_blueprint | repeated_decomposition
        if repeated_repair:
            repair_labels = [
                label for label in retry_labels if label in repeated_repair
            ]
            repair_kind = (
                "decomposition" if repeated_decomposition else "blueprint"
            )
            raise RepairRequest(
                repeated.reason_for(repair_labels),
                repair_labels,
                decomposition_helpers=(
                    repeated.helpers_for(repeated_decomposition)
                    if repair_kind == "decomposition"
                    else []
                ),
                section_labels=repair_labels,
                context_labels=context_labels,
                authorizes_blueprint_repair=True,
                model_repair_labels=repair_labels,
            )
        route = _route_lean_generation_failure(retry_labels)
        invalidate_exhausted_entries(
            retry_labels, reason="frontier_semantic_reaudit_rejected"
        )
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_gateway",
            labels=ordered,
            context_labels=context_labels,
            status="still_rejected",
            rejected_labels=retry_labels,
            correction_tier=correction_tier,
        )
        raise RepairRequest(
            repeated_reason,
            list(route.failed_labels),
            section_labels=retry_labels,
            context_labels=context_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            plan_revision_required=True,
        )

    _clear_retry_lifecycle(ctx, rejected_ordered, stage="phase1_statement")
    _prune_stale_generation_candidates(ctx)
    _record(
        ctx.telemetry,
        "phase1_frontier_plan_gateway",
        labels=ordered,
        context_labels=context_labels,
        status="accepted_after_correction",
        corrected_labels=rejected_ordered,
        correction_tier=correction_tier,
        remaining_global_closure_labels=sorted(closure_findings),
    )
    return closure_findings


def _closure_component_evidence(
    ctx: Ctx,
    component: list[str],
    findings: dict[str, list[str]],
    *,
    after_alternate: bool = False,
) -> tuple[str, list[str], list[str]]:
    """Render complete evidence for one connected closure component."""
    consumers = [label for label in component if label in findings]
    providers = sorted(
        {
            issue.provider
            for issue in _design_plan_contract_closure_issues(ctx, consumers)
            if issue.provider is not None and issue.provider in ctx.nodes
        }
    )
    prefix = (
        "Phase 1 interface-plan contract closure still rejected after trying "
        "the retained alternate candidate:\n- "
        if after_alternate
        else "Phase 1 interface-plan contract closure rejected:\n- "
    )
    evidence = prefix + "\n- ".join(
        finding for label in consumers for finding in findings[label]
    )
    editable_providers = [provider for provider in providers if provider in component]
    read_only_providers = [
        provider for provider in providers if provider not in component
    ]
    if editable_providers:
        evidence += (
            "\nProvider contract(s) with missing public members: "
            + ", ".join(editable_providers)
            + ". Correct provider and consumer surfaces together."
        )
    if read_only_providers:
        evidence += (
            "\nExisting dependency provider contract(s), supplied as read-only "
            "context: " + ", ".join(read_only_providers)
            + ". Correct the consumer; do not redesign these providers."
        )
    return evidence, consumers, providers


def _closure_component_score(
    ctx: Ctx,
    component: Iterable[str],
    findings: dict[str, list[str]],
) -> tuple[int, int, int]:
    """Monotonic score for one isolated closure-correction transaction."""
    scoped = _closure_findings_for_scope(ctx, findings, component)
    blocked = _closure_blocked_labels(ctx, scoped) if scoped else set()
    return (
        sum(len(messages) for messages in scoped.values()),
        len(blocked),
        len(scoped),
    )


def _closure_correction_stage(
    ctx: Ctx,
    component: list[str],
    findings: dict[str, list[str]],
) -> tuple[list[str], dict[str, list[str]]]:
    """Return the next provider-aware edit set and its exact evidence.

    Missing-member defects are handled first with the provider and only the
    consumers that impose requirements on its surface. Once provider surfaces
    are coherent, remaining authorization/alias/cycle defects edit consumers
    only.
    """
    member_findings: dict[str, list[str]] = {}
    member_targets: set[str] = set()
    for issue in _design_plan_contract_closure_issues(ctx, findings):
        if (
            issue.consumer in findings
            and issue.provider in component
            and issue.missing_provider_members
        ):
            member_targets.update((issue.consumer, issue.provider))
            member_findings.setdefault(issue.consumer, []).append(issue.message)
    stage_findings = member_findings or findings
    targets = member_targets or set(stage_findings)
    ordered_targets = [
        label
        for label in _design_plan_order(ctx, component)
        if label in targets
    ]
    return ordered_targets, stage_findings


def _correct_plan_closure_component_from_snapshot(
    ctx: Ctx,
    ordered: list[str],
    snapshot: dict[str, dict[str, Any]],
    component: list[str],
    evidence: str,
) -> PlanClosureCorrectionResult:
    """Make one bounded correction without mutating the live plan.

    Initial-plan closure is on Phase 1's critical path. Retained alternates are
    tried before this function, so one exact-evidence base call is the only paid
    correction permitted here. A strict partial improvement is preserved as an
    alternate, but unresolved contracts return to selective replanning instead
    of paying for serial base/escalation calls before any contract can freeze.
    """
    isolated = copy.copy(ctx)
    isolated.design_plan_entries = copy.deepcopy(snapshot)
    isolated.design_plan_alternates = {}
    isolated.design_plan = ""
    _sync_design_plan(isolated)
    started = time.time()
    initial = _evaluate_design_plan_candidate(
        isolated, ordered, isolated.design_plan_entries, "component-initial"
    )
    initial_findings = _closure_findings_for_scope(
        isolated, initial.findings, component
    )
    initial_score = _closure_component_score(
        isolated, component, initial_findings
    )
    targets, stage_findings = _closure_correction_stage(
        isolated, component, initial_findings
    )
    if not targets:
        finished = time.time()
        return PlanClosureCorrectionResult(
            tuple(component), {}, "not_corrected", initial_findings,
            finished - started, started, finished,
        )

    residual_evidence, _consumers, providers = _closure_component_evidence(
        isolated, component, stage_findings
    )
    corrected = _correct_phase1_design_plan(
        isolated,
        targets,
        residual_evidence,
        escalated=False,
        try_alternate=False,
        context_labels=[*component, *providers],
    )
    if corrected:
        candidate = _evaluate_design_plan_candidate(
            isolated,
            ordered,
            isolated.design_plan_entries,
            "component-correction",
        )
        candidate_findings = _closure_findings_for_scope(
            isolated, candidate.findings, component
        )
        candidate_score = _closure_component_score(
            isolated, component, candidate_findings
        )
    else:
        candidate_findings = initial_findings
        candidate_score = initial_score

    improved = corrected and candidate_score < initial_score
    _record(
        ctx.telemetry,
        "phase1_design_plan_closure_attempt",
        labels=targets,
        component_labels=component,
        context_labels=list(
            dict.fromkeys(
                [label for label in component if label not in targets]
                + [provider for provider in providers if provider not in targets]
            )
        ),
        attempt=1,
        tier="base",
        corrected=corrected,
        improved=improved,
        before_score=list(initial_score),
        after_score=list(candidate_score),
        residual_findings=candidate_findings,
    )

    finished = time.time()
    status = (
        "accepted"
        if corrected and not candidate_findings
        else "partially_improved"
        if improved
        else "still_rejected"
    )
    return PlanClosureCorrectionResult(
        tuple(component),
        (
            {
                label: copy.deepcopy(isolated.design_plan_entries[label])
                for label in component
            }
            if status in {"accepted", "partially_improved"}
            else {}
        ),
        status,
        candidate_findings,
        finished - started,
        started,
        finished,
    )


def _repair_phase1_design_plan_closure(
    ctx: Ctx,
    ordered: list[str],
    closure_findings: dict[str, list[str]],
    *,
    repair_scope: Iterable[str] | None = None,
) -> None:
    """Repair disjoint closure components concurrently from one plan snapshot.

    Retained alternates remain the zero-call first choice. The unresolved
    components are disjoint in the provider-consumer graph, so each model call
    sees the same immutable plan and only successful component entries are
    merged. A failed component cannot roll back a successful sibling.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    scope = set(repair_scope or [])
    remaining = (
        _closure_findings_for_scope(ctx, closure_findings, scope)
        if scope
        else closure_findings
    )

    # Alternates cost no model calls. Apply them first, then rescore once so
    # every paid correction starts from the same selected-plan snapshot.
    alternate_by_component: dict[tuple[str, ...], bool] = {}
    for component in _design_plan_closure_repair_components(ctx, remaining):
        evidence, consumers, _providers = _closure_component_evidence(
            ctx, component, remaining
        )
        if not consumers:
            continue
        alternate_by_component[tuple(component)] = (
            _try_alternate_design_plan_component(ctx, component, evidence)
        )
    if any(alternate_by_component.values()):
        validated = _validate_design_plan_contract_closure(ctx, ordered)
        remaining = (
            _closure_findings_for_scope(ctx, validated, scope)
            if scope
            else validated
        )
        if not remaining:
            return

    components = _design_plan_closure_repair_components(ctx, remaining)
    snapshot = copy.deepcopy(entries)
    pre_merge = _evaluate_design_plan_candidate(
        ctx, ordered, snapshot, "closure-wave-before"
    )
    wave_started = time.time()
    wave_id = hashlib.sha256(
        (
            str(time.time_ns())
            + json.dumps(
                {
                    label: _design_plan_audit_fingerprint(ctx, label)
                    for label in ordered
                    if label in entries
                },
                sort_keys=True,
            )
        ).encode("utf-8")
    ).hexdigest()[:16]
    work: list[tuple[list[str], str, list[str], list[str]]] = []
    for component in components:
        evidence, consumers, providers = _closure_component_evidence(
            ctx,
            component,
            remaining,
            after_alternate=alternate_by_component.get(tuple(component), False),
        )
        if consumers:
            work.append((component, evidence, consumers, providers))

    results: dict[tuple[str, ...], PlanClosureCorrectionResult] = {}
    worker_count = min(max(1, int(getattr(ctx, "workers", 1))), len(work))
    if work:
        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
            futures = {
                pool.submit(
                    _correct_plan_closure_component_from_snapshot,
                    ctx,
                    ordered,
                    snapshot,
                    component,
                    evidence,
                ): (component, consumers, providers)
                for component, evidence, consumers, providers in work
            }
            for future in concurrent.futures.as_completed(futures):
                component, consumers, providers = futures[future]
                result = future.result()
                results[tuple(component)] = result
                _record(
                    ctx.telemetry,
                    "phase1_outline_plan_closure_correction",
                    labels=component,
                    rejected_labels=consumers,
                    provider_labels=providers,
                    alternate_applied=alternate_by_component.get(
                        tuple(component), False
                    ),
                    corrected=result.status == "accepted",
                    correction_status=result.status,
                    reason="deterministic_contract_closure",
                    tier="base",
                    wave_id=wave_id,
                    wave_started_at_s=wave_started,
                    correction_started_at_s=result.started_at_s,
                    correction_finished_at_s=result.finished_at_s,
                    duration_s=result.duration_s,
                    pre_merge_score=list(pre_merge.score),
                    statement_fingerprints={
                        label: ctx.stmt_fps.get(label, "")
                        for label in component
                    },
                    plan_fingerprints={
                        label: _design_plan_audit_fingerprint(ctx, label)
                        for label in component
                    },
                    component_findings=result.findings,
                )

    merged_entries = copy.deepcopy(snapshot)
    merged_labels: set[str] = set()
    for component, _evidence, _consumers, _providers in work:
        result = results.get(tuple(component))
        if result is None or not result.entries:
            continue
        overlap = merged_labels & set(component)
        if overlap:
            raise RuntimeError(
                "closure correction components overlapped unexpectedly: "
                + ", ".join(sorted(overlap))
            )
        for label, entry in result.entries.items():
            merged_entries[label] = copy.deepcopy(entry)
            merged_entries[label]["closure_wave_id"] = wave_id
        merged_labels.update(result.entries)
    ctx.design_plan_entries = merged_entries
    entries = ctx.design_plan_entries
    _sync_design_plan(ctx)
    validated = _validate_design_plan_contract_closure(ctx, ordered)
    remaining = (
        _closure_findings_for_scope(ctx, validated, scope)
        if scope
        else validated
    )
    post_merge = _evaluate_design_plan_candidate(
        ctx, ordered, entries, "closure-wave-after"
    )
    _record(
        ctx.telemetry,
        "phase1_design_plan_closure_wave",
        labels=[label for component in components for label in component],
        wave_id=wave_id,
        started_at_s=wave_started,
        finished_at_s=time.time(),
        worker_count=worker_count if work else 0,
        component_count=len(work),
        merged_labels=sorted(merged_labels),
        failed_components=[
            list(component)
            for component, _evidence, _consumers, _providers in work
            if results.get(tuple(component)) is None
            or results[tuple(component)].status != "accepted"
        ],
        pre_merge_score=list(pre_merge.score),
        post_merge_score=list(post_merge.score),
    )
    if not remaining:
        return

    failed_components = _design_plan_closure_repair_components(ctx, remaining)
    failed = list(
        dict.fromkeys(label for component in failed_components for label in component)
    )
    alternates = getattr(ctx, "design_plan_alternates", None)
    if alternates is None:
        alternates = {}
        ctx.design_plan_alternates = alternates
    for label in failed:
        # A monotonically improved but not-yet-closed candidate remains a
        # retained alternate. Fresh planning may beat it, but it is no longer
        # silently lost merely because a sibling finding survived the wave.
        if label in entries and label in merged_labels:
            alternates[label] = copy.deepcopy(entries[label])
        entries.pop(label, None)
    _sync_design_plan(ctx)
    _record(
        ctx.telemetry,
        "phase1_design_plan_invalidated",
        labels=failed,
        rejected_labels=sorted(remaining),
        reason="contract_closure_correction_exhausted",
    )
    route = _route_lean_generation_failure(failed)
    raise RepairRequest(
        "Phase 1 cannot generate Lean from a mechanically impossible "
        "interface plan. The retained alternate and one bounded correction "
        "did not close these connected provider-consumer contracts; their "
        "plan entries were discarded for fresh planning on the next bounded "
        "retry:\n- "
        + "\n- ".join(
            finding
            for label in sorted(remaining)
            for finding in remaining[label]
        ),
        list(route.failed_labels),
        section_labels=failed,
        authorizes_blueprint_repair=False,
        failure_route=route,
        plan_revision_required=True,
    )


def _design_plan_context_labels(ctx: Ctx, labels: Iterable[str]) -> set[str]:
    """Small complete plan slice: targets plus direct providers/consumers."""
    targets = {label for label in labels if label in ctx.nodes}
    relevant = set(targets)
    for label in targets:
        relevant.update(dep for dep in ctx.nodes[label].uses if dep in ctx.nodes)
    relevant.update(
        label
        for label, node in ctx.nodes.items()
        if set(node.uses) & targets
    )
    return relevant


def _design_plan_block(
    ctx: Ctx, labels: Iterable[str] | None = None, *, budget: int = 9000
) -> str:
    """Render the relevant typed contract or compact semantic guidance."""
    entries = getattr(ctx, "design_plan_entries", {})
    if entries:
        selected = (
            set(entries)
            if labels is None
            else _design_plan_context_labels(ctx, labels) & set(entries)
        )
        plan = "\n".join(
            _render_design_plan_entry(label, entries[label])
            for label in _design_plan_order(ctx, selected)
            if not _uses_blueprint_direct_generation(ctx, label)
            if str(entries[label].get("target_signature") or "").strip()
        )
    else:
        semantic_entries = getattr(ctx, "semantic_plan_entries", {})
        selected = (
            set(semantic_entries)
            if labels is None
            else _design_plan_context_labels(ctx, labels) & set(semantic_entries)
        )
        plan = "\n".join(
            _render_semantic_plan_entry(label, semantic_entries[label])
            for label in _design_plan_order(ctx, selected)
        )
        if not plan:
            plan = getattr(ctx, "design_plan", "")
    target_labels = set(labels or [])
    direct_labels = sorted(
        label
        for label in target_labels
        if _uses_blueprint_direct_generation(ctx, label)
    )
    blocks: list[str] = []
    if plan:
        plan_kind = (
            "Exact typed contracts already realized by Phase-1 candidates"
            if entries
            else "Compact semantic guidance (advisory; blueprint is authoritative)"
        )
        blocks.append(
            plan_kind
            + " (use only when consistent with the blueprint and frozen Lean):\n```text\n"
            + plan[:budget]
            + "\n```\n"
        )
    if direct_labels:
        direct = getattr(ctx, "blueprint_direct_generation", {})
        evidence = "\n\n".join(
            f"{label}:\n{str((direct.get(label) or {}).get('evidence') or '')[-4000:]}"
            for label in direct_labels
        )
        blocks.append(
            "PLAN CIRCUIT BREAKER ACTIVE for: "
            + ", ".join(direct_labels)
            + ". The saved interface plan for these targets is known to be "
            "unusable. Generate their exact public statements directly from "
            "the blueprint, frozen dependency interfaces, and the rejection "
            "evidence below. Do not preserve or repair the rejected plan.\n"
            "```text\n"
            + evidence[-12000:]
            + "\n```\n"
        )
    return "\n".join(blocks)


def _compact_dependency_contract_table(ctx: Ctx, labels: Iterable[str]) -> str:
    """Lossless graph authority for planning without per-edge prose.

    The verbose compiler-facing table repeats ownership explanations for every
    edge. The semantic planner needs the same information, but only as stable
    names and two adjacency lists.
    """
    rows: list[str] = []
    for label in _design_plan_order(ctx, labels):
        node = ctx.nodes[label]
        statement = sorted(_statement_uses(node))
        proof_only = sorted(_proof_uses(node) - set(statement))
        rows.append(
            json.dumps(
                {
                    "label": label,
                    "lean": (
                        str(node.lean_decl or "").strip()
                        if node.mathlibok
                        else _lean_name(label)
                    ),
                    "statement": statement,
                    "proof_only": proof_only,
                },
                separators=(",", ":"),
                ensure_ascii=True,
            )
        )
    return "\n".join(rows)


def _semantic_plan_prompt(
    ctx: Ctx,
    labels: list[str],
    *,
    timeout_s: int,
) -> str:
    """Request compact root-aware guidance, never a Lean interface plan."""
    roots = _blueprint_roots(ctx.nodes, labels)
    root_text = "\n\n".join(
        f"### {label}\n{ctx.stmt_blocks.get(label, '')[:1800]}"
        for label in roots[:16]
    )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; `{_lean_name(label)}`)\n"
        f"{ctx.stmt_blocks.get(label, '')[:1400]}"
        for label in labels
    )
    return f"""TASK: COMPACT-BLUEPRINT-SEMANTIC-PLAN

Return JSON only:
{{
  "contracts": [
    {{
      "label": "exact blueprint label",
      "representation": "brief mathematical representation choice",
      "vocabulary": [{{"name": "stable Lean-style name", "purpose": "brief role"}}],
      "obligations": ["mathematical content the later statement must preserve"],
      "provider_requirements": [{{"provider": "direct statement dependency label", "capabilities": ["surface needed from that provider"]}}]
    }}
  ]
}}

This is a lightweight advisory plan for Phase 1, not a Lean declaration pass.
Do NOT write Lean signatures, binder types, structure fields, constructors,
proofs, imports, or definition bodies. The Phase-1 statement generator will
create the exact typed contract together with the actual Lean declaration, and
the compiler plus independent audit will judge that declaration directly.

Include exactly one compact entry for every requested label. Keep each
representation under 300 characters, at most 8 vocabulary names, at most 6
obligations, and at most 8 capabilities per provider. Root obligations may
shape representation choices and required semantics, but cannot add graph
edges. The graph table is authoritative:
- only `statement` providers may appear in `provider_requirements` or a public
  Phase-1 signature;
- `proof_only` providers are reserved for Phase 2 and must not shape a public
  signature merely because a proof will use them;
- Mathlib-owned names are already settled under the listed `lean` spelling.

The blueprint remains the sole mathematical source of truth. This plan may
coordinate vocabulary, but it may not weaken, strengthen, replace, or bundle
away any blueprint claim. If uncertain, preserve the obligation in plain
mathematical language and leave exact Lean typing to Phase 1.

This call has a wall-clock budget of about {timeout_s}s. Do not inspect files,
run Lean, or search libraries.

Blueprint: {ctx.name}

Authoritative dependency graph (JSON Lines):
```jsonl
{_compact_dependency_contract_table(ctx, labels)}
```

Root obligations:
{root_text or '- none'}

Nodes to coordinate ({len(labels)}):
{target_text}
"""


def _ensure_phase1_semantic_plan(
    ctx: Ctx, pending: set[str]
) -> None:
    """Create one bounded advisory plan without any pre-Phase-1 repair loop."""
    ordered = _design_plan_order(ctx, pending)
    entries = getattr(ctx, "semantic_plan_entries", {})
    ctx.semantic_plan_entries = entries
    stale = {
        label
        for label, entry in entries.items()
        if label not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        or int(entry.get("schema_version") or 0) != SEMANTIC_PLAN_SCHEMA_VERSION
    }
    for label in stale:
        entries.pop(label, None)
    missing = [label for label in ordered if label not in entries]
    if not missing:
        _record(
            ctx.telemetry,
            "phase1_semantic_plan_reused",
            labels=ordered,
            entry_count=len(ordered),
        )
        return

    # Unit-level scheduler callers intentionally use a lightweight context
    # with no runner configuration. They exercise traversal, not planning.
    # Populate the same deterministic fallback a failed advisory call would
    # produce, without requiring every test double to emulate a model runner.
    if not hasattr(ctx, "hard_timeout"):
        for label in missing:
            entries[label] = _semantic_plan_fallback_entry(ctx, label)
        return

    _log(
        "==> Phase 1 semantic plan: coordinating "
        f"{len(missing)} node(s) in one compact full-context call"
    )
    try:
        result = _call_model(
            ctx,
            _semantic_plan_prompt(ctx, missing, timeout_s=ctx.hard_timeout),
            purpose="phase1_semantic_plan",
            timeout=ctx.hard_timeout,
            effort=ctx.base_effort,
            labels=missing,
        )
    except RunnerError as exc:
        if not is_transient_error(exc) or is_environment_error(exc):
            raise
        # This plan is advisory: a provider/network outage must not prevent the
        # authoritative blueprint from proceeding to Phase 1 generation. The
        # mandatory generation call still uses the shared strict failure policy.
        result = CallResult(status="transport_exhausted", error=str(exc))
        _log(
            "  compact semantic planner unavailable after transport retries; "
            "using blueprint-only fallback guidance"
        )
    parsed: dict[str, dict[str, Any]] = {}
    findings: dict[str, list[str]] = {}
    if result.status == "ok" and result.text.strip():
        parsed, findings = _parse_semantic_plan_entries(ctx, missing, result.text)
    entries.update(parsed)
    fallback_labels = [label for label in missing if label not in parsed]
    for label in fallback_labels:
        entries[label] = _semantic_plan_fallback_entry(ctx, label)
    _record(
        ctx.telemetry,
        "phase1_semantic_plan_result",
        labels=missing,
        status=result.status,
        planned_count=len(parsed),
        fallback_count=len(fallback_labels),
        response_chars=len(result.text or ""),
        sanitized_findings=findings,
        schema_version=SEMANTIC_PLAN_SCHEMA_VERSION,
        authoritative=False,
    )
    _log(
        f"  semantic plan stored {len(parsed)}/{len(missing)} model entry/entries; "
        f"{len(fallback_labels)} blueprint-only fallback(s); no planning repair calls"
    )


def _blueprint_roots(nodes: dict[str, Node], labels: Iterable[str]) -> list[str]:
    """Theorem-like labels nothing else depends on: the paper's public results."""
    ordered_labels = list(dict.fromkeys(labels))
    consumed = {dep for label in nodes for dep in nodes[label].uses}
    return [
        label
        for label in ordered_labels
        if _is_theorem_like_kind(nodes[label].kind) and label not in consumed
    ]


def _design_plan_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    timeout_s: int,
    root_context_labels: Iterable[str] | None = None,
    feedback: str = "",
) -> str:
    """Ask for the interface plan only — no bodies, no proofs.

    Deciding the vocabulary root-first is cheap reasoning; writing every
    declaration is not. Splitting them keeps this call small enough to always
    land, and the resulting plan is short enough to inject into every later
    skeleton prompt, so all sections share one coherent design instead of each
    re-deriving it.
    """
    roots = _blueprint_roots(
        ctx.nodes, root_context_labels if root_context_labels is not None else labels
    )
    root_text = "\n\n".join(
        f"### ROOT {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`)\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:2500]}\n```"
        for label in roots[:12]
    )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:1200]}\n```"
        for label in labels
    )
    signatures = _frozen_interface_digest(sections, import_modules, budget=10000)
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    return f"""TASK: BLUEPRINT-SKELETON-DESIGN-PLAN

Return a PLAN only. No proofs and no definition bodies. Return exactly one
JSON object in this schema:
{{
  "contracts": [
    {{
      "label": "exact blueprint label",
      "target_signature": "complete Lean-ish target signature using the required Lean name",
      "helpers": [
        {{"name": "stable helper name", "kind": "structure|inductive|class", "members": [{{"name": "stable_field_or_constructor", "type": "complete Lean-ish member type"}}], "purpose": "brief type-interface role"}}
      ],
      "decisions": ["semantic/interface decision generation must preserve"]
    }}
  ]
}}

You are fixing the shared vocabulary for a Lean skeleton before it is written
section by section. Reason ROOT-FIRST: start from the public results under
"Root obligations", decide what each needs in order to be a NON-TRIVIAL,
faithful claim, and let that determine the shape of every definition beneath
it. The declarations themselves will be emitted later in dependency order.

Hard design rule: a definition must never assume the conclusion of a theorem
that depends on it. If a root asserts `X = Y` or `X ⊆ Y`, then `X` and `Y`
must be defined independently — folding the relation into either definition
makes the root vacuous.

Include exactly one contract for every requested node. A helper is permitted
only when the target needs an auxiliary `structure`, `inductive`, or `class`
type interface in order to be stated. Put that helper under its owning node and
give every stable field or constructor its complete Lean-ish type. A member-name
list without types is invalid: the later statement writer must copy the planned
interface rather than invent it. Never create helper `def`, `abbrev`,
`theorem`, or `lemma` declarations: their bodies/proofs would be untracked by
Phase 2. Put equations and semantic properties in the target signature when
they are part of the statement, or in `decisions` when they govern the target's
Phase-2 implementation. Record up to five decisions per node that a later
writer could otherwise get wrong. Do not collapse concrete blueprint objects
into opaque predicates or package names unless the compact helper surface
explicitly exposes the complete promised interface.

Each `target_signature` must contain exactly one top-level declaration and it
must use that node's required Lean name. A blueprint node may describe several
related mathematical operations, but that does not authorize several public
Lean targets for one node. Represent such a bundle with one plan-owned
`structure` or `class` helper whose fields expose the operations and defining
laws, then make the single canonical target return that interface.

The deterministic dependency-contract table below is the sole authoritative
allowed-symbol table for generated dependencies. A `statement interface` entry
may appear in `target_signature`. A `proof only` entry may guide the later
Phase-2 implementation, but it MUST NOT appear in `target_signature` merely
because the proof uses it. Every other non-library name in `target_signature`
must be the target's required Lean name or a structure/inductive/class helper
declared in that same contract. Do not infer another generated dependency from
the root context, surrounding prose, or mathematical convenience. Root context
may shape the meaning and strength of an interface, but it cannot add a
dependency edge absent from the blueprint graph. Do not put an executable
convenience function such as a custom logarithm, conversion, or constructor in
the signature unless it is an authorized statement-interface dependency or a
verified library declaration. Express it directly with available library
vocabulary, or require blueprint decomposition.

Keep signatures and decisions compact. This call has a budget of about
{timeout_s}s; it is a planning call, so do not verify every Mathlib API now —
note the intended type and move on.

{_design_plan_rules(ctx, labels)}

Correction required from a previous invalid planning response:
{feedback[-5000:] if feedback else '- none'}

Blueprint name: {ctx.name}

Frozen Lean interface already available (do not redesign these):
```lean
{signatures or '-- none'}
```

Authoritative direct dependency contracts (generated deterministically from
the blueprint graph; do not infer or invent additional dependency edges):
```text
{dependency_contracts}
```

Root obligations — design everything below to serve these:
{root_text or '- (no unconsumed theorem-like roots in this batch)'}

Target nodes to plan ({len(labels)} node(s), root-first planning order):
{target_text}
"""


def _generate_design_plan_candidate(
    ctx: Ctx,
    ordered: list[str],
    sections: list[Section],
    imports: list[str],
    root_context: list[str],
    candidate_id: str,
    *,
    max_empty_response_retries: int = 1,
    initial_feedback: str = "",
    timeout_s: int | None = None,
) -> DesignPlanCandidate:
    """Generate one independent full-context plan candidate."""
    call_timeout = timeout_s if timeout_s is not None else ctx.base_timeout
    candidate_entries: dict[str, dict[str, Any]] = {}
    missing = list(ordered)
    empty_response_retries = 0
    invalid_response_feedback = initial_feedback
    while missing:
        plan_labels = missing[:DESIGN_PLAN_MAX_NODES]
        result = _call_model(
            ctx,
            _design_plan_prompt(
                ctx,
                plan_labels,
                sections,
                imports,
                timeout_s=call_timeout,
                root_context_labels=root_context,
                feedback=invalid_response_feedback,
            ),
            purpose=f"phase1_design_plan_candidate_{candidate_id.lower()}",
            timeout=call_timeout,
            effort=ctx.base_effort,
            labels=plan_labels,
        )
        if result.status != "ok" or not result.text.strip():
            _record(
                ctx.telemetry,
                "phase1_design_plan_candidate_result",
                candidate_id=candidate_id,
                labels=plan_labels,
                status=result.status,
                planned_count=0,
            )
            break
        parsed = _parse_design_plan_entries(ctx, plan_labels, result.text)
        candidate_entries.update(parsed)
        missing_from_reply = sorted(set(plan_labels) - set(parsed))
        _record(
            ctx.telemetry,
            "phase1_design_plan_candidate_result",
            candidate_id=candidate_id,
            labels=plan_labels,
            status="ok" if parsed else "invalid_empty_contracts",
            planned_labels=sorted(parsed),
            planned_count=len(parsed),
            missing_labels=missing_from_reply,
            chars=len(result.text),
        )
        if not parsed:
            if empty_response_retries < max_empty_response_retries:
                empty_response_retries += 1
                invalid_response_feedback = (
                    "The previous response contained zero usable contracts. "
                    f"Return exactly {len(plan_labels)} contracts, one for each "
                    "requested label, in the required JSON schema. Do not return "
                    "an empty contracts array or any Lean code."
                )
                continue
            break
        empty_response_retries = 0
        invalid_response_feedback = ""
        missing = [label for label in ordered if label not in candidate_entries]

    return _evaluate_design_plan_candidate(
        ctx, ordered, candidate_entries, candidate_id
    )


def _initial_design_plan_tournament(
    ctx: Ctx,
    ordered: list[str],
    sections: list[Section],
    imports: list[str],
    root_context: list[str],
) -> tuple[DesignPlanCandidate, DesignPlanCandidate]:
    """Admit the first complete plan whose initial frontier is executable.

    Two independent full-context candidates hedge model variability. A plan
    with complete JSON coverage is not automatically usable: deterministic
    closure must leave the entire initial dependency-ready frontier open. A
    qualifying lane may start Phase 1 without waiting for a redundant sibling;
    if neither lane qualifies, the outer bounded repair loop restarts the whole
    tournament instead of serially repairing a catastrophic shared plan.
    """
    _log(
        "==> Phase 1 design plan: generating two independent full-context "
        f"candidates concurrently ({len(ordered)} nodes)"
    )
    candidates: list[DesignPlanCandidate] = []
    # Lightweight callers created before the separate hard-timeout setting may
    # only provide base_timeout. Preserve that compatibility while ensuring a
    # real run gives both full-context lanes the longer configured budget.
    planner_timeout = max(
        ctx.base_timeout,
        getattr(ctx, "hard_timeout", ctx.base_timeout),
    )
    retry_feedback = _generation_feedback_for(ctx, ordered)

    def finish(
        selected: DesignPlanCandidate,
        completed: list[DesignPlanCandidate],
        merged_components: list[list[str]],
        *,
        selection_mode: str = "closed_initial_frontier",
    ) -> tuple[DesignPlanCandidate, DesignPlanCandidate]:
        alternates = [candidate for candidate in completed if candidate is not selected]
        alternate = min(
            alternates or [selected],
            key=lambda item: (item.score, item.candidate_id),
        )
        for candidate in completed:
            clean_admissible, frontier, blocked = _initial_plan_admission(
                ctx, ordered, candidate
            )
            repairable, _frontier, _blocked, repair_work, tournament_work = (
                _initial_plan_repair_admission(ctx, ordered, candidate)
            )
            _record(
                ctx.telemetry,
                "phase1_design_plan_candidate_scored",
                candidate_id=candidate.candidate_id,
                labels=ordered,
                score=list(candidate.score),
                planned_count=len(candidate.entries),
                missing_labels=candidate.missing,
                blocked_labels=sorted(candidate.blocked),
                component_count=len(candidate.components),
                findings=[
                    finding
                    for label in sorted(candidate.findings)
                    for finding in candidate.findings[label]
                ],
                initial_frontier=frontier,
                blocked_initial_frontier=blocked,
                admissible=clean_admissible or repairable,
                clean_initial_frontier=clean_admissible,
                scoped_repair_admissible=repairable,
                estimated_repair_work=repair_work,
                estimated_tournament_work=tournament_work,
                selected=candidate is selected,
            )
        _record(
            ctx.telemetry,
            "phase1_design_plan_tournament",
            labels=ordered,
            primary_candidate=selected.candidate_id,
            alternate_candidate=alternate.candidate_id,
            selected_candidate=selected.candidate_id,
            selected_score=list(selected.score),
            merged_components=merged_components,
            admission_policy="complete_frontier_or_cheaper_scoped_repair",
            selection_mode=selection_mode,
        )
        if selection_mode == "cheaper_scoped_repair":
            repair_work, tournament_work = _initial_plan_repair_costs(
                selected, len(ordered)
            )
            _log(
                "  design-plan tournament admitted "
                f"{selected.candidate_id} for scoped closure repair "
                f"({repair_work} estimated work units vs {tournament_work} "
                "for another tournament); "
                f"merged {len(merged_components)} improving component(s)"
            )
        else:
            _log(
                "  design-plan tournament admitted "
                f"{selected.candidate_id} with score {selected.score}; "
                f"merged {len(merged_components)} improving component(s)"
            )
        fallback_entries: dict[str, dict[str, Any]] = {}
        for label in ordered:
            selected_entry = selected.entries.get(label)
            for candidate in completed:
                candidate_entry = candidate.entries.get(label)
                if candidate_entry is not None and candidate_entry != selected_entry:
                    fallback_entries[label] = copy.deepcopy(candidate_entry)
                    break
        fallback = _evaluate_design_plan_candidate(
            ctx, ordered, fallback_entries, "per-node-alternate"
        )
        return selected, fallback

    pool = concurrent.futures.ThreadPoolExecutor(max_workers=2)
    futures = {
        pool.submit(
            _generate_design_plan_candidate,
            ctx,
            ordered,
            sections,
            imports,
            root_context,
            candidate_id,
            max_empty_response_retries=0,
            initial_feedback=retry_feedback,
            timeout_s=planner_timeout,
        ): candidate_id
        for candidate_id in ("A", "B")
    }
    returned_early = False
    try:
        while futures:
            done, _pending = concurrent.futures.wait(
                futures,
                return_when=concurrent.futures.FIRST_COMPLETED,
            )
            for future in done:
                candidate_id = futures.pop(future)
                candidate = future.result()
                candidates.append(candidate)
                admissible, frontier, blocked = _initial_plan_admission(
                    ctx, ordered, candidate
                )
                _record(
                    ctx.telemetry,
                    "phase1_design_plan_candidate_admission",
                    candidate_id=candidate_id,
                    score=list(candidate.score),
                    initial_frontier=frontier,
                    blocked_initial_frontier=blocked,
                    admissible=admissible,
                )
                if not admissible:
                    _log(
                        "  design-plan tournament rejected "
                        f"{candidate_id}: initial frontier "
                        f"{len(frontier) - len(blocked)}/{len(frontier)} ready"
                    )
                    continue
                for sibling in futures:
                    sibling.cancel()
                returned_early = True
                pool.shutdown(wait=False, cancel_futures=True)
                return finish(candidate, candidates, [])
    finally:
        if not returned_early:
            pool.shutdown(wait=True, cancel_futures=True)

    candidates.sort(key=lambda item: (item.score, item.candidate_id))
    primary = candidates[0]
    alternate = candidates[1] if len(candidates) > 1 else candidates[0]
    selected, merged_components = _merge_design_plan_candidates(
        ctx, ordered, primary, alternate
    )
    admissible, frontier, blocked = _initial_plan_admission(ctx, ordered, selected)
    if admissible:
        return finish(selected, candidates, merged_components)

    repair_options: list[
        tuple[int, tuple[int, int, int, int], str, DesignPlanCandidate]
    ] = []
    seen_options: set[int] = set()
    for option in [selected, *candidates]:
        if id(option) in seen_options:
            continue
        seen_options.add(id(option))
        repairable, _frontier, _blocked, repair_work, _tournament_work = (
            _initial_plan_repair_admission(ctx, ordered, option)
        )
        if repairable:
            repair_options.append(
                (repair_work, option.score, option.candidate_id, option)
            )
    if repair_options:
        repair_selected = min(repair_options)[-1]
        return finish(
            repair_selected,
            candidates,
            merged_components if repair_selected is selected else [],
            selection_mode="cheaper_scoped_repair",
        )

    for candidate in candidates:
        (
            candidate_repairable,
            _frontier,
            candidate_blocked,
            candidate_repair_work,
            candidate_tournament_work,
        ) = _initial_plan_repair_admission(ctx, ordered, candidate)
        _record(
            ctx.telemetry,
            "phase1_design_plan_candidate_scored",
            candidate_id=candidate.candidate_id,
            labels=ordered,
            score=list(candidate.score),
            planned_count=len(candidate.entries),
            missing_labels=candidate.missing,
            blocked_labels=sorted(candidate.blocked),
            component_count=len(candidate.components),
            findings=[
                finding
                for label in sorted(candidate.findings)
                for finding in candidate.findings[label]
            ],
            initial_frontier=frontier,
            blocked_initial_frontier=candidate_blocked,
            admissible=False,
            clean_initial_frontier=False,
            scoped_repair_admissible=candidate_repairable,
            estimated_repair_work=candidate_repair_work,
            estimated_tournament_work=candidate_tournament_work,
            selected=False,
        )
    _record(
        ctx.telemetry,
        "phase1_design_plan_tournament",
        labels=ordered,
        primary_candidate=primary.candidate_id,
        alternate_candidate=alternate.candidate_id,
        selected_candidate="",
        selected_score=list(selected.score),
        merged_components=merged_components,
        admission_policy="complete_frontier_or_cheaper_scoped_repair",
        status="rejected_no_admissible_plan",
    )
    _log(
        "  design-plan tournament produced no admissible plan; restarting "
        "the complete tournament through the bounded repair loop"
    )
    evidence = (
        "The independent initial planning candidates were complete or exhausted, "
        "but none left the entire initial dependency-ready frontier mechanically "
        "closed or had a bounded closure-repair estimate cheaper than another "
        "two-lane full-context tournament. Discard every candidate and restart "
        "the full-context planning tournament; do not enter Phase 1 with a "
        "globally expensive plan.\n"
        + "\n".join(
            f"- candidate {candidate.candidate_id}: score={candidate.score}; "
            f"blocked initial frontier="
            f"{', '.join(sorted(set(frontier) & candidate.blocked)) or 'none'}; "
            f"repair/tournament work={_initial_plan_repair_costs(candidate, len(ordered))}"
            for candidate in candidates
        )
    )
    raise RepairRequest(
        evidence,
        list(ordered),
        section_labels=list(ordered),
        authorizes_blueprint_repair=False,
        failure_route=_route_lean_generation_failure(ordered),
    )


def _ensure_phase1_design_plan(
    ctx: Ctx,
    pending: set[str],
    sections: list[Section],
    *,
    defer_closure_repair: bool = False,
) -> dict[str, list[str]]:
    """Create or extend the shared root-first contract plan for Phase 1.

    Traversal still controls declaration generation. This planning call is
    traversal-independent: it fixes shared contract decisions once so either
    traversal can transcribe them without redesigning each section locally.
    """
    _prune_stale_design_plan(ctx)
    ordered = _design_plan_order(ctx, pending)
    entries = getattr(ctx, "design_plan_entries", None)
    if entries is None:
        entries = {}
        ctx.design_plan_entries = entries
    missing = [
        label
        for label in ordered
        if label not in entries
        and not _uses_blueprint_direct_generation(ctx, label)
    ]
    if not missing:
        if ordered:
            _record(
                ctx.telemetry,
                "phase1_design_plan_reused",
                labels=ordered,
                entry_count=len(ordered),
            )

    imports = _sections_for_deps(ctx, ordered, sections)
    root_context = [
        label for label, node in ctx.nodes.items() if not node.mathlibok
    ]
    if not entries and len(missing) > 1:
        selected, alternate = _initial_design_plan_tournament(
            ctx,
            ordered,
            sections,
            imports,
            root_context,
        )
        entries.update(copy.deepcopy(selected.entries))
        ctx.design_plan_alternates = {
            label: copy.deepcopy(entry)
            for label, entry in alternate.entries.items()
            if label in entries and entry != entries[label]
        }
        _sync_design_plan(ctx)
        _record(
            ctx.telemetry,
            "phase1_design_plan_result",
            labels=ordered,
            status="tournament_selected",
            planned_labels=sorted(entries),
            planned_count=len(entries),
            missing_labels=[label for label in ordered if label not in entries],
            alternate_count=len(ctx.design_plan_alternates),
            selected_score=list(selected.score),
        )
        missing = [
            label
            for label in ordered
            if label not in entries
            and not _uses_blueprint_direct_generation(ctx, label)
        ]
        if missing:
            _activate_blueprint_direct_generation(
                ctx,
                missing,
                "The full-context planning tournament returned no usable "
                "contract for these labels. Phase 1 must formalize their "
                "statements directly from the blueprint instead of paying "
                "another global planning call.",
                source="initial_plan_missing_contract",
            )
            missing = []

    empty_response_retries = 0
    invalid_response_feedback = ""
    while missing:
        # Ordinary papers fit in one call. Very large graphs are bounded here
        # so planning itself cannot become the oversized prompt Phase 1 is
        # intended to eliminate.
        plan_labels = missing[:DESIGN_PLAN_MAX_NODES]
        _log(
            f"==> Phase 1 design plan: fixing {len(plan_labels)} missing contract "
            f"decision(s) root-first ({len(entries)} reused)"
        )
        result = _call_model(
            ctx,
            _design_plan_prompt(
                ctx,
                plan_labels,
                sections,
                imports,
                timeout_s=ctx.base_timeout,
                root_context_labels=root_context,
                feedback=(
                    invalid_response_feedback
                    or _generation_feedback_for(ctx, plan_labels)
                ),
            ),
            purpose="phase1_design_plan",
            timeout=ctx.base_timeout,
            effort=ctx.base_effort,
            labels=plan_labels,
        )
        if result.status != "ok" or not result.text.strip():
            _record(
                ctx.telemetry,
                "phase1_design_plan_result",
                labels=plan_labels,
                status=result.status,
                planned_count=0,
            )
            _log(
                f"  design plan {result.status}; Phase 1 continues with existing "
                "plan entries"
            )
            break

        parsed = _parse_design_plan_entries(ctx, plan_labels, result.text)
        entries.update(parsed)
        _sync_design_plan(ctx)
        missing_from_reply = sorted(set(plan_labels) - set(parsed))
        response_status = "ok" if parsed else "invalid_empty_contracts"
        _record(
            ctx.telemetry,
            "phase1_design_plan_result",
            labels=plan_labels,
            status=response_status,
            planned_labels=sorted(parsed),
            planned_count=len(parsed),
            missing_labels=missing_from_reply,
            chars=len(result.text),
        )
        _log(
            f"  design plan stored {len(parsed)}/{len(plan_labels)} contract "
            f"decision(s); {len(entries)} reusable entry/entries total"
        )
        if not parsed:
            if empty_response_retries < 1:
                empty_response_retries += 1
                invalid_response_feedback = (
                    "The previous response contained zero usable contracts. "
                    f"Return exactly {len(plan_labels)} contracts, one for each "
                    "requested label, in the required JSON schema. Do not return "
                    "an empty contracts array or any Lean code."
                )
                _log(
                    "  invalid zero-contract design plan; retrying once with "
                    "explicit completeness feedback"
                )
                continue
            break
        empty_response_retries = 0
        invalid_response_feedback = ""
        missing = [
            label
            for label in ordered
            if label not in entries
            and not _uses_blueprint_direct_generation(ctx, label)
        ]

    missing = [
        label
        for label in ordered
        if label not in entries
        and not _uses_blueprint_direct_generation(ctx, label)
    ]
    if missing:
        _activate_blueprint_direct_generation(
            ctx,
            missing,
            "The scoped design-plan call omitted these contracts. Generate "
            "their exact statements directly from the blueprint and frozen "
            "dependency interfaces.",
            source="scoped_plan_missing_contract",
        )
    closure_findings = _validate_design_plan_contract_closure(ctx, ordered)
    if closure_findings:
        if defer_closure_repair:
            _record(
                ctx.telemetry,
                "phase1_design_plan_closure_deferred",
                labels=sorted(closure_findings),
                blocked_labels=sorted(
                    _closure_blocked_labels(ctx, closure_findings)
                ),
            )
            return closure_findings
        _repair_phase1_design_plan_closure(ctx, ordered, closure_findings)
    # Do not audit the complete proposed plan here. The dependency-ready
    # frontier gateway checks only contracts that are about to reach statement
    # generation, with direct providers and consumers as bounded context.
    # Generated declarations still have to satisfy deterministic checks,
    # compile, and pass the independent statement-alignment audit before they
    # freeze; a frontier-plan verdict is never evidence of Lean correctness.
    _record(
        ctx.telemetry,
        "phase1_design_plan_ready",
        labels=ordered,
        entry_count=len(ordered),
        acceptance_policy="compiled_declarations_final_audit",
    )
    return {}


def _bulk_skeleton_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    timeout_s: int,
    initial_only: bool = False,
) -> str:
    """Emit one chunk of the skeleton using the shared design proposal.

    Statements are compiled leaf-first (Lean cannot elaborate a reference to a
    declaration that does not exist yet), but they were *designed* root-first
    by the plan pass, so this call is transcription rather than design.
    """
    if initial_only:
        return _initial_declaration_prompt(
            ctx,
            labels,
            sections,
            import_modules,
            timeout_s=timeout_s,
        )
    roots = _blueprint_roots(ctx.nodes, labels)
    root_text = "\n\n".join(
        f"### ROOT {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`)\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:3000]}\n```"
        for label in roots[:12]
    )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:2500]}\n```"
        for label in labels
    )
    signatures = _frozen_interface_digest(sections, import_modules, budget=14000)
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    return f"""TASK: BLUEPRINT-SKELETON-SECTION

Return exactly one Lean 4 file (one code block). No commentary.

Emit the statement of EVERY target node below — statements only, no proofs.
The compact guidance above coordinates semantic choices and vocabulary, but
is not a typed Lean contract. Emit declarations in dependency order. The exact
typed target/helper surfaces in this response are persisted together as the
candidate contract and then checked deterministically, compiled, and audited
against the blueprint.

Per-node rules:
- definition-kind nodes (definition/defn/construction/notation/convention):
  emit the exact public type/interface. End a `def`/`abbrev` body in
  `:= sorry`; Phase 2 implements it. A `structure`/`inductive` must expose its
  exact fields/constructors and cannot contain `sorry`. A type-valued target
  whose complete contract is a same-node structure/class/inductive returned
  in this response
  may be a transparent alias directly to that helper; this is an interface,
  not an implementation body.
- theorem-like nodes (lemma/proposition/theorem/corollary and EVERY other
  environment kind, e.g. claim/fact/remark): the exact statement as a
  `theorem` ending in `:= sorry`. Do NOT attempt proofs in this pass.
- Give each blueprint node exactly the Lean name listed for it.
- Besides same-node `structure`/`inductive`/`class` interfaces, emit no
  auxiliary declarations. Executable helpers are not Phase-1 outline work; a
  separate mathematical obligation requires `NEEDS-DECOMPOSITION`.
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

{_design_plan_block(ctx, labels)}

Root obligations these statements must serve:
{root_text or '- (no unconsumed theorem-like roots in this batch)'}

Target nodes for THIS file ({len(labels)} node(s), listed in dependency order):
{target_text}
"""


def _delivered_decl_texts(
    parsed: ParsedModule,
    part_labels: list[str],
    all_target_names: set[str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> list[str] | None:
    """Select a complete helper-connected target component.

    A candidate cannot be split across a helper used by targets on both sides:
    doing so either drops the helper or emits the same global helper in two
    imported modules. Return ``None`` for such a split so routing keeps that
    component atomic.
    """
    part_names = {_lean_name(label) for label in part_labels}
    target_by_name = {name: name for name in all_target_names}
    # This slicing helper represents target identities by Lean declaration
    # name, while the plan ownership map stores blueprint labels. Normalize the
    # latter at this boundary so ownership comparisons use one identity space.
    explicit = {
        name: owner if owner in all_target_names else _lean_name(owner)
        for name, owner in (explicit_owner_by_name or {}).items()
    }
    components = _target_components_from_helpers(
        parsed, target_by_name, explicit
    )
    for component in components:
        if component & part_names and not component <= part_names:
            return None
    consumers = _declaration_target_consumers(
        parsed, target_by_name, explicit
    )
    chosen: list[str] = []
    seen: set[str] = set()
    for index, decl in enumerate(parsed.decls):
        name = decl.name or ""
        if name in part_names:
            chosen.append(decl.text)
            seen.add(name)
        elif name not in all_target_names and consumers.get(index, set()) & part_names:
            chosen.append(decl.text)
    if part_names != seen:
        return None
    return chosen


def _salvage_timeout_declarations(
    ctx: Ctx,
    labels: list[str],
    partial_text: str,
    *,
    realize_contracts: bool = False,
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
        parsed = _ingest_model_lean(
            ctx,
            labels,
            partial_text,
            realize_contracts=realize_contracts,
        ).parsed
    except (ValueError, Exception):
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
    initial_only: bool = False,
    generation_tier: str = "delivered",
    failure_evidence: list[str] | None = None,
    failure_candidate_code: list[str] | None = None,
    route_plan_defects: bool = False,
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
    section_kind = "Initial declaration section" if initial_only else "Skeleton section"
    _log(
        f"==> {section_kind} {next_number:02d}: {len(labels)} node(s) from "
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
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    module_code, _ranges = _compose_module(
        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
    )
    sessions: dict[str, str] = {}
    # The initial pass exists only to establish a compilable environment for
    # root-first Phase 1.  Coverage and compilation are required here; exact
    # blueprint-contract alignment is deliberately deferred to Phase 1.
    findings = [] if initial_only else _skeleton_code_findings(
        module_code,
        target_kinds,
        label_by_lean_name,
        _planned_helper_owner_by_name(ctx, labels),
    )
    defer_alignment = bool(getattr(ctx, "defer_phase1_alignment", False))
    if not initial_only:
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
                if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                    decl.text = _normalize_terminal_sorry(decl.text)
            module_code, _ranges = _compose_module(
                [f"import {module}" for module in import_modules]
                + list(parsed.imports),
                parsed.preamble,
                [decl.text for decl in parsed.decls],
            )
            findings = [] if initial_only else _skeleton_code_findings(
                module_code,
                target_kinds,
                label_by_lean_name,
                _planned_helper_owner_by_name(ctx, labels),
            )
            if not initial_only:
                findings += _skeleton_deterministic_findings(
                    module_code, ctx, labels
                )
    if findings:
        if failure_candidate_code is not None:
            failure_candidate_code.append(module_code)
        if failure_evidence is not None:
            failure_evidence.append(
                "Deterministic checks rejected delivered statements:\n"
                + _format_skeleton_findings(findings)
            )
        _log(
            f"  delivered code failed deterministic checks ({len(findings)} "
            "issue(s)); regenerating the part"
        )
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="deterministic_rejected")
        _discard_section_artifacts(path)
        return None
    path.write_text(module_code, encoding="utf-8")
    ok, output = _check_lean(path, ctx.lean_command)
    if not ok:
        # Diagnose import/environment failures with the identical declarations
        # before paying a model to rewrite them. The broad environment is kept
        # only when it makes the unchanged candidate compile.
        original_output = output
        broad_imports = ["import Mathlib"] + [
            f"import {module}" for module in import_modules
        ] + list(parsed.imports)
        broad_code, broad_ranges = _compose_module(
            broad_imports,
            parsed.preamble,
            [decl.text for decl in parsed.decls],
        )
        path.write_text(broad_code, encoding="utf-8")
        broad_ok, broad_output = _check_lean(path, ctx.lean_command)
        if broad_ok:
            parsed.imports = list(
                dict.fromkeys(["import Mathlib"] + list(parsed.imports))
            )
            module_code, _ranges = broad_code, broad_ranges
            ok, output = True, broad_output
            _record(
                ctx.telemetry,
                "phase1_environment_fallback",
                labels=labels,
                status="resolved_without_model",
                added_import="Mathlib",
            )
            _log(f"  {origin} compiled unchanged under the complete Mathlib environment")
        else:
            path.write_text(module_code, encoding="utf-8")
            output = original_output

    if (
        not ok
        and allow_patch
        and route_plan_defects
        and not initial_only
        and _phase1_compile_plan_defects(ctx, labels, module_code, output)
    ):
        if failure_candidate_code is not None:
            failure_candidate_code.append(module_code)
        if failure_evidence is not None:
            failure_evidence.append(
                "Lean rejected a plan-realizing interface:\n" + output[-12000:]
            )
        _record(
            ctx.telemetry,
            "phase1_compile_plan_defect_short_circuit",
            labels=labels,
            error_shape=_lean_error_shape(output),
        )
        _log(
            f"  {origin} copied a compiler-invalid accepted plan; "
            "skipping statement patches"
        )
        _discard_section_artifacts(path)
        return None

    if not ok and allow_patch:
        if not initial_only:
            _store_generation_candidates(
                ctx,
                labels,
                module_code,
                source=f"{origin}_compile_baseline",
                all_labels=labels,
                generation_tier=generation_tier,
                lean_status="failed",
                lean_output=output,
            )
        pending_findings: list[SkeletonFinding] = []
        for correction_round in range(1, COMPILER_CORRECTION_ROUNDS + 1):
            compile_findings = pending_findings or _lean_compile_findings(
                parsed,
                labels,
                _ranges,
                output,
                path.name,
                _planned_helper_owner_by_name(ctx, labels),
            )
            pending_findings = []
            if not _patchable_skeleton_labels(compile_findings, labels):
                break
            _log(
                f"  {origin} failed Lean; correcting the isolated declaration(s) "
                f"inside the same transaction ({correction_round}/"
                f"{COMPILER_CORRECTION_ROUNDS})"
            )
            patched, _note = _targeted_patch_skeleton_decls(
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
            if patched is None:
                break
            parsed = patched
            for decl in parsed.decls:
                if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                    decl.text = _normalize_terminal_sorry(decl.text)
            current_imports = [
                f"import {module}" for module in import_modules
            ] + list(parsed.imports)
            module_code, _ranges = _compose_module(
                current_imports,
                parsed.preamble,
                [decl.text for decl in parsed.decls],
            )
            post = [] if initial_only else _skeleton_code_findings(
                module_code,
                target_kinds,
                label_by_lean_name,
                _planned_helper_owner_by_name(ctx, labels),
            )
            if not initial_only:
                post += _skeleton_deterministic_findings(
                    module_code, ctx, labels
                )
            if not initial_only and post:
                _store_generation_candidates(
                    ctx,
                    labels,
                    module_code,
                    source=f"{origin}_compiler_correction",
                    all_labels=labels,
                    generation_tier=generation_tier,
                    lean_status="unknown",
                )
                retained_code = _retained_generation_candidate_code(ctx, labels)
                if retained_code:
                    module_code = retained_code
                    parsed = _parse_module(module_code)
                    module_code, _ranges = _compose_module(
                        parsed.imports,
                        parsed.preamble,
                        [decl.text for decl in parsed.decls],
                    )
                    post = _skeleton_code_findings(
                        module_code,
                        target_kinds,
                        label_by_lean_name,
                        _planned_helper_owner_by_name(ctx, labels),
                    )
                    post += _skeleton_deterministic_findings(
                        module_code, ctx, labels
                    )
            if post:
                pending_findings = post
                output = _format_skeleton_findings(post)
                continue
            path.write_text(module_code, encoding="utf-8")
            ok, output = _check_lean(path, ctx.lean_command)
            if (
                not ok
                and route_plan_defects
                and _phase1_compile_plan_defects(
                    ctx, labels, module_code, output
                )
            ):
                _record(
                    ctx.telemetry,
                    "phase1_compile_plan_defect_short_circuit",
                    labels=labels,
                    error_shape=_lean_error_shape(output),
                    after_correction_round=correction_round,
                )
                _log(
                    f"  {origin} repeated a compiler failure while exactly "
                    "realizing its accepted plan; stopping statement patches"
                )
                break
            if not initial_only:
                _store_generation_candidates(
                    ctx,
                    labels,
                    module_code,
                    source=f"{origin}_compiler_check",
                    all_labels=labels,
                    generation_tier=generation_tier,
                    lean_status="passed" if ok else "failed",
                    lean_output=output,
                )
                # Keep compiling from this deterministic-clean intermediate
                # even when it has the same number of Lean errors as the best
                # candidate. The best remains the rollback point in persisted
                # state; rebasing here would repeat the old error forever.
            if ok:
                break
    if not ok:
        if failure_candidate_code is not None:
            failure_candidate_code.append(module_code)
        if failure_evidence is not None:
            failure_evidence.append("Lean rejected delivered statements:\n" + output[-12000:])
        _log("  delivered code failed Lean; regenerating the part")
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="lean_rejected")
        _discard_section_artifacts(path)
        return None
    if not initial_only and not defer_alignment:
        audit = _model_alignment_audit(ctx, labels, module_code, tag="delivered")
        if audit is not None:
            kind, reason, rejected, helpers = audit
            if kind in {"blueprint", "decomposition"}:
                _discard_section_artifacts(path)
                raise RepairRequest(
                    reason,
                    sorted(rejected),
                    decomposition_helpers=helpers if kind == "decomposition" else None,
                    section_labels=labels,
                )
            _log("  delivered code rejected by alignment audit; regenerating the part")
            if failure_candidate_code is not None:
                failure_candidate_code.append(module_code)
            if failure_evidence is not None:
                failure_evidence.append(
                    "Statement alignment rejected delivered statements:\n"
                    + reason[-12000:]
                )
            _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="audit_rejected")
            _discard_section_artifacts(path)
            return None
    object_attempt = _compile_module_olean(path, ctx.lean_command)
    if not object_attempt.ok:
        if failure_candidate_code is not None:
            failure_candidate_code.append(module_code)
        if failure_evidence is not None:
            failure_evidence.append(
                "Lean object compilation rejected delivered statements:\n"
                + object_attempt.output[-12000:]
            )
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="olean_failed")
        _discard_section_artifacts(path)
        return None
    state_word = (
        "provisioned"
        if initial_only
        else "compiled candidate"
        if defer_alignment
        else "frozen"
    )
    _log(
        f"  section {next_number:02d} {state_word} "
        f"({len(parsed.decls)} declaration(s)) from {origin}"
    )
    _record(
        ctx.telemetry,
        "initial_declaration_section"
        if initial_only
        else "skeleton_section_candidate"
        if defer_alignment
        else "skeleton_section_frozen",
        section=next_number,
        labels=labels,
        decls=len(parsed.decls),
        source="delivered",
    )
    if not initial_only and not defer_alignment:
        _note_frozen_section(ctx, labels)
    return [
        Section(
            number=next_number,
            labels=list(labels),
            path=path,
            module=module,
            import_modules=import_modules,
            refined_labels=set() if initial_only or defer_alignment else None,
            generation_tier=generation_tier,
        )
    ]


def _parallel_initial_emission(
    ctx: Ctx,
    order: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
) -> tuple[list[Section], set[str]]:
    """Emit provisional chunks concurrently, then compile them in topo order.

    Stage zero needs names and compilable provisional signatures, not accepted
    contracts. Model emission is therefore independent enough to parallelize;
    installation remains dependency ordered so Lean sees providers first. A
    non-compiling delivered chunk gets one base-tier regeneration through the
    lightweight ``initial_only`` path. There is no semantic audit or escalation
    runner in this pass.
    """
    chunks = [
        order[start : start + BULK_SKELETON_CHUNK]
        for start in range(0, len(order), BULK_SKELETON_CHUNK)
    ]
    if not chunks:
        return [], set()

    _log(
        f"==> Initial declaration pass: emitting {len(chunks)} provisional "
        f"chunk(s) with {min(ctx.workers, len(chunks))} worker(s)"
    )

    def emit(chunk: list[str]) -> ParsedModule | None:
        imports = _sections_for_deps(ctx, chunk, sections)
        result = _call_model(
            ctx,
            _bulk_skeleton_prompt(
                ctx,
                chunk,
                sections,
                imports,
                timeout_s=ctx.base_timeout,
                initial_only=True,
            ),
            purpose="initial_declaration_generation",
            timeout=ctx.base_timeout,
            effort=ctx.base_effort,
            labels=chunk,
        )
        text = result.text
        if result.status == "timeout" and result.partial_text:
            text = result.partial_text
        if result.status not in {"ok", "timeout"} or not text.strip():
            return None
        try:
            return _ingest_model_lean(ctx, chunk, text).parsed
        except ValueError:
            return None

    emitted: list[ParsedModule | None] = [None] * len(chunks)
    with concurrent.futures.ThreadPoolExecutor(
        max_workers=max(1, min(ctx.workers, len(chunks)))
    ) as pool:
        futures = {
            pool.submit(emit, chunk): index
            for index, chunk in enumerate(chunks)
        }
        for future in concurrent.futures.as_completed(futures):
            index = futures[future]
            emitted[index] = future.result()

    frozen: list[Section] = []
    covered: set[str] = set()
    for chunk, parsed in zip(chunks, emitted):
        combined = sections + frozen
        added: list[Section] | None = None
        if parsed is not None:
            delivered_names = {decl.name for decl in parsed.decls if decl.name}
            delivered_labels = [
                label for label in chunk if _lean_name(label) in delivered_names
            ]
            decl_texts = _delivered_decl_texts(
                parsed,
                delivered_labels,
                {_lean_name(label) for label in order},
                _planned_helper_owner_by_name(ctx, order),
            )
            if set(delivered_labels) == set(chunk) and decl_texts is not None:
                added = _freeze_section_from_code(
                    ctx,
                    delivered_labels,
                    combined,
                    alloc,
                    decl_texts,
                    list(parsed.imports),
                    list(parsed.preamble),
                    origin="parallel initial emission",
                    allow_patch=False,
                    initial_only=True,
                )

        if added is None:
            # One bounded base-tier regeneration is enough for scaffolding.
            # Failure propagates as generation/compiler evidence; the main loop
            # can retry it within the configured budget without editing TeX.
            added = _freeze_section(
                ctx,
                chunk,
                combined,
                alloc,
                initial_only=True,
            )

        frozen.extend(added)
        covered.update(label for sec in added for label in sec.labels)
        _save_ctx_state(ctx, sections + frozen)

    _record(
        ctx.telemetry,
        "initial_declaration_parallel_emission",
        chunks=len(chunks),
        workers=min(ctx.workers, len(chunks)),
        requested=len(order),
        provisioned=len(covered),
    )
    return frozen, covered


def _bulk_skeleton_pass(
    ctx: Ctx,
    order: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    initial_only: bool = False,
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
    # Initial declarations are boilerplate only. Any Phase-1 bulk caller uses
    # the same shared planner as the normal top-down and bottom-up paths.
    if not initial_only:
        _ensure_phase1_semantic_plan(ctx, set(order))
    # Stage 2: transcribe the plan in section-sized chunks.
    if initial_only and ctx.workers > 1:
        return _parallel_initial_emission(ctx, order, sections, alloc)

    frozen: list[Section] = []
    covered: set[str] = set()
    for start in range(0, len(order), BULK_SKELETON_CHUNK):
        chunk = order[start : start + BULK_SKELETON_CHUNK]
        # Do not resume across independent emission chunks. Resume is useful
        # for local repair/patch calls, but here it caused Codex to repeat
        # earlier chunk declarations; those contain skeleton `sorry`s and are
        # correctly rejected as non-target helper declarations.
        chunk_sessions: dict[str, str] = {}
        pass_name = "Initial declaration pass" if initial_only else "Skeleton design pass"
        _log(
            f"==> {pass_name}: stating {len(chunk)} node(s) in one call "
            f"({len(order) - start - len(chunk)} node(s) after this chunk)"
        )
        prompt = _bulk_skeleton_prompt(
            ctx,
            chunk,
            sections + frozen,
            import_modules,
            timeout_s=ctx.base_timeout,
            initial_only=initial_only,
        )
        result = _call_model(
            ctx,
            prompt,
            purpose=(
                "initial_declaration_generation"
                if initial_only
                else "skeleton_design_pass"
            ),
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
                purpose=(
                    "initial_declaration_generation"
                    if initial_only
                    else "skeleton_design_pass"
                ),
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
            parsed = _ingest_model_lean(
                ctx,
                chunk,
                result.text,
                realize_contracts=not initial_only,
            ).parsed
        except ValueError:
            _log("  design pass returned no Lean code; falling back")
            break
        delivered_names = {decl.name for decl in parsed.decls if decl.name}
        delivered_labels = [
            label for label in chunk if _lean_name(label) in delivered_names
        ]
        chunk_decl_texts = _delivered_decl_texts(
            parsed,
            delivered_labels,
            {_lean_name(label) for label, node in ctx.nodes.items() if not node.mathlibok},
            _planned_helper_owner_by_name(
                ctx,
                [label for label, node in ctx.nodes.items() if not node.mathlibok],
            ),
        )
        _log(
            f"  design pass delivered {len(delivered_labels)}/{len(chunk)} target "
            f"declaration(s); verifying them section by section"
        )
        if not delivered_labels or chunk_decl_texts is None:
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
            chunk_decl_texts,
            list(parsed.imports),
            list(parsed.preamble),
            origin="initial pass" if initial_only else "design pass",
            # Initial-pass compiler feedback belongs in the lightweight
            # provisional prompt, not the exact-contract patch prompt.
            allow_patch=not initial_only,
            initial_only=initial_only,
        )
        if added is not None:
            frozen.extend(added)
            covered.update(delivered_labels)
            _save_ctx_state(ctx, sections + frozen)
        elif initial_only:
            # A failed broad declaration chunk is evidence that the optimistic
            # sweep is not producing reusable work for this blueprint.  Do not
            # pay for every remaining broad chunk and then regenerate all of
            # them in the compiler-feedback loop, as that duplicates the whole
            # initial pass.  Fall through immediately with smaller groups.
            old_size = ctx.effective_section_size or ctx.section_size
            new_size = max(1, min(old_size, max(1, len(chunk) // 2)))
            ctx.effective_section_size = new_size
            ctx.section_clean_streak = 0
            _log(
                "  initial broad declaration chunk did not compile; "
                f"ending the broad sweep and using {new_size}-node "
                "compiler-feedback groups"
            )
            _record(
                ctx.telemetry,
                "adaptive_section_size",
                previous_size=old_size,
                size=new_size,
                reason="initial_broad_chunk_rejected",
                labels=delivered_labels or chunk,
                pipeline_stage="initial_declaration",
            )
            break
    if frozen:
        _record(
            ctx.telemetry,
            "initial_declaration_pass" if initial_only else "skeleton_design_pass",
            requested=len(order),
            frozen_labels=sorted(covered),
            frozen_count=len(covered),
            sections=len(frozen),
        )
        _log(
            f"  {'initial pass provisioned' if initial_only else 'design pass froze'} "
            f"{len(covered)}/{len(order)} node(s) in "
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
    initial_only: bool = False,
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

    # A bottom-up Phase-1 layer contains no dependencies between its members.
    # When one broad response is routed into independent fragments, process
    # those fragments concurrently instead of serializing the exact workload
    # that routing was meant to isolate. Candidates remain unaudited here; the
    # caller's single layer gate performs the semantic judgment afterwards.
    active_parts = [part for part in parts if part]
    if (
        getattr(ctx, "defer_phase1_alignment", False)
        and len(active_parts) > 1
    ):
        all_names = {_lean_name(label) for part in active_parts for label in part}

        def freeze_candidate(part: list[str]) -> list[Section]:
            added: list[Section] | None = None
            if delivered is not None and not (set(part) & exclude):
                decl_texts = _delivered_decl_texts(
                    delivered,
                    part,
                    all_names,
                    _planned_helper_owner_by_name(
                        ctx, [label for item in active_parts for label in item]
                    ),
                )
                if decl_texts:
                    added = _freeze_section_from_code(
                        ctx,
                        part,
                        sections,
                        alloc,
                        decl_texts,
                        list(delivered.imports),
                        list(delivered.preamble),
                        initial_only=initial_only,
                    )
            if added is None:
                added = _freeze_section(
                    ctx,
                    part,
                    sections,
                    alloc,
                    initial_only=initial_only,
                )
            return added

        worker_count = max(
            1,
            min(
                getattr(ctx, "workers", 1),
                len(active_parts),
            ),
        )
        _log(
            f"  routing {len(active_parts)} independent Phase-1 fragment(s) "
            f"across {worker_count} worker(s)"
        )
        _record(
            ctx.telemetry,
            "phase1_fragments_parallel",
            part_labels=active_parts,
            part_sizes=[len(part) for part in active_parts],
            workers=worker_count,
        )
        results: list[list[Section] | None] = [None] * len(active_parts)
        failures: list[tuple[int, RepairRequest]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
            futures = {
                pool.submit(freeze_candidate, part): index
                for index, part in enumerate(active_parts)
            }
            for future in concurrent.futures.as_completed(futures):
                index = futures[future]
                try:
                    results[index] = future.result()
                except RepairRequest as request:
                    failures.append((index, request))
        for result in results:
            if result:
                frozen.extend(result)
        for _index, request in failures:
            frozen.extend(request.frozen_sections)
            request.frozen_sections = []
        if failures:
            failures.sort(key=lambda item: item[0])
            request = failures[0][1]
            request.frozen_sections = frozen
            raise request
        return frozen

    try:
        for part in parts:
            if not part:
                continue
            added: list[Section] | None = None
            if delivered is not None and not (set(part) & exclude):
                decl_texts = _delivered_decl_texts(
                    delivered,
                    part,
                    all_target_names,
                    _planned_helper_owner_by_name(ctx, labels),
                )
                if decl_texts:
                    added = _freeze_section_from_code(
                        ctx,
                        part,
                        combined,
                        alloc,
                        decl_texts,
                        list(delivered.imports),
                        list(delivered.preamble),
                        initial_only=initial_only,
                    )
            if added is None:
                added = _freeze_section(
                    ctx,
                    part,
                    combined,
                    alloc,
                    initial_only=initial_only,
                )
            frozen.extend(added)
            combined.extend(added)
            # Persist each frozen part (and any scheduler change it caused):
            # a later part can raise RepairRequest or the process can die, and
            # unsaved frozen parts were being pruned as stale artifacts on the
            # next --continue.
            if not getattr(ctx, "defer_phase1_alignment", False):
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
    _release_local_group_partitions(ctx, labels)
    _clear_generation_feedback(ctx, labels)
    _clear_generation_candidates(ctx, labels)
    _clear_retry_lifecycle(ctx, labels, stage="phase1_statement")
    for label in labels:
        entry = getattr(ctx, "design_plan_entries", {}).get(label) or {}
        wave_id = str(entry.pop("closure_wave_id", ""))
        if wave_id:
            _record(
                ctx.telemetry,
                "phase1_design_plan_closure_outcome",
                labels=[label],
                wave_id=wave_id,
                outcome="statement_frozen",
                statement_fp=ctx.stmt_fps.get(label, ""),
                plan_fp=_design_plan_audit_fingerprint(ctx, label),
            )
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
    order: list[str],
    index: int,
    size: int,
    quarantined: set[str],
    local_partitions: dict[str, dict[str, Any]] | None = None,
) -> list[str]:
    """Choose one group without remixing known-problematic local scopes."""
    if index >= len(order):
        return []
    if order[index] in quarantined:
        return [order[index]]
    local_partitions = local_partitions or {}
    local = local_partitions.get(order[index])
    if local:
        members = set(local.get("group") or [order[index]])
        group: list[str] = []
        for label in order[index:]:
            if label not in members:
                break
            group.append(label)
        return group or [order[index]]

    protected = set(local_partitions)
    group: list[str] = []
    for label in order[index : index + size]:
        if label in quarantined or label in protected:
            break
        group.append(label)
    return group or [order[index]]


def _candidate_component_labels(ctx: Ctx, label: str, available: set[str]) -> list[str]:
    """Return a persisted shared-helper component valid for this frontier."""
    with _STATE_LOCK:
        stored = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
    entry = stored.get(label) or {}
    declared_component = set(entry.get("component_labels") or [label])
    code = str(entry.get("code") or "")
    component = [
        item
        for item in entry.get("component_labels") or [label]
        if item in available
        and getattr(ctx, "stmt_fps", {}).get(item)
        == str((stored.get(item) or {}).get("statement_fp") or "")
        and set((stored.get(item) or {}).get("component_labels") or [item])
        == declared_component
        and str((stored.get(item) or {}).get("code") or "") == code
    ]
    expected = declared_component & available
    if set(component) != expected or label not in component:
        return [label]
    return component


def _coalesce_candidate_components(ctx: Ctx, labels: list[str]) -> list[str]:
    """Place persisted atomic components contiguously without changing a layer."""
    available = set(labels)
    emitted: set[str] = set()
    ordered: list[str] = []
    for label in labels:
        if label in emitted:
            continue
        component = set(_candidate_component_labels(ctx, label, available))
        for item in labels:
            if item in component and item not in emitted:
                ordered.append(item)
                emitted.add(item)
    return ordered


def _freeze_section(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    force_first_escalated: bool = False,
    initial_only: bool = False,
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
    section_kind = "Initial declaration section" if initial_only else "Skeleton section"
    _log(
        f"==> {section_kind} {next_number:02d}: {len(labels)} node(s): "
        + ", ".join(labels[:6])
        + ("..." if len(labels) > 6 else "")
    )

    froze = False
    try:
        # One backend session per runner spec for this section's whole lifecycle
        # (generation, patches, error-fix rounds, audit): follow-up calls keep the
        # Mathlib exploration and module context instead of rebuilding it cold.
        sessions: dict[str, str] = {}
        feedback = _generation_feedback_for(ctx, labels)
        previous_code = (
            "" if initial_only else _generation_candidates_for(ctx, labels)
        )
        escalated_refusals: set[str] = set()
        force_escalated_round = force_first_escalated and not initial_only
        completed_exchanges: set[tuple[str, str, str]] = set()
        invalid_mathlib_refusal_count = 0
        attempt_limit = (
            1
            if initial_only or force_first_escalated
            else SKELETON_GENERATION_ATTEMPTS
        )
        for attempt in range(1, attempt_limit + 1):
            use_escalated_runner = (
                not initial_only and (force_escalated_round or attempt > 1)
            )
            force_escalated_round = False
            effort = ctx.escalation_effort if use_escalated_runner else ctx.base_effort
            timeout = ctx.hard_timeout if use_escalated_runner else ctx.base_timeout
            try:
                prompt = _skeleton_prompt(
                    ctx,
                    labels,
                    sections,
                    import_modules,
                    feedback=feedback,
                    previous_code=previous_code,
                    timeout_s=timeout,
                    initial_only=initial_only,
                )
            except ValueError as exc:
                raise RepairRequest(
                    "Model context could not be made complete deterministically: "
                    + str(exc),
                    labels,
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                ) from exc
            result = _call_model(
                ctx,
                prompt,
                purpose=(
                    "initial_declaration_generation"
                    if initial_only
                    else "skeleton_generation"
                ),
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
                salvage = _salvage_timeout_declarations(
                    ctx,
                    labels,
                    result.partial_text,
                    realize_contracts=not initial_only,
                )
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
                        allow_patch=not initial_only,
                        initial_only=initial_only,
                        generation_tier=(
                            "escalation" if result_was_escalated else "base"
                        ),
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
                            rest = _freeze_section(
                                ctx,
                                remaining,
                                sections + added,
                                alloc,
                                initial_only=initial_only,
                            )
                        except RepairRequest as request:
                            request.frozen_sections = added + request.frozen_sections
                            raise
                        return added + rest
                # Nothing salvageable: subdivide rather than re-ask the same
                # question with a bigger stopwatch.
                if len(labels) > 1:
                    route = _route_lean_generation_failure(labels)
                    parts = [list(part) for part in route.parts]
                    mid = len(parts[0])
                    _log(
                        "  section call timed out; shared failure router is "
                        f"bisecting into {len(parts[0])} + {len(parts[1])} node(s)"
                    )
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
                            reason=(
                                "initial_declaration_timeout"
                                if initial_only
                                else "skeleton_timeout"
                            ),
                            pipeline_stage=(
                                "initial_declaration" if initial_only else "phase1"
                            ),
                            labels=labels,
                        )
                        _save_ctx_state(ctx, sections)
                    return _freeze_parts(
                        ctx,
                        parts,
                        sections,
                        alloc,
                        initial_only=initial_only,
                    )
                if initial_only:
                    raise RepairRequest(
                        "Initial declaration generation timed out for this node. "
                        "Stage zero does not escalate or refine statements; retry "
                        "the provisional declaration within the repair budget.",
                        labels,
                        section_labels=labels,
                    )
                result = _call_model(
                    ctx,
                    prompt,
                    purpose=(
                        "initial_declaration_generation"
                        if initial_only
                        else "skeleton_generation"
                    ),
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
                if len(labels) > 1:
                    route = _route_lean_generation_failure(labels)
                    _record(
                        ctx.telemetry,
                        "lean_generation_failure_routed",
                        stage=(
                            "initial_declaration"
                            if initial_only
                            else "phase1_generation"
                        ),
                        action=route.action,
                        labels=labels,
                        failing_labels=list(route.failed_labels),
                        accepted_labels=list(route.accepted_labels),
                        part_sizes=[len(part) for part in route.parts],
                        model_status=result.status,
                    )
                    return _freeze_parts(
                        ctx,
                        [list(part) for part in route.parts],
                        sections,
                        alloc,
                        initial_only=initial_only,
                    )
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
                    purpose=(
                        "initial_declaration_generation"
                        if initial_only
                        else "skeleton_generation"
                    ),
                    labels=labels,
                    escalated=result_was_escalated,
                    prompt_sha256=exchange[1],
                    response_sha256=exchange[2],
                )
                sessions.pop(exchange[0], None)
                if len(labels) > 1:
                    route = _route_lean_generation_failure(labels)
                    _record(
                        ctx.telemetry,
                        "lean_generation_failure_routed",
                        stage=(
                            "initial_declaration"
                            if initial_only
                            else "phase1_generation"
                        ),
                        action=route.action,
                        labels=labels,
                        failing_labels=list(route.failed_labels),
                        accepted_labels=list(route.accepted_labels),
                        part_sizes=[len(part) for part in route.parts],
                        model_status="duplicate_response",
                    )
                    return _freeze_parts(
                        ctx,
                        [list(part) for part in route.parts],
                        sections,
                        alloc,
                        initial_only=initial_only,
                    )
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
                            candidate = _canonicalize_model_lean(
                                ctx, labels, delivered_code
                            ).parsed
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
                            initial_only=initial_only,
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
                        "this section without adding executable helper declarations. "
                        "Do not add a separate mathematical result or "
                        "weaken the blueprint statement.\n\n"
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

            parsed = _ingest_model_lean(
                ctx,
                labels,
                result.text,
                realize_contracts=not initial_only,
            ).parsed
            missing_imports = _missing_olean_imports(parsed.imports)
            if missing_imports:
                ctx.unavailable_imports.update(missing_imports)
                parsed.imports = [item for item in parsed.imports if item not in set(missing_imports)]
            # Normalize `:= by sorry` to the canonical terminal form.
            for decl in parsed.decls:
                if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                    decl.text = _normalize_terminal_sorry(decl.text)
            all_imports = [f"import {m}" for m in import_modules] + parsed.imports
            module_code, _ranges = _compose_module(all_imports, parsed.preamble, [d.text for d in parsed.decls])

            if initial_only:
                delivered_names = {
                    decl.name for decl in parsed.decls if decl.name
                }
                missing_labels = [
                    label
                    for label in labels
                    if _lean_name(label) not in delivered_names
                ]
                if missing_labels:
                    feedback = (
                        "The provisional file omitted required declaration(s): "
                        + ", ".join(
                            f"{label} -> `{_lean_name(label)}`"
                            for label in missing_labels
                        )
                        + ". Emit every requested name; bodies may use `by sorry`."
                    )
                    previous_code = module_code
                    if len(labels) > 1 and set(missing_labels) < set(labels):
                        _log(
                            "  initial declaration coverage isolated "
                            + ", ".join(missing_labels)
                            + "; preserving delivered declarations and routing "
                            "the missing subset separately"
                        )
                        return _freeze_parts(
                            ctx,
                            _parts_around_labels(labels, missing_labels),
                            sections,
                            alloc,
                            delivered=parsed,
                            delivered_exclude=set(missing_labels),
                            initial_only=True,
                        )
                    if attempt < attempt_limit:
                        continue
                    raise RepairRequest(
                        "Initial declaration generation repeatedly omitted a "
                        "required Lean name. This is generation evidence, not an "
                        "accepted statement: " + feedback,
                        missing_labels,
                        section_labels=labels,
                    )
                findings = []
            else:
                findings = _skeleton_code_findings(
                    module_code,
                    target_kinds,
                    label_by_lean_name,
                    _planned_helper_owner_by_name(ctx, labels),
                )
            if not initial_only:
                findings += _skeleton_deterministic_findings(
                    module_code, ctx, labels
                )
            patch_note = ""
            if findings:
                plan_revision_required = _findings_require_plan_revision(
                    ctx, findings
                )
                patched, patch_note = (None, "plan revision required")
                if plan_revision_required:
                    evidence = _format_skeleton_findings(findings)
                    plan_labels = (
                        _isolated_deterministic_failure_labels(findings, labels)
                        or labels
                    )
                    corrected = _correct_phase1_design_plan(
                        ctx, plan_labels, evidence, escalated=False
                    )
                    _record(
                        ctx.telemetry,
                        "phase1_outline_plan_closure_correction",
                        labels=plan_labels,
                        corrected=bool(corrected),
                        reason="deterministic_contract_closure",
                    )
                    if corrected:
                        _clear_retry_lifecycle(
                            ctx, plan_labels, stage="phase1_statement"
                        )
                        _prune_stale_generation_candidates(ctx)
                        raise RepairRequest(
                            "Phase 1 outline plan was not closed over its "
                            "generated declarations and was corrected; regenerate "
                            "only these statements under the closed plan.\n"
                            + evidence[-8000:],
                            plan_labels,
                            section_labels=plan_labels,
                            authorizes_blueprint_repair=False,
                        )
                else:
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
                    findings = _skeleton_code_findings(
                        module_code,
                        target_kinds,
                        label_by_lean_name,
                        _planned_helper_owner_by_name(ctx, labels),
                    )
                    findings += _skeleton_deterministic_findings(module_code, ctx, labels)
            if findings:
                feedback = _format_skeleton_findings(findings)
                if patch_note and patch_note != "not patchable":
                    feedback += f"\n\nTargeted declaration patch result: {patch_note}"
                deterministic_failure_labels = _isolated_deterministic_failure_labels(
                    findings, labels
                )
                route = _route_lean_generation_failure(
                    labels,
                    deterministic_failure_labels
                    if deterministic_failure_labels
                    else None,
                )
                routed_labels = list(route.failed_labels)
                _store_generation_candidates(
                    ctx,
                    routed_labels,
                    module_code,
                    source="deterministic_audit",
                    all_labels=labels,
                    generation_tier=(
                        "escalation" if result_was_escalated else "base"
                    ),
                )
                previous_code = (
                    _generation_candidates_for(ctx, routed_labels) or module_code
                )
                if len(labels) > 1:
                    _store_generation_feedback(
                        ctx,
                        routed_labels,
                        feedback,
                        source="deterministic_audit",
                    )
                    if route.action == "isolate":
                        _quarantine_labels(
                            ctx, routed_labels, "deterministic_audit"
                        )
                    parts = [list(part) for part in route.parts]
                    retained = list(route.accepted_labels)
                    _log(
                        "  deterministic audit failure routed as "
                        + route.action
                        + " across "
                        + " + ".join(str(len(part)) for part in parts)
                        + " node(s)"
                    )
                    _record(
                        ctx.telemetry,
                        "skeleton_deterministic_routed",
                        labels=labels,
                        action=route.action,
                        failing_labels=routed_labels,
                        retained_labels=retained,
                        part_sizes=[len(part) for part in parts],
                        finding_classes=[
                            _skeleton_finding_class(finding.message)
                            for finding in findings
                        ],
                        statement_fps={
                            label: ctx.stmt_fps.get(label, "")
                            for label in labels
                        },
                    )
                    return _freeze_parts(
                        ctx,
                        parts,
                        sections,
                        alloc,
                        delivered=parsed,
                        delivered_exclude=(
                            set(routed_labels) if route.action == "isolate" else set()
                        ),
                        initial_only=initial_only,
                    )
                if attempt < attempt_limit:
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
                    parsed,
                    labels,
                    _ranges,
                    output,
                    path.name,
                    _planned_helper_owner_by_name(ctx, labels),
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
                if patch_labels and not initial_only:
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
                        if _may_defer_target_body(
                            decl, target_kinds.get(decl.name or "")
                        ):
                            decl.text = _normalize_terminal_sorry(decl.text)
                    all_imports = [f"import {m}" for m in import_modules] + parsed.imports
                    module_code, _ranges = _compose_module(
                        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
                    )
                    post_findings = [] if initial_only else _skeleton_code_findings(
                        module_code,
                        target_kinds,
                        label_by_lean_name,
                        _planned_helper_owner_by_name(ctx, labels),
                    )
                    if not initial_only:
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
                    attributable_compile_labels = []
                    if not any(finding.label is None for finding in compile_findings):
                        attributable_compile_labels = [
                            label
                            for label in labels
                            if any(finding.label == label for finding in compile_findings)
                        ]
                    route = _route_lean_generation_failure(
                        labels,
                        attributable_compile_labels
                        if attributable_compile_labels
                        else None,
                    )
                    failure_labels = route.failed_labels
                    _store_generation_candidates(
                        ctx,
                        failure_labels,
                        module_code,
                        source="lean_compile_failure",
                        all_labels=labels,
                        generation_tier=(
                            "escalation" if result_was_escalated else "base"
                        ),
                        lean_status="failed",
                        lean_output=output,
                    )
                    previous_code = (
                        _generation_candidates_for(ctx, failure_labels) or module_code
                    )
                    if len(labels) > 1:
                        if route.action == "isolate":
                            _quarantine_labels(
                                ctx, failure_labels, "lean_compile_failure"
                            )
                        _store_generation_feedback(
                            ctx,
                            failure_labels,
                            feedback,
                            source="lean_compile_failure",
                        )
                        _record(
                            ctx.telemetry,
                            "lean_generation_failure_routed",
                            stage="phase1_compile",
                            action=route.action,
                            labels=labels,
                            failing_labels=list(failure_labels),
                            accepted_labels=list(route.accepted_labels),
                            part_sizes=[len(part) for part in route.parts],
                            lean_error_shape=_lean_error_shape(output),
                            escalated=result_was_escalated,
                        )
                        parts = [list(part) for part in route.parts]
                        _log(
                            "  Lean generation failure routed as "
                            + route.action
                            + "; validating reusable declarations and routing "
                            + " + ".join(str(len(part)) for part in parts)
                            + " node(s)"
                        )
                        return _freeze_parts(
                            ctx,
                            parts,
                            sections,
                            alloc,
                            delivered=parsed,
                            delivered_exclude=(
                                set(failure_labels)
                                if route.action == "isolate"
                                else set()
                            ),
                            initial_only=initial_only,
                        )
                    if attempt < attempt_limit:
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
            defer_alignment = bool(getattr(ctx, "defer_phase1_alignment", False))
            audit = None if initial_only or defer_alignment else _model_alignment_audit(
                ctx, labels, module_code
            )
            if audit is not None:
                audit = _coerce_alignment_audit_result(audit)
                plan_request = _audit_plan_revision_request(
                    ctx,
                    audit,
                    layer_no=-1,
                    source="section_alignment",
                )
                if plan_request is not None:
                    raise plan_request
                kind, reason, rejected, helpers = audit
                if kind in {"blueprint", "decomposition"}:
                    raise RepairRequest(
                        reason,
                        sorted(rejected),
                        decomposition_helpers=helpers if kind == "decomposition" else None,
                        section_labels=labels,
                    )
                route = _route_lean_generation_failure(labels, rejected)
                _store_generation_candidates(
                    ctx,
                    route.failed_labels,
                    module_code,
                    source="statement_alignment",
                    all_labels=labels,
                    generation_tier=(
                        "escalation" if result_was_escalated else "base"
                    ),
                    lean_status="passed",
                    semantic_status="rejected",
                    semantic_evidence=reason,
                )
                _record(
                    ctx.telemetry,
                    "lean_generation_failure_routed",
                    stage="phase1_alignment",
                    action=route.action,
                    labels=labels,
                    failing_labels=list(route.failed_labels),
                    accepted_labels=list(route.accepted_labels),
                    part_sizes=[len(part) for part in route.parts],
                )
                if len(labels) > 1:
                    _store_generation_feedback(
                        ctx,
                        route.failed_labels,
                        reason,
                        source="statement_alignment",
                    )
                    if route.action == "isolate":
                        _quarantine_labels(
                            ctx, route.failed_labels, "statement_alignment"
                        )
                    parts = [list(part) for part in route.parts]
                    _log(
                        "  statement-alignment failure routed as "
                        + route.action
                        + " across "
                        + " + ".join(str(len(part)) for part in parts)
                        + " node(s)"
                    )
                    return _freeze_parts(
                        ctx,
                        parts,
                        sections,
                        alloc,
                        delivered=parsed,
                        delivered_exclude=(
                            set(route.failed_labels)
                            if route.action == "isolate"
                            else set()
                        ),
                        initial_only=initial_only,
                    )
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
                        if _may_defer_target_body(
                            decl, target_kinds.get(decl.name or "")
                        ):
                            decl.text = _normalize_terminal_sorry(decl.text)
                    all_imports = [f"import {m}" for m in import_modules] + parsed.imports
                    module_code, _ranges = _compose_module(
                        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
                    )
                    post_patch_findings = _skeleton_code_findings(
                        module_code,
                        target_kinds,
                        label_by_lean_name,
                        _planned_helper_owner_by_name(ctx, labels),
                    )
                    post_patch_findings += _skeleton_deterministic_findings(
                        module_code, ctx, labels
                    )
                    path.write_text(module_code, encoding="utf-8")
                    post_patch_ok, post_patch_output = _check_lean(path, ctx.lean_command)
                    if not post_patch_findings and not post_patch_ok:
                        retry_parsed, retry_code, retry_note = (
                            _retry_statement_patch_compile_once(
                                ctx,
                                labels,
                                sorted(rejected),
                                sections,
                                import_modules,
                                parsed,
                                module_code,
                                post_patch_output,
                                path,
                                sessions=sessions,
                            )
                        )
                        if retry_parsed is not None:
                            parsed = retry_parsed
                            module_code = retry_code
                            post_patch_ok = True
                            post_patch_output = ""
                        else:
                            post_patch_output += (
                                "\nOne compiler-feedback correction failed: "
                                + retry_note
                            )
                    if post_patch_findings or not post_patch_ok:
                        patch_note = (
                            "correction failed deterministic checks:\n"
                            + _format_skeleton_findings(post_patch_findings)
                            if post_patch_findings
                            else "Lean rejected the corrected file:\n"
                            + post_patch_output[-10000:]
                        )
                    else:
                        _store_generation_candidates(
                            ctx,
                            rejected,
                            module_code,
                            source="statement_alignment_correction",
                            all_labels=labels,
                            generation_tier="escalation",
                            repair_stage="semantic_corrected",
                            lean_status="passed",
                            semantic_status="correction_pending",
                            semantic_evidence=reason,
                        )
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
                            reaudit = _coerce_alignment_audit_result(reaudit)
                            plan_request = _audit_plan_revision_request(
                                ctx,
                                reaudit,
                                layer_no=-1,
                                source="section_alignment_post_correction",
                            )
                            if plan_request is not None:
                                raise plan_request
                            kind2, reason2, rejected2, helpers2 = reaudit
                            if kind2 in {"blueprint", "decomposition"}:
                                raise RepairRequest(
                                    reason2,
                                    sorted(rejected2),
                                    decomposition_helpers=(
                                        helpers2 if kind2 == "decomposition" else None
                                    ),
                                    section_labels=labels,
                                )
                            _store_generation_candidates(
                                ctx,
                                rejected2,
                                module_code,
                                source="statement_alignment_reaudit",
                                all_labels=labels,
                                generation_tier="escalation",
                                repair_stage="semantic_corrected",
                                lean_status="passed",
                                semantic_status="rejected",
                                semantic_evidence=reason2,
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
                    _store_generation_candidates(
                        ctx,
                        rejected,
                        module_code,
                        source="statement_alignment_correction_failed",
                        all_labels=labels,
                        generation_tier="escalation",
                        repair_stage="semantic_corrected",
                        lean_status=(
                            "passed"
                            if patched is not None
                            and not post_patch_findings
                            and post_patch_ok
                            else "failed"
                            if patched is not None and not post_patch_findings
                            else "unknown"
                        ),
                        lean_output=(
                            post_patch_output
                            if patched is not None and not post_patch_findings
                            else ""
                        ),
                        semantic_status="correction_pending",
                        semantic_evidence=feedback,
                    )
                    previous_code = (
                        _generation_candidates_for(ctx, rejected) or module_code
                    )
                    if attempt < attempt_limit:
                        _log(
                            "  alignment audit correction failed; regenerating once "
                            "at escalated effort"
                        )
                        continue
                    _store_generation_candidates(
                        ctx,
                        rejected,
                        module_code,
                        source="statement_alignment",
                        all_labels=labels,
                        lean_status="passed",
                        semantic_status="rejected",
                        semantic_evidence=reason,
                    )
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
                if attempt < attempt_limit:
                    continue
                raise RepairRequest(
                    ".olean compilation failed on both bounded attempts for this "
                    "section.\n" + feedback,
                    labels,
                    section_labels=labels,
                )
            state_word = (
                "provisioned"
                if initial_only
                else "compiled candidate"
                if defer_alignment
                else "frozen"
            )
            _log(
                f"  section {next_number:02d} {state_word} "
                f"({len(parsed.decls)} declaration(s))"
            )
            _record(
                ctx.telemetry,
                "initial_declaration_section"
                if initial_only
                else "skeleton_section_candidate"
                if defer_alignment
                else "skeleton_section_frozen",
                section=next_number,
                labels=labels,
                decls=len(parsed.decls),
            )
            if not initial_only and not defer_alignment:
                _note_frozen_section(ctx, labels)
            froze = True
            return [
                Section(
                    number=next_number,
                    labels=list(labels),
                    path=path,
                    module=module,
                    import_modules=import_modules,
                    refined_labels=set() if initial_only or defer_alignment else None,
                    generation_tier=(
                        "initial"
                        if initial_only
                        else "escalation"
                        if result_was_escalated
                        else "base"
                    ),
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


def _run_initial_declaration_pass(
    ctx: Ctx, sections: list[Section], pending: set[str]
) -> list[Section]:
    """Create every provisional Lean name once, then hand off to Phase 1.

    This pass exists only because root-first Phase 1 needs every lower-level
    name to exist before it can elaborate root interfaces. It deliberately does
    not run Lean, retry generation, audit statements, edit the blueprint, or
    spend repair budget. Model omissions are filled with deterministic internal
    placeholders; Phase 1 replaces and validates every provisional declaration.
    """
    order = [
        label
        for label in _topo_order(ctx.nodes)
        if label in pending and not ctx.nodes[label].mathlibok
    ]
    if not order:
        return sections

    next_number = max((sec.number for sec in sections), default=0) + 1
    module, path = _section_module(ctx.name, next_number)
    path.parent.mkdir(parents=True, exist_ok=True)
    import_modules = _sections_for_deps(ctx, order, sections)

    _log(
        f"==> Initial declaration pass: creating one complete boilerplate "
        f"file for {len(order)} node(s)"
    )
    result = _call_model(
        ctx,
        _initial_declaration_prompt(
            ctx,
            order,
            sections,
            import_modules,
            timeout_s=ctx.base_timeout,
        ),
        purpose="initial_declaration_generation",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=order,
        escalated=False,
    )

    candidate = result.text or result.partial_text
    parsed = ParsedModule(imports=[], preamble=[], decls=[])
    parse_error = ""
    if candidate.strip():
        try:
            parsed = _ingest_model_lean(ctx, order, candidate).parsed
        except ValueError as exc:
            parse_error = str(exc)
    elif result.error:
        parse_error = result.error

    missing_imports = _missing_olean_imports(parsed.imports)
    if missing_imports:
        ctx.unavailable_imports.update(missing_imports)
    usable_imports = [
        item for item in parsed.imports if item not in set(missing_imports)
    ]
    delivered = {decl.name: decl for decl in parsed.decls if decl.name}
    decl_texts: list[str] = []
    fallback_labels: list[str] = []
    for label in order:
        lean_name = _lean_name(label)
        decl = delivered.get(lean_name)
        if decl is not None:
            decl_texts.append(decl.text)
            continue
        fallback_labels.append(label)
        if _is_theorem_like_kind(ctx.nodes[label].kind):
            decl_texts.append(f"theorem {lean_name} : True := by trivial")
        else:
            decl_texts.append(f"def {lean_name} : Unit := ()")

    all_imports = [f"import {item}" for item in import_modules] + usable_imports
    module_code, _ranges = _compose_module(
        all_imports, parsed.preamble, decl_texts
    )
    path.write_text(module_code, encoding="utf-8")
    section = Section(
        number=next_number,
        labels=list(order),
        path=path,
        module=module,
        import_modules=import_modules,
        refined_labels=set(),
        provisional_environment=True,
        generation_tier="initial",
    )
    result_sections = sections + [section]
    _save_ctx_state(ctx, result_sections)
    _record(
        ctx.telemetry,
        "initial_declaration_environment",
        labels=order,
        count=len(order),
        module=module,
        model_status=result.status,
        model_declarations=len(order) - len(fallback_labels),
        fallback_labels=fallback_labels,
        parse_error=parse_error,
    )
    if fallback_labels:
        _log(
            f"  filled {len(fallback_labels)} omitted boilerplate name(s) "
            "deterministically; Phase 1 will replace them"
        )
    _log(
        f"==> Initial declaration pass complete: one boilerplate file "
        f"contains all {len(order)} generated names"
    )
    return result_sections


def _add_phase1_boilerplate_names(
    ctx: Ctx, sections: list[Section], pending: set[str]
) -> list[Section]:
    """Add names introduced by a Phase-1 repair without rerunning stage zero."""
    environment = next(
        (sec for sec in sections if sec.provisional_environment), None
    )
    if environment is None:
        raise ValueError(
            "Phase 1 needs new provisional names, but the persisted initial "
            "boilerplate environment is unavailable"
        )
    parsed, index = _module_decl_texts(environment)
    added: list[str] = []
    for label in _topo_order(ctx.nodes):
        if label not in pending or ctx.nodes[label].mathlibok:
            continue
        lean_name = _lean_name(label)
        if lean_name not in index:
            if _is_theorem_like_kind(ctx.nodes[label].kind):
                text = f"theorem {lean_name} : True := by trivial"
            else:
                text = f"def {lean_name} : Unit := ()"
            parsed.decls.append(
                DeclBlock(
                    kind="theorem" if _is_theorem_like_kind(ctx.nodes[label].kind) else "def",
                    name=lean_name,
                    text=text,
                )
            )
            index[lean_name] = len(parsed.decls) - 1
        if label not in environment.labels:
            environment.labels.append(label)
        added.append(label)
    environment.deferred = False
    if environment.refined_labels is None:
        environment.refined_labels = set()
    _write_section(environment, parsed)
    _discard_section_objects(environment.path)
    _save_ctx_state(ctx, sections)
    _record(
        ctx.telemetry,
        "phase1_boilerplate_names_added",
        labels=added,
        count=len(added),
        module=environment.module,
    )
    _log(
        f"==> Phase 1: added {len(added)} provisional name(s) introduced "
        "by blueprint repair; continuing statement refinement"
    )
    return sections


# ---------------------------------------------------------------------------
# Phase 1: root-first statement refinement


def _generate_phase1_statement_group(
    ctx: Ctx,
    sec: Section,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    parsed: ParsedModule,
    *,
    force_first_escalated: bool = False,
    sessions: dict[str, str] | None = None,
    generation_tier_out: list[str] | None = None,
) -> ParsedModule:
    """Replace stage-zero boilerplate with exact Phase-1 declarations first.

    The initial file exists only to provide names. Its declarations are never
    valid statement-audit evidence. This generation transaction must therefore
    run before deterministic checks, Lean compilation, or blueprint repair.
    """
    sessions = sessions if sessions is not None else {}
    feedback = _generation_feedback_for(ctx, labels)
    previous_code = _generation_candidates_for(ctx, labels)

    def route_multi_failure(
        evidence: str, attributable_labels: Iterable[str] | None = None
    ) -> None:
        """Return multi-node statement failures to the shared scope router."""
        if len(labels) <= 1:
            return
        route = _route_lean_generation_failure(labels, attributable_labels)
        raise RepairRequest(
            evidence,
            list(route.failed_labels),
            section_labels=labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
        )

    for escalated in ((True,) if force_first_escalated else (False, True)):
        timeout = ctx.hard_timeout if escalated else ctx.base_timeout
        prompt = (
            _bulk_skeleton_prompt(
                ctx,
                labels,
                sections,
                import_modules,
                timeout_s=timeout,
            )
            if not feedback and not previous_code
            else _skeleton_prompt(
                ctx,
                labels,
                sections,
                import_modules,
                feedback=feedback,
                previous_code=previous_code,
                timeout_s=timeout,
            )
        )
        result = _call_model(
            ctx,
            prompt,
            purpose="phase1_statement_generation",
            timeout=timeout,
            effort=ctx.escalation_effort if escalated else ctx.base_effort,
            labels=labels,
            escalated=escalated,
            sessions=sessions,
        )
        candidate = result.text or result.partial_text
        refusal = _parse_decomposition_refusal(candidate)
        if refusal is not None:
            feedback = (
                "The previous statement-generation call requested decomposition. "
                "Before changing the blueprint, make one stronger attempt to emit "
                "the exact statements using the provisional dependency names.\n"
                f"Reason: {refusal.get('reason', '')}\n"
                "Requested helpers: "
                + ", ".join(refusal.get("missing_helpers") or [])
            )
            previous_code = candidate
            if escalated:
                raise RepairRequest(
                    "The escalated Phase 1 statement generator determined that "
                    "the blueprint contract needs decomposition.\n"
                    f"Reason: {refusal.get('reason', '')}",
                    [str(refusal.get("label") or labels[0])],
                    decomposition_helpers=[
                        str(item) for item in refusal.get("missing_helpers") or []
                    ],
                    section_labels=labels,
                )
            continue
        if result.status != "ok" and not candidate.strip():
            feedback = (
                f"The statement-generation call {result.status}: "
                f"{result.error or 'no complete response'}. Return every target "
                "declaration in one Lean code block."
            )
            if not escalated:
                route_multi_failure(feedback)
            continue
        try:
            replacement_module = _ingest_model_lean(
                ctx, labels, candidate, realize_contracts=True
            ).parsed
            replacement_code, _ = _compose_module(
                replacement_module.imports,
                replacement_module.preamble,
                [decl.text for decl in replacement_module.decls],
            )
        except ValueError as exc:
            feedback = f"The response was not a Lean statement file: {exc}"
            previous_code = candidate
            if not escalated:
                route_multi_failure(feedback)
            continue
        _store_generation_candidates(
            ctx,
            labels,
            replacement_code,
            source="phase1_statement_generation",
            all_labels=labels,
        )
        self_import = f"import {sec.module}"
        if self_import in replacement_module.imports:
            replacement_module.imports = [
                item for item in replacement_module.imports if item != self_import
            ]
            _record(
                ctx.telemetry,
                "phase1_self_import_removed",
                section=sec.number,
                module=sec.module,
                labels=labels,
            )
            replacement_code, _ = _compose_module(
                replacement_module.imports,
                replacement_module.preamble,
                [decl.text for decl in replacement_module.decls],
            )
        patched = _apply_skeleton_replacements(
            parsed,
            labels,
            labels,
            replacement_code,
            _planned_helper_owner_by_name(ctx, labels),
            unavailable_imports=ctx.unavailable_imports,
        )
        if patched is None:
            delivered = {
                decl.name for decl in replacement_module.decls if decl.name
            }
            missing = [
                label for label in labels if _lean_name(label) not in delivered
            ]
            feedback = (
                "The response omitted required Phase 1 declarations: "
                + ", ".join(
                    f"{label} -> `{_lean_name(label)}`" for label in missing
                )
                + ". Return every target statement, not a subset."
            )
            previous_code = candidate
            generation_tier = "escalation" if escalated else "base"
            salvaged = _salvage_partial_phase1_response(
                ctx,
                labels,
                replacement_module,
                sections,
                generation_tier=generation_tier,
            )
            unresolved = [label for label in labels if label not in salvaged]
            if salvaged:
                feedback += (
                    " Preserved deterministically valid returned declarations: "
                    + ", ".join(salvaged)
                    + ". Retry only the unresolved declarations."
                )
            route_multi_failure(
                feedback,
                unresolved if unresolved and len(unresolved) < len(labels) else None,
            )
            continue
        patched.preamble = list(
            dict.fromkeys(
                patched.preamble
                + [
                    line
                    for line in replacement_module.preamble
                    if line.strip().startswith("open")
                ]
            )
        )
        _record(
            ctx.telemetry,
            "phase1_statement_generation",
            section=sec.number,
            labels=labels,
            count=len(labels),
            escalated=escalated,
            status="applied",
        )
        if generation_tier_out is not None:
            generation_tier_out.append("escalation" if escalated else "base")
        return patched

    route = _route_lean_generation_failure(labels)
    raise RepairRequest(
        "Phase 1 statement generation could not deliver every requested "
        "declaration after base and escalation attempts. This is generation "
        "failure evidence, not evidence that provisional placeholders were "
        "mathematically wrong.\n" + feedback,
        list(route.failed_labels),
        section_labels=labels,
        authorizes_blueprint_repair=False,
        failure_route=route,
    )


def _phase1_layer_candidate_code(candidate: Phase1LayerCandidate) -> str:
    imports = [f"import {module}" for module in candidate.import_modules]
    return _compose_module(
        imports + candidate.parsed.imports,
        candidate.parsed.preamble,
        [decl.text for decl in candidate.parsed.decls],
    )[0]


def _phase1_layer_candidates_code(candidates: list[Phase1LayerCandidate]) -> str:
    """Combine candidate declarations for one batched semantic judgment."""
    return "\n\n".join(
        decl.text
        for candidate in candidates
        for decl in candidate.parsed.decls
    )


def _subset_phase1_candidate(
    ctx: Ctx, candidate: Phase1LayerCandidate, labels: Iterable[str]
) -> Phase1LayerCandidate | None:
    """Extract selected targets and their owned local helpers in original order."""
    wanted = [label for label in candidate.labels if label in set(labels)]
    if not wanted:
        return None
    decl_texts = _delivered_decl_texts(
        candidate.parsed,
        wanted,
        {_lean_name(label) for label in candidate.labels},
        _planned_helper_owner_by_name(ctx, candidate.labels),
    )
    if not decl_texts:
        return None
    return Phase1LayerCandidate(
        labels=wanted,
        parsed=ParsedModule(
            imports=list(candidate.parsed.imports),
            preamble=list(candidate.parsed.preamble),
            decls=[
                DeclBlock(decl.kind, decl.name, decl.text)
                for decl in _parse_module(
                    _compose_module([], [], decl_texts)[0]
                ).decls
            ],
        ),
        import_modules=list(candidate.import_modules),
        generation_tier=candidate.generation_tier,
        sessions=candidate.sessions,
    )


def _generate_uncompiled_phase1_candidate(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
) -> Phase1LayerCandidate:
    """Generate and deterministically validate statements without running Lean."""
    repaired = _semantic_repair_candidate(ctx, labels, sections)
    if repaired is not None:
        return repaired
    reused = _reusable_uncompiled_candidate(ctx, labels, sections)
    if reused is not None:
        return reused
    import_modules = _sections_for_deps(ctx, labels, sections)
    placeholders = ParsedModule(
        imports=[],
        preamble=[],
        decls=[
            DeclBlock(
                "theorem" if _is_theorem_like_kind(ctx.nodes[label].kind) else "def",
                _lean_name(label),
                (
                    f"theorem {_lean_name(label)} : True := sorry"
                    if _is_theorem_like_kind(ctx.nodes[label].kind)
                    else f"def {_lean_name(label)} : Unit := ()"
                ),
            )
            for label in labels
        ],
    )
    fake_section = Section(
        number=0,
        labels=list(labels),
        path=SCRATCH_DIR / ctx.name / "Phase1Uncompiled.lean",
        module=f"AutoBlueprint.Generated.{_module_safe_name(ctx.name)}.Phase1Uncompiled",
        import_modules=import_modules,
        refined_labels=set(),
    )
    sessions: dict[str, str] = {}
    tier: list[str] = []
    parsed = _generate_phase1_statement_group(
        ctx,
        fake_section,
        labels,
        sections,
        import_modules,
        placeholders,
        force_first_escalated=bool(
            len(labels) == 1
            and _retry_next_tier(ctx, labels[0], "phase1_statement") == "escalation"
        ),
        sessions=sessions,
        generation_tier_out=tier,
    )
    target_kinds = {_lean_name(label): ctx.nodes[label].kind for label in labels}
    label_by_name = {_lean_name(label): label for label in labels}
    for decl in parsed.decls:
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    candidate = Phase1LayerCandidate(
        labels=list(labels),
        parsed=parsed,
        import_modules=import_modules,
        generation_tier=tier[-1] if tier else "base",
        sessions=sessions,
    )
    code = _phase1_layer_candidate_code(candidate)
    findings = _skeleton_code_findings(
        code,
        target_kinds,
        label_by_name,
        _planned_helper_owner_by_name(ctx, labels),
    )
    findings += _skeleton_deterministic_findings(code, ctx, labels)
    if findings:
        plan_revision_required = _findings_require_plan_revision(ctx, findings)
        patched, note = (None, "plan revision required")
        if not plan_revision_required:
            patched, note = _targeted_patch_skeleton_decls(
                ctx,
                labels,
                sections,
                import_modules,
                parsed,
                code,
                findings,
                timeout=(
                    ctx.hard_timeout
                    if candidate.generation_tier == "escalation"
                    else ctx.base_timeout
                ),
                sessions=sessions,
                escalated=candidate.generation_tier == "escalation",
            )
        if patched is not None:
            candidate.parsed = patched
            for decl in candidate.parsed.decls:
                if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                    decl.text = _normalize_terminal_sorry(decl.text)
            code = _phase1_layer_candidate_code(candidate)
            findings = _skeleton_code_findings(
                code,
                target_kinds,
                label_by_name,
                _planned_helper_owner_by_name(ctx, labels),
            )
            findings += _skeleton_deterministic_findings(code, ctx, labels)
        if findings:
            evidence = _format_skeleton_findings(findings)
            if note and note != "not patchable":
                evidence += "\n\nTargeted declaration patch result: " + note
            failed = _isolated_deterministic_failure_labels(findings, labels)
            route = _route_lean_generation_failure(labels, failed or None)
            _store_generation_candidates(
                ctx,
                route.failed_labels,
                code,
                source="semantic_first_deterministic",
                all_labels=labels,
            )
            _store_generation_feedback(
                ctx,
                route.failed_labels,
                evidence,
                source="semantic_first_deterministic",
            )
            raise RepairRequest(
                "Uncompiled Phase-1 candidate failed deterministic checks:\n"
                + evidence[-10000:],
                list(route.failed_labels),
                section_labels=labels,
                authorizes_blueprint_repair=False,
                failure_route=route,
                plan_revision_required=plan_revision_required,
            )
    _record(
        ctx.telemetry,
        "phase1_uncompiled_candidate",
        labels=labels,
        count=len(labels),
        generation_tier=candidate.generation_tier,
    )
    _store_generation_candidates(
        ctx,
        labels,
        code,
        source="semantic_first_pre_audit",
        all_labels=labels,
        reusable_uncompiled=True,
        generation_tier=candidate.generation_tier,
        repair_stage="deterministic_valid",
    )
    return candidate


def _revise_semantic_candidates(
    ctx: Ctx,
    candidates: list[Phase1LayerCandidate],
    rejected: set[str],
    reason: str,
    sections: list[Section],
    *,
    required_dependencies: dict[str, set[str]] | None = None,
) -> list[Phase1LayerCandidate]:
    """Apply one exact-feedback revision only to audit-rejected candidates."""
    revisions: list[Phase1LayerCandidate] = []
    for candidate in candidates:
        subset = _subset_phase1_candidate(ctx, candidate, rejected)
        if subset is None:
            continue
        findings = [
            SkeletonFinding(reason, label=label, lean_name=_lean_name(label))
            for label in subset.labels
        ]
        code = _phase1_layer_candidate_code(subset)
        patched, note = _targeted_patch_skeleton_decls(
            ctx,
            subset.labels,
            sections,
            subset.import_modules,
            subset.parsed,
            code,
            findings,
            timeout=(
                ctx.hard_timeout
                if subset.generation_tier == "escalation"
                else ctx.base_timeout
            ),
            sessions=subset.sessions,
            escalated=subset.generation_tier == "escalation",
        )
        if patched is None:
            raise RepairRequest(
                "Semantic correction failed for the rejected declaration(s): "
                + note
                + "\n"
                + reason,
                subset.labels,
                section_labels=subset.labels,
                authorizes_blueprint_repair=False,
                failure_route=_route_lean_generation_failure(subset.labels),
            )
        subset.parsed = patched
        target_kinds = {
            _lean_name(label): ctx.nodes[label].kind for label in subset.labels
        }
        label_by_name = {_lean_name(label): label for label in subset.labels}
        for decl in subset.parsed.decls:
            if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                decl.text = _normalize_terminal_sorry(decl.text)
        revised_code = _phase1_layer_candidate_code(subset)
        deterministic = _skeleton_code_findings(
            revised_code,
            target_kinds,
            label_by_name,
            _planned_helper_owner_by_name(ctx, subset.labels),
        )
        deterministic += _skeleton_deterministic_findings(
            revised_code, ctx, subset.labels
        )
        if deterministic:
            evidence = _format_skeleton_findings(deterministic)
            plan_revision_required = _findings_require_plan_revision(
                ctx, deterministic
            )
            confirmed_dependencies: dict[str, set[str]] = {}
            for finding in deterministic:
                if not finding.label or not finding.dependencies:
                    continue
                certified = set(
                    (required_dependencies or {}).get(finding.label, set())
                )
                matched = set(finding.dependencies) & certified
                if matched:
                    confirmed_dependencies.setdefault(
                        finding.label, set()
                    ).update(matched)
            if confirmed_dependencies:
                _record(
                    ctx.telemetry,
                    "phase1_dependency_repair_authorized",
                    labels=sorted(confirmed_dependencies),
                    required_dependencies={
                        label: sorted(dependencies)
                        for label, dependencies in confirmed_dependencies.items()
                    },
                    evidence=evidence[-4000:],
                    authorization=(
                        "statement critic and deterministic closure finding agree"
                    ),
                )
                raise RepairRequest(
                    "Semantic correction requires missing blueprint statement "
                    "dependency edge(s):\n" + evidence,
                    sorted(confirmed_dependencies),
                    section_labels=subset.labels,
                    authorizes_blueprint_repair=True,
                    required_dependencies=confirmed_dependencies,
                )
            raise RepairRequest(
                "Semantic correction introduced deterministic statement errors:\n"
                + evidence,
                subset.labels,
                section_labels=subset.labels,
                authorizes_blueprint_repair=False,
                failure_route=_route_lean_generation_failure(subset.labels),
                plan_revision_required=plan_revision_required,
            )
        revisions.append(subset)
        _record(
            ctx.telemetry,
            "phase1_semantic_revision",
            labels=subset.labels,
            producing_tier=subset.generation_tier,
            status="delivered",
        )
    return revisions


def _route_phase1_compile_failure(
    ctx: Ctx,
    failed: Phase1LayerCandidate,
    evidence: str,
    failed_code: str,
    *,
    layer_no: int,
) -> RepairRequest:
    """Persist and route one completed Phase-1 compile failure immediately.

    Candidate groups compile independently.  Once one worker has produced a
    complete failure, neither its diagnostics nor its next action depends on
    slower siblings.  Keeping this routing in one helper lets the coordinator
    overlap plan correction/retry bookkeeping with those still-running workers
    without changing any of the existing failure classification rules.
    """
    plan_defects = _phase1_compile_plan_defects(
        ctx, failed.labels, failed_code, evidence
    )
    _store_generation_candidates(
        ctx,
        failed.labels,
        failed_code,
        source="validated_contract_compile",
        all_labels=failed.labels,
        lean_status="failed",
        lean_output=evidence,
    )
    _store_generation_feedback(
        ctx,
        failed.labels,
        evidence,
        source="validated_contract_compile",
    )
    revised: set[str] = set()
    if plan_defects:
        plan_evidence = (
            "A generated Phase-1 target copied its accepted plan, but "
            "Lean rejected that plan-owned interface. Correct the plan "
            "to use verified Lean/Mathlib declarations or a faithful "
            "plan-owned helper; do not weaken the blueprint claim.\n"
            + "\n".join(
                f"- {label}: {reason}"
                for label, reason in sorted(plan_defects.items())
            )
            + "\n\nCompiler evidence:\n"
            + evidence[-10000:]
        )
        revised = _revise_exhausted_phase1_contracts(
            ctx,
            plan_defects,
            plan_evidence,
            policy="post_compile_plan_realization",
        )
        _record(
            ctx.telemetry,
            "phase1_plan_realized_compile_rejection",
            layer=layer_no,
            labels=sorted(plan_defects),
            revised_labels=sorted(revised),
            reasons=plan_defects,
            error_shape=_lean_error_shape(evidence),
        )

    ordinary_labels = [
        label for label in failed.labels if label not in revised
    ]
    if ordinary_labels:
        route = _route_lean_generation_failure(ordinary_labels)
        _record(
            ctx.telemetry,
            "phase1_compile_failure_routed",
            layer=layer_no,
            labels=ordinary_labels,
            classification="lean_generation",
            route=route.action,
        )
        return RepairRequest(
            "A contract-planned statement candidate failed Lean "
            "compilation:\n" + evidence[-12000:],
            list(route.failed_labels),
            section_labels=ordinary_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
        )
    _record(
        ctx.telemetry,
        "phase1_compile_failure_routed",
        layer=layer_no,
        labels=sorted(revised),
        classification="plan_revision",
        route="plan_revision_required",
    )
    return RepairRequest(
        "The accepted Phase-1 plan was corrected after its "
        "exact emitted interface failed Lean compilation:\n"
        + evidence[-12000:],
        sorted(revised),
        section_labels=sorted(revised),
        authorizes_blueprint_repair=False,
        plan_revision_required=True,
    )


def _compile_semantic_phase1_candidates(
    ctx: Ctx,
    candidates: list[Phase1LayerCandidate],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    layer_no: int,
) -> list[Section]:
    """Compile contract-planned candidates in parallel before final auditing."""
    if not candidates:
        return []
    worker_count = max(1, min(getattr(ctx, "workers", 1), len(candidates)))
    _log(
        f"==> Phase 1 layer {layer_no}: compiling {len(candidates)} "
        f"validated-contract candidate group(s) with {worker_count} worker(s)"
    )
    results: list[list[Section] | None] = [None] * len(candidates)
    failures: list[tuple[int, RepairRequest]] = []
    old_defer = getattr(ctx, "defer_phase1_alignment", False)
    ctx.defer_phase1_alignment = True
    try:
        def compile_one(
            index: int, candidate: Phase1LayerCandidate
        ) -> tuple[int, Phase1LayerCandidate, list[Section] | None, str, str]:
            evidence: list[str] = []
            failed_code: list[str] = []
            result = _freeze_section_from_code(
                ctx,
                candidate.labels,
                sections,
                alloc,
                [decl.text for decl in candidate.parsed.decls],
                list(candidate.parsed.imports),
                list(candidate.parsed.preamble),
                origin=f"validated-contract layer {layer_no}",
                allow_patch=True,
                generation_tier=candidate.generation_tier,
                failure_evidence=evidence,
                failure_candidate_code=failed_code,
                route_plan_defects=True,
            )
            return (
                index,
                candidate,
                result,
                "\n\n".join(evidence) or "candidate did not compile",
                failed_code[-1]
                if failed_code
                else _phase1_layer_candidate_code(candidate),
            )

        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
            futures = [
                pool.submit(compile_one, index, candidate)
                for index, candidate in enumerate(candidates)
            ]
            for future in concurrent.futures.as_completed(futures):
                index, candidate, result, evidence, failed_code = future.result()
                results[index] = result
                if result is None:
                    # Route this completed outcome while unrelated workers are
                    # still compiling.  The previous batch barrier delayed a
                    # known plan correction by the full timeout of its slowest
                    # sibling.
                    failures.append(
                        (
                            index,
                            _route_phase1_compile_failure(
                                ctx,
                                candidate,
                                evidence,
                                failed_code,
                                layer_no=layer_no,
                            ),
                        )
                    )
    finally:
        ctx.defer_phase1_alignment = old_defer

    compiled = [section for result in results if result for section in result]
    if failures:
        failures.sort(key=lambda item: item[0])
        requests = [request for _index, request in failures]
        _record(
            ctx.telemetry,
            "phase1_parallel_compile_failures",
            layer=layer_no,
            failure_count=len(requests),
            failing_groups=[request.section_labels for request in requests],
            accepted_labels=[
                label for section in compiled for label in section.labels
            ],
        )
        raise _aggregate_retry_requests(requests, frozen_sections=compiled)
    return compiled


def _compile_and_finalize_semantic_candidates(
    ctx: Ctx,
    candidates: list[Phase1LayerCandidate],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    layer_no: int,
) -> list[Section]:
    """Compile candidates, integrate their modules, and mark accepted contracts."""
    try:
        compiled = _compile_semantic_phase1_candidates(
            ctx, candidates, sections, alloc, layer_no=layer_no
        )
    except RepairRequest as request:
        # Parallel compilation can succeed for independent siblings before one
        # candidate fails. They are preservable only after the same integrated
        # import and cache-backed semantic gate as a fully successful layer.
        partial = request.frozen_sections
        request.frozen_sections = []
        if partial:
            try:
                request.frozen_sections = _audit_phase1_layer_candidates(
                    ctx, layer_no, partial, sections, alloc
                )
            except RepairRequest as audit_request:
                if audit_request.authorizes_blueprint_repair:
                    raise
                raise _aggregate_retry_requests(
                    [request, audit_request],
                    frozen_sections=audit_request.frozen_sections,
                )
        raise
    if not compiled:
        return []
    return _audit_phase1_layer_candidates(
        ctx, layer_no, compiled, sections, alloc
    )


def _refine_statement_group(
    ctx: Ctx,
    sec: Section,
    labels: list[str],
    sections: list[Section],
) -> None:
    """Refine selected declarations without exposing failed candidates.

    Every deterministic/model/Lean gate runs against a disposable attempt file.
    The canonical skeleton is replaced atomically only after all gates pass.
    """
    existing_code = sec.path.read_text(encoding="utf-8")
    parsed = _canonicalize_model_lean(
        ctx, sec.labels, existing_code, strict_duplicates=False
    ).parsed
    index = {
        decl.name: position
        for position, decl in enumerate(parsed.decls)
        if decl.name
    }
    # Heal state written by older versions of the Phase-1 loop. Self-imports
    # can never be valid and duplicate names can only make Lean reject a module.
    self_import = f"import {sec.module}"
    parsed.imports = [item for item in parsed.imports if item != self_import]
    seen_existing: set[str] = set()
    healed_decls: list[DeclBlock] = []
    for decl in parsed.decls:
        if decl.name and decl.name in seen_existing:
            continue
        if decl.name:
            seen_existing.add(decl.name)
        healed_decls.append(decl)
    parsed.decls = healed_decls
    missing = [label for label in labels if _lean_name(label) not in index]
    if missing:
        raise RepairRequest(
            "Initial declaration pass omitted required generated names: "
            + ", ".join(missing),
            missing,
            section_labels=labels,
        )
    import_modules = [module for module in sec.import_modules if module != sec.module]
    # The file may also contain provisional theorem declarations from lower
    # layers. Their terminal ``sorry`` is legal until their own Phase-1 turn.
    target_kinds = {
        _lean_name(label): ctx.nodes[label].kind for label in sec.labels
    }
    label_by_name = {_lean_name(label): label for label in sec.labels}
    sessions: dict[str, str] = {}
    # Rollback uses the deterministically healed baseline, allowing --continue
    # to recover files poisoned by the pre-transaction implementation.
    original_code, _original_ranges = _compose_module(
        parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
    )
    attempt_dir = SCRATCH_DIR / ctx.name / "phase1-attempts"
    attempt_dir.mkdir(parents=True, exist_ok=True)
    attempt_path = attempt_dir / sec.path.name

    _log(
        f"==> Phase 1: generating exact statements for {len(labels)} "
        "provisional declaration(s)"
    )
    parsed = _generate_phase1_statement_group(
        ctx,
        sec,
        labels,
        sections,
        import_modules,
        parsed,
        force_first_escalated=bool(
            len(labels) == 1
            and _retry_next_tier(ctx, labels[0], "phase1_statement")
            == "escalation"
        ),
    )

    def current_code() -> str:
        code, _ranges = _compose_module(
            parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
        )
        return code

    def write_attempt() -> tuple[str, list[tuple[int, int]]]:
        code, ranges = _compose_module(
            parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
        )
        attempt_path.write_text(code, encoding="utf-8")
        return code, ranges

    module_code = current_code()
    findings = [
        finding
        for finding in _skeleton_code_findings(
            module_code,
            target_kinds,
            label_by_name,
            _planned_helper_owner_by_name(ctx, sec.labels),
        )
        if finding.label is None or finding.label in set(labels)
    ]
    findings += _skeleton_deterministic_findings(module_code, ctx, labels)
    if findings:
        patched, note = _targeted_patch_skeleton_decls(
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
        if patched is None:
            raise RepairRequest(
                "Phase 1 could not correct provisional statement contracts: "
                + note
                + "\n"
                + _format_skeleton_findings(findings),
                _patchable_skeleton_labels(findings, labels) or labels,
                section_labels=labels,
                authorizes_blueprint_repair=False,
            )
        parsed = patched
        module_code = current_code()
        findings = [
            finding
            for finding in _skeleton_code_findings(
                module_code,
                target_kinds,
                label_by_name,
                _planned_helper_owner_by_name(ctx, sec.labels),
            )
            if finding.label is None or finding.label in set(labels)
        ]
        findings += _skeleton_deterministic_findings(module_code, ctx, labels)
        if findings:
            attributable = _isolated_deterministic_failure_labels(findings, labels)
            if len(labels) > 1:
                route = _route_lean_generation_failure(
                    labels, attributable if attributable else None
                )
                raise RepairRequest(
                    "Phase 1 statement correction still failed deterministic gates:\n"
                    + _format_skeleton_findings(findings),
                    list(route.failed_labels),
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                    failure_route=route,
                )
            patched, note = _targeted_patch_skeleton_decls(
                ctx,
                labels,
                sections,
                import_modules,
                parsed,
                module_code,
                findings,
                timeout=ctx.hard_timeout,
                sessions=sessions,
                escalated=True,
            )
            if patched is None:
                raise RepairRequest(
                    "Phase 1 statement correction still failed deterministic gates: "
                    + note
                    + "\n"
                    + _format_skeleton_findings(findings),
                    _patchable_skeleton_labels(findings, labels) or labels,
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                )
            parsed = patched
            module_code = current_code()
            findings = [
                finding
                for finding in _skeleton_code_findings(
                    module_code,
                    target_kinds,
                    label_by_name,
                    _planned_helper_owner_by_name(ctx, sec.labels),
                )
                if finding.label is None or finding.label in set(labels)
            ]
            findings += _skeleton_deterministic_findings(
                module_code, ctx, labels
            )
            if findings:
                raise RepairRequest(
                    "Phase 1 statement correction remained invalid after escalation:\n"
                    + _format_skeleton_findings(findings),
                    _patchable_skeleton_labels(findings, labels) or labels,
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                )

    module_code, ranges = write_attempt()
    ok, output = _check_lean(attempt_path, ctx.lean_command)
    # A root statement can elaborate only after every declaration in the
    # shared provisional environment has a valid header. Repair malformed
    # lower scaffolding in small owned batches, retaining ``sorry`` bodies and
    # without marking those nodes refined. Then resume the original root.
    repaired_provisional: set[str] = set()
    while not ok:
        compile_findings = _lean_compile_findings(
            parsed,
            sec.labels,
            ranges,
            output,
            attempt_path.name,
            _planned_helper_owner_by_name(ctx, sec.labels),
        )
        owned = [
            label
            for label in sec.labels
            if any(finding.label == label for finding in compile_findings)
            and label not in repaired_provisional
        ]
        if not owned:
            break
        provisional_owned = [label for label in owned if label not in set(labels)]
        patch_labels = (
            provisional_owned or [label for label in owned if label in set(labels)]
        )[:TARGETED_DECL_PATCH_MAX_LABELS]
        patch_findings = [
            finding for finding in compile_findings if finding.label in set(patch_labels)
        ]
        singleton_patch = len(patch_labels) == 1
        patched, note = _targeted_patch_skeleton_decls(
            ctx,
            sec.labels,
            sections,
            import_modules,
            parsed,
            module_code,
            patch_findings,
            timeout=ctx.hard_timeout if singleton_patch else ctx.base_timeout,
            sessions=sessions,
            escalated=singleton_patch,
            provisional_only=not set(patch_labels) <= set(labels),
            escalate_timeout=singleton_patch,
        )
        if patched is None:
            break
        parsed = patched
        repaired_provisional.update(patch_labels)
        if provisional_owned:
            _record(
                ctx.telemetry,
                "phase1_provisional_scaffolding_repair",
                labels=patch_labels,
                root_labels=labels,
                count=len(patch_labels),
            )
        module_code, ranges = write_attempt()
        ok, output = _check_lean(attempt_path, ctx.lean_command)
    if not ok:
        compile_findings = _lean_compile_findings(
            parsed,
            sec.labels,
            ranges,
            output,
            attempt_path.name,
            _planned_helper_owner_by_name(ctx, sec.labels),
        )
        remaining = [
            label
            for label in sec.labels
            if any(finding.label == label for finding in compile_findings)
        ]
        route = _route_lean_generation_failure(
            labels,
            [label for label in remaining if label in set(labels)] or None,
        )
        raise RepairRequest(
            "Phase 1 provisional environment still does not compile after "
            "repairing declaration-owned scaffolding:\n" + output[-8000:],
            list(route.failed_labels),
            section_labels=labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
        )

    audit = _model_alignment_audit(ctx, labels, module_code, tag="phase1")
    if audit is not None:
        audit = _coerce_alignment_audit_result(audit)
        plan_request = _audit_plan_revision_request(
            ctx,
            audit,
            layer_no=-1,
            source="top_down_alignment",
        )
        if plan_request is not None:
            raise plan_request
        kind, reason, rejected, helpers = audit
        if kind in {"blueprint", "decomposition"}:
            raise RepairRequest(
                reason,
                sorted(rejected),
                decomposition_helpers=helpers if kind == "decomposition" else None,
                section_labels=labels,
            )
        route = _route_lean_generation_failure(labels, rejected)
        if len(labels) > 1:
            raise RepairRequest(
                reason,
                list(route.failed_labels),
                section_labels=labels,
                authorizes_blueprint_repair=False,
                failure_route=route,
            )
        audit_findings = [
            SkeletonFinding(reason, label=label, lean_name=_lean_name(label))
            for label in sorted(rejected)
        ]
        patched, note = _targeted_patch_skeleton_decls(
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
        if patched is None:
            raise RepairRequest(
                "Phase 1 statement-alignment correction failed: " + note + "\n" + reason,
                sorted(rejected),
                section_labels=labels,
                authorizes_blueprint_repair=False,
            )
        parsed = patched
        module_code, _ranges = write_attempt()
        ok, output = _check_lean(attempt_path, ctx.lean_command)
        if not ok:
            retry_parsed, retry_code, retry_note = (
                _retry_statement_patch_compile_once(
                    ctx,
                    sec.labels,
                    sorted(rejected),
                    sections,
                    import_modules,
                    parsed,
                    module_code,
                    output,
                    attempt_path,
                    sessions=sessions,
                )
            )
            if retry_parsed is None:
                raise RepairRequest(
                    "Phase 1 alignment correction does not compile:\n"
                    + output[-8000:]
                    + "\nOne compiler-feedback correction failed: "
                    + retry_note,
                    sorted(rejected),
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                )
            parsed = retry_parsed
            module_code = retry_code
        reaudit = _model_alignment_audit(
            ctx, labels, module_code, tag="phase1-post-correction"
        )
        if reaudit is not None:
            reaudit = _coerce_alignment_audit_result(reaudit)
            plan_request = _audit_plan_revision_request(
                ctx,
                reaudit,
                layer_no=-1,
                source="top_down_alignment_post_correction",
            )
            if plan_request is not None:
                raise plan_request
            kind, reason, rejected, helpers = reaudit
            raise RepairRequest(
                reason,
                sorted(rejected),
                decomposition_helpers=helpers if kind == "decomposition" else None,
                section_labels=labels,
                authorizes_blueprint_repair=(kind in {"blueprint", "decomposition"}),
            )

    # All candidate gates passed. Atomically publish the source before building
    # its importable object; an interrupted earlier gate can never corrupt it.
    commit_path = sec.path.with_suffix(".phase1-commit.tmp")
    commit_path.write_text(module_code, encoding="utf-8")
    os.replace(commit_path, sec.path)
    object_attempt = _compile_module_olean(sec.path, ctx.lean_command)
    if not object_attempt.ok:
        rollback_path = sec.path.with_suffix(".phase1-rollback.tmp")
        rollback_path.write_text(original_code, encoding="utf-8")
        os.replace(rollback_path, sec.path)
        _compile_module_olean(sec.path, ctx.lean_command)
        route = _route_lean_generation_failure(labels)
        raise RepairRequest(
            "Phase 1 could not compile the refined module object:\n"
            + object_attempt.output[-8000:],
            list(route.failed_labels),
            section_labels=labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
        )
    attempt_path.unlink(missing_ok=True)
    if sec.refined_labels is None:
        sec.refined_labels = set(sec.labels)
    else:
        sec.refined_labels.update(labels)
    _note_frozen_section(ctx, labels)
    _log(
        f"  Phase 1 froze {len(labels)} top-down statement contract(s): "
        + ", ".join(labels[:6])
        + ("..." if len(labels) > 6 else "")
    )
    _record(
        ctx.telemetry,
        "phase1_statement_refined",
        section=sec.number,
        labels=labels,
        count=len(labels),
    )


def _phase1_candidate_code(candidates: list[Section]) -> str:
    """Collect target declarations for one layer-wide semantic audit."""
    declarations: list[str] = []
    for section in candidates:
        parsed, _index = _module_decl_texts(section)
        declarations.extend(decl.text for decl in parsed.decls)
    return "\n\n".join(declarations)


def _patch_phase1_candidate_section(
    ctx: Ctx,
    section: Section,
    rejected: set[str],
    reason: str,
) -> bool:
    """Patch only audit-rejected declarations in one compiled candidate."""
    local_rejected = [label for label in section.labels if label in rejected]
    if not local_rejected:
        return True
    original = section.path.read_text(encoding="utf-8")
    parsed = _parse_module(original)
    findings = [
        SkeletonFinding(reason, label=label, lean_name=_lean_name(label))
        for label in local_rejected
    ]
    patched, _note = _targeted_patch_skeleton_decls(
        ctx,
        section.labels,
        [],
        section.import_modules,
        parsed,
        original,
        findings,
        timeout=ctx.hard_timeout,
        sessions={},
        escalated=True,
    )
    if patched is None:
        return False
    target_kinds = {
        _lean_name(label): ctx.nodes[label].kind for label in section.labels
    }
    for decl in patched.decls:
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    code, _ranges = _compose_module(
        patched.imports, patched.preamble, [decl.text for decl in patched.decls]
    )
    label_by_name = {_lean_name(label): label for label in section.labels}
    deterministic = _skeleton_code_findings(
        code,
        target_kinds,
        label_by_name,
        _planned_helper_owner_by_name(ctx, section.labels),
    )
    deterministic += _skeleton_deterministic_findings(code, ctx, section.labels)
    if deterministic:
        return False
    section.path.write_text(code, encoding="utf-8")
    ok, output = _check_lean(section.path, ctx.lean_command)
    if not ok:
        retry_parsed, retry_code, _retry_note = (
            _retry_statement_patch_compile_once(
                ctx,
                section.labels,
                local_rejected,
                [],
                section.import_modules,
                patched,
                code,
                output,
                section.path,
                sessions={},
            )
        )
        if retry_parsed is None:
            section.path.write_text(original, encoding="utf-8")
            return False
        patched = retry_parsed
        code = retry_code
    object_attempt = _compile_module_olean(section.path, ctx.lean_command)
    if not object_attempt.ok:
        section.path.write_text(original, encoding="utf-8")
        return False
    return True


def _expand_rejected_section_components(
    ctx: Ctx, candidates: list[Section], rejected: set[str]
) -> set[str]:
    """Keep every shared-helper component atomic after a critic rejection."""
    expanded = set(rejected)
    for section in candidates:
        if not (set(section.labels) & expanded) or not section.path.is_file():
            continue
        parsed = _parse_module(section.path.read_text(encoding="utf-8"))
        target_by_name = {_lean_name(label): label for label in section.labels}
        for component in _target_components_from_helpers(
            parsed,
            target_by_name,
            _planned_helper_owner_by_name(ctx, section.labels),
        ):
            if component & expanded:
                expanded.update(component)
    return expanded


def _audit_phase1_layer_candidates(
    ctx: Ctx,
    layer_no: int,
    candidates: list[Section],
    existing_sections: list[Section] | None = None,
    alloc: _SectionNumberAllocator | None = None,
) -> list[Section]:
    """Integrate compiled candidates and audit only compiler-modified contracts.

    Semantic-first callers have already cached a verdict for each candidate.
    Importing every module together remains mandatory. The cache key includes
    the target declaration and its owned helpers, so the subsequent audit call
    is free when compilation changed nothing and judges only contracts changed
    by a compiler-driven patch otherwise. The older compile-first callers still
    receive the same full layer audit through this function.
    """
    if not candidates:
        return []
    labels = [label for section in candidates for label in section.labels]

    gate = SCRATCH_DIR / ctx.name / f"Phase1Layer{layer_no:02d}Gate.lean"
    gate.parent.mkdir(parents=True, exist_ok=True)
    gate.write_text(
        "\n".join(f"import {section.module}" for section in candidates)
        + "\n\nset_option autoImplicit false\n\ntheorem phase1_layer_gate : True := by trivial\n",
        encoding="utf-8",
    )
    try:
        integrated, output = _check_lean(gate, ctx.lean_command)
    finally:
        with contextlib.suppress(OSError):
            gate.unlink(missing_ok=True)
    if not integrated:
        for section in candidates:
            _discard_section_artifacts(section.path)
        raise RepairRequest(
            "Compiled Phase-1 candidates conflict when imported together:\n"
            + output[-12000:],
            labels,
            section_labels=labels,
            authorizes_blueprint_repair=False,
        )

    _log(
        f"==> Phase 1 layer {layer_no}: checking {len(labels)} integrated "
        "declaration(s); unchanged semantic verdicts are reused"
    )
    audit = _model_alignment_audit(
        ctx, labels, _phase1_candidate_code(candidates), tag=f"layer-{layer_no}"
    )
    if audit is None:
        for section in candidates:
            section.refined_labels = set(section.labels)
            _note_frozen_section(ctx, section.labels)
        _record(
            ctx.telemetry,
            "phase1_layer_frozen",
            layer=layer_no,
            labels=labels,
            sections=len(candidates),
        )
        _log(
            f"  Phase 1 layer {layer_no} frozen "
            f"({len(labels)} declaration(s), {len(candidates)} section(s))"
        )
        return candidates

    audit = _coerce_alignment_audit_result(audit)
    kind, reason, rejected, helpers = audit
    lean_rejected = audit.labels_for("lean-generation")
    decomposition_rejected = audit.labels_for("decomposition")
    blueprint_rejected = audit.labels_for("blueprint")
    plan_revised = _revise_decomposition_plans_once(
        ctx,
        decomposition_rejected,
        audit.reason_for(sorted(decomposition_rejected)),
        layer_no=layer_no,
        source="integrated_alignment",
    )
    decomposition_rejected.difference_update(plan_revised)
    reported_plan_defects = _revise_audit_reported_plan_defects(
        ctx,
        audit,
        layer_no=layer_no,
        source="integrated_alignment",
    )
    if reported_plan_defects:
        plan_revised.update(reported_plan_defects)
        lean_rejected.difference_update(reported_plan_defects)
    # A compiling candidate that exactly realizes every public surface in its
    # accepted plan cannot repair a semantic omission by being regenerated
    # under that unchanged plan. Correct the plan immediately from the audit
    # evidence instead of paying for an escalation candidate and the same
    # audit a second time. Conservative exact matching leaves all ambiguous
    # cases on the existing generation-retry lifecycle.
    realized_plan_defects = _plan_realized_semantic_rejections(
        ctx, lean_rejected, _phase1_candidate_code(candidates)
    )
    if realized_plan_defects:
        immediately_revised = _revise_exhausted_phase1_contracts(
            ctx,
            realized_plan_defects,
            audit.reason_for(sorted(realized_plan_defects)),
        )
        if immediately_revised:
            plan_revised.update(immediately_revised)
            lean_rejected.difference_update(immediately_revised)
            _record(
                ctx.telemetry,
                "phase1_plan_realized_semantic_rejection",
                layer=layer_no,
                labels=sorted(immediately_revised),
                route="immediate_plan_revision",
                additional_calls_vs_existing_exhaustion_route=0,
                replacement_call="phase1_design_plan_correction",
                avoided_route="unchanged_plan_generation_retry",
            )
            _log(
                "  compiling candidate exactly realized its rejected plan; "
                "revised the plan before regeneration: "
                + ", ".join(sorted(immediately_revised))
            )
    repair_rejected = decomposition_rejected | blueprint_rejected
    audit_required_dependencies = getattr(
        audit, "required_dependencies", {}
    )
    expanded_rejected = _expand_rejected_section_components(
        ctx, candidates, rejected
    )
    if expanded_rejected != rejected:
        _record(
            ctx.telemetry,
            "phase1_shared_helper_component_expanded",
            layer=layer_no,
            critic_rejected_labels=sorted(rejected),
            component_labels=sorted(expanded_rejected),
        )
        rejected = expanded_rejected
    request_labels = set(rejected)
    failure_route: FailureScopeDecision | None = None
    if lean_rejected:
        for section in candidates:
            section_rejected = lean_rejected & set(section.labels)
            if section_rejected:
                _store_generation_candidates(
                    ctx,
                    section_rejected,
                    section.path.read_text(encoding="utf-8"),
                    source=f"phase1_layer_{layer_no}_alignment",
                    all_labels=section.labels,
                    repair_stage="semantic_rejected",
                    required_dependencies=audit_required_dependencies,
                    lean_status="passed",
                    semantic_status="rejected",
                    semantic_evidence=reason,
                )
        tier_by_label = {
            label: (
                section.generation_tier
                if section.generation_tier in {"base", "escalation"}
                else _retry_next_tier(ctx, label, "phase1_statement")
            )
            for section in candidates
            for label in section.labels
            if label in lean_rejected
        }
        exhausted: set[str] = set()
        for tier in ("base", "escalation"):
            tier_labels = [
                label for label in labels
                if label in lean_rejected and tier_by_label.get(label, "base") == tier
            ]
            if tier_labels:
                exhausted.update(
                    _record_retry_failure(
                        ctx,
                        tier_labels,
                        stage="phase1_statement",
                        attempted_tier=tier,
                        evidence=reason,
                        source=f"phase1_layer_{layer_no}_alignment",
                    )
                )
        _store_generation_feedback(
            ctx, lean_rejected, reason, source="statement_alignment"
        )
        _quarantine_labels(ctx, lean_rejected, "statement_alignment")
        if exhausted:
            decomposition_after_revision, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    exhausted,
                    reason,
                    layer_no=layer_no,
                    source="integrated_alignment",
                )
            )
            if decomposition_after_revision:
                decomposition_rejected.update(decomposition_after_revision)
                repair_rejected.update(decomposition_after_revision)
            if revised:
                kind = "plan-revised"
                request_labels = revised
                failure_route = FailureScopeDecision(
                    action="independent",
                    parts=tuple((label,) for label in sorted(revised)),
                    failed_labels=tuple(sorted(revised)),
                    accepted_labels=(),
                )
            if unresolved:
                kind = "generation-exhausted"
                request_labels = set(unresolved) | set(revised)
                failure_route = None
                _log(
                    f"  Phase 1 layer {layer_no}: retry lifecycle exhausted for "
                    + ", ".join(sorted(unresolved))
                    + "; consuming bounded generation retry budget without editing "
                    "the blueprint"
                )
        else:
            ordered_rejected = tuple(label for label in labels if label in lean_rejected)
            failure_route = FailureScopeDecision(
                action="independent",
                parts=tuple((label,) for label in ordered_rejected),
                failed_labels=ordered_rejected,
                accepted_labels=tuple(label for label in labels if label not in rejected),
            )
            _log(
                f"  Phase 1 layer {layer_no}: preserving {len(lean_rejected)} "
                "independent retry lifecycle(s); next attempts start at "
                "the escalation tier"
            )
        _record(
            ctx.telemetry,
            "lean_generation_failure_routed",
            stage="phase1_alignment",
            action=(failure_route.action if failure_route else "exhausted"),
            labels=labels,
            failing_labels=sorted(lean_rejected),
            accepted_labels=[label for label in labels if label not in rejected],
            part_sizes=(
                [len(part) for part in failure_route.parts]
                if failure_route
                else [1 for _label in lean_rejected]
            ),
            layer=layer_no,
            candidate_tiers=tier_by_label,
        )

    # A single audit may contain unrelated Lean-translation failures and
    # missing blueprint interfaces. Preserve the former's candidates and retry
    # state above, but immediately route only the independently authorized
    # blueprint/decomposition subset to the transactional blueprint repair.
    if repair_rejected:
        request_labels = set(repair_rejected)
        kind = "decomposition" if decomposition_rejected else "blueprint"
        reason = audit.reason_for(sorted(repair_rejected))
        helpers = audit.helpers_for(sorted(decomposition_rejected))
        if decomposition_rejected and not helpers:
            helpers = [
                "introduce explicit blueprint definitions or lemmas for the "
                "mathematical interfaces named by the repeated contract rejection"
            ]
        failure_route = None
        _record(
            ctx.telemetry,
            "phase1_mixed_alignment_routed",
            layer=layer_no,
            repair_labels=sorted(repair_rejected),
            decomposition_labels=sorted(decomposition_rejected),
            blueprint_labels=sorted(blueprint_rejected),
            deferred_lean_labels=sorted(lean_rejected),
        )
    elif lean_rejected:
        kind = "lean-generation" if kind == "mixed" else kind
        request_labels = set(request_labels) & set(lean_rejected)

    if plan_revised and not repair_rejected:
        revision_route = FailureScopeDecision(
            action="independent",
            parts=tuple((label,) for label in sorted(plan_revised)),
            failed_labels=tuple(sorted(plan_revised)),
            accepted_labels=(),
        )
        failure_route = (
            _combine_failure_routes([failure_route, revision_route])
            if failure_route is not None
            else revision_route
        )
        request_labels.update(plan_revised)
        if not lean_rejected:
            kind = "plan-revised"
            reason = audit.reason_for(sorted(plan_revised))

    accepted: list[Section] = []
    discarded_labels: set[str] = set()
    for section in candidates:
        section_rejected = rejected & set(section.labels)
        if section_rejected:
            retained_labels = [
                label for label in section.labels if label not in section_rejected
            ]
            retained: list[Section] | None = None
            if retained_labels and alloc is not None:
                parsed = _parse_module(section.path.read_text(encoding="utf-8"))
                decl_texts = _delivered_decl_texts(
                    parsed,
                    retained_labels,
                    {_lean_name(label) for label in section.labels},
                    _planned_helper_owner_by_name(ctx, section.labels),
                )
                if decl_texts:
                    # The layer critic already accepted these declarations.
                    # Rebuild them without the rejected siblings and rerun all
                    # deterministic and Lean gates, but do not pay for another
                    # semantic audit. If a retained declaration secretly used
                    # a rejected sibling or shared helper, Lean rejects the
                    # extraction and the normal regeneration fallback remains.
                    old_defer = getattr(ctx, "defer_phase1_alignment", False)
                    ctx.defer_phase1_alignment = True
                    try:
                        retained = _freeze_section_from_code(
                            ctx,
                            retained_labels,
                            list(existing_sections or []) + accepted,
                            alloc,
                            decl_texts,
                            list(parsed.imports),
                            list(parsed.preamble),
                            origin="accepted layer siblings",
                        )
                    finally:
                        ctx.defer_phase1_alignment = old_defer
            _discard_section_artifacts(section.path)
            if retained:
                for kept in retained:
                    kept.refined_labels = set(kept.labels)
                    _note_frozen_section(ctx, kept.labels)
                accepted.extend(retained)
                discarded_labels.update(section_rejected)
                _log(
                    f"  retained {len(retained_labels)} accepted declaration(s) "
                    f"beside {len(section_rejected)} rejected sibling(s)"
                )
                _record(
                    ctx.telemetry,
                    "phase1_partial_section_retained",
                    layer=layer_no,
                    retained_labels=retained_labels,
                    rejected_labels=sorted(section_rejected),
                    source_section=section.number,
                )
            else:
                discarded_labels.update(section.labels)
            continue
        section.refined_labels = set(section.labels)
        _note_frozen_section(ctx, section.labels)
        accepted.append(section)
    _record(
        ctx.telemetry,
        "phase1_layer_rejected",
        layer=layer_no,
        labels=labels,
        rejected_labels=sorted(rejected),
        discarded_labels=sorted(discarded_labels),
        accepted_labels=[label for sec in accepted for label in sec.labels],
        classification=kind,
    )
    raise RepairRequest(
        reason,
        sorted(request_labels),
        decomposition_helpers=helpers if kind == "decomposition" else None,
        # Normalization is an editing operation, so its scope must match the
        # exact contracts authorized for repair. In a mixed-tier rejection,
        # other rejected siblings retain their independent escalation state.
        section_labels=sorted(request_labels),
        context_labels=sorted(discarded_labels or rejected),
        frozen_sections=accepted,
        authorizes_blueprint_repair=kind in {
            "blueprint",
            "decomposition",
        },
        failure_route=(
            failure_route
            if kind in {"lean-generation", "plan-revised"}
            else None
        ),
        required_dependencies={
            label: dependencies
            for label, dependencies in audit_required_dependencies.items()
            if label not in plan_revised
        },
        model_repair_labels=sorted(
            decomposition_rejected
            | (blueprint_rejected - set(audit_required_dependencies))
        ),
    )


def _semantic_first_failure_request(
    ctx: Ctx,
    layer_no: int,
    candidates: list[Phase1LayerCandidate],
    audit: AlignmentAuditResult,
    frozen: list[Section],
) -> RepairRequest:
    """Route a semantic-first rejection while retaining independently accepted work."""
    audit = _coerce_alignment_audit_result(audit)
    kind, reason, rejected, helpers = audit
    lean_rejected = audit.labels_for("lean-generation")
    decomposition_rejected = audit.labels_for("decomposition")
    blueprint_rejected = audit.labels_for("blueprint")
    plan_revised = _revise_decomposition_plans_once(
        ctx,
        decomposition_rejected,
        audit.reason_for(sorted(decomposition_rejected)),
        layer_no=layer_no,
        source="semantic_first_alignment",
    )
    decomposition_rejected.difference_update(plan_revised)
    reported_plan_defects = _revise_audit_reported_plan_defects(
        ctx,
        audit,
        layer_no=layer_no,
        source="semantic_first_alignment",
    )
    if reported_plan_defects:
        plan_revised.update(reported_plan_defects)
        lean_rejected.difference_update(reported_plan_defects)
    repair_rejected = decomposition_rejected | blueprint_rejected
    audit_required_dependencies = getattr(
        audit, "required_dependencies", {}
    )
    request_labels = set(rejected)
    failure_route: FailureScopeDecision | None = None
    if lean_rejected:
        tier_by_label = {
            label: candidate.generation_tier
            for candidate in candidates
            for label in candidate.labels
            if label in lean_rejected
        }
        exhausted: set[str] = set()
        for tier in ("base", "escalation"):
            tier_labels = [
                label
                for label in sorted(lean_rejected)
                if tier_by_label.get(label, "base") == tier
            ]
            if tier_labels:
                exhausted.update(
                    _record_retry_failure(
                        ctx,
                        tier_labels,
                        stage="phase1_statement",
                        attempted_tier=tier,
                        evidence=reason,
                        source=f"phase1_layer_{layer_no}_semantic_first",
                    )
                )
        for candidate in candidates:
            local = lean_rejected & set(candidate.labels)
            if local:
                _store_generation_candidates(
                    ctx,
                    local,
                    _phase1_layer_candidate_code(candidate),
                    source=f"phase1_layer_{layer_no}_semantic_first",
                    all_labels=candidate.labels,
                    repair_stage="semantic_rejected",
                    required_dependencies=audit_required_dependencies,
                    semantic_status="rejected",
                    semantic_evidence=reason,
                )
        _store_generation_feedback(
            ctx, lean_rejected, reason, source="semantic_first_statement_alignment"
        )
        _quarantine_labels(ctx, lean_rejected, "statement_alignment")
        if exhausted:
            decomposition_after_revision, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    exhausted,
                    reason,
                    layer_no=layer_no,
                    source="semantic_first_alignment",
                )
            )
            if decomposition_after_revision:
                decomposition_rejected.update(decomposition_after_revision)
                repair_rejected.update(decomposition_after_revision)
            if revised:
                kind = "plan-revised"
                request_labels = revised
                failure_route = FailureScopeDecision(
                    action="independent",
                    parts=tuple((label,) for label in sorted(revised)),
                    failed_labels=tuple(sorted(revised)),
                    accepted_labels=(),
                )
            if unresolved:
                kind = "generation-exhausted"
                request_labels = set(unresolved) | set(revised)
                failure_route = None
                _log(
                    f"  Phase 1 layer {layer_no}: retry lifecycle exhausted for "
                    + ", ".join(sorted(unresolved))
                    + "; consuming bounded generation retry budget without editing "
                    "the blueprint"
                )
        else:
            ordered = tuple(
                label
                for candidate in candidates
                for label in candidate.labels
                if label in lean_rejected
            )
            failure_route = FailureScopeDecision(
                action="independent",
                parts=tuple((label,) for label in ordered),
                failed_labels=ordered,
                accepted_labels=(),
            )
    if repair_rejected:
        request_labels = set(repair_rejected)
        kind = "decomposition" if decomposition_rejected else "blueprint"
        reason = audit.reason_for(sorted(repair_rejected))
        helpers = audit.helpers_for(sorted(decomposition_rejected))
        if decomposition_rejected and not helpers:
            helpers = [
                "introduce explicit blueprint definitions or lemmas for the "
                "mathematical interfaces named by the repeated contract rejection"
            ]
        failure_route = None
        _record(
            ctx.telemetry,
            "phase1_mixed_alignment_routed",
            layer=layer_no,
            repair_labels=sorted(repair_rejected),
            decomposition_labels=sorted(decomposition_rejected),
            blueprint_labels=sorted(blueprint_rejected),
            deferred_lean_labels=sorted(lean_rejected),
            source="semantic_first_alignment",
        )
    elif lean_rejected:
        kind = "lean-generation" if kind == "mixed" else kind
        request_labels = set(request_labels) & set(lean_rejected)
    if plan_revised and not repair_rejected:
        revision_route = FailureScopeDecision(
            action="independent",
            parts=tuple((label,) for label in sorted(plan_revised)),
            failed_labels=tuple(sorted(plan_revised)),
            accepted_labels=(),
        )
        failure_route = (
            _combine_failure_routes([failure_route, revision_route])
            if failure_route is not None
            else revision_route
        )
        request_labels.update(plan_revised)
        if not lean_rejected:
            kind = "plan-revised"
            reason = audit.reason_for(sorted(plan_revised))
    _record(
        ctx.telemetry,
        "phase1_semantic_first_rejected",
        layer=layer_no,
        labels=[label for candidate in candidates for label in candidate.labels],
        rejected_labels=sorted(rejected),
        accepted_labels=[label for section in frozen for label in section.labels],
        classification=kind,
    )
    return RepairRequest(
        reason,
        sorted(request_labels),
        decomposition_helpers=helpers if kind == "decomposition" else None,
        section_labels=sorted(request_labels),
        context_labels=sorted(rejected),
        frozen_sections=frozen,
        authorizes_blueprint_repair=kind in {
            "blueprint",
            "decomposition",
        },
        failure_route=(
            failure_route
            if kind in {"lean-generation", "plan-revised"}
            else None
        ),
        required_dependencies={
            label: dependencies
            for label, dependencies in audit_required_dependencies.items()
            if label not in plan_revised
        },
        model_repair_labels=sorted(
            decomposition_rejected
            | (blueprint_rejected - set(audit_required_dependencies))
        ),
    )


def _revise_exhausted_phase1_contracts(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    policy: str = "post_semantic_rejection",
) -> set[str]:
    """Revise plan contracts that survived generation but failed semantics.

    Once both generation tiers have emitted a compiling statement and the
    publication critic still rejects it, regenerating under the identical plan
    cannot help. Apply the critic evidence to the untrusted plan once, then
    update candidate plan provenance and reset retry provenance tied to the old
    plan. The compiling candidate remains the correction seed; the blueprint
    remains untouched and every revision still passes the normal deterministic,
    Lean, and semantic gates.
    """
    entries = getattr(ctx, "design_plan_entries", {}) or {}
    eligible = sorted(
        label
        for label in set(labels)
        if label in entries
        and int((entries.get(label) or {}).get("schema_version") or 0)
        == DESIGN_PLAN_SCHEMA_VERSION
    )
    if not eligible:
        return set()
    previous_revision_counts = {
        label: int((entries.get(label) or {}).get("semantic_revision_count") or 0)
        for label in eligible
    }
    if not _correct_phase1_design_plan(
        ctx, eligible, evidence, escalated=True
    ):
        return set()

    for label in eligible:
        entries[label]["semantic_revision_count"] = (
            previous_revision_counts[label] + 1
        )

    _clear_retry_lifecycle(ctx, eligible, stage="phase1_statement")
    with _STATE_LOCK:
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
    retained_seeds: list[tuple[list[str], str, str, dict[str, set[str]]]] = []
    seen_seed_hashes: set[str] = set()
    reset_candidate_labels: set[str] = set(eligible)
    for label in eligible:
        candidate = candidates.get(label)
        if not isinstance(candidate, dict):
            continue
        component = [
            item
            for item in candidate.get("component_labels") or [label]
            if item in ctx.nodes
        ]
        code = str(candidate.get("code") or "").strip()
        seed_hash = _candidate_hash(code)
        if not code or seed_hash in seen_seed_hashes:
            continue
        seen_seed_hashes.add(seed_hash)
        reset_candidate_labels.update(component)
        seed_code, _ = _compose_module(
            [str(item) for item in candidate.get("imports") or []],
            [str(item) for item in candidate.get("preamble") or []],
            [code],
        )
        retained_seeds.append(
            (
                component,
                seed_code,
                str(candidate.get("generation_tier") or "base"),
                {
                    item: {
                        str(dep)
                        for dep in (candidates.get(item) or {}).get(
                            "required_dependencies"
                        )
                        or []
                    }
                    for item in component
                },
            )
        )
    _clear_retry_lifecycle(
        ctx, reset_candidate_labels, stage="phase1_statement"
    )
    with _STATE_LOCK:
        live_candidates = getattr(ctx, "generation_candidates", {})
        for label in reset_candidate_labels:
            live_candidates.pop(label, None)
    retained: list[str] = []
    for component, code, tier, required in retained_seeds:
        retained.extend(
            _store_generation_candidates(
                ctx,
                component,
                code,
                source="interface_plan_revised",
                all_labels=component,
                generation_tier=tier,
                repair_stage="semantic_rejected",
                required_dependencies=required,
                semantic_status="rejected",
                semantic_evidence=evidence,
            )
        )
    _release_quarantine(ctx, eligible, reason="interface_plan_revised")
    _record(
        ctx.telemetry,
        "phase1_exhausted_contract_revised",
        labels=eligible,
        evidence=evidence[-4000:],
        policy=policy,
        retained_candidate_labels=retained,
    )
    _log(
        "  revised rejected Phase 1 contract plan for: "
        + ", ".join(eligible)
        + "; retrying only those nodes under the new contract"
    )
    return set(eligible)


def _revise_decomposition_plans_once(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    layer_no: int,
    source: str,
) -> set[str]:
    """Correct an untried interface plan before editing the blueprint.

    A semantic critic can correctly observe that a generated declaration lacks
    a mathematical interface while incorrectly concluding that the blueprint
    itself must be decomposed. When the shared plan has not yet consumed its
    one evidence-driven revision, repair that cheaper untrusted artifact first.
    A second decomposition verdict under the revised plan follows the existing
    transactional blueprint-decomposition path.
    """
    entries = getattr(ctx, "design_plan_entries", {}) or {}
    eligible = {
        label
        for label in labels
        if label in entries
        and int((entries.get(label) or {}).get("schema_version") or 0)
        == DESIGN_PLAN_SCHEMA_VERSION
        and int((entries.get(label) or {}).get("semantic_revision_count") or 0)
        < 1
    }
    if not eligible:
        return set()
    revised = _revise_exhausted_phase1_contracts(ctx, eligible, evidence)
    if revised:
        _record(
            ctx.telemetry,
            "phase1_decomposition_deferred_for_plan_revision",
            layer=layer_no,
            source=source,
            labels=sorted(revised),
            evidence=evidence[-4000:],
        )
        _log(
            "  decomposition verdict first corrected the untried interface "
            "plan for: " + ", ".join(sorted(revised))
        )
    return revised


def _semantic_exhaustion_policy(ctx: Ctx, label: str) -> str:
    """Classify the next bounded action without mutating refinement state.

    This pure policy is deliberately separate from the router so historical
    traces can validate a proposed lifecycle before it changes live behavior.
    """
    if _uses_blueprint_direct_generation(ctx, label):
        return "decomposition"
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label) or {}
    if int(entry.get("semantic_revision_count") or 0) >= 1:
        return "blueprint-direct"
    return "plan-revision"


def _route_exhausted_phase1_semantics(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    layer_no: int,
    source: str,
) -> tuple[set[str], set[str], set[str]]:
    """Route semantic exhaustion identically in every Phase-1 transaction.

    The first exhausted lifecycle revises the node's saved interface plan from
    exact critic evidence. A second exhaustion disables that plan for the same
    statement fingerprint and tries blueprint-direct generation. Only
    exhaustion of that direct lifecycle routes the node to decomposition.

    Returns ``(decomposition, revised, unresolved)`` label sets.
    """
    exhausted = set(labels)
    actions = {
        label: _semantic_exhaustion_policy(ctx, label)
        for label in exhausted
    }
    decomposition = {
        label for label, action in actions.items() if action == "decomposition"
    }
    if decomposition:
        exhausted.difference_update(decomposition)
        _log(
            "  semantic rejection survived the blueprint-direct generation "
            "lifecycle; routing to blueprint decomposition: "
            + ", ".join(sorted(decomposition))
        )
        _record(
            ctx.telemetry,
            "phase1_semantic_exhaustion_decomposition",
            layer=layer_no,
            source=source,
            labels=sorted(decomposition),
            statement_fps={
                label: ctx.stmt_fps.get(label, "")
                for label in sorted(decomposition)
            },
            evidence=evidence[-4000:],
        )

    direct_requested = {
        label
        for label, action in actions.items()
        if action == "blueprint-direct"
    }
    direct = _activate_blueprint_direct_generation(
        ctx,
        direct_requested,
        evidence,
        source="post_semantic_rejection_after_plan_revision",
    )
    exhausted.difference_update(direct)
    revised = direct | _revise_exhausted_phase1_contracts(
        ctx, exhausted, evidence
    )
    unresolved = exhausted - revised
    return decomposition, revised, unresolved


def _run_validated_contract_phase1_layer(
    ctx: Ctx,
    layer_no: int,
    groups: list[list[str]],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
) -> list[Section]:
    """Generate from shared plan entries, compile, then audit final statements.

    The plan is untrusted guidance, so this transaction spends no critic call
    on it. Compiler correction remains local to each candidate; the integrated,
    compiling declarations receive the mandatory publication audit exactly
    once (or a cache hit when byte-identical).
    """
    worker_count = max(1, min(getattr(ctx, "workers", 1), len(groups)))
    _log(
        f"==> Phase 1 layer {layer_no}: generating {len(groups)} uncompiled "
        f"candidate group(s) with {worker_count} worker(s)"
    )
    generated: list[Phase1LayerCandidate | None] = [None] * len(groups)
    failures: list[tuple[int, RepairRequest]] = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
        future_map = {
            pool.submit(_generate_uncompiled_phase1_candidate, ctx, group, sections): index
            for index, group in enumerate(groups)
        }
        for future in concurrent.futures.as_completed(future_map):
            index = future_map[future]
            try:
                generated[index] = future.result()
            except RepairRequest as request:
                failures.append((index, request))
    candidates = [candidate for candidate in generated if candidate is not None]
    if failures:
        # A plan-closure finding cannot be repaired honestly by compiler
        # patching. Correct only the owning plan entries before ordinary retry.
        plan_requests = [
            request
            for _index, request in failures
            if request.plan_revision_required
        ]
        plan_labels = sorted(
            {
                label
                for request in plan_requests
                for label in request.labels
            }
        )
        if plan_labels:
            plan_evidence = "\n\n".join(
                request.evidence[-6000:] for request in plan_requests
            )
            corrected = _correct_phase1_design_plan(
                ctx, plan_labels, plan_evidence, escalated=False
            )
            _record(
                ctx.telemetry,
                "phase1_outline_plan_closure_correction",
                labels=plan_labels,
                corrected=bool(corrected),
                reason="deterministic_contract_closure",
            )
            if corrected:
                _clear_retry_lifecycle(
                    ctx, plan_labels, stage="phase1_statement"
                )
                _prune_stale_generation_candidates(ctx)
                _log(
                    "  corrected mechanically unclosed Phase 1 outline plan: "
                    + ", ".join(plan_labels)
                )
        for candidate in candidates:
            _store_generation_candidates(
                ctx,
                candidate.labels,
                _phase1_layer_candidate_code(candidate),
                source=f"phase1_layer_{layer_no}_incomplete_generation",
                all_labels=candidate.labels,
                reusable_uncompiled=True,
                generation_tier=candidate.generation_tier,
            )
        failures.sort(key=lambda item: item[0])
        # A failed generation group must not hold deterministically valid
        # siblings behind a frontier-wide barrier. Advance those siblings
        # through the ordinary compile/integration/alignment transaction now;
        # only their accepted contracts are attached to the retry request.
        accepted: list[Section] = []
        downstream_request: RepairRequest | None = None
        if candidates:
            try:
                accepted = _compile_and_finalize_semantic_candidates(
                    ctx, candidates, sections, alloc, layer_no=layer_no
                )
            except RepairRequest as request:
                accepted = list(request.frozen_sections)
                request.frozen_sections = []
                downstream_request = request

        # Prefer evidence that authorizes an actual blueprint edit. Every
        # non-selected generation/semantic failure has already persisted its
        # candidate, exact evidence, and retry lifecycle for the next frontier.
        requests = [request for _index, request in failures]
        if downstream_request is not None:
            requests.append(downstream_request)
        authorized = [
            request for request in requests if request.authorizes_blueprint_repair
        ]
        if authorized:
            selected = _aggregate_authorized_repair_requests(
                authorized,
                frozen_sections=accepted,
            )
            _record(
                ctx.telemetry,
                "phase1_authorized_repairs_aggregated",
                layer=layer_no,
                request_count=len(authorized),
                labels=selected.labels,
                model_repair_labels=selected.model_repair_labels,
                required_dependencies={
                    label: sorted(dependencies)
                    for label, dependencies in selected.required_dependencies.items()
                },
            )
        else:
            selected = _aggregate_retry_requests(
                requests, frozen_sections=accepted
            )
        _record(
            ctx.telemetry,
            "phase1_partial_frontier_advanced",
            layer=layer_no,
            generated_failure_labels=sorted(
                {
                    label
                    for _index, request in failures
                    for label in request.labels
                }
            ),
            additional_failure_labels=(
                sorted(downstream_request.labels)
                if downstream_request is not None
                else []
            ),
            frozen_labels=[
                label for section in accepted for label in section.labels
            ],
        )
        raise selected

    labels = [label for candidate in candidates for label in candidate.labels]
    _record(
        ctx.telemetry,
        "phase1_validated_contract_transaction",
        layer=layer_no,
        labels=labels,
        groups=[candidate.labels for candidate in candidates],
        stage="compile_then_final_audit",
    )
    return _compile_and_finalize_semantic_candidates(
        ctx, candidates, sections, alloc, layer_no=layer_no
    )


def _run_phase1(
    ctx: Ctx,
    sections: list[Section],
    pending: set[str],
    refinement_order: str,
) -> list[Section]:
    """Freeze exact statement contracts in the selected graph direction."""
    if not pending:
        return sections

    # The global pass coordinates semantics and vocabulary only. Exact typed
    # contracts are created atomically with each Phase-1 Lean candidate below;
    # this avoids a separate typed planning phase and its correction loop.
    _ensure_phase1_semantic_plan(ctx, pending)
    # Resumed state from the legacy typed planner remains valid and keeps its
    # historical closure behavior. Fresh compact-plan runs have no typed
    # entries yet; their closure starts when each candidate realizes one.
    legacy_plan_labels = {
        label
        for label in pending
        if label in getattr(ctx, "design_plan_entries", {})
        and (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            != "phase1_candidate"
        )
    }
    closure_findings: dict[str, list[str]] = (
        _validate_design_plan_contract_closure(ctx, legacy_plan_labels)
        if legacy_plan_labels
        else {}
    )
    _save_ctx_state(ctx, sections)
    plan_order = _design_plan_order(ctx, pending)

    if refinement_order == "bottom-up":
        alloc = _SectionNumberAllocator(
            max((section.number for section in sections), default=0) + 1
        )
        remaining = set(pending)
        frontier_no = 0
        while remaining:
            frozen = _frozen_labels(sections)
            targets = _bottom_up_ready_frontier(ctx.nodes, remaining, frozen)
            if not targets:
                blocked_by = {
                    label: sorted(
                        dep
                        for dep in ctx.nodes[label].uses
                        if dep in remaining and not ctx.nodes[dep].mathlibok
                    )
                    for label in sorted(remaining)
                }
                _record(
                    ctx.telemetry,
                    "phase1_ready_frontier_stalled",
                    pending_labels=sorted(remaining),
                    frozen_labels=sorted(frozen),
                    blocked_by=blocked_by,
                )
                raise RepairRequest(
                    "Bottom-up Phase 1 has pending declarations but no "
                    "dependency-ready frontier. Validation should have rejected "
                    "a dependency cycle; blocked dependencies: "
                    + json.dumps(blocked_by, sort_keys=True),
                    sorted(remaining),
                    section_labels=sorted(remaining),
                    authorizes_blueprint_repair=False,
                )
            closure_findings = _phase1_frontier_plan_gateway(
                ctx,
                targets,
                plan_order,
                closure_findings,
            )
            targets = _coalesce_candidate_components(ctx, targets)
            _log(
                f"==> Phase 1: refining bottom-up ready frontier {frontier_no} "
                f"({len(targets)} node(s))"
            )
            groups: list[list[str]] = []
            index = 0
            while index < len(targets):
                component = set(
                    _candidate_component_labels(ctx, targets[index], set(targets))
                )
                forced = [
                    label for label in targets[index:] if label in component
                ]
                with _STATE_LOCK:
                    reusable_entry = copy.deepcopy(
                        getattr(ctx, "generation_candidates", {}).get(
                            targets[index]
                        )
                    )
                if len(forced) > 1 or (
                    isinstance(reusable_entry, dict)
                    and _candidate_is_reusable_uncompiled(reusable_entry)
                ):
                    group = forced
                else:
                    size = ctx.effective_section_size or ctx.section_size
                    group = _next_phase1_group(
                        targets,
                        index,
                        size,
                        ctx.quarantined_labels,
                        getattr(ctx, "local_group_partitions", {}),
                    )
                groups.append(group)
                index += len(group)

            groups = _partition_phase1_groups_by_dependency_context(
                ctx, groups, sections
            )
            worker_count = max(1, min(getattr(ctx, "workers", 1), len(groups)))
            _record(
                ctx.telemetry,
                "phase1_layer_started",
                layer=frontier_no,
                scheduling="dynamic_dependency_ready_frontier",
                labels=targets,
                groups=groups,
                workers=worker_count,
                transaction_order="validated-contract_compile_final-audit",
            )
            try:
                accepted = _run_validated_contract_phase1_layer(
                    ctx, frontier_no, groups, sections, alloc
                )
            except RepairRequest as request:
                if request.frozen_sections:
                    sections.extend(request.frozen_sections)
                    remaining.difference_update(
                        label
                        for section in request.frozen_sections
                        for label in (
                            section.labels
                            if section.refined_labels is None
                            else section.refined_labels
                        )
                    )
                    request.frozen_sections = []
                    _save_ctx_state(ctx, sections)
                raise
            sections.extend(accepted)
            accepted_labels = {
                label
                for section in accepted
                for label in (
                    section.labels
                    if section.refined_labels is None
                    else section.refined_labels
                )
            }
            if not accepted_labels:
                raise RepairRequest(
                    "Bottom-up Phase 1 transaction returned without freezing "
                    "any dependency-ready declaration.",
                    targets,
                    section_labels=targets,
                    authorizes_blueprint_repair=False,
                )
            remaining.difference_update(accepted_labels)
            _save_ctx_state(ctx, sections)
            frontier_no += 1
        return sections

    layers = _top_down_statement_layers(ctx.nodes)

    owner = {label: sec for sec in sections for label in sec.labels}
    for layer_no, layer in enumerate(layers):
        targets = [label for label in layer if label in pending]
        if not targets:
            continue
        closure_findings = _phase1_frontier_plan_gateway(
            ctx,
            targets,
            plan_order,
            closure_findings,
        )
        _log(
            f"==> Phase 1: refining top-down statement layer {layer_no} "
            f"({len(targets)} node(s))"
        )
        by_section: dict[int, list[str]] = {}
        for label in targets:
            sec = owner.get(label)
            if sec is None or sec.deferred:
                raise RepairRequest(
                    f"Initial declaration for {label} is unavailable during Phase 1",
                    [label],
                    section_labels=[label],
                )
            by_section.setdefault(sec.number, []).append(label)
        for number in sorted(by_section):
            sec = next(item for item in sections if item.number == number)
            group = by_section[number]
            isolated = [
                label for label in group if label in ctx.quarantined_labels
            ]
            parts = _parts_around_labels(group, isolated) if isolated else [group]
            parts = _partition_phase1_groups_by_dependency_context(
                ctx, parts, sections
            )
            def refine_part(part: list[str]) -> None:
                starting_tier = (
                    _retry_next_tier(ctx, part[0], "phase1_statement")
                    if len(part) == 1
                    else "base"
                )
                try:
                    _refine_statement_group(ctx, sec, part, sections)
                    _save_ctx_state(ctx, sections)
                except RepairRequest as request:
                    route = request.failure_route
                    if not request.authorizes_blueprint_repair:
                        failed_labels = (
                            list(route.failed_labels) if route is not None else request.labels
                        )
                        attempted_tier = (
                            starting_tier
                            if len(part) == 1
                            else "base"
                        )
                        exhausted = _record_retry_failure(
                            ctx,
                            failed_labels,
                            stage="phase1_statement",
                            attempted_tier=attempted_tier,
                            evidence=request.evidence,
                            source="phase1_top_down",
                        )
                        _store_generation_feedback(
                            ctx,
                            failed_labels,
                            request.evidence,
                            source="phase1_top_down_retry",
                        )
                        if exhausted and len(part) == 1:
                            # Exhausting translation attempts is not evidence
                            # that the blueprint contract is mathematically
                            # wrong. Keep the draft immutable and consume the
                            # configured outer generation budget instead.
                            request.failure_route = None
                            raise
                    if route is None or route.action == "singleton":
                        raise
                    _record(
                        ctx.telemetry,
                        "lean_generation_failure_routed",
                        stage="phase1_top_down",
                        action=route.action,
                        labels=part,
                        failing_labels=list(route.failed_labels),
                        accepted_labels=list(route.accepted_labels),
                        part_sizes=[len(item) for item in route.parts],
                        layer=layer_no,
                    )
                    _log(
                        "  top-down Phase 1 failure routed as "
                        + route.action
                        + " across "
                        + " + ".join(str(len(item)) for item in route.parts)
                        + " node(s)"
                    )
                    for routed_part in route.parts:
                        refine_part(list(routed_part))

            for part in parts:
                refine_part(part)
    return sections


def _phase1_recompile_environment(ctx: Ctx, sections: list[Section]) -> set[str]:
    """Recompile all refined modules after lower contracts have settled.

    Returns labels whose owning module no longer compiles. They are moved back
    into Phase 1 rather than being misclassified as proof or blueprint failure.
    """
    active = [item for item in sections if not item.deferred]
    by_module = {sec.module: sec for sec in active}
    ordered: list[Section] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(sec: Section) -> None:
        if sec.module in visited:
            return
        if sec.module in visiting:
            # Blueprint validation should prevent a dependency cycle. Keep the
            # check total and let Lean report the malformed import graph.
            return
        visiting.add(sec.module)
        for module in sec.import_modules:
            dependency = by_module.get(module)
            if dependency is not None:
                visit(dependency)
        visiting.remove(sec.module)
        visited.add(sec.module)
        ordered.append(sec)

    for section in sorted(active, key=lambda item: item.number):
        visit(section)

    failed: set[str] = set()
    for sec in ordered:
        attempt = _compile_module_olean(sec.path, ctx.lean_command)
        if attempt.ok:
            continue
        refined = set(sec.labels) if sec.refined_labels is None else set(sec.refined_labels)
        failed.update(refined)
        sec.refined_labels = (
            set(sec.labels) - refined if sec.refined_labels is None else sec.refined_labels - refined
        )
        _log(
            f"  Phase 1 integration recheck returned {len(refined)} statement "
            f"contract(s) to refinement from {sec.file_name}"
        )
        _record(
            ctx.telemetry,
            "phase1_integration_recheck",
            section=sec.number,
            labels=sorted(refined),
            status="compile_failed",
            output_tail=attempt.output[-4000:],
        )
    return failed


# ---------------------------------------------------------------------------
# Phase 2: deferred declaration bodies


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
) -> tuple[list[str], dict[str, str], dict[str, list[str]]]:
    """Splice returned bodies into the module; compile and audit survivors.

    Returns ``(implemented_labels, errors_by_label, repair_helpers_by_label)``.
    """
    parsed, index = _module_decl_texts(sec)
    try:
        model_parsed = _ingest_model_lean(
            ctx, targets.keys(), response_code
        ).parsed
    except ValueError as exc:
        return (
            [],
            {label: f"invalid Lean response structure: {exc}" for label in targets},
            {},
        )
    model_decls = {decl.name: decl for decl in model_parsed.decls if decl.name}
    new_imports = [
        item
        for item in model_parsed.imports
        if item not in _missing_olean_imports(model_parsed.imports)
    ]
    errors: dict[str, str] = {}
    repair_helpers: dict[str, list[str]] = {}
    originals: dict[str, str] = {}
    spliced: list[str] = []
    for label, frozen_text in targets.items():
        name = _lean_name(label)
        model_decl = model_decls.get(name)
        if model_decl is None:
            errors[label] = f"response omitted frozen declaration `{name}`"
            continue
        proof = _extract_by_proof(model_decl.text)
        if proof is None:
            errors[label] = (
                f"response body for `{name}` must be a tactic block introduced by `:= by`"
            )
            continue
        if re.search(r"\bsorry\b|\badmit\b", proof):
            errors[label] = f"response body for `{name}` still contains sorry/admit"
            continue
        originals[label] = parsed.decls[index[name]].text
        parsed.decls[index[name]].text = _splice_proof(frozen_text, proof)
        spliced.append(label)
    if not spliced:
        return [], errors, repair_helpers
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
            return [], errors, repair_helpers
        proved = []
        for label in spliced:
            idx = index[_lean_name(label)]
            if idx in errors_by_decl:
                errors[label] = "\n".join(
                    errors_by_decl[idx]
                )[-4000:]
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
                    "implementation compiled but does not visibly use required dependency "
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
    semantic_body_labels = [
        label for label in proved if not _is_theorem_like_kind(ctx.nodes[label].kind)
    ]
    if semantic_body_labels:
        module_code = sec.path.read_text(encoding="utf-8")
        audit = _model_alignment_audit(
            ctx, semantic_body_labels, module_code, tag=f"{tag}-owned-body"
        )
        _record(
            ctx.telemetry,
            "definition_body_audit_result",
            section=sec.number,
            labels=semantic_body_labels,
            accepted=audit is None,
            routed_kind=audit[0] if audit is not None else "accepted",
            rejected_labels=(sorted(audit[2]) if audit is not None else []),
        )
        if audit is not None:
            kind, reason, rejected, helpers = audit
            rejected_bundles = set(semantic_body_labels) & set(rejected)
            if not rejected_bundles:
                rejected_bundles = set(semantic_body_labels)
            for label in rejected_bundles:
                errors[label] = reason
                parsed.decls[index[_lean_name(label)]].text = originals[label]
                if kind in {"blueprint", "decomposition"}:
                    repair_helpers[label] = list(helpers)
            proved = [label for label in proved if label not in rejected_bundles]
            _write_section(sec, parsed)
            if proved:
                ok4, output4 = _check_lean(sec.path, ctx.lean_command)
                if not ok4:
                    for label in proved:
                        parsed.decls[index[_lean_name(label)]].text = originals[label]
                        errors[label] = (
                            "accepted subset failed after definition-body audit rollback:\n"
                            + output4[-2000:]
                        )
                    _write_section(sec, parsed)
                    proved = []
    if proved:
        _log(f"accepted {len(proved)} implementation(s): {', '.join(proved[:6])}", tag=tag)
    return proved, errors, repair_helpers


def _prove_section(
    ctx: Ctx,
    sec: Section,
    sections: list[Section],
    requested_labels: list[str] | None = None,
) -> SectionProofOutcome:
    tag = f"S{sec.number:02d}"
    outcome = SectionProofOutcome(section=sec)
    # Per-section backend sessions (worker-thread local): implementation rounds over the
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
            ladder_labels = [
                label for label in sorry_labels if _is_theorem_like_kind(ctx.nodes[label].kind)
            ]
            proved = _run_tactic_ladder(ctx, sec, ladder_labels, tag=tag)
        except Exception as exc:  # noqa: BLE001 - the ladder is best-effort only
            _log(f"tactic ladder crashed ({exc}); continuing with model implementations", tag=tag)
            proved = []
        outcome.proved.extend(proved)
        _clear_retry_lifecycle(ctx, proved, stage="phase2_body")
        sorry_labels = [label for label in sorry_labels if label not in proved]

    import_modules = sec.import_modules
    remaining = list(sorry_labels)
    errors: dict[str, str] = {}
    batch_size = ctx.proof_batch
    # Enough base-tier rounds to reduce a repeatedly failing batch to
    # singletons by bisection. The old fixed two rounds could send every label
    # from a still-large failed batch straight to singleton escalation.
    max_batch_rounds = max(2, (max(1, batch_size) - 1).bit_length() + 1)
    round_no = 0
    while remaining and round_no < max_batch_rounds:
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
                route = _route_lean_generation_failure(batch)
                batch_size = min(
                    batch_size,
                    max(len(part) for part in route.parts),
                )
                next_remaining.extend(batch)
                _log(
                    "batch timed out; shared failure router reduced batch size "
                    f"to {batch_size}",
                    tag=tag,
                )
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
                    routing_action=route.action,
                )
                continue
            if result.status != "ok":
                route = _route_lean_generation_failure(batch)
                if route.action == "bisect":
                    batch_size = min(
                        batch_size,
                        max(len(part) for part in route.parts),
                    )
                    _log(
                        f"proof model call {result.status}; shared failure router "
                        f"reduced the next unit to {batch_size}",
                        tag=tag,
                    )
                _record(
                    ctx.telemetry,
                    "lean_generation_failure_routed",
                    stage="phase2_body",
                    action=route.action,
                    labels=batch,
                    failing_labels=list(route.failed_labels),
                    accepted_labels=list(route.accepted_labels),
                    part_sizes=[len(part) for part in route.parts],
                    round=round_no,
                    section=sec.number,
                    model_status=result.status,
                )
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
                    routing_action=route.action,
                    next_batch_size=batch_size,
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
            proved, batch_errors, batch_repairs = _apply_proof_batch(
                ctx, sec, result.text, targets, tag=tag
            )
            outcome.proved.extend(proved)
            errors.update(batch_errors)
            outcome.decomposition.update(batch_repairs)
            failed_batch = [
                label
                for label in batch
                if label not in proved and label not in batch_repairs
            ]
            local_unit = [label for label in batch if label not in batch_repairs]
            route = (
                _route_lean_generation_failure(local_unit, failed_batch)
                if failed_batch
                else None
            )
            if route is not None and route.action == "bisect":
                batch_size = min(
                    batch_size,
                    max(len(part) for part in route.parts),
                )
                _log(
                    "Lean-generation failure affected the full proof batch; "
                    f"shared router reduced the next unit to {batch_size}",
                    tag=tag,
                )
            if route is not None:
                _record(
                    ctx.telemetry,
                    "lean_generation_failure_routed",
                    stage="phase2_body",
                    action=route.action,
                    labels=local_unit,
                    failing_labels=list(route.failed_labels),
                    accepted_labels=list(route.accepted_labels),
                    part_sizes=[len(part) for part in route.parts],
                    round=round_no,
                    section=sec.number,
                )
            _record(
                ctx.telemetry,
                "proof_attempt_result",
                section=sec.number,
                phase="proof_batch",
                round=round_no,
                labels=batch,
                status=(
                    "needs_decomposition"
                    if batch_repairs and not proved and not failed_batch
                    else "partial"
                    if proved and (failed_batch or batch_repairs)
                    else "success"
                    if proved
                    else "failed"
                ),
                proved_labels=proved,
                failed_labels=failed_batch,
                decomposition_labels=sorted(batch_repairs),
                errors={label: batch_errors[label] for label in failed_batch if label in batch_errors},
                routing_action=route.action if route is not None else "accepted",
                next_batch_size=batch_size,
            )
            next_remaining.extend(
                label for label in batch if label not in proved and label not in outcome.decomposition
            )
        remaining = next_remaining

    # Escalation: only singleton calls reach the configured escalation runner.
    still: list[str] = []
    for label in remaining:
        parsed, index = _module_decl_texts(sec)
        name = _lean_name(label)
        if name not in index or not _has_terminal_sorry(parsed.decls[index[name]].text):
            continue
        if _retry_next_tier(ctx, label, "phase2_body") == "base":
            _record_retry_failure(
                ctx,
                [label],
                stage="phase2_body",
                attempted_tier="base",
                evidence=errors.get(label, "base proof generation did not close the body"),
                source="proof_batch_residue",
            )
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
                _record_retry_failure(
                    ctx,
                    [label],
                    stage="phase2_body",
                    attempted_tier="escalation",
                    evidence=result.error or result.status,
                    source="proof_singleton_model_call",
                )
                errors.setdefault(
                    label,
                    f"escalated implementation call {result.status}: {result.error[:400]}",
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
            proved, batch_errors, batch_repairs = _apply_proof_batch(
                ctx, sec, result.text, targets, tag=tag
            )
            errors.update(batch_errors)
            outcome.decomposition.update(batch_repairs)
            if batch_repairs:
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
                    decomposition_labels=sorted(batch_repairs),
                    missing_helpers=batch_repairs,
                )
                break
            if proved:
                outcome.proved.extend(proved)
                _clear_retry_lifecycle(ctx, proved, stage="phase2_body")
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
            _record_retry_failure(
                ctx,
                [label],
                stage="phase2_body",
                attempted_tier="escalation",
                evidence=batch_errors.get(label, errors.get(label, "proof rejected")),
                source="proof_singleton_validation",
            )
            parsed, index = _module_decl_texts(sec)
        if not solved and label not in outcome.decomposition:
            still.append(label)

    for label in still:
        outcome.failed[label] = errors.get(
            label, "no implementation found within the configured budgets"
        )
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
        if sec.provisional_environment:
            parsed, _index = _module_decl_texts(sec)
            # This is permanent name scaffolding. A blueprint repair makes
            # affected contracts provisional again; it does not erase the
            # declarations and restart the initial model pass. Remove only
            # nodes deleted from the blueprint. New helper names are added
            # deterministically by Phase 1 on the next loop iteration.
            surviving = [label for label in sec.labels if label in ctx.nodes]
            surviving_names = {_lean_name(label) for label in surviving}
            parsed.decls = [
                decl for decl in parsed.decls if decl.name in surviving_names
            ]
            invalidated |= set(sec.labels) & descendants
            sec.labels = surviving
            if sec.refined_labels is None:
                sec.refined_labels = set()
            else:
                sec.refined_labels &= set(surviving) - descendants
            sec.deferred = False
            _write_section(sec, parsed)
            _discard_section_objects(sec.path)
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
                _discard_section_artifacts(sec.path)
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
                _discard_section_artifacts(sec.path)
                continue
            prefix_names = {_lean_name(label) for label in prefix}
            parsed.decls = [
                decl for decl in parsed.decls if decl.name in prefix_names
            ]
            sec.labels = prefix
            if sec.refined_labels is not None:
                sec.refined_labels &= set(prefix)
            _write_section(sec, parsed)
            ok, _output = _check_lean(sec.path, lean_command)
            if ok and _compile_module_olean(sec.path, lean_command).ok:
                sec.deferred = False
                kept.append(sec)
            else:
                invalidated |= set(prefix)
                _discard_section_artifacts(sec.path)
            continue
        sec.deferred = True
        invalidated |= set(sec.labels)
        _discard_section_objects(sec.path)
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
                _discard_section_artifacts(sec.path)
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
                _discard_section_artifacts(sec.path)
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
            _discard_section_artifacts(sec.path)
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
    draft_content = ctx.content_path.relative_to(REPO_ROOT)
    draft_dir = ctx.blueprint_dir.relative_to(REPO_ROOT)
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

The unpublished blueprint draft lives at `{draft_content}`;
read it from disk as needed (locate the failing nodes via their `\\label{{...}}`
anchors) and edit it in place. Everything you must know about the failing
nodes is already excerpted below — do not re-read the whole file into context.

Rules:
- Edit only `{draft_content}`. Do not edit the canonical blueprint under
  `blueprints/{ctx.name}/`; it is published only after the entire run succeeds.
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
- After editing, run `python scripts/validate_blueprint.py {ctx.name} --blueprint-dir {draft_dir}`.

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
    draft_content = ctx.content_path.relative_to(REPO_ROOT)
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
  "content_tex": "full replacement for the unpublished draft {draft_content}",
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


def _insert_statement_dependencies(
    text: str, label: str, dependencies: Iterable[str]
) -> tuple[str, set[str]]:
    """Add direct ``\\uses`` edges to one node without changing its prose.

    This is intentionally a narrow TeX transformation. The caller validates
    the complete draft and rolls it back unless every requested edge is parsed
    as a statement dependency.
    """
    requested = set(dict.fromkeys(str(dep).strip() for dep in dependencies))
    requested.discard("")
    marker = rf"\label{{{label}}}"
    label_pos = text.find(marker)
    if label_pos < 0 or not requested:
        return text, set()
    begin = text.rfind(r"\begin{", 0, label_pos)
    end = text.find(r"\end{", label_pos)
    if begin < 0 or end < 0:
        return text, set()
    block = text[begin:end]
    uses_match = re.search(r"\\uses\s*\{([^{}]*)\}", block)
    if uses_match is not None:
        existing = {
            item.strip()
            for item in uses_match.group(1).split(",")
            if item.strip()
        }
        added = requested - existing
        if not added:
            return text, set()
        replacement = r"\uses{" + ", ".join(sorted(existing | added)) + "}"
        absolute_start = begin + uses_match.start()
        absolute_end = begin + uses_match.end()
        return text[:absolute_start] + replacement + text[absolute_end:], added

    line_start = text.rfind("\n", 0, label_pos) + 1
    indent = re.match(r"[ \t]*", text[line_start:label_pos]).group(0)
    marker_end = label_pos + len(marker)
    insertion = "\n" + indent + r"\uses{" + ", ".join(sorted(requested)) + "}"
    return text[:marker_end] + insertion + text[marker_end:], requested


def _dependency_path(
    nodes: dict[str, Node], start: str, target: str
) -> list[str] | None:
    """Return one existing dependency path from ``start`` to ``target``."""
    if start == target:
        return [start]
    queue: list[tuple[str, list[str]]] = [(start, [start])]
    seen = {start}
    index = 0
    while index < len(queue):
        current, path = queue[index]
        index += 1
        node = nodes.get(current)
        if node is None:
            continue
        for dependency in sorted(node.uses):
            if dependency == target:
                return [*path, dependency]
            if dependency in nodes and dependency not in seen:
                seen.add(dependency)
                queue.append((dependency, [*path, dependency]))
    return None


def _cyclic_dependency_repair_findings(
    nodes: dict[str, Node], required_dependencies: dict[str, set[str]]
) -> dict[str, dict[str, str]]:
    """Describe proposed edges that would close a dependency cycle."""
    findings: dict[str, dict[str, str]] = {}
    for label, dependencies in required_dependencies.items():
        if label not in nodes:
            continue
        for dependency in dependencies:
            if dependency not in nodes:
                continue
            path = _dependency_path(nodes, dependency, label)
            if path is None:
                continue
            findings.setdefault(label, {})[dependency] = (
                f"reject `{label} -> {dependency}`: existing dependency path "
                + " -> ".join(path)
                + f" would close the cycle back to {dependency}"
            )
    return findings


def _mark_repair_boundary_pending(
    ctx: Ctx,
    changed: Iterable[str],
    previous_nodes: dict[str, Node],
) -> set[str]:
    """Persist statement-level blueprint mutations that need an early audit.

    Full contract fingerprints also change for proof-prose edits. Those edits
    still invalidate/recheck Lean normally, but they do not need this extra
    pre-generation call because the public statement and statement-scoped
    dependency contract are unchanged.
    """
    before_statements = _statement_blocks(previous_nodes)
    before_fps = _statement_fingerprints(previous_nodes)
    labels = {
        label
        for label in changed
        if label in ctx.nodes
        and before_fps.get(label) != ctx.stmt_fps.get(label)
    }
    if not labels:
        return set()
    ordered = sorted(
        labels,
        key=lambda label: (ctx.nodes[label].file, ctx.nodes[label].line, label),
    )
    ctx.repair_boundary_pending = {
        "mode": "audit",
        "labels": ordered,
        "statement_fps": {label: ctx.stmt_fps[label] for label in ordered},
        "previous_statements": {
            label: before_statements.get(label, "") for label in ordered
        },
        "evidence": "",
        "repair_labels": [],
        "required_dependencies": {},
        "decomposition_helpers": [],
    }
    _record(
        ctx.telemetry,
        "post_repair_boundary_queued",
        labels=ordered,
        count=len(ordered),
    )
    return set(ordered)


def _post_repair_boundary_prompt(ctx: Ctx, labels: list[str]) -> str:
    """Build the one scoped blueprint-only audit used after a repair."""
    pending = ctx.repair_boundary_pending
    previous = pending.get("previous_statements") or {}
    changed_blocks = []
    for label in labels:
        node = ctx.nodes[label]
        changed_blocks.append(
            f"## {label} ({node.kind})\n"
            f"Previous public statement:\n```tex\n{str(previous.get(label) or '(new node)')[:6000]}\n```\n"
            f"Repaired public statement:\n```tex\n{ctx.stmt_blocks.get(label, '')[:6000]}\n```\n"
            f"Current statement dependencies: "
            f"{', '.join(sorted(_statement_uses(node))) or '(none)'}"
        )
    target_set = set(labels)
    nearby = target_set | {
        dependency
        for label in labels
        for dependency in ctx.nodes[label].uses
        if dependency in ctx.nodes
    }
    nearby |= {
        label
        for label, node in ctx.nodes.items()
        if node.uses & target_set
    }
    boundary = "\n".join(
        f"- {label} ({ctx.nodes[label].kind}): statement uses "
        f"{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or '(none)'}"
        for label in sorted(nearby)
    )
    paper = _paper_excerpt_for(ctx, labels, budget=12000)
    return f"""TASK: AUDIT-MODEL-BLUEPRINT-REPAIR-BOUNDARY

A model just edited the public statements below. Before spending Lean
generation and compilation calls, check only whether the repaired component is
self-consistent and has the statement-scoped dependencies required to state
what it now claims.

This is NOT a Lean audit and NOT a proof audit. Do not reject stylistic proof
changes, request implementation details, or demand that proof-only lemmas occur
in public statements. The blueprint remains the source of truth.

Return exactly one JSON object:
{{
  "accepted": true,
  "issues": [
    {{
      "node": "existing blueprint label",
      "severity": "reject",
      "classification": "missing_statement_dependency | blueprint_contract_defect | needs_decomposition",
      "reason": "specific mathematical defect in the repaired statement",
      "required_dependencies": ["existing label needed by the public statement"],
      "missing_helpers": ["helper statement needed to express the claim"]
    }}
  ]
}}

Rules:
- Accept when the repaired statement is complete as written.
- Use `missing_statement_dependency` only when an existing blueprint node is
  semantically required by the repaired PUBLIC statement and its direct
  statement `\\uses` edge is absent.
- Do not request a dependency merely because its theorem is useful in a proof.
- Use `blueprint_contract_defect` only for concrete missing or contradictory
  mathematical content introduced or left unresolved by the repair.
- Use `needs_decomposition` only when the repaired public claim still bundles
  genuinely separate statement-level obligations that require explicit
  blueprint helper nodes.
- Never suggest weakening, deleting, or replacing a claim with a placeholder.
- Every issue must name one of the changed labels. Every required dependency
  must be an existing label from the label inventory.

Changed statements:
{chr(10).join(changed_blocks)}

Immediate dependency/consumer boundary:
{boundary}

Existing label inventory:
{chr(10).join(f'- {label} ({node.kind})' for label, node in sorted(ctx.nodes.items()))}

Relevant paper excerpt:
<paper>
{paper}
</paper>
"""


def _audit_post_repair_boundary(
    ctx: Ctx, labels: list[str]
) -> RepairBoundaryAuditOutcome:
    """Audit one repaired component once; failures fall back to later gates."""
    prompt = _post_repair_boundary_prompt(ctx, labels)
    result = _call_model(
        ctx,
        prompt,
        purpose="post_repair_blueprint_audit",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=labels,
        tag="repair-boundary",
    )
    if result.status != "ok":
        _record(
            ctx.telemetry,
            "post_repair_boundary_audit",
            labels=labels,
            status="unavailable",
            reason=result.error,
        )
        return RepairBoundaryAuditOutcome("unavailable", result.error)
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        _record(
            ctx.telemetry,
            "post_repair_boundary_audit",
            labels=labels,
            status="unavailable",
            reason=str(exc),
        )
        return RepairBoundaryAuditOutcome("unavailable", str(exc))

    issues = [item for item in payload.get("issues") or [] if isinstance(item, dict)]
    rejected_issues = [
        item
        for item in issues
        if str(item.get("severity") or "reject").lower() == "reject"
    ]
    if bool(payload.get("accepted")) and not rejected_issues:
        _record(
            ctx.telemetry,
            "post_repair_boundary_audit",
            labels=labels,
            status="accepted",
            issue_count=0,
        )
        return RepairBoundaryAuditOutcome("accepted")

    label_set = set(labels)
    required: dict[str, set[str]] = {}
    repair_labels: set[str] = set()
    helpers: list[str] = []
    formatted: list[str] = []
    for issue in rejected_issues:
        label = str(issue.get("node") or "")
        if label not in label_set:
            continue
        classification = str(issue.get("classification") or "")
        reason = str(issue.get("reason") or "unspecified repair defect").strip()
        formatted.append(f"{label} [{classification or 'unclassified'}]: {reason}")
        dependencies = {
            str(dep).strip()
            for dep in issue.get("required_dependencies") or []
            if str(dep).strip() in ctx.nodes and str(dep).strip() != label
        }
        if dependencies:
            required.setdefault(label, set()).update(dependencies)
        if classification != "missing_statement_dependency" or not dependencies:
            repair_labels.add(label)
        if classification == "needs_decomposition":
            helpers.extend(
                str(item).strip()
                for item in issue.get("missing_helpers") or []
                if str(item).strip()
            )
    if not formatted:
        repair_labels = set(labels)
        formatted = [
            "The repair-boundary critic rejected the component without usable "
            "per-node routing evidence. Recheck the changed public statements."
        ]
    evidence = "Post-repair blueprint boundary audit rejected:\n- " + "\n- ".join(formatted)
    _record(
        ctx.telemetry,
        "post_repair_boundary_audit",
        labels=labels,
        status="repair_required",
        repair_labels=sorted(repair_labels),
        required_dependencies={
            label: sorted(dependencies)
            for label, dependencies in required.items()
        },
        decomposition_helpers=list(dict.fromkeys(helpers)),
        issue_count=len(formatted),
    )
    return RepairBoundaryAuditOutcome(
        "repair",
        evidence,
        tuple(sorted(repair_labels)),
        required,
        tuple(dict.fromkeys(helpers)),
    )


def _pending_repair_boundary_request(ctx: Ctx) -> RepairRequest | None:
    """Resume or perform the persisted post-repair boundary transaction."""
    pending = ctx.repair_boundary_pending
    if not pending:
        return None
    labels = [
        label
        for label in pending.get("labels") or []
        if label in ctx.nodes
        and (pending.get("statement_fps") or {}).get(label) == ctx.stmt_fps.get(label)
    ]
    if not labels:
        ctx.repair_boundary_pending = {}
        return None
    if str(pending.get("mode") or "audit") == "repair":
        return RepairRequest(
            str(pending.get("evidence") or "Post-repair boundary audit rejected."),
            list(pending.get("repair_labels") or labels),
            decomposition_helpers=list(pending.get("decomposition_helpers") or []),
            authorizes_blueprint_repair=True,
            required_dependencies={
                label: set(dependencies)
                for label, dependencies in (
                    pending.get("required_dependencies") or {}
                ).items()
            },
            model_repair_labels=list(pending.get("repair_labels") or []),
        )

    _log(
        "==> Auditing repaired blueprint component before Lean generation: "
        + ", ".join(labels[:8])
    )
    outcome = _audit_post_repair_boundary(ctx, labels)
    if outcome.status in {"accepted", "unavailable"}:
        ctx.repair_boundary_pending = {}
        if outcome.status == "unavailable":
            _log(
                "  repair-boundary audit unavailable; continuing to the existing "
                "mandatory Lean statement-alignment gate"
            )
        else:
            _log("  repaired blueprint component passed its scoped boundary audit")
        return None
    ctx.repair_boundary_pending = {
        **pending,
        "mode": "repair",
        "evidence": outcome.evidence,
        "repair_labels": list(outcome.repair_labels),
        "required_dependencies": {
            label: set(dependencies)
            for label, dependencies in outcome.required_dependencies.items()
        },
        "decomposition_helpers": list(outcome.decomposition_helpers),
    }
    return _pending_repair_boundary_request(ctx)


def _apply_required_dependency_edges(
    ctx: Ctx, required_dependencies: dict[str, set[str]]
) -> set[str]:
    """Transactionally add critic-and-Lean-confirmed statement graph edges."""
    normalized = {
        label: {
            dep
            for dep in dependencies
            if label in ctx.nodes and dep in ctx.nodes
        }
        for label, dependencies in required_dependencies.items()
    }
    normalized = {label: deps for label, deps in normalized.items() if deps}
    cycle_findings = _cyclic_dependency_repair_findings(ctx.nodes, normalized)
    ctx.last_dependency_edge_rejections = cycle_findings
    if cycle_findings:
        for label, rejected in cycle_findings.items():
            normalized[label].difference_update(rejected)
        normalized = {label: deps for label, deps in normalized.items() if deps}
        messages = [
            message
            for rejected in cycle_findings.values()
            for message in rejected.values()
        ]
        _log(
            "==> Rejected cyclic blueprint dependency repair(s):\n  - "
            + "\n  - ".join(messages)
        )
        _record(
            ctx.telemetry,
            "blueprint_dependency_edge_repair",
            labels=sorted(cycle_findings),
            status="cycle_rejected",
            rejected_dependencies={
                label: dict(rejected)
                for label, rejected in cycle_findings.items()
            },
        )
    if not normalized:
        return set()

    paths = {ctx.nodes[label].file for label in normalized}
    before = {path: path.read_text(encoding="utf-8") for path in paths}
    added_by_label: dict[str, set[str]] = {}
    try:
        for label, dependencies in normalized.items():
            path = ctx.nodes[label].file
            current = path.read_text(encoding="utf-8")
            updated, added = _insert_statement_dependencies(
                current, label, dependencies
            )
            if added:
                path.write_text(updated, encoding="utf-8")
                added_by_label[label] = added

        validation = _validate_draft(ctx)
        if not validation.ok:
            raise ValueError("dependency-edge edit made the blueprint invalid")
        for label, dependencies in added_by_label.items():
            parsed = validation.nodes.get(label)
            if parsed is None or not dependencies <= set(parsed.statement_uses):
                raise ValueError(
                    f"validator did not parse required dependency edges for {label}"
                )
        ctx.refresh_nodes(validation.nodes)
    except (OSError, ValueError):
        for path, text in before.items():
            path.write_text(text, encoding="utf-8")
        restored = _validate_draft(ctx)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        _record(
            ctx.telemetry,
            "blueprint_dependency_edge_repair",
            labels=sorted(normalized),
            status="rolled_back",
            required_dependencies={
                label: sorted(dependencies)
                for label, dependencies in normalized.items()
            },
        )
        return set()

    changed = set(added_by_label)
    _record(
        ctx.telemetry,
        "blueprint_dependency_edge_repair",
        labels=sorted(changed),
        status="applied",
        required_dependencies={
            label: sorted(dependencies)
            for label, dependencies in added_by_label.items()
        },
    )
    if changed:
        _log(
            "==> Deterministic blueprint dependency repair: "
            + "; ".join(
                f"{label} -> {', '.join(sorted(added_by_label[label]))}"
                for label in sorted(changed)
            )
        )
    return changed


def _repair_blueprint(
    ctx: Ctx,
    evidence: str,
    labels: list[str],
    *,
    trial: int,
    max_trials: int,
    escalation_note: str,
    repair_runner_agent: bool,
    decomposition_roots: Iterable[str] = (),
) -> set[str]:
    """Run one transactional blueprint-repair attempt.

    Agent runners can edit ``content.tex`` before timing out. Every unsuccessful
    call therefore restores the exact pre-call source. The caller treats an
    empty result as a consumed no-op repair and continues until the configured
    repair budget is exhausted.
    """
    content_path = ctx.content_path
    before_content = content_path.read_text(encoding="utf-8")
    before_nodes = dict(ctx.nodes)
    blueprint_source = _read_draft_blueprint_source(ctx)
    before_fps = dict(ctx.contract_fps)
    ctx.last_blueprint_repair_rejection = ""
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
            transport_error=is_transient_error(exc),
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
        if is_environment_error(exc) or is_transient_error(exc):
            raise
        return set()
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        duration = time.monotonic() - started
        status = _runner_failure_status(exc)
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
            transport_error=status == "transport_exhausted",
        )
        # A CLI agent may have written a partial repair before the process
        # timed out. Never let a failed call mutate the next attempt's input.
        content_path.write_text(before_content, encoding="utf-8")
        restored = _validate_draft(ctx)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        if is_environment_error(exc) or status == "transport_exhausted":
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
                decomposition_roots=decomposition_roots,
            )
            right = _repair_blueprint(
                ctx,
                evidence,
                labels[mid:],
                trial=trial,
                max_trials=max_trials,
                escalation_note=escalation_note,
                repair_runner_agent=repair_runner_agent,
                decomposition_roots=decomposition_roots,
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
            _write_api_refinement_to(content_path, result.text)
        validation = _validate_draft(ctx)
        if not validation.ok:
            print_result(validation)
            raise ValueError("blueprint repair produced an invalid blueprint")
        orientation_findings = _decomposition_orientation_findings(
            before_nodes, validation.nodes, decomposition_roots
        )
        if orientation_findings:
            raise ValueError(
                "blueprint decomposition put helper nodes in the wrong graph "
                "direction:\n- " + "\n- ".join(orientation_findings)
            )
    except (OSError, ValueError) as exc:
        ctx.last_blueprint_repair_rejection = str(exc)
        content_path.write_text(before_content, encoding="utf-8")
        restored = _validate_draft(ctx)
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


def _stuck_state_for(
    states: list[SectionStuckState], section_labels: list[str]
) -> SectionStuckState:
    """Return retry state for one exact editable repair scope.

    Partially overlapping failure sets are not interchangeable: merging them
    can authorize normalization of siblings that have not exhausted their own
    retry lifecycle. Related nodes may still be supplied as read-only prompt
    context, but edit authority remains tied to this exact label set.
    """
    current = set(section_labels)
    for state in states:
        if state.labels == current:
            return state
    state = SectionStuckState(labels=current)
    states.append(state)
    return state


def _section_normalization_prompt(
    ctx: Ctx,
    blueprint_source: str,
    section_labels: list[str],
    context_labels: list[str],
    evidence: str,
    *,
    model_timeout_s: int,
    api_mode: bool,
) -> str:
    draft_content = ctx.content_path.relative_to(REPO_ROOT)
    draft_dir = ctx.blueprint_dir.relative_to(REPO_ROOT)
    blocks = _node_tex_blocks(ctx.nodes)
    section_nodes = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; uses "
        f"{', '.join(sorted(ctx.nodes[label].uses)) or 'none'})\n"
        f"```tex\n{blocks.get(label, '')[:5000]}\n```"
        for label in section_labels
        if label in ctx.nodes
    )
    context_only = [
        label for label in context_labels
        if label not in set(section_labels) and label in ctx.nodes
    ]
    context_nodes = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; read-only context)\n"
        f"```tex\n{blocks.get(label, '')[:3000]}\n```"
        for label in context_only
    )
    context_block = (
        "\nRelated rejected nodes supplied as read-only context; do not edit "
        "them:\n" + context_nodes + "\n"
        if context_nodes
        else ""
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
The unpublished blueprint draft lives at `{draft_content}`;
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
- Edit only `{draft_content}`. Do not edit the canonical blueprint.
- Do not weaken, delete, or replace claims with placeholders.
- Preserve existing labels unless a node must be split.
- If splitting is necessary, insert helper nodes immediately before the node
  that uses them and add explicit `\\uses{{...}}` edges.
- Do not touch unrelated downstream sections.
- Do not rewrite the whole blueprint.
- Keep changes small: target the listed section plus direct helper nodes only.
- After editing, run `python scripts/validate_blueprint.py {ctx.name} --blueprint-dir {draft_dir}`.
- This call has a wall-clock budget of about {model_timeout_s}s.

{_HARNESS_CONVENTIONS_NOTE}

The recurring evidence is:
```text
{evidence[-12000:]}
```

Section nodes to normalize:
{section_nodes}

{context_block}

{paper_block}
{source_block}
"""
    if not api_mode:
        return base
    return f"""{base}

API MODE: Return exactly one JSON object:
{{
  "content_tex": "full replacement for the unpublished draft {draft_content}",
  "notes": "short explanation of the small section-normalization changes"
}}

Do not include `\\begin{{document}}` or `\\end{{document}}`.
"""


def _normalize_stuck_section(
    ctx: Ctx,
    evidence: str,
    section_labels: list[str],
    *,
    context_labels: list[str] | None = None,
    trial: int,
    max_trials: int,
    repair_runner_agent: bool,
) -> set[str]:
    """One constrained normalization pass for a repeatedly failing section.

    Rolls back if the model invalidates the blueprint or edits too broadly.
    """
    content_path = ctx.content_path
    before_content = content_path.read_text(encoding="utf-8")
    blueprint_source = _read_draft_blueprint_source(ctx)
    before_fps = dict(ctx.contract_fps)
    _log(
        f"==> Section normalization {trial}/{max_trials} for: "
        + ", ".join(section_labels[:8])
    )
    prompt = _section_normalization_prompt(
        ctx,
        blueprint_source,
        section_labels,
        context_labels or section_labels,
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
        if is_environment_error(exc) or is_transient_error(exc):
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
            status=_runner_failure_status(exc),
            duration_s=time.monotonic() - started,
            timeout_s=ctx.hard_timeout,
            backend=runner.backend_name,
            model=runner.model,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
            transport_error=_runner_failure_status(exc) == "transport_exhausted",
        )
        content_path.write_text(before_content, encoding="utf-8")
        restored = _validate_draft(ctx)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        if is_environment_error(exc) or _runner_failure_status(exc) == "transport_exhausted":
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
            _write_api_refinement_to(content_path, result.text)
        validation = _validate_draft(ctx)
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
        validation = _validate_draft(ctx)
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
        validation = _validate_draft(ctx)
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
    root_first_layers = _top_down_proof_layers(nodes)
    scheduled_layers = (
        root_first_layers
        if proof_order == "top-down"
        else list(reversed(root_first_layers))
    )
    proof_depth = {
        label: depth
        for depth, labels in enumerate(root_first_layers)
        for label in labels
    }
    traversal_depth = {
        label: depth
        for depth, labels in enumerate(scheduled_layers)
        for label in labels
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
        layers=scheduled_layers,
        roots=root_first_layers[0] if root_first_layers else [],
        immediate_theorem_dependencies=immediate_theorem_deps,
    )
    node_blocks = _node_tex_blocks(nodes)
    targets = nodes if focus_labels is None else {
        label: node for label, node in nodes.items() if label in focus_labels
    }
    roots = set(root_first_layers[0]) if root_first_layers else set()
    for label, node in targets.items():
        telemetry.record(
            "node_features",
            **node_structural_features(
                label, node.kind, node_blocks.get(label, ""), len(node.uses)
            ),
            proof_depth=proof_depth.get(label),
            traversal_depth=traversal_depth.get(label),
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


def _phase2_body_progress(
    ctx: Ctx, sections: list[Section]
) -> tuple[set[str], set[str]]:
    """Return ``(implemented, required)`` body labels among frozen contracts.

    Phase 1 freezes structures, inductives, classes, theorem statements, and
    typed definitions. Only declaration kinds with replaceable bodies belong
    to Phase 2; interface-only declarations are already complete in Phase 1.
    """
    frozen = _frozen_labels(sections)
    required: set[str] = set()
    implemented: set[str] = set()
    body_kinds = {"theorem", "lemma", "def", "abbrev", "instance"}
    for sec in sections:
        if sec.deferred:
            continue
        try:
            parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        except OSError:
            continue
        by_name = {decl.name: decl for decl in parsed.decls if decl.name}
        for label in set(sec.labels) & frozen:
            if label not in ctx.nodes or ctx.nodes[label].mathlibok:
                continue
            decl = by_name.get(_lean_name(label))
            if decl is None or decl.kind not in body_kinds:
                continue
            required.add(label)
            if not _has_terminal_sorry(decl.text):
                implemented.add(label)
    return implemented, required


def _print_pipeline_progress(
    ctx: Ctx, sections: list[Section], repair_trials: int, max_trials: int
) -> None:
    phase1_required = {
        label for label, node in ctx.nodes.items() if not node.mathlibok
    }
    phase1_frozen = _frozen_labels(sections) & phase1_required
    phase2_implemented, phase2_required = _phase2_body_progress(ctx, sections)
    verified = _verified_node_labels(ctx, sections)
    print(
        f"==> Progress: Phase 1 contracts {len(phase1_frozen)}/{len(phase1_required)} frozen; "
        f"Phase 2 Lean implementations {len(phase2_implemented)}/{len(phase2_required)} complete; "
        f"overall {len(verified)}/{len(ctx.nodes)} verified; "
        f"repairs {repair_trials}/{max_trials}",
        flush=True,
    )
    _record(
        ctx.telemetry,
        "pipeline_progress",
        phase1_frozen_labels=sorted(phase1_frozen),
        phase1_frozen_count=len(phase1_frozen),
        phase1_required_count=len(phase1_required),
        phase2_implemented_labels=sorted(phase2_implemented),
        phase2_implemented_count=len(phase2_implemented),
        phase2_required_count=len(phase2_required),
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
    parser.add_argument("--max-trials", type=int, default=100, help="Blueprint-repair budget")
    parser.add_argument("--timeout", type=int, default=300, help="Base per-model-call timeout (s)")
    parser.add_argument("--hard-timeout", type=int, default=600, help="Escalated per-call timeout (s)")
    parser.add_argument("--section-size", type=int, default=DEFAULT_SECTION_SIZE)
    parser.add_argument("--proof-batch-size", type=int, default=DEFAULT_PROOF_BATCH)
    parser.add_argument(
        "--workers",
        type=int,
        default=DEFAULT_WORKERS,
        help=(
            "Parallel Phase-2 body workers and bottom-up Phase-1 independent "
            "group/fragment workers"
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
        proof_order=PHASE2_PROOF_ORDER,
        phase1_order=PHASE1_STATEMENT_ORDER,
        phase2_order=PHASE2_PROOF_ORDER,
        phase1_validation_order="validated-contract_compile_final-audit",
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

    prior_draft = _draft_blueprint_dir(args.name)
    draft_was_resumed = bool(
        args.continue_run
        and (prior_draft / "blueprint" / "src" / "content.tex").is_file()
    )
    discarded_prior_draft = bool(not args.continue_run and prior_draft.exists())
    blueprint_dir = _prepare_blueprint_draft(
        args.name, continue_run=args.continue_run
    )
    draft_content_path = blueprint_dir / "blueprint" / "src" / "content.tex"
    telemetry.record(
        "blueprint_draft_ready",
        mode="resumed" if draft_was_resumed else "created_from_published",
        discarded_prior_draft=discarded_prior_draft,
        draft=str(draft_content_path.relative_to(REPO_ROOT)),
        draft_sha256=hashlib.sha256(draft_content_path.read_bytes()).hexdigest(),
    )
    validation = validate_blueprint(
        REPO_ROOT, args.name, blueprint_dir=blueprint_dir
    )
    print_result(validation)
    if not validation.ok:
        return finish(1, "blueprint_validation_failed")
    _record_proof_graph_telemetry(
        telemetry,
        validation.nodes,
        proof_order=PHASE2_PROOF_ORDER,
        reason="initial",
    )

    blueprint_source = _read_blueprint_source_at(args.name, blueprint_dir)
    print("==> Searching local Lean libraries once for this run", flush=True)
    library_context, library_candidates = _search_local_lean_libraries(
        args.name, validation.nodes, blueprint_source, term_runner=None
    )

    ctx = Ctx(
        name=args.name,
        blueprint_dir=blueprint_dir,
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
        workers=args.workers,
        use_ladder=args.ladder,
        refinement_order=PHASE1_STATEMENT_ORDER,
    )
    ctx.refresh_nodes(validation.nodes)

    generated_dir = _generated_module_dir(args.name)
    if not args.continue_run:
        # Fresh run: clear skeleton modules from previous runs (old ChunkNN
        # files from the legacy pipeline are cleared too; the two pipelines do
        # not share caches).
        if generated_dir.exists():
            shutil.rmtree(generated_dir)
        lake_generated_dir = _generated_lake_module_dir(args.name)
        if lake_generated_dir.exists():
            shutil.rmtree(lake_generated_dir)
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
        f"- Phase 1 statement order: `{PHASE1_STATEMENT_ORDER}`",
        f"- Phase 2 implementation order: `{PHASE2_PROOF_ORDER}`",
        f"- blueprint repair budget: `{args.max_trials}`",
        f"- library candidates: `{len(library_candidates)}`",
        "",
    ]

    repair_trials = 0
    noop_repairs = 0
    escalation_note = ""
    stuck_sections: list[SectionStuckState] = []
    started = time.monotonic()
    # A resumed state must prove that all individually refined contracts still
    # compile together before Phase 2 can use them. Keep this run-scoped so the
    # deterministic recheck is paid once per statement-state, not once per
    # proof frontier.
    phase1_integration_checked = False
    _print_pipeline_progress(ctx, sections, repair_trials, args.max_trials)
    try:
        while True:
            repair_boundary_active = bool(ctx.repair_boundary_pending)
            boundary_request = _pending_repair_boundary_request(ctx)
            if repair_boundary_active:
                # Persist both an accepted audit (cleared state) and a routed
                # rejection before any further model call can be interrupted.
                _save_ctx_state(ctx, sections)
            if boundary_request is None:
                sections, reactivated, dropped_cached = _reactivate_deferred_sections(
                    ctx, sections
                )
            else:
                reactivated, dropped_cached = set(), set()
            if reactivated or dropped_cached:
                phase1_integration_checked = False
                _save_ctx_state(ctx, sections)
            required_skeleton = {
                label for label, node in ctx.nodes.items() if not node.mathlibok
            }
            frozen = _frozen_labels(sections)
            if any(sec.deferred for sec in sections):
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
            repair_context_labels: list[str] = []
            repair_required_dependencies: dict[str, set[str]] = {}
            repair_model_labels: list[str] = []
            phase1_repair = False
            repair_authorized = True

            if boundary_request is not None:
                evidence_for_repair = boundary_request.evidence
                repair_labels = boundary_request.labels
                repair_authorized = True
                repair_required_dependencies = boundary_request.required_dependencies
                repair_model_labels = boundary_request.model_repair_labels
                repair_helpers = boundary_request.decomposition_helpers
                repair_section_labels = list(boundary_request.section_labels)
                repair_context_labels = list(boundary_request.context_labels)
                phase1_repair = True
                _quarantine_labels(
                    ctx, boundary_request.labels, "post_repair_boundary_audit"
                )

            if evidence_for_repair is None:
                phase1_pending = required_skeleton - _frozen_labels(sections)
                if phase1_pending:
                    print(
                        f"==> Phase 1: refining statements {PHASE1_STATEMENT_ORDER} for "
                        f"{len(phase1_pending)} node(s) "
                        f"({len(required_skeleton) - len(phase1_pending)} already frozen)",
                        flush=True,
                    )
                    try:
                        sections = _run_phase1(
                            ctx, sections, phase1_pending, PHASE1_STATEMENT_ORDER
                        )
                        integration_failures = _phase1_recompile_environment(
                            ctx, sections
                        )
                        phase1_integration_checked = not integration_failures
                        _save_ctx_state(ctx, sections)
                        _print_pipeline_progress(
                            ctx, sections, repair_trials, args.max_trials
                        )
                        if integration_failures:
                            continue
                    except RepairRequest as request:
                        evidence_for_repair = request.evidence
                        repair_labels = request.labels
                        repair_authorized = request.authorizes_blueprint_repair
                        repair_required_dependencies = request.required_dependencies
                        repair_model_labels = request.model_repair_labels
                        if _requires_blueprint_transaction(
                            repair_authorized,
                            repair_required_dependencies,
                        ):
                            _quarantine_labels(
                                ctx,
                                request.labels,
                                (
                                    "blueprint_repair_request"
                                    if repair_authorized
                                    else "statement_dependency_edge_request"
                                ),
                            )
                        else:
                            _apply_phase1_retry_scheduling(ctx, request)
                        repair_helpers = request.decomposition_helpers
                        # Defense in depth: no caller may widen an editable
                        # normalization scope beyond the labels whose evidence
                        # actually authorized blueprint repair.
                        authorized = set(request.labels)
                        repair_section_labels = sorted(
                            authorized & set(request.section_labels)
                        ) or sorted(authorized)
                        repair_context_labels = list(request.context_labels)
                        phase1_repair = True

                elif not phase1_integration_checked:
                    _log(
                        "==> Phase 1 integration gate: recompiling every refined "
                        "statement module in dependency order"
                    )
                    integration_failures = _phase1_recompile_environment(
                        ctx, sections
                    )
                    phase1_integration_checked = not integration_failures
                    _save_ctx_state(ctx, sections)
                    if integration_failures:
                        continue

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
                if all_unproved:
                    proof_layer, frontier_labels, proof_roots = (
                        _next_implementation_frontier(
                            ctx.nodes, all_unproved, PHASE2_PROOF_ORDER
                        )
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
                        f"{PHASE2_PROOF_ORDER} frontier {proof_layer} "
                        f"({len(frontier_labels)} node(s))"
                    )
                    print(
                        f"==> Phase 2: implementing deferred bodies for {mode_note} "
                        f"with {args.workers} worker(s)",
                        flush=True,
                    )
                    _record(
                        ctx.telemetry,
                        "proof_frontier_scheduled",
                        proof_order=PHASE2_PROOF_ORDER,
                        phase1_order=PHASE1_STATEMENT_ORDER,
                        layer=proof_layer,
                        labels=frontier_labels,
                        theorem_labels=[
                            label
                            for label in frontier_labels
                            if _is_theorem_like_kind(ctx.nodes[label].kind)
                        ],
                        definition_body_labels=[
                            label
                            for label in frontier_labels
                            if not _is_theorem_like_kind(ctx.nodes[label].kind)
                        ],
                        node_kinds={
                            label: ctx.nodes[label].kind
                            for label in frontier_labels
                        },
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
                            "Body implementation failed for the nodes below after batched "
                            "and escalated attempts. Repair the blueprint: add the missing "
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
                            proof_order=PHASE2_PROOF_ORDER,
                            phase1_order=PHASE1_STATEMENT_ORDER,
                            layer=proof_layer,
                            labels=frontier_labels,
                            proved_labels=proved_now,
                            remaining_after=len(remaining_after),
                            status="accepted",
                        )
                        if proof_layer == 0:
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
                        if remaining_after:
                            # The accepted frontier is cached against immutable
                            # statement contracts. Advance one graph layer in the
                            # selected direction before the completeness gate.
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
                        promoted = _promote_blueprint_draft(ctx)
                        published = _publish_lean_text(args.name, final_code)
                        report_lines += [
                            "## Complete",
                            f"- elapsed: `{int(time.monotonic() - started)}s`",
                            f"- blueprint repairs used: `{repair_trials}/{args.max_trials}`",
                            f"- published blueprint: `{promoted.relative_to(REPO_ROOT)}`",
                            f"- published Lean: `{published.relative_to(REPO_ROOT)}`",
                        ]
                        if args.build:
                            site_lean = _rebuild_site_for(args.name)
                            report_lines.append(f"- site Lean: `{site_lean.relative_to(REPO_ROOT)}`")
                        report = _write_report(args.name, report_lines)
                        print(f"All nodes formalized. Published {published.relative_to(REPO_ROOT)}")
                        print(f"Report written to {report.relative_to(REPO_ROOT)}")
                        shutil.rmtree(ctx.blueprint_dir, ignore_errors=True)
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

            if evidence_for_repair is not None and not _requires_blueprint_transaction(
                repair_authorized,
                repair_required_dependencies,
            ):
                if repair_trials >= args.max_trials:
                    report_lines += [
                        "## Stopped: Phase 1 generation retry budget exhausted",
                        "",
                        "```text",
                        evidence_for_repair[-6000:],
                        "```",
                    ]
                    report = _write_report(args.name, report_lines)
                    print(
                        "Stopped after the configured retry budget was exhausted "
                        "without obtaining valid Phase 1 Lean statements."
                    )
                    print(f"Report written to {report.relative_to(REPO_ROOT)}")
                    return finish(
                        1,
                        "max_trials_exhausted",
                        unresolved=repair_labels,
                    )
                repair_trials += 1
                _record(
                    ctx.telemetry,
                    "phase1_generation_retry",
                    labels=repair_labels,
                    trial=repair_trials,
                    max_trials=args.max_trials,
                    evidence=evidence_for_repair[-4000:],
                    blueprint_edited=False,
                )
                _log(
                    f"==> Phase 1 generation retry {repair_trials}/"
                    f"{args.max_trials}; blueprint unchanged; affected: "
                    + ", ".join(repair_labels[:8])
                )
                evidence_tail = "\n".join(evidence_for_repair.splitlines()[-12:])
                if evidence_tail:
                    _log("  retry evidence (last lines):\n" + evidence_tail)
                report_lines.append(
                    f"- Phase 1 generation retry {repair_trials} without "
                    f"blueprint edit: `{', '.join(repair_labels[:8])}`"
                )
                _store_generation_feedback(
                    ctx,
                    repair_labels,
                    evidence_for_repair,
                    source="outer_phase1_retry",
                )
                _save_ctx_state(ctx, sections)
                _print_pipeline_progress(
                    ctx, sections, repair_trials, args.max_trials
                )
                continue

            # --- blueprint repair path (the ONLY route that edits the unpublished draft)
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
                print(
                    "The unpublished blueprint draft, frozen statements, and "
                    "accepted proofs are kept; rerun with --continue."
                )
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
            content_path = ctx.content_path
            content_before_repair = content_path.read_text(encoding="utf-8")
            note = escalation_note
            if repair_helpers:
                note = _decomposition_note(
                    repair_model_labels or repair_labels, repair_helpers
                )
            action = (
                "compound-repair"
                if repair_required_dependencies and repair_model_labels
                else "dependency-edge-repair"
                if repair_required_dependencies
                else ("normalization" if use_section_normalization else "repair")
            )
            if repair_required_dependencies:
                _record(
                    ctx.telemetry,
                    "statement_dependency_edge_routed",
                    labels=sorted(repair_required_dependencies),
                    required_dependencies={
                        label: sorted(dependencies)
                        for label, dependencies in repair_required_dependencies.items()
                    },
                    remaining_blueprint_repair_authorized=repair_authorized,
                    model_repair_labels=repair_model_labels,
                    route=(
                        "compound-repair"
                        if repair_model_labels
                        else "dependency-edge-repair"
                    ),
                )
                dependency_changed = _apply_required_dependency_edges(
                    ctx, repair_required_dependencies
                )
                changed = set(dependency_changed)
                cycle_rejections = getattr(
                    ctx, "last_dependency_edge_rejections", {}
                )
                cycle_labels = list(cycle_rejections)
                cycle_evidence = "\n".join(
                    message
                    for rejected in cycle_rejections.values()
                    for message in rejected.values()
                )
                model_labels = list(
                    dict.fromkeys([*repair_model_labels, *cycle_labels])
                )
                if not dependency_changed and not cycle_rejections:
                    # A direct edge can be invalid, most notably when it would
                    # create a cycle. Include those labels in the model repair
                    # rather than replacing any concurrently requested
                    # decomposition/blueprint repair.
                    action = "repair"
                    model_labels = list(
                        dict.fromkeys([*model_labels, *repair_required_dependencies])
                    )
                if model_labels:
                    model_changed = _repair_blueprint(
                        ctx,
                        evidence_for_repair,
                        model_labels,
                        trial=repair_trials,
                        max_trials=args.max_trials,
                        escalation_note=(
                            (
                                "The proposed direct dependency edge was rejected "
                                "because it would create a cycle. Repair the "
                                "provider/helper direction without weakening any "
                                "claim. Do not request the rejected edge again.\n\n"
                                + cycle_evidence
                                + "\n\n"
                                + note
                            )
                            if cycle_rejections
                            else note
                            if dependency_changed
                            else (
                                "The semantic critic and corrected Lean agree that "
                                "the listed statement dependencies are required, "
                                "but adding the direct edge failed blueprint validation. "
                                "Repair the dependency structure without weakening claims.\n\n"
                                + note
                            )
                        ),
                        repair_runner_agent=(
                            escalation_runner.partition(":")[0]
                            in {"codex", "claude-code"}
                        ),
                        decomposition_roots=(
                            repair_model_labels or repair_labels
                            if repair_helpers
                            else ()
                        ),
                    )
                    changed.update(model_changed)
                report_lines.append(
                    f"- {action.replace('-', ' ')} {repair_trials}: {len(changed)} node "
                    f"contract(s) changed for `{', '.join(repair_labels[:8])}`"
                )
            elif use_section_normalization and stuck_state is not None:
                try:
                    changed = _normalize_stuck_section(
                        ctx,
                        evidence_for_repair,
                        repair_section_labels,
                        context_labels=repair_context_labels,
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
                        decomposition_roots=(repair_labels if repair_helpers else ()),
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
                    decomposition_roots=(repair_labels if repair_helpers else ()),
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
                    restored = _validate_draft(ctx)
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
                boundary_labels = _mark_repair_boundary_pending(
                    ctx, changed, nodes_before_repair
                )
                sections, invalidated = _invalidate_after_repair(
                    ctx,
                    sections,
                    changed,
                    lean_command,
                    previous_nodes=nodes_before_repair,
                )
                phase1_integration_checked = False
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
                    proof_order=PHASE2_PROOF_ORDER,
                    phase1_order=PHASE1_STATEMENT_ORDER,
                )
                _record_proof_graph_telemetry(
                    ctx.telemetry,
                    ctx.nodes,
                    proof_order=PHASE2_PROOF_ORDER,
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
                if boundary_labels:
                    print(
                        "  queued one scoped post-repair blueprint audit before "
                        "Lean generation for: "
                        + ", ".join(sorted(boundary_labels)[:8]),
                        flush=True,
                    )
            else:
                noop_repairs += 1
                repair_rejection = str(
                    getattr(ctx, "last_blueprint_repair_rejection", "") or ""
                )
                if disconnected_rollback:
                    print(
                        "  out-of-scope repair changes rolled back; "
                        "retrying with narrower scope",
                        flush=True,
                    )
                elif repair_rejection:
                    escalation_note = (
                        "The previous repair was rolled back by a deterministic "
                        "transaction guard. Correct this exact graph error without "
                        "weakening claims:\n\n" + repair_rejection
                    )
                    print(
                        "  invalid repair rolled back; exact graph evidence will "
                        "be supplied to the next attempt",
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
                if repair_boundary_active and ctx.repair_boundary_pending:
                    prior = str(
                        ctx.repair_boundary_pending.get("evidence") or ""
                    ).rstrip()
                    ctx.repair_boundary_pending["evidence"] = (
                        prior
                        + "\n\nThe preceding corrective repair was a no-op. "
                        "Materially correct the exact audited statement defect."
                    )[-12000:]
                    _save_ctx_state(ctx, sections)
                if not disconnected_rollback:
                    print("  repair was a no-op; escalating instructions", flush=True)
            _print_pipeline_progress(ctx, sections, repair_trials, args.max_trials)
    except RunnerError as exc:
        report_lines += ["## Stopped on runner error", "", "```text", str(exc)[-4000:], "```"]
        report = _write_report(args.name, report_lines)
        print(f"Runner error stopped the run: {exc}", flush=True)
        print(f"Report written to {report.relative_to(REPO_ROOT)}")
        print(
            "The unpublished blueprint draft and Lean state are saved; rerun "
            "with --continue once the environment is fixed."
        )
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
            old_sigterm = signal.getsignal(signal.SIGTERM)

            def log_sigterm(signum, _frame) -> None:
                print(
                    "received SIGTERM; "
                    f"pid={os.getpid()} ppid={os.getppid()} pgid={os.getpgrp()} "
                    f"active_stage={_active_stage()!r}; exiting {128 + signum}",
                    file=sys.stderr,
                    flush=True,
                )
                with contextlib.suppress(Exception):
                    log_file.flush()
                os._exit(128 + signum)

            signal.signal(signal.SIGTERM, log_sigterm)
            print(f"Log file: {log_path.relative_to(REPO_ROOT)}", flush=True)
            try:
                return main(argv)
            except (FileNotFoundError, RunnerError, subprocess.CalledProcessError) as exc:
                print(f"error: {exc}", file=sys.stderr)
                return 2
            finally:
                signal.signal(signal.SIGTERM, old_sigterm)
                print(f"Log file: {log_path.relative_to(REPO_ROOT)}", flush=True)


if __name__ == "__main__":
    raise SystemExit(logged_main())
