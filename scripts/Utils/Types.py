"""Shared dataclasses and classes: parsed-module model, audit/plan verdicts, run context.

Part of formalize_blueprint.py — the statements-first Lean formalization
pipeline. This file is not an importable module: formalize_blueprint.py
compiles and executes every part file into its own module namespace, in a
fixed order, so the pipeline keeps the single `formalize_blueprint`
namespace that its tests and tooling patch and import against. Names used
here may therefore be defined in earlier parts or in
formalize_blueprint.py's import block. See organize.md.
"""
from __future__ import annotations
# ruff: noqa: F821


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
    failure_identities_by_label: dict[str, dict[str, Any]] = field(
        default_factory=dict
    )
    forbidden_dependencies: dict[str, set[str]] = field(default_factory=dict)
    # Structured, critic-certified representation changes that require an
    # explicit blueprint-owned interface before Lean generation can continue.
    # Keeping this separate from prose reasons lets Phase 1 route the defect
    # without provider-specific keyword matching.
    representation_repairs_by_label: dict[str, dict[str, Any]] = field(
        default_factory=dict
    )

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

    def failure_identity_for(self, label: str) -> dict[str, Any]:
        """Return objective audit facts used to recognize the same failure.

        Human-readable ``reason`` text remains the correction prompt.  This
        identity contains only the critic's structured fields, so harmless
        wording changes do not create a new retry epoch.
        """
        value = self.failure_identities_by_label.get(label)
        return copy.deepcopy(value) if isinstance(value, dict) else {}

    def representation_repair_labels(self, kind: str) -> set[str]:
        return {
            label
            for label, repair in self.representation_repairs_by_label.items()
            if str(repair.get("kind") or "") == kind
        }


@dataclass(frozen=True)
class RepairBoundaryAuditOutcome:
    """One scoped semantic check of a model-mutated blueprint component."""

    status: str  # accepted | repair | unavailable
    evidence: str = ""
    repair_labels: tuple[str, ...] = ()
    required_dependencies: dict[str, set[str]] = field(default_factory=dict)
    decomposition_helpers: tuple[str, ...] = ()
    provider_repair_labels: tuple[str, ...] = ()


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
    # The compact Phase-1 semantic planner can use either configured model
    # tier. This changes only that advisory call (including its hedge); normal
    # generation and repair routing keep their existing tier policies.
    planner_tier: str = "escalation"
    # ``record`` preserves conjectures as exact proposition definitions and
    # does not claim to prove them. ``attempt`` first requires the blueprint to
    # contain a proof, then asks Phase 2 to formalize that blueprint proof.
    conjecture_policy: str = "record"
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
    # Authoritative, typed diagnostic facts. ``generation_feedback`` above is
    # retained as a compatibility projection for old state/tests; prompt reads
    # and invalidation decisions use this ledger.
    diagnostic_evidence: dict[str, dict[str, Any]] = field(default_factory=dict)
    # A deterministic closure rejection proves that an actual generated Lean
    # statement referenced these blueprint nodes.  Keep that structured fact
    # across generation-plan epoch changes so a later independent statement
    # audit can certify the same edge without another model round-trip.  This
    # evidence never authorizes an edge by itself and is valid only for the
    # unchanged blueprint statement fingerprint.
    phase1_dependency_observations: dict[str, dict[str, Any]] = field(
        default_factory=dict
    )
    # Exact Phase-1 model exchanges survive outer retries and ``--continue``.
    # The ledger does not suppress distinct stochastic samples; it prevents a
    # byte-identical response to the same correction context from being paid
    # for, compiled, and audited again after a transaction boundary resets.
    phase1_exchange_history: dict[str, dict[str, Any]] = field(default_factory=dict)
    # Best-effort model conversation handles captured on timeout. These are
    # keyed by the exact model-call context, not just the label, so an outer
    # retry can resume useful work without carrying a stale session across a
    # changed statement/plan/prompt/model epoch. Backends without resume
    # support ignore the id safely.
    model_resume_sessions: dict[str, dict[str, Any]] = field(default_factory=dict)
    # Rejected Phase-1 declarations are retained as revision inputs instead of
    # being regenerated from an empty file. Entries are statement-fingerprinted
    # for the same reason as feedback: a blueprint edit must invalidate the old
    # Lean candidate automatically.
    generation_candidates: dict[str, dict[str, Any]] = field(default_factory=dict)
    # Complete Phase-2 declaration candidates survive outer retries and
    # ``--continue``.  This is deliberately separate from Phase-1 candidate
    # state: Phase 1 permits a terminal target ``sorry`` while every entry here
    # contains the statement and its real body as one atomic node.
    phase2_node_candidates: dict[str, dict[str, Any]] = field(
        default_factory=dict
    )
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
    # Parallel Phase-2 workers may independently prove that different
    # blueprint nodes need repair. Preserve each edit authorization as its own
    # transaction; unioning them gives one model accidental authority over a
    # large, unrelated part of the graph.
    phase2_repair_queue: list[dict[str, Any]] = field(default_factory=list)
    # Exactly one queued repair may own the mutable blueprint at a time. The
    # `verify` stage survives interruption and prevents later queued evidence
    # from editing the graph before this repair's complete Lean is accepted.
    phase2_repair_active: dict[str, Any] = field(default_factory=dict)
    # Local dependency-first exceptions to the normal top-down Phase-2 order.
    # These are created only from concrete evidence that a consumer must unfold
    # a still-deferred definition body. Once the prerequisites compile, normal
    # top-down scheduling resumes automatically.
    phase2_prerequisite_labels: set[str] = field(default_factory=set)
    # Phase 1 is a one-way workflow milestone. Once the complete initial
    # skeleton freezes, later blueprint edits belong to Phase 2 and are
    # formalized as complete statement+body declarations in one transaction.
    # They must never reopen Phase 1 or make its progress counter regress.
    phase2_started: bool = False
    phase1_baseline_labels: set[str] = field(default_factory=set)

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
        _prune_stale_diagnostic_evidence(self)
        _prune_stale_phase1_dependency_observations(self)
        _prune_stale_generation_candidates(self)
        _prune_stale_phase2_node_candidates(self)
        _prune_stale_retry_lifecycle(self)
        _prune_stale_design_plan(self)


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
    # Hash of the source, Lean environment, and imported generated interfaces
    # used for the most recent successful object build.
    compile_fingerprint: str = ""

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
    # The contract/strategy epoch that produced these exact declarations.
    # A concurrent failure may replace a plan or activate blueprint-direct
    # generation before this candidate is persisted.  In that case the old
    # code is useful evidence, but it must never be relabelled as a candidate
    # generated under the new strategy.
    plan_fps: dict[str, str] = field(default_factory=dict)


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
