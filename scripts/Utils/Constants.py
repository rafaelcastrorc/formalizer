"""Pipeline policy constants, budgets, node-kind sets and predicates, and shared regexes.

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
OPEN_CONJECTURE_TARGET_KIND = "open-conjecture-proposition"


def _is_theorem_like_kind(kind: str | None) -> bool:
    return (
        bool(kind)
        and kind != OPEN_CONJECTURE_TARGET_KIND
        and kind not in DEFINITION_LIKE_KINDS
    )
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
PHASE1_EXCHANGE_SAMPLE_LIMIT = 3
# One declaration-local patch is allowed at each model tier. A second failure
# moves to the escalation tier or blueprint repair instead of looping inside
# the same anchored generation session.
TARGETED_DECL_PATCH_ROUNDS = 1
COMPILER_CORRECTION_ROUNDS = 3
# Translation candidates are disposable working files, not the final accepted
# aggregate.  A candidate that cannot elaborate within this wall-clock budget
# is too expensive to publish and should be corrected before the full final
# integration check.  The final checks retain ``LEAN_CHECK_TIMEOUT`` below.
CANDIDATE_LEAN_CHECK_TIMEOUT = 90
# ``lean -o`` is an acceptance gate, but it is also a usability test for the
# public interface.  Historical measurements showed ordinary generated
# modules finish in seconds, while one deeply dependent public statement took
# 500-600s and repeatedly timed out even when its proof was replaced by
# ``sorry``.  Waiting the old hard-coded 600s and calling the model to rewrite
# the proof cannot fix that class of failure.
OBJECT_COMPILE_USABILITY_TIMEOUT = 90
OBJECT_INTERFACE_FAILURE_PREFIX = "Lean public-interface usability gate failed"
OBJECT_IMPLEMENTATION_FAILURE_PREFIX = "Lean implementation object-generation gate failed"
# A complete-node correction starts from compiling/audited evidence and is a
# narrower task than generating a node from scratch.  Do not let the fallback
# inherit a very large hard-node timeout and recreate the historical 600-second
# full-regeneration loop.
PHASE2_COMPLETE_CORRECTION_TIMEOUT = 300

# Diagnostic facts have different validity boundaries.  Keeping all of them in
# one statement-scoped text field caused both historical failure modes: semantic
# requirements disappeared at unrelated transaction boundaries, while fixed
# compiler errors continued to contaminate replacement candidates.  The ledger
# below is the authority for diagnostic lifetime; candidate state, retry policy,
# and model-call history remain separate concerns.
DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION = 1
EVIDENCE_LIFETIMES = {"statement", "plan", "candidate", "transaction"}


def _requires_initial_declaration_pass(refinement_order: str) -> bool:
    """Only root-first elaboration needs unresolved lower names predeclared."""
    return refinement_order == "top-down"
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
PHASE1_SEMANTIC_CORRECTION_WAVE_MAX = 3
SECTION_NORMALIZATION_REPAIR_TRIGGER = 1
SECTION_NORMALIZATION_MAX_CHANGED = 16
SECTION_STUCK_MAX_REPAIRS_AFTER_NORMALIZATION = 2
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


_MODEL_WRAPPER_START_RE = re.compile(
    r"^\s*(?P<kind>namespace|section)(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?\s*$"
)
_MODEL_WRAPPER_END_RE = re.compile(
    r"^\s*end(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?\s*$"
)
_ALLOWED_MODEL_PREAMBLE_RE = re.compile(
    r"^\s*(?:open(?:\s+scoped)?\b.*|noncomputable\s+section)\s*$"
)


_MISSING_LEAN_SURFACE_RE = re.compile(
    r"\b(?:unknown identifier|unknown constant|unknown namespace)\b",
    re.IGNORECASE,
)


_MISSING_LEAN_NAME_RE = re.compile(
    r"\b(?:unknown identifier|unknown constant|unknown namespace)\b\s+"
    r"[`'\"]?([A-Za-z_][A-Za-z0-9_'.]*)",
    re.IGNORECASE,
)


_TEX_LABEL_RE = re.compile(r"\\label\s*\{([^{}]+)\}")


_SECTION_OBJECT_FINGERPRINT_PREFIX = "opaque-theorem-v2:"


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


PHASE1_DEPENDENCY_CONTEXT_BUDGET = 10000


_PLAN_ENTRY_PROGRESS_KEYS = ("semantic_revision_count",)


DESIGN_PLAN_SCHEMA_VERSION = 6
DESIGN_PLAN_CLOSURE_VERSION = 4
SEMANTIC_PLAN_SCHEMA_VERSION = 2
SEMANTIC_READINESS_VALUES = {"ready", "underspecified", "explicitly_unresolved"}

# Phase 1 may introduce only declaration-only type interfaces. Ordinary helper
# definitions and theorems would need bodies/proofs, but Phase 2 implements only
# blueprint targets; accepting them here either forces proof work into Phase 1
# or leaves an untracked ``sorry`` in the final module.
DESIGN_PLAN_HELPER_KINDS = {"structure", "inductive", "class"}


_PLAN_REVISION_FINDING_CATEGORIES = {
    "plan_contract_closure",
}


_UNKNOWN_LEAN_NAME_RE = re.compile(
    r"unknown\s+(?:constant|identifier|namespace)\s+[`']([^`']+)[`']",
    re.IGNORECASE,
)


_PAPER_EXCERPT_HEAD = 2000
_WORD_TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9_-]{3,}")


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
