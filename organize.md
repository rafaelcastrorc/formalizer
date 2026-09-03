# organize.md — `scripts/formalize_blueprint.py` organization study

> **Scope of this document.** This is a *proposal only*. Nothing has been changed. Every
> suggestion here is about where code lives and how it is grouped — never about what it
> does. The pipeline's documented design (transactional edits, evidence-scoped authority,
> deterministic gates, the statements-first two-phase traversal) is taken as intentional
> and is preserved exactly by every suggestion below.

## 1. The file as it stood (before the split — see section 5 for the implemented layout)

- **30,971 lines**, ~1.2 MB, **466 top-level definitions** (functions, classes, constants)
  plus ~48 methods, all in one module.
- Largest single definitions: `main` (~1,555 lines), `_freeze_section` (~1,334),
  `_load_state` (~829), `_save_state` (~759), `_freeze_section_from_code` (~617),
  `_store_generation_candidates` (~486).
- It imports **~45 underscore-private helpers from `refine_blueprint_with_lean.py`**
  (the legacy loop), which therefore doubles as a de facto shared library.
- It is imported *by* other code, including by private name:
  - `tests/` (6+ test files: `_call_model`, `_runner_failure_status`,
    `PHASE2_COMPLETE_CORRECTION_TIMEOUT`, and many more via `from formalize_blueprint import (...)`),
  - `scripts/diagnostics/benchmark_lean_candidate.py` (`_compose_module`, `_normalize_terminal_sorry`, `_parse_module`),
  - `tests/replay/replay_phase1_plans.py` (a multi-symbol import block).
- It is invoked as a script: `python scripts/formalize_blueprint.py <name> ...` — a path
  hard-coded in the README, and in `webui.py`'s subprocess commands *and* its permission
  allowlist (`"scripts/formalize_blueprint.py"`).

These four facts — its size, its private-import consumers, its legacy-module dependency,
and its hard-coded invocation path — are the constraints any reorganization must respect.

## 2. Function-by-function catalog, grouped by file

Every top-level definition with its purpose, grouped by the part file it now lives in.
Locations are `file:line` within `scripts/` as of the implemented split (section 5).
Files appear in the order the loader executes them (constants first, phase drivers and
repair later), with what remains in `formalize_blueprint.py` itself at the end. All of
these names still belong to the single `formalize_blueprint` module at runtime.

---

## 2.1 `scripts/Utils/Constants.py`

All pipeline policy constants, budgets, node-kind sets and predicates, prompt boilerplate, and shared regexes.

### `SCRIPTS_DIR` / `REPO_ROOT` / `SKILL_PATH` / `SCRATCH_DIR` (Utils/Constants.py) — constants
Filesystem anchors: the scripts dir, repo root, the paper-to-blueprint skill file, and
`.auto-blueprint/formalization` scratch directory where working state lives.

### `DEFINITION_LIKE_KINDS` (Utils/Constants.py:28) — constant
Set of blueprint node kinds (`definition`, `defn`, `construction`, `notation`,
`convention`, `setup`) whose Lean form is a definition with a real body; theorem-likeness
is computed by exclusion so arbitrary `\newtheorem` environments default to theorem-like.

### `OPEN_CONJECTURE_TARGET_KIND` (Utils/Constants.py:29) — constant
Sentinel kind `"open-conjecture-proposition"` excluded from theorem-like treatment (open
conjectures are not proof obligations).

### `_is_theorem_like_kind` (Utils/Constants.py:32) — function
True for any node kind that is neither definition-like nor the open-conjecture kind; the
single predicate deciding whether a node becomes a Lean theorem with a deferred proof
versus a definition.

### Traversal/batching knobs (Utils/Constants.py) — constants
`DEFAULT_SECTION_SIZE` (12), `DEFAULT_PROOF_BATCH` (12), `DEFAULT_WORKERS` (3),
`PHASE1_STATEMENT_ORDER` ("bottom-up"), `PHASE2_PROOF_ORDER` ("top-down") — default
section/batch sizes, parallelism, and fixed phase traversal directions.

### Retry/timeout budget constants (Utils/Constants.py) — constants
`SKELETON_GENERATION_ATTEMPTS` (2, one base + one escalated attempt per section),
`PHASE1_EXCHANGE_SAMPLE_LIMIT` (3), `TARGETED_DECL_PATCH_ROUNDS` (1),
`COMPILER_CORRECTION_ROUNDS` (3), `CANDIDATE_LEAN_CHECK_TIMEOUT` (90s),
`OBJECT_COMPILE_USABILITY_TIMEOUT` (90s), `OBJECT_INTERFACE_FAILURE_PREFIX` /
`OBJECT_IMPLEMENTATION_FAILURE_PREFIX` (error-message tags for the two object-compile
gates), `PHASE2_COMPLETE_CORRECTION_TIMEOUT` (300s cap for complete-node corrections).

### `DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION` / `EVIDENCE_LIFETIMES` (Utils/Constants.py) — constants
Version and allowed lifetime scopes (`statement`/`plan`/`candidate`/`transaction`) for the
diagnostic-evidence ledger that governs how long failure facts stay valid.

### `_requires_initial_declaration_pass` (Utils/Constants.py:86) — function
True only for `"top-down"` refinement order: root-first elaboration needs provisional
declarations of lower names to exist before Lean can resolve them.

### Skeleton/plan sizing constants (Utils/Constants.py) — constants
`BULK_SKELETON_MIN_NODES` (6), `BULK_SKELETON_CHUNK` (12), `DESIGN_PLAN_MAX_NODES` (120),
`TARGETED_DECL_PATCH_MAX_LABELS` (4), `PHASE1_SEMANTIC_CORRECTION_WAVE_MAX` (3),
`SECTION_NORMALIZATION_REPAIR_TRIGGER` (1), `SECTION_NORMALIZATION_MAX_CHANGED` (16),
`SECTION_STUCK_MAX_REPAIRS_AFTER_NORMALIZATION` (2), `PROOF_SINGLETON_RETRIES` (2),
`LEAN_CHECK_TIMEOUT` (900s final checks), `LADDER_HEARTBEATS` (400_000).

### `LADDER_IMPORTS` (Utils/Constants.py:117) — constant
The imports (`Mathlib.Tactic.Ring`, `Mathlib.Tactic.NormNum`, `Aesop`) the deterministic
tactic ladder may need; unavailable imports drop the corresponding tactic.

### Declaration/diagnostic regexes (Utils/Constants.py) — constants
`_DECL_START_RE` (matches a Lean declaration head with modifiers/attributes, capturing
kind and optional name), `_DECL_PREFIX_RE` (attribute/`set_option ... in`/docstring/comment
lines belonging to the following declaration), `_TERMINAL_SORRY_RE` (a declaration ending
in `:= sorry` / `:= by sorry`), `_LOC_RE` (parses `path.lean:line:col: error|warning`
diagnostics), `_FORBIDDEN_TOPLEVEL_RE` (top-level `variable`/`namespace`/`section`/`end`/
`example` commands the pipeline forbids).

### `_MODEL_WRAPPER_START_RE` / `_MODEL_WRAPPER_END_RE` / `_ALLOWED_MODEL_PREAMBLE_RE` (Utils/Constants.py) — constants
Regexes recognizing model-emitted `namespace`/`section` wrapper lines and their `end`s,
and the only preamble commands models may emit (`open`/`open scoped`,
`noncomputable section`).

### `_MISSING_LEAN_SURFACE_RE` (Utils/Constants.py:154) — constant (regex)
Matches "unknown identifier/constant/namespace" in Lean output — the error class where
importing more of Mathlib could actually help.

### `_MISSING_LEAN_NAME_RE` (Utils/Constants.py:160) — constant (regex)
Like `_MISSING_LEAN_SURFACE_RE` but additionally captures the unresolved Lean identifier
itself from the error message.

### `_TEX_LABEL_RE` (Utils/Constants.py:167) — module-level constant (compiled regex)
Regex matching `\label{...}` occurrences; used by the scoped-repair validator to enumerate labels inside replacement TeX chunks.

### `_SECTION_OBJECT_FINGERPRINT_PREFIX` (Utils/Constants.py:170) — constant
String `"opaque-theorem-v2:"` prefixed onto section compile fingerprints; distinguishes
the v2 fingerprint scheme (theorem proof bodies opaque) from legacy keys, driving
migration logic.

### `_TERMINAL_PROOF_RE` (Utils/Constants.py:176) — constant
Regex matching a terminal `:= by ...` / `:= sorry` body at the end of a declaration;
everything before it is the frozen public type that Phase 1 may defer.

### `_INTERFACE_DECL_CAP` (Utils/Constants.py:180) — constant
Per-declaration character cap (2400) for definition-kind interface text in digests, so one
huge body cannot evict whole modules from the digest budget.

### `FROZEN_INTERFACE_NOTE` (Utils/Constants.py:182) — constant
Prompt boilerplate telling models the frozen-interface listing is complete and
reference-only; the blueprint TeX remains the sole mathematical source of truth.

### `PHASE1_DEPENDENCY_CONTEXT_BUDGET` (Utils/Constants.py:197) — constant
Soft character budget (10000) for the Phase-1 dependency-interface context used in
batching decisions.

### `_PLAN_ENTRY_PROGRESS_KEYS` (Utils/Constants.py:200) — constant
Tuple of plan-entry counter keys (`"semantic_revision_count"`) that must survive
replacement of a plan entry, so retry-bounding progress is never reset by a plan rewrite.

### `DESIGN_PLAN_SCHEMA_VERSION` (Utils/Constants.py:203) — constant
Current schema version (6) for persisted typed design-plan (contract) entries.

### `DESIGN_PLAN_CLOSURE_VERSION` (Utils/Constants.py:204) — constant
Version (4) mixed into closure fingerprints so cached closure validation is invalidated
when the closure rules change.

### `SEMANTIC_PLAN_SCHEMA_VERSION` (Utils/Constants.py:205) — constant
Schema version (2) for the advisory semantic-plan entries.

### `SEMANTIC_READINESS_VALUES` (Utils/Constants.py:206) — constant
Allowed `readiness` values (`ready`, `underspecified`, `explicitly_unresolved`) for
semantic-plan entries; anything else is coerced to `ready` with a finding.

### `DESIGN_PLAN_HELPER_KINDS` (Utils/Constants.py:212) — constant
The only helper kinds a plan may own (`structure`, `inductive`, `class`) —
declaration-only type interfaces, since helpers needing bodies or proofs would force proof
work into Phase 1 or leave untracked `sorry`s.

### `_PLAN_REVISION_FINDING_CATEGORIES` (Utils/Constants.py:215) — constant
Set of skeleton-finding categories (`plan_contract_closure`) indicating the interface plan
itself is at fault and requires plan revision rather than statement regeneration.

### `_UNKNOWN_LEAN_NAME_RE` (Utils/Constants.py:220) — constant (regex)
Matches Lean compiler "unknown constant/identifier/namespace `X`" diagnostics to extract
the offending names.

### `_PAPER_EXCERPT_HEAD` (Utils/Constants.py:226) — constant
Number of leading characters of the paper (title/abstract) always included in a
deterministic paper excerpt (2000).

### `_WORD_TOKEN_RE` (Utils/Constants.py:227) — constant
Regex for word tokens (4+ chars) used to score paper paragraphs against target-node TeX
for excerpt selection.

### `_HARNESS_CONVENTIONS_NOTE` (Utils/Constants.py:230) — constant
Prompt boilerplate explaining pipeline conventions to repair models (terminal `sorry`
statements are by design, definition bodies must be complete, what the deterministic audit
rejects, fixes belong in the blueprint TeX).

### `_REPAIR_SCOPE_RULES` (Utils/Constants.py:243) — constant
Prompt boilerplate stating repair-scope rules: prefer additive helper-node repairs, never
rewrite downstream consumers (such edits are detected and rolled back).

---

## 2.2 `scripts/Utils/Logging.py`

Global locks, per-thread stage tracking, and thread-safe log/telemetry primitives.

### `_ACTIVE_STAGE_LOCK` / `_ACTIVE_STAGES` (Utils/Logging.py) — module-level mutable globals
Lock plus per-thread-id map recording each worker thread's current pipeline stage label,
for status reporting.

### `_set_active_stage` (Utils/Logging.py:18) — function
Sets or clears the calling thread's current stage label in `_ACTIVE_STAGES` under the lock.

### `_active_stage` (Utils/Logging.py:27) — function
Returns the calling thread's stage, or a `" | "`-joined summary of all threads' stages
("idle" if none) — used for progress/heartbeat display.

### `_thread_active_stage` (Utils/Logging.py:36) — function
Returns only the calling thread's own stage string ("" if unset); used by `_stage` to
save/restore nesting.

### `_stage` (Utils/Logging.py:42) — context manager function
Pushes a stage label for the duration of a block and restores the previous label on exit,
enabling nested stage tracking.

### `_PRINT_LOCK` / `_TELEMETRY_LOCK` / `_STATE_LOCK` (Utils/Logging.py) — module-level mutable globals
Thread locks: print serialization, telemetry-write serialization, and a reentrant `RLock`
guarding all shared Phase-1 candidate/evidence state (reentrant because state helpers call
one another).

### `_log` (Utils/Logging.py:58) — function
Thread-safe tagged print with flush; the pipeline's console logging primitive.

### `_record` (Utils/Logging.py:64) — function
Thread-safe wrapper around `TelemetryRun.record` for structured event telemetry.

### `_store_text` (Utils/Logging.py:69) — function
Thread-safe wrapper around `TelemetryRun.store_text` to archive text blobs (prompts,
responses, Lean files) alongside telemetry.

---

## 2.3 `scripts/Utils/Types.py`

Shared dataclasses and classes: the parsed-module model, audit/plan verdicts, section records, and the `Ctx` run context.

### `DeclBlock` (Utils/Types.py:20) — dataclass
One parsed Lean declaration: `kind` (theorem/def/...), optional `name`, and full `text`
including attributes/docstrings.

### `ParsedModule` (Utils/Types.py:27) — dataclass
A parsed Lean module split into `imports`, `preamble` lines, and a list of `DeclBlock`s —
the pipeline's working representation of Lean code.

### `CanonicalModelModule` (Utils/Types.py:34) — dataclass
Pipeline-owned canonical form of one model Lean response: the `parsed` module plus
`owner_by_index` assigning every declaration (targets and helpers) to a blueprint node;
raw file wrappers deliberately absent since the pipeline owns module structure.

### `SkeletonFinding` (Utils/Types.py:47) — dataclass
One Phase-1 skeleton audit finding (`message`, optional `label`/`lean_name`, `category`,
`dependencies`); targeting a finding to a node lets Phase 1 replace one bad declaration
instead of regenerating a whole section.

### `PlanClosureFinding` (Utils/Types.py:62) — frozen dataclass
A mechanical plan inconsistency: `consumer` owns the invalid reference; `provider`,
`unauthorized_dependencies`, `missing_provider_members`, `cycle_paths` structure the
evidence so an invented consumer reference cannot needlessly block or rewrite a healthy
provider.

### `DesignPlanCandidate` (Utils/Types.py:80) — dataclass
One independently generated full-plan candidate: `candidate_id`, per-label `entries`,
`missing`, `findings`, `blocked`, `components`. Property `score` (tuple of
missing/blocked/finding/component counts, lower is better) ranks candidates mechanically;
property `closed` means no missing entries and no findings.

### `PlanClosureCorrectionResult` (Utils/Types.py:105) — dataclass
The outcome of one isolated closure-correction call in a concurrent wave: the `component`
of labels, replacement `entries`, `status`, remaining `findings`, and wall-clock timing.

### `AlignmentAuditResult` (Utils/Types.py:118) — frozen dataclass
The semantic (blueprint-alignment) audit verdict: overall `kind`/`reason`, `rejected`
labels, `helpers`, plus per-label maps (kinds, helpers, reasons, origins, plan
requirements, failure identities, required/forbidden dependencies). `__iter__`/
`__getitem__` expose the historical 4-tuple form for backward compatibility; methods
`labels_for`, `helpers_for`, `labels_for_origin`, `plan_requirements_for`, `reason_for`
slice per-label evidence, and `failure_identity_for` returns only the critic's structured
fields so wording changes don't create a new retry epoch.

### `RepairBoundaryAuditOutcome` (Utils/Types.py:210) — frozen dataclass
Result of one scoped semantic check of a model-mutated blueprint component: `status`
(accepted/repair/unavailable), `evidence`, `repair_labels`, `required_dependencies`,
`decomposition_helpers`, `provider_repair_labels`.

### `_coerce_alignment_audit_result` (Utils/Types.py:221) — function
Normalizes the historical tuple form of an alignment audit into an
`AlignmentAuditResult` at consumer boundaries, erroring if fewer than four fields.

### `SectionStuckState` (Utils/Types.py:241) — dataclass
Tracks a Phase-1 section that keeps failing across blueprint edits so the pipeline can escalate its handling. Fields: `labels`, `repairs`, `normalized`, `repairs_after_normalization`.

### `SectionNormalizationRejected` (Utils/Types.py:250) — exception class (RuntimeError subclass)
Signals that a section-normalization attempt was rolled back; caught so the overall run continues rather than aborting.

### `Ctx` (Utils/Types.py:255) — dataclass
The central run-context object for the whole formalization pipeline: configuration (blueprint dir, model runner specs, effort tiers, timeouts, Lean command, worker/section/batch sizes, conjecture policy), plus a large family of fingerprint-scoped persistent state stores — quarantine records, local bisection partitions, diagnostic-evidence ledger, generation feedback, dependency observations, Phase-1 exchange history, model resume sessions, Phase-1/Phase-2 candidate caches, retry lifecycle, design/semantic plan entries, statement-audit cache, Phase-2 repair queue, and phase-transition flags. Members:
- `blueprint_src_dir` (property, 4481) — path to `blueprint/src` under the blueprint dir.
- `content_path` (property, 4485) — path to `content.tex`.
- `refresh_nodes` (method, 4488) — installs a freshly parsed node map, recomputes statement/contract fingerprints and TeX blocks, then invokes every `_prune_stale_*` helper so all fingerprint-scoped evidence stores drop entries invalidated by the blueprint edit.

### `Section` (Utils/Types.py:460) — dataclass
Persistent record of one generated skeleton section file: `number`, `labels`, `path`,
`module`, `import_modules`, plus lifecycle flags `deferred` (retained but must recompile
after an upstream repair), `refined_labels` (which labels passed Phase-1 statement gates),
`provisional_environment` (the permanent whole-blueprint scaffolding file),
`generation_tier`, and `compile_fingerprint`. Property `file_name`.

### `Phase1LayerCandidate` (Utils/Types.py:495) — dataclass
In-memory uncompiled Phase-1 statement candidate owned by one generation transaction:
`labels`, `parsed` (ParsedModule), `import_modules`, `generation_tier`, `sessions`
(per-runner resume ids), and `plan_fps` (the contract/strategy epoch that produced these
declarations, guarding against relabelling old code under a new strategy).

### `_SectionNumberAllocator` (Utils/Types.py:521) — class
Thread-safe callable allocating monotonically increasing skeleton section numbers. Gaps
from abandoned attempts are harmless because assembly keys on relative order only.

---

## 2.4 `scripts/Utils/Graph.py`

Blueprint fingerprints, dependency-graph ordering and frontiers, label bookkeeping, and repair-scope gates.

### `_statement_blocks` (Utils/Graph.py:19) — function
Returns each node's TeX with the trailing `proof` environment stripped — the alignment
contract for the frozen Lean statement (only statements must correspond 1-1).

### `_statement_fingerprints` (Utils/Graph.py:33) — function
SHA-256 hashes of the proof-stripped statement blocks, used to detect statement changes
and selectively invalidate frozen Phase-1 entries.

### `_contract_fingerprints` (Utils/Graph.py:40) — function
SHA-256 hashes of full node TeX including proof sketches; fast-mode resume uses this
broader fingerprint so a proof-prose repair invalidates Lean generated for the old proof
structure.

### `_topo_order` (Utils/Graph.py:52) — function
Kahn-style topological sort of blueprint nodes over the `uses` graph, tie-broken by
blueprint source position; appends leftover labels defensively since validation guarantees
acyclicity.

### `_bottom_up_statement_layers` (Utils/Graph.py:80) — function
Partitions all generated (non-mathlibok) nodes into dependency-first frontiers: a node
enters a layer only after all its generated dependencies appear in earlier layers; the
Phase-1 static schedule.

### `_bottom_up_ready_frontier` (Utils/Graph.py:111) — function
Dynamic replacement for the static layers: returns pending contracts whose generated
dependencies are all frozen, recomputed after each transaction, so a difficult node blocks
only its own dependents.

### `_partition_sections` (Utils/Graph.py:135) — function
Chunks pending nodes into contiguous topo-order sections of `section_size`, guaranteeing
every dependency lives in an earlier section, a frozen section, or Mathlib — the unit of
batched statement generation.

### `_immediate_theorem_dependencies` (Utils/Graph.py:154) — function
Computes the nearest theorem-like dependencies below a node, treating definition nodes as
transparent for proof scheduling; affects proof order only.

### `_top_down_proof_layers` (Utils/Graph.py:179) — function
Builds Phase-2's schedule: theorem-like nodes layered breadth-first from public roots down
to proof leaves via nearest theorem dependencies, keeping the longest root-to-node depth
so a consumer never shares a frontier with its dependency.

### `_next_top_down_frontier` (Utils/Graph.py:231) — function
Returns `(layer, unresolved labels, roots)` for the shallowest top-down proof layer that
still contains unproved theorems — the next Phase-2 proof wave.

### `_bottom_up_proof_layers` (Utils/Graph.py:244) — function
The reversed top-down proof layers: theorem-like nodes from proof leaves upward, for the
bottom-up proof-order option.

### `_next_bottom_up_frontier` (Utils/Graph.py:249) — function
Bottom-up analogue of `_next_top_down_frontier`: the next dependency-first theorem
frontier still containing unproved nodes.

### `_next_implementation_frontier` (Utils/Graph.py:262) — function
Branch-local ready-frontier scheduler for deferred implementations: in top-down mode a
node is ready when all its unresolved generated consumers are done, in bottom-up mode when
all unresolved dependencies are done; static layers order results but are not barriers,
with a deterministic fallback for malformed graphs.

### `_top_down_statement_layers` (Utils/Graph.py:332) — function
Layers all generated nodes from public theorem roots (plus unconsumed public definitions
as sibling roots) down to graph leaves, appending unreachable components in
consumer-before-dependency order — the top-down Phase-1 refinement schedule.

### `_frozen_labels` (Utils/Graph.py:408) — function
The set of labels whose contracts are frozen, i.e. labels of non-deferred sections
(respecting `refined_labels` when a section was partially refined).

### `_reserved_labels` (Utils/Graph.py:419) — function
All labels owned by any section, active or deferred — contracts the scheduler must not
hand out to a new section.

### `_proved_labels` (Utils/Graph.py:424) — function
Parses each non-deferred section's Lean source and returns labels whose declaration exists
and no longer ends in a terminal `sorry` — nodes whose proofs/bodies are complete.

### `_sections_for_deps` (Utils/Graph.py:442) — function
Computes which frozen skeleton modules a new section must `import`: the owners of the
transitive dependencies of the given labels.

### `_dependency_contract_table` (Utils/Graph.py:466) — function
Renders a deterministic text table telling the model how each direct dependency is owned
(Mathlib-settled `\lean` name, same-file, frozen in a named module, or not yet frozen) and
whether each edge is statement-interface or proof-only. Chiefly prevents models from
generating label-derived names for `\mathlibok` nodes.

### `_transitive_dependencies` (Utils/Graph.py:505) — function
DFS over `node.uses` returning the full transitive dependency closure of a label.

### `_statement_uses` (Utils/Graph.py:518) — function
The dependencies that belong in a node's public declaration (`statement_uses`), falling
back to the whole `uses` set for legacy `Node`s without scoped edge information.

### `_proof_uses` (Utils/Graph.py:531) — function
Accessor for a node's proof-only dependency set (empty for legacy nodes).

### `_transitive_statement_dependencies` (Utils/Graph.py:535) — function
Transitive closure over statement-scoped edges only — the public-interface dependency
closure excluding proof-only edges, used to gate what a deferred declaration may
reference.

### `_repair_graph_distances` (Utils/Graph.py:552) — function
BFS over the union of the before/after undirected dependency graphs, returning each
changed contract's distance from a requested repair target. Deterministic repair-scope
telemetry evidence; never blocks a repair.

### `_upstream_contract_closure` (Utils/Graph.py:591) — function
The labels whose contracts may legitimately change while repairing the given labels: the
labels themselves plus their dependency side. Downstream consumers excluded by
construction.

### `_phase1_repair_scope_violations` (Utils/Graph.py:610) — function
Given before/after node graphs, flags changed contracts outside the targets'
dependency/decomposition scope during a Phase 1 statement repair, while permitting newly
added helpers transitively connected to the targets.

### `_phase2_existing_repair_scope_violations` (Utils/Graph.py:644) — function
Stricter Phase-2 variant: flags any pre-existing contract edited that is not itself a
named repair target.

### `_decomposition_orientation_findings` (Utils/Graph.py:664) — function
Validates that each new decomposition helper sits in some repaired root's dependency
closure; reports helpers placed on the consumer side (which would leave dead scaffolding
or create cycles).

### `_decomposition_orientation_dependency_edges` (Utils/Graph.py:708) — function
For the narrow single-root case, mechanically computes the safe root→helper `\uses` edges
a decomposition repair forgot to add, so graph direction can be fixed without a model
call; multi-root and reverse-edge cases deliberately left to fail.

### `_invalid_mathlib_refusal_mappings` (Utils/Graph.py:738) — function
When a model refuses a node (`NEEDS-DECOMPOSITION`), detects cases where the refusal was
really a misreading of a Mathlib-owned dependency: returns generated-name → settled
`lean_decl` mappings for Mathlib deps mentioned in the refusal text.

### `_parts_around_labels` (Utils/Graph.py:758) — function
Splits a dependency-ordered label list into contiguous parts, isolating each named label
as a singleton part while preserving order — used for bisection/isolation of failing
group members.

### `_lean_failure_fingerprint` (Utils/Graph.py:776) — function
Returns a `(code_sha256, normalized_output_sha256)` pair identifying a generated file
failing with byte-identical Lean output — exact stagnation detection.

### `_lean_error_shape` (Utils/Graph.py:785) — function
Hashes a normalized "shape" of Lean compiler output (stripping ANSI codes, locations,
metavariable numbers, whitespace) so a rewritten candidate that moves the same error to a
different line is still recognized as repeated failure.

---

## 2.5 `scripts/Utils/LeanSource.py`

Lean module parsing, model-output canonicalization, helper namespacing, and body defer/splice.

### `_block_comment_line_spans` (Utils/LeanSource.py:15) — function
Scans Lean source for whole-line block comments, tracking nesting depth like Lean's lexer;
returns `(opened_by, covered)` so declaration-boundary detection skips commented lines,
and marks unterminated comments' tails as covered so truncated model prose can't leak into
a declaration.

### `_parse_module` (Utils/LeanSource.py:59) — function
Parses raw Lean text into a `ParsedModule`: extracts/dedupes imports, drops the pipeline's
own `set_option` lines, finds declaration starts via `_DECL_START_RE`, and walks backward
over attributes/docstrings/comments so multi-line docstrings attach to their declaration
rather than becoming invalid preamble.

### `_normalize_theorem_like_keywords` (Utils/LeanSource.py:129) — function
Rewrites `corollary`-keyword declarations whose name matches a theorem-like blueprint
target to Lean's `theorem` command, so a model using blueprint prose vocabulary doesn't
produce an invalid Lean command plus an apparent omission.

### `_remove_model_module_wrappers` (Utils/LeanSource.py:161) — function
Strips balanced `namespace`/`section` ... `end` wrappers models habitually add around
output; raises on unmatched, mismatched, or unclosed wrappers instead of letting them leak
into persistent state.

### `_declaration_owner_map` (Utils/LeanSource.py:198) — function
Assigns each declaration index to an owning blueprint node: explicit plan-fixed owners
win; otherwise adjacency (nearest following, then nearest preceding, target declaration)
is the fallback for genuinely unplanned helpers.

### `_declaration_target_consumers` (Utils/LeanSource.py:231) — function
Builds the canonical ownership relation by textual reference closure: for each
declaration, the set of blueprint targets that transitively reference it — needed because
one local helper may serve several targets; feeds namespacing, cache keys, candidate
slicing, and persistence.

### `_target_components_from_helpers` (Utils/LeanSource.py:303) — function
Union-find over `_declaration_target_consumers`: targets sharing a local helper are merged
into connected components, so acceptance/rejection decisions can act on coherent groups.

### `_lean_identifier_replace` (Utils/LeanSource.py:339) — function
Replaces one Lean identifier in text using boundary lookarounds so longer dotted/primed
names are untouched.

### `_declared_name_replace` (Utils/LeanSource.py:348) — function
Renames only the declaration head introduced by a block, not body references — so a
structure field spelled like the old global name keeps shadowing it.

### `_restore_planned_member_declarations` (Utils/LeanSource.py:362) — function
After helper namespacing, restores planned structure/class field names that
alias-rewriting mangled (a plan may legally give a helper and one of its fields the same
name); type references stay canonicalized.

### `_planned_member_names` (Utils/LeanSource.py:387) — function
Collects the member/field names bound by one planned structure/class helper spec, which
shadow equally named globals inside the declaration body.

### `_owned_helper_name` (Utils/LeanSource.py:407) — function
Computes the canonical stable global name for a model-created local helper:
`_autobp_<12-hex-digest>_<sanitized name>`, deterministic per owning node set so
independently compiled candidates can't collide.

### `_planned_helper_specs` (Utils/LeanSource.py:425) — function
Returns the valid (current-schema-version) plan-owned helper contract dicts for the
requested labels from `ctx.design_plan_entries`.

### `_planned_helper_owner_by_name` (Utils/LeanSource.py:441) — function
Maps each canonical (owned) plan-helper name to its blueprint-node owner label.

### `_semantic_helper_owner_by_name` (Utils/LeanSource.py:451) — function
From advisory semantic-plan vocabulary, maps a helper name to its owner only when exactly
one requested label claims it — unambiguous advisory ownership for first-pass ingestion.

### `_planned_helper_aliases` (Utils/LeanSource.py:473) — function
Builds the alias table from every model-facing plan spelling of a helper
(`target.Helper`, flattened, bare name when unique) to its canonical `_autobp_` global
name, so consumer modules generated in later batches resolve helpers without waiting for
Lean rejections.

### `_planned_helper_assignments` (Utils/LeanSource.py:518) — function
Matches emitted non-target declarations to accepted plan helper contracts: exact/suffix/
canonical name matches first, then a mutual-unique match on kind plus complete
required-member surface; never guesses — ambiguous output is left for the deterministic
gate to reject.

### `_namespace_owned_helpers` (Utils/LeanSource.py:612) — function
The deterministic alpha-renaming pass: gives every model-created helper its stable
node-owned global name (targets keep their required names), applies plan aliases
longest-first, protects shadowed member names, restores planned member declarations, and
records telemetry — preventing cross-candidate global name collisions with zero model
calls.

### `_canonicalize_model_lean` (Utils/LeanSource.py:719) — function
The model-output boundary: strips wrappers, parses, normalizes theorem-like keywords,
rejects unsupported module-level commands and (optionally) duplicate declaration names,
namespaces helpers, computes owner map, and records telemetry — producing the
`CanonicalModelModule` that is the only representation the pipeline stores.

### `_realize_typed_contracts_from_candidate` (Utils/LeanSource.py:815) — function
Makes the checked Phase-1 Lean candidate its own authoritative typed contract: for each
requested label it writes a `design_plan_entries` entry (`origin: "phase1_candidate"`)
containing the target's interface text (bodies stripped) and structural helper interfaces,
preserving retry-lifecycle progress keys so contract refreshes don't reset bounded
exhaustion accounting; legacy resumed contracts are left alone.

### `_ingest_model_lean` (Utils/LeanSource.py:967) — function
Convenience entry point for a raw model response: extracts the Lean code block,
canonicalizes it, optionally defers Phase-1 target bodies to `sorry` and realizes typed
contracts — the standard ingestion path for model output.

### `_compose_module` (Utils/LeanSource.py:990) — function
Composes a Lean module file from imports (deduped, defaulting to
`import Mathlib.Data.Real.Basic`), the fixed `set_option` block, preamble, and declaration
texts; returns the text plus per-declaration 1-based `(start, end)` line ranges so
compiler diagnostics can be mapped back to declarations.

### `_has_terminal_sorry` (Utils/LeanSource.py:1016) — function
True when a declaration text ends in `:= sorry` / `:= by sorry` — the marker of a properly
deferred body (as opposed to a scaffolding sorry mid-declaration).

### `_normalize_terminal_sorry` (Utils/LeanSource.py:1020) — function
Rewrites a declaration's trailing terminal-sorry marker into the canonical `:= sorry`
spelling, giving downstream comparisons and splices one uniform representation.

### `_terminal_sorry_interface_text` (Utils/LeanSource.py:1024) — function
Strips only the final Phase-1 `:= sorry` marker off a declaration, returning the bare
public interface text (or `None`). Deliberately avoids searching for the first `:=`,
since result types may legally contain `let`/`letI` assignments.

### `_top_level_assignment_index` (Utils/LeanSource.py:1040) — function
A small character-level lexer that finds the index of a declaration's top-level `:=` while
correctly skipping strings, comments, and bracket-nested binder syntax. Used to split a
model-authored declaration into a public header and a deferrable body.

### `_phase1_target_interface_text` (Utils/LeanSource.py:1109) — function
Returns the Phase-1 "target contract" for a declaration: for `def`/`abbrev`/`theorem`/
`lemma` it drops the implementation/proof body; for other kinds it falls back to the
generic interface extractor.

### `_deferred_prop_structure` (Utils/LeanSource.py:1121) — function
Detects the invalid Phase-1 shape `structure ... : Prop where` (models sometimes spell a
predicate as a Prop-sorted structure) and deterministically converts its header into a
deferred `def ... := sorry`, avoiding a compile failure and a paid model repair round.

### `_defer_phase1_target_bodies` (Utils/LeanSource.py:1141) — function
Enforces the Phase-1 output contract on a canonical model module: every target
definition/theorem body the model implemented is replaced with `:= sorry` so
model-authored bodies never become authoritative input to later correction prompts.
Exempts plan-owned structural interfaces and their transparent type aliases; records
telemetry per deferred body.

### `_may_defer_target_body` (Utils/LeanSource.py:1228) — function
Predicate deciding whether Phase 1 may legally leave a target's implementation to Phase 2:
terminal sorry present, not an open conjecture, and the right decl kind for the node.

### `_is_phase1_structural_target_alias` (Utils/LeanSource.py:1239) — function
Narrow exception check: a completed target body is allowed in Phase 1 only when it is a
transparent type alias whose right-hand side directly applies a
structure/class/inductive owned by the same blueprint node. Prevents the body deferrer
from erasing a purely interface-level alias.

### `_splice_proof` (Utils/LeanSource.py:1306) — function
Replaces a declaration's terminal `:= sorry` with a supplied tactic proof body, leaving
the frozen statement header untouched. This is how Phase-2 proofs are installed into
pipeline-owned statements.

### `_extract_by_proof` (Utils/LeanSource.py:1314) — function
Pulls just the `by ...` proof term out of a model-returned declaration; only the proof is
used so a model that silently reshapes the statement cannot smuggle the change in.

---

## 2.6 `scripts/Utils/LeanCheck.py`

Lean compilation, per-declaration error attribution, and import resolution.

### `_errors_by_decl` (Utils/LeanCheck.py:15) — function
Parses Lean compiler output and groups error messages by declaration index using
per-declaration line ranges; unattributable errors are returned separately as file-level.

### `_lean_compile_findings` (Utils/LeanCheck.py:50) — function
Converts grouped Lean diagnostics into `SkeletonFinding` objects targeted at specific
declarations/blueprint labels, plus file-level findings; guarantees at least one finding
when compilation failed.

### `_check_lean` (Utils/LeanCheck.py:86) — function
Compiles a module with the configured Lean command (allowing sorry warnings, i.e.
skeleton-phase mode), polling with a hard timeout and killing the whole process group on
expiry. On failure it attempts a deterministic repair of missing universe-level
declarations and retries the identical compile once repaired.

### `_lean_failure_may_be_fixed_by_broad_mathlib` (Utils/LeanCheck.py:125) — function
Gate deciding whether the broad-`import Mathlib` fallback diagnosis is worth running for a
failed candidate: only missing-name errors qualify; type mismatches, unfinished tactics,
and heartbeat exhaustion are excluded to avoid pointless recompiles.

### `_missing_lean_surface_names` (Utils/LeanCheck.py:137) — function
Extracts the deduplicated list of unresolved Lean names from compiler output, without
treating other error kinds as import problems.

### `_specific_import_modules_for_missing_names` (Utils/LeanCheck.py:147) — function
Deterministically resolves each missing declaration name to specific local library modules
(via ripgrep over the selected library roots), so a narrow import can replace the
expensive persisted `import Mathlib`. Returns empty when resolution is
ambiguous/incomplete so the caller keeps the broad fallback rather than guessing.

---

## 2.7 `scripts/Utils/Audits.py`

The deterministic skeleton audit and the model-driven blueprint-alignment audit.

### `_skeleton_code_findings` (Utils/Audits.py:15) — function
The Phase-1 (skeleton) deterministic correctness audit for generated Lean code: allows
`sorry` only as a target's terminal deferred body, and flags forbidden placeholders,
`autoImplicit`, top-level assumptions, invented blueprint helpers, unplanned helpers,
malformed recorded conjectures, non-terminal sorries, placeholder names, `Prop := True`
cop-outs, and bad file shape. Returns declaration-attributed `SkeletonFinding`s.

### `_skeleton_code_issues` (Utils/Audits.py:204) — function
Thin wrapper that runs `_skeleton_code_findings` and returns just the message strings.

### `_format_skeleton_findings` (Utils/Audits.py:208) — function
Renders findings into the human/model-facing "Deterministic skeleton audit rejected the
file" bullet text, prefixing each with its blueprint label and/or Lean name.

### `_skeleton_finding_class` (Utils/Audits.py:224) — function
Maps a finding message to a stable, paper-independent classification string
(`missing_decl`, `placeholder_name`, `nonterminal_sorry`, `wrong_kind`,
`bad_file_shape`, …) used for deterministic routing of skeleton failures.

### `_skeleton_findings_fingerprint` (Utils/Audits.py:249) — function
Builds a deterministic stagnation key (sorted (label, obligation-id) tuples) from Phase-1
audit failures; if the key is unchanged after a model patch, the pipeline escalates or
shrinks instead of repeating the same patch/regenerate cycle.

### `_dependency_closed_subset` (Utils/Audits.py:267) — function
Given a section's label list and target labels, returns the smallest original-order subset
containing the targets plus all their same-section transitive `\uses` dependencies — used
to carve out dependency-closed retry units.

### `_plan_owned_declaration_cycle_findings` (Utils/Audits.py:292) — function
Deterministically detects impossible mutual-reference cycles between a target declaration
and its plan-owned helper declarations in emitted Phase-1 code, returning
`plan_contract_closure` findings.

### `_skeleton_deterministic_findings` (Utils/Audits.py:353) — function
The core deterministic Phase-1 section audit: checks plan-owned helper
presence/kind/required members, missing target declarations, wrong declaration kinds,
references outside the blueprint dependency closure (statement-scoped for deferred
bodies, full closure otherwise), and missing required dependency mentions in completed
bodies; also realizes typed contracts from a clean candidate and records dependency
observations.

### `_skeleton_deterministic_audit` (Utils/Audits.py:549) — function
Thin wrapper returning just the message strings from `_skeleton_deterministic_findings`.

### `_alignment_issue_failure_identity` (Utils/Audits.py:553) — function
Builds a provider-neutral canonical failure identity from one critic issue's structured
fact arrays, deliberately excluding the free-text `reason`; returns empty when no
structured facts exist so the evidence ledger falls back to normalized prose.

### `_append_alignment_failure_identity` (Utils/Audits.py:603) — function
Appends a canonical failure identity to a per-label accumulator, deduplicating by
canonical JSON encoding.

### `_model_alignment_audit` (Utils/Audits.py:622) — function (~470 lines)
The batched model-driven blueprint-contract (semantic alignment) audit for Phase 1. Caches
per-label verdicts keyed on blueprint/plan/Lean/paper content, runs an independent-judge
model call (deliberately session-free to avoid rubber-stamping), downgrades body-only
complaints on deferred definitions to `defer`, then routes each rejection into
`lean-generation` / `decomposition` / `blueprint` kinds with per-label reasons, failure
origins, required/forbidden dependency edges, missing helpers, and failure identities.
Returns `None` on acceptance or a rich `AlignmentAuditResult`.

---

## 2.8 `scripts/Utils/FailureRouting.py`

Failure-scope routing policy, the `RepairRequest` exception, and request aggregation/serialization.

### `CallResult` (Utils/FailureRouting.py:20) — dataclass
Result of one model-backend call: `status` (ok/timeout/cancelled/transport_exhausted/
error), `text`, `error`, `duration_s`, and `partial_text` — the output emitted before a
timeout killed the call, which callers may salvage complete declarations from.

### `_runner_failure_status` (Utils/FailureRouting.py:30) — function
Classifies a backend exception into a `CallResult`-style status so infrastructure failures
never masquerade as mathematical evidence.

### `FailureScopeDecision` (Utils/FailureRouting.py:42) — frozen dataclass
Provider-neutral description of the retry scope after a Lean-generation failure: an
`action` (isolate/bisect/singleton/independent), the `parts` to retry, and the
`failed_labels`/`accepted_labels` split. Exists so Phase 1 and Phase 2 make identical
decisions about the size of the next generation unit.

### `_route_lean_generation_failure` (Utils/FailureRouting.py:57) — function
The scope-routing policy itself: a known proper subset of attributable labels is isolated
(siblings stay independently eligible), any unresolved multi-label unit is bisected in
half, and only a singleton passes through to the caller's escalation policy.

### `_combine_failure_routes` (Utils/FailureRouting.py:100) — function
Merges several independent `FailureScopeDecision`s into a single "independent"-action
decision that unions their parts and label sets — a compatibility value for older
single-scope callers/logs while `failure_routes` preserves each original.

### `RepairRequest` (Utils/FailureRouting.py:131) — class (Exception)
The central control-flow exception carrying bounded failure evidence back to the main
orchestration loop. Its large `__init__` captures the failing labels, per-label evidence
and canonical failure identities, decomposition helpers, frozen sibling sections to
preserve, failure routes, required dependency edges, whether it authorizes blueprint
repair (vs. scheduling-only rescheduling / implementation prerequisites), retry-tier
provenance, provider-contract rerouting labels, and repair components.

### `_requires_blueprint_transaction` (Utils/FailureRouting.py:253) — function
Whether the outer loop must enter its transactional blueprint-edit path: either full model
repair is authorized, or there are required-dependency edges that warrant the
deterministic, cycle-checked `\uses` edge transaction (which by itself never authorizes a
model rewrite).

### `_aggregate_retry_requests` (Utils/FailureRouting.py:270) — function
Merges independent non-blueprint-authorized failures from one parallel transaction into a
single aggregate `RepairRequest`, preserving every retry scope, accepted sibling sections,
per-label evidence, and dependency requirements — so one outer trial handles them all
instead of hiding failures behind an arbitrary single exception.

### `_aggregate_authorized_repair_requests` (Utils/FailureRouting.py:355) — function
The blueprint-authorized counterpart: merges multiple authorized repairs into one shared
transaction (used by Phase 1 for a dependency-closed generation component), unioning
labels, helpers, dependencies, evidence, and building per-component repair scopes.
Phase-2 workers deliberately don't use it — their failures stay independent queue items.

### `_combine_deferred_phase1_requests` (Utils/FailureRouting.py:454) — function
Chooses the next safe outer action after draining independent Phase-1 branches:
model-authorized repairs are aggregated/serialized via
`_aggregate_authorized_repair_requests`, and pure retry failures via
`_aggregate_retry_requests`, without widening non-editing failures into a model-edit
transaction.

### `_failure_route_to_payload` (Utils/FailureRouting.py:480) — function
Serializes a `FailureScopeDecision` into a plain JSON-able dict for persisted state.

### `_failure_route_from_payload` (Utils/FailureRouting.py:489) — function
Inverse: reconstructs a `FailureScopeDecision` from its persisted dict payload.

### `_phase2_repair_request_payload` (Utils/FailureRouting.py:505) — function
Serializes one independently authorized Phase-2 repair into a queue payload, deriving a
content-addressed `request_id` (SHA-256 over labels, statement fingerprints,
dependency-context fingerprint, repair scope, and evidence signatures) so identical
diagnoses dedupe and stale ones can be detected.

---

## 2.9 `scripts/Utils/Transactions.py`

The Phase-1 checkpoint and the Phase-2 repair transaction queue and lifecycle.

### `_phase2_repair_context_fingerprint` (Utils/Transactions.py:15) — function
Hashes the exact blueprint dependency environment behind repair evidence: a deterministic
walk over the targets' transitive statement/proof `\uses` closure plus each node's
statement fingerprint. A queued diagnosis stays valid only while this hash is unchanged.

### `_phase2_repair_transaction_dir` (Utils/Transactions.py:76) — function
Path helper: the durable scratch directory acting as the rollback point for one
unpublished Phase-2 graph edit, keyed by run name and request id.

### `_phase1_checkpoint_dir` (Utils/Transactions.py:81) — function
Path helper: the immutable restart-point directory captured at the Phase 1/Phase 2
boundary for a run.

### `_phase1_checkpoint_available` (Utils/Transactions.py:86) — function
Checks that a complete, valid Phase-1 checkpoint exists (manifest version 1 plus the
blueprint draft `content.tex` and `skeleton_state.json` files).

### `_replace_tree_from_snapshot` (Utils/Transactions.py:100) — function
Utility that replaces an optional directory wholesale with its exact snapshotted copy
(deleting the destination first, copying only if the source exists).

### `_create_phase1_checkpoint` (Utils/Transactions.py:109) — function
Saves one immutable, coherent copy of completed Phase-1 state — blueprint draft, generated
modules, lake-generated objects, and scheduler state together, committed atomically via a
pending directory and `os.replace` — because checkpointing only the state JSON would
create a mixed-version resume. First committed checkpoint wins; records telemetry.

### `_restore_phase1_checkpoint` (Utils/Transactions.py:183) — function
Restores the mutable unpublished state (draft, generated modules, scheduler state) from
the Phase-1 snapshot, discarding all later unpublished Phase-2 changes including the
repair-transaction directory.

### `_begin_phase2_repair_transaction` (Utils/Transactions.py:210) — function
Persists the exact blueprint, Lean, and scheduler state into an atomic snapshot before a
Phase-2 repair model is allowed to edit, so a rejected provisional component (or
interrupted process) can be rolled back cleanly rather than becoming input to another
repair.

### `_restore_phase2_repair_transaction_files` (Utils/Transactions.py:285) — function
Restores the complete pre-edit filesystem state (draft, generated dirs, state file) from
one repair's transaction snapshot; refuses if the snapshot manifest is missing.

### `_discard_phase2_repair_transaction` (Utils/Transactions.py:305) — function
Deletes a repair's rollback snapshot — only after its replacement Lean has been accepted.

### `_restore_interrupted_phase2_repair` (Utils/Transactions.py:314) — function
Startup recovery: if the persisted state shows a repair still in stage `repair` (i.e., the
process died while the repair model may have been writing), restores the pre-edit snapshot
before blueprint validation can see a partial edit; a `verify`-stage repair is
deliberately retained for continuation. Returns the restored request id.

### `_merge_phase2_repair_followup` (Utils/Transactions.py:346) — function
After a staged provisional component is rolled back, rebases the new verification evidence
onto the original queued repair payload: edit authority returns to the original blueprint
roots, discarded provisional helper labels become diagnostic evidence only, and
evidence/fingerprints/helpers are merged into the queue entry before re-issuing.

### `_restart_active_phase2_repair` (Utils/Transactions.py:455) — function
Full rollback-and-retry of a rejected staged Phase-2 component: restores the transaction
snapshot, revalidates the draft, reloads state, carries forward evidence learned from the
rejection (and any still-valid queued requests), merges the follow-up, and returns the
restored sections plus the rebuilt request.

### `_reroute_active_phase2_repair_to_provider` (Utils/Transactions.py:540) — function
Handles the case where the boundary audit finds the defect lives in an unchanged
dependency's contract rather than in the consumer edit: rolls back the consumer repair,
retires its request, and enqueues a separate provider-owned repair (validated against the
original dependency closure), so edit authority never crosses the transaction boundary.

### `_prune_stale_phase2_repair_queue` (Utils/Transactions.py:614) — function
Drops persisted repair diagnoses whose identity is invalid or whose target
statements/dependency-context fingerprints have since changed (the active transaction is
exempt); backfills missing context fingerprints for schema migration and records
superseded entries.

### `_enqueue_phase2_repair_requests` (Utils/Transactions.py:671) — function
Queues blueprint-authorized worker failures as independent payloads (deduped by
content-derived request id) without unioning their edit scopes; rejects non-authorized
requests and records queue telemetry.

### `_pending_phase2_repair_request` (Utils/Transactions.py:706) — function
Peeks (without removing) the next persisted Phase-2 repair: prunes stale entries, respects
an active request in `verify` stage, prefers the currently active request id, and
reconstructs a full `RepairRequest` from the payload.

### `_activate_phase2_repair_request` (Utils/Transactions.py:775) — function
Marks a single request as the one active Phase-2 blueprint writer (stage `repair`) before
any edit; refuses to activate a second repair while one is unverified; records telemetry.

### `_start_phase2_repair_transaction` (Utils/Transactions.py:815) — function
The single transaction gate every Phase-2 repair must cross before mutating the draft:
activates the request, persists state, and creates/verifies the durable pre-edit snapshot.

### `_start_caught_phase2_repair_transaction` (Utils/Transactions.py:857) — function
Small wrapper routing a caught queued request through `_start_phase2_repair_transaction`,
returning "" for requests without a persisted queue identity.

### `_mark_phase2_repair_verifying` (Utils/Transactions.py:867) — function
Transitions the active repair to stage `verify` (blocking further edits), recording which
labels are owned repaired declarations vs. cache-recheck labels — persisted on the queue
payload because rollback restores the pre-edit active marker.

### `_complete_phase2_repair_request` (Utils/Transactions.py:921) — function
Removes a request from the queue, clears the active marker, prunes stale entries, and
discards the rollback snapshot — acknowledged only after replacement Lean verifies.

### `_complete_verified_phase2_repair` (Utils/Transactions.py:945) — function
Checks whether the active `verify`-stage repair is fully done — every verification label
frozen and every body-requiring label implemented — and if so completes the request and
records `phase2_repair_verified`.

---

## 2.10 `scripts/Utils/Draft.py`

Blueprint draft lifecycle, conjecture-policy predicates, and the scoped TeX repair writer.

### `_is_conjecture_node` (Utils/Draft.py:15) — function
Recognizes a blueprint node as a conjecture/open claim via its `kind`, a `conj:` label prefix, or an `open_claim` flag. Routes conjectures through the conjecture policy.

### `_records_conjecture` (Utils/Draft.py:24) — function
True when the run's `conjecture_policy` is `"record"` and the label is a conjecture node — i.e. the node should be preserved as a stated proposition rather than proved.

### `_phase1_target_kind` (Utils/Draft.py:31) — function
Returns the Phase-1 target kind for a label, substituting the special `OPEN_CONJECTURE_TARGET_KIND` when the conjecture is being recorded rather than attempted.

### `_phase1_target_kinds` (Utils/Draft.py:37) — function
Maps each label's Lean name to its Phase-1 target kind for a batch of labels.

### `_blueprint_block_has_proof` (Utils/Draft.py:41) — function
Checks whether a TeX block contains a non-empty `\begin{proof}...\end{proof}` environment (comments stripped). Supports the `attempt` conjecture policy, which requires a blueprint proof before formalizing.

### `_blueprint_node_has_proof` (Utils/Draft.py:51) — function
Looks up a label's TeX block on the context and reports whether it carries a non-empty proof, via `_blueprint_block_has_proof`.

### `_canonical_blueprint_dir` (Utils/Draft.py:58) — function
Returns the published blueprint location `REPO_ROOT/blueprints/<name>` — the canonical source the run reads from and eventually promotes back into.

### `_draft_blueprint_dir` (Utils/Draft.py:62) — function
Returns the scratch-directory location of the unpublished working copy of a blueprint (`SCRATCH_DIR/<name>/blueprint-draft`).

### `_prepare_blueprint_draft` (Utils/Draft.py:66) — function
Creates (or, on `--continue`, resumes) the draft working tree by copying the canonical blueprint into scratch, so all model-driven blueprint edits happen on an unpublished copy.

### `_validate_draft` (Utils/Draft.py:83) — function
Thin wrapper running `validate_blueprint` against the context's draft blueprint directory.

### `_read_blueprint_source_at` (Utils/Draft.py:87) — function
Reads a blueprint's `content.tex` (plus `macros/common.tex` if present) into one annotated string with `% FILE:` headers, for feeding blueprint source to model prompts.

### `_read_draft_blueprint_source` (Utils/Draft.py:102) — function
Convenience wrapper reading the current draft's blueprint source via `_read_blueprint_source_at`.

### `_write_api_refinement_to` (Utils/Draft.py:106) — function
Parses a model refinement response as JSON, validates its `content_tex` (non-empty, no `\begin{document}`), writes it to the given path, and prints any notes. Used for whole-file blueprint refinements returned by a model.

### `_scoped_blueprint_repair_content` (Utils/Draft.py:119) — function
The core scoped-repair validator: applies model-returned per-label TeX node replacements to the immutable pre-call content string while enforcing strict scope — every requested target must be returned exactly once, replacements may only add brand-new helper labels (each owned by one target), may not touch any other pre-existing label, and replaced blocks must be uniquely locatable and non-overlapping. Prevents a model from smuggling unrelated edits into a repair.

### `_write_scoped_blueprint_repair_to` (Utils/Draft.py:238) — function
Validates a scoped repair via `_scoped_blueprint_repair_content` and atomically writes the result to disk (temp file + `os.replace`), printing refinement notes and returning the metadata.

### `_promote_blueprint_draft` (Utils/Draft.py:264) — function
Atomically publishes the successful draft `content.tex` back into the canonical `blueprints/<name>` location and records a `blueprint_draft_promoted` telemetry event — the end-of-run publication step.

---

## 2.11 `scripts/Utils/Evidence.py`

Quarantine, local bisection, the diagnostic-evidence ledger, and generation feedback.

### `_quarantine_labels` (Utils/Evidence.py:15) — function
Marks exact failing statement versions for singleton scheduling: records each label's statement fingerprint and first-observed failure class in `ctx.quarantine` so it is kept out of broad Phase-1 batches, and emits telemetry. Quarantine is routing evidence, auto-released when the statement changes.

### `_release_quarantine` (Utils/Evidence.py:48) — function
Removes labels from the quarantine set/records (e.g. when a statement freezes) and records a release telemetry event with the reason.

### `_prune_stale_quarantine` (Utils/Evidence.py:70) — function
Drops quarantine entries whose label vanished or whose statement fingerprint changed after a blueprint edit; called from `Ctx.refresh_nodes`.

### `_release_local_group_partitions` (Utils/Evidence.py:86) — function
Removes stored local bisection partitions that involve any of the given (accepted or changed) labels — identified by shared `partition_id` — with telemetry.

### `_prune_stale_local_group_partitions` (Utils/Evidence.py:113) — function
Invalidates local bisection records once any participating statement's fingerprint changed or a label disappeared.

### `_store_local_bisection` (Utils/Evidence.py:132) — function
Persists one failure-routing bisection (`FailureScopeDecision`) as fingerprinted per-label partition records, so only the exact failed group is subdivided on retry without shrinking unrelated batches; emits telemetry.

### `_apply_phase1_retry_scheduling` (Utils/Evidence.py:168) — function
Translates a `RepairRequest`'s generation-failure evidence into scheduler state: plan-revision failures leave scheduling untouched, an unrouted failure quarantines its labels, and routed failures either quarantine (`isolate`/`singleton`/`independent`) or store a local bisection (`bisect`), with telemetry.

### `_current_diagnostic_candidate_fp` (Utils/Evidence.py:208) — function
Returns the hash of the exact candidate Lean currently eligible for correction — preferring the Phase-2 node candidate, then the Phase-1 working candidate, then the stored/derived candidate hash. Anchors candidate-lifetime diagnostic evidence.

### `_diagnostic_evidence_policy` (Utils/Evidence.py:229) — function
Classifies a diagnostic producer string into a fact kind and validity boundary: interface-usability gates and unknown producers become statement-scoped `operational`, plan producers plan-scoped, compiler/deterministic producers candidate-scoped, and alignment/semantic/audit producers statement-scoped `semantic`.

### `_canonical_failure_identity` (Utils/Evidence.py:270) — function
Recursively normalizes a structured failure payload (sorting maps, deduplicating/sorting lists, collapsing whitespace) so equivalent structured failure reports produce a stable identity while free-text failures stay distinct.

### `_diagnostic_failure_signature` (Utils/Evidence.py:296) — function
Fingerprints one failure: prefers the canonicalized structured identity; otherwise the location-insensitive Lean error shape for compiler diagnostics, or a normalized-text hash for prose. Enables deduplicating the same failure reported by different producers.

### `_diagnostic_evidence_id` (Utils/Evidence.py:331) — function
Computes the stable ledger id of one diagnostic record from its label, statement/plan/candidate fingerprints, kind, lifetime, and failure signature.

### `_record_diagnostic_evidence` (Utils/Evidence.py:357) — function
The write path of the typed diagnostic ledger: stores one immutable diagnostic fact with an explicit validity scope (statement/plan/candidate/transaction), resolving plan/candidate fingerprints, discarding candidate-scoped facts with no attached candidate (so stale compiler errors cannot poison a regenerated candidate), and merging or replacing duplicate/broader records under `_STATE_LOCK`. Returns the evidence id.

### `_diagnostic_record_is_active` (Utils/Evidence.py:493) — function
Determines whether a ledger record is still valid: not consumed, label still present with matching statement fingerprint, and for plan/candidate lifetimes the corresponding current fingerprint still matches.

### `_prune_stale_diagnostic_evidence` (Utils/Evidence.py:515) — function
Removes ledger entries whose validity boundary no longer holds; called from `refresh_nodes` and before evidence reads.

### `_active_diagnostic_evidence` (Utils/Evidence.py:529) — function
Returns deep copies of all currently valid ledger records for the given labels, optionally filtered by kind — the read path for prompts and authorization checks.

### `_consume_diagnostic_evidence` (Utils/Evidence.py:547) — function
Marks matching ledger records as consumed (then prunes them), used once evidence has served its purpose, e.g. after acceptance.

### `_migrate_legacy_generation_feedback` (Utils/Evidence.py:569) — function
Imports pre-ledger `generation_feedback` continuation state into the typed diagnostic ledger (tagged `legacy:<source>`) without duplicating existing facts — backwards compatibility for old `--continue` state.

### `_sync_generation_feedback_projection` (Utils/Evidence.py:599) — function
Rebuilds the legacy per-label `ctx.generation_feedback` mapping as a read-only projection of the active prompt-relevant ledger records, keeping old state/tests compatible with the new ledger.

### `_prune_stale_generation_feedback` (Utils/Evidence.py:626) — function
Combined maintenance pass: migrates legacy feedback, prunes stale ledger records, drops legacy feedback entries whose statement fingerprint changed, and resyncs the projection; returns the set of labels whose evidence went stale.

### `_prune_stale_phase1_dependency_observations` (Utils/Evidence.py:656) — function
Drops observed generated-Lean dependency references for labels whose blueprint statement changed or vanished.

### `_record_phase1_dependency_observations` (Utils/Evidence.py:673) — function
Persists exact `outside_dependency_closure` findings — generated Lean statements referencing blueprint nodes outside the declared `\uses` closure — both as `dependency_reference` ledger facts and in `ctx.phase1_dependency_observations`, keyed by statement fingerprint with candidate hashes. Explicitly only half of dependency-edge authorization; the statement critic must independently confirm.

### `_confirmed_phase1_dependency_observations` (Utils/Evidence.py:756) — function
Joins the persisted deterministic candidate-reference observations with the independent statement critic's required dependencies; only intersecting edges are "confirmed" and authorized for the transactional dependency-edge writer. Emits authorization telemetry.

### `_clear_phase1_dependency_observations` (Utils/Evidence.py:807) — function
Consumes dependency observations (ledger records and the observation store) after an edge transaction is attempted.

### `_explicit_generation_evidence_by_label` (Utils/Evidence.py:842) — function
Splits a formatted multi-node audit/compiler evidence text into per-label chunks using stable `- <label> ...:` prefixes, so each node's retry prompt sees only its own findings; unattributed file-level diagnostics are never copied to every node of a batch.

### `_generation_evidence_from_findings` (Utils/Evidence.py:882) — function
Groups structured `SkeletonFinding`s by owning label and renders each group with `_format_skeleton_findings` (capped to 12k chars); unowned findings attach only in the single-label case.

### `_compiler_generation_evidence_by_label` (Utils/Evidence.py:903) — function
Attributes raw Lean compiler diagnostics to individual declarations in a multi-node module by parsing the code, computing declaration line ranges, matching error locations, and mapping planned helpers to their owners.

### `_store_generation_feedback` (Utils/Evidence.py:933) — function
Persists per-label correction evidence for the current statement epoch into the diagnostic ledger (using an explicit `evidence_by_label` mapping or the prefix-based splitter), resyncs the legacy projection, and records telemetry — so the next retry sees every still-relevant rejection reason.

### `_generation_feedback_for` (Utils/Evidence.py:1002) — function
Renders the deduplicated (by failure signature) active rejection evidence for a set of labels into a prompt-ready text block, compacting long entries under a per-group character budget; records injection telemetry.

### `_clear_generation_feedback` (Utils/Evidence.py:1077) — function
Consumes all prompt-relevant ledger evidence and removes legacy feedback entries for labels whose statements were accepted.

---

## 2.12 `scripts/Utils/Exchange.py`

The Phase-1 exchange sample budget and the model resume-session store.

### `_phase1_exchange_start` (Utils/Exchange.py:15) — function
Reserves one stochastic sample for an exact Phase-1 model-call context (labels + statement/plan fingerprints + candidate + prompt + tier hashed into a key), persisted so retries, restarts, and `--continue` cannot reset the `PHASE1_EXCHANGE_SAMPLE_LIMIT` allowance; returns "" when the epoch is exhausted, telling the caller to route evidence without another model call.

### `_phase1_exchange_finish` (Utils/Exchange.py:75) — function
Records a model call's outcome (status + response hash) against its reservation and returns whether the response was byte-identical to a previous one for the same context — preventing paying to compile/audit a duplicate response again.

### `_model_resume_session_key` (Utils/Exchange.py:104) — function
Computes a stable hash key for a captured model session from purpose, labels, statement/plan fingerprints, runner spec, and prompt hash, so a resume never crosses a changed statement/plan/prompt/model epoch.

### `_get_model_resume_session` (Utils/Exchange.py:132) — function
Looks up a stored resume session id for a key, returning it only if the runner spec still matches.

### `_set_model_resume_session` (Utils/Exchange.py:145) — function
Stores a best-effort model conversation session id (captured, e.g., on timeout) keyed by exact call context, so an outer retry can resume the model's partial work.

### `_clear_model_resume_session` (Utils/Exchange.py:178) — function
Deletes one stored resume session by key.

### `_prune_stale_model_resume_sessions` (Utils/Exchange.py:183) — function
Discards captured sessions whose label, statement fingerprint, or plan fingerprint has since changed.

### `_prune_stale_phase1_exchange_history` (Utils/Exchange.py:205) — function
Discards exchange-history reservations whose statement or accepted-plan epoch changed, restoring the sample allowance for genuinely new contexts.

### `_clear_phase1_exchange_history` (Utils/Exchange.py:227) — function
Explicitly forgets all exchange reservations touching any of the given labels (e.g. after a plan-epoch change).

---

## 2.13 `scripts/Utils/Candidates.py`

The Phase-1/Phase-2 candidate state machines and the retry lifecycle.

### `_prune_stale_generation_candidates` (Utils/Candidates.py:15) — function
Removes stored Phase-1 Lean candidates whose blueprint statement fingerprint or plan
fingerprint no longer matches the current context, so stale generated code can't be reused
after a statement/plan change.

### `_candidate_plan_fingerprint` (Utils/Candidates.py:40) — function
SHA-256 fingerprint of the exact "plan contract" a node's Lean code was generated under —
either the blueprint-direct-generation record or the design-plan entry. Detects when a
candidate's generating strategy changed and it must be invalidated.

### `_design_plan_public_surface_fingerprint` (Utils/Candidates.py:71) — function
Fingerprints only the public Lean surface (declaration headers, helper declarations, typed
members) of one design-plan entry, deliberately excluding decisions/prose — so downstream
nodes detect interface changes without being invalidated by prose-only plan edits.

### `_candidate_is_reusable_uncompiled` (Utils/Candidates.py:90) — function
Whether a stored candidate has passed every deterministic generation gate and may skip
regeneration up to its first compile: a Lean-failed candidate is never reusable, an
explicit `reusable_uncompiled` flag is, and legacy sources are grandfathered.

### `_candidate_hash` (Utils/Candidates.py:113) — function
SHA-256 of stripped candidate code — the canonical identity for candidate comparison and
dedup throughout the candidate-state machinery.

### `_phase2_node_candidate_epoch` (Utils/Candidates.py:117) — function
Fingerprints the complete blueprint/dependency contract for one node (statement fp,
contract fp, repair-context fp) into an "epoch" hash. Phase-2 complete-node candidates are
only valid within the epoch they were produced in.

### `_prune_stale_phase2_node_candidates` (Utils/Candidates.py:134) — function
Drops Phase-2 complete-node candidates whose stored epoch no longer matches the current
epoch, i.e. after any blueprint or dependency contract change.

### `_phase2_node_candidate` (Utils/Candidates.py:158) — function
Returns a deep copy of the current Phase-2 complete-node correction seed for a label
(after pruning stale entries) — the exact rejected statement+body that correction loops
should edit.

### `_store_phase2_node_candidate` (Utils/Candidates.py:168) — function
Persists one exact Phase-2 statement+body candidate together with its current rejection
evidence, tracking `seen_states` hashes so a repeated candidate/failure pair is recognized
and never re-paid for. Also routes the failure into the diagnostic-evidence ledger with
the right kind/lifetime.

### `_note_phase2_candidate_correction` (Utils/Candidates.py:272) — function
Appends a correction fingerprint to a candidate's `attempted_corrections` list (bounded to
24) so the same correction approach is not retried against the same candidate.

### `_clear_phase2_node_candidate` (Utils/Candidates.py:287) — function
Deletes a node's Phase-2 candidate (on acceptance), then prunes stale diagnostic evidence
and re-syncs the generation-feedback projection.

### `_finding_obligation_ids` (Utils/Candidates.py:294) — function
Maps a human-readable deterministic `SkeletonFinding` to a set of stable obligation IDs by
pattern-matching the message text — giving findings stable identities so two candidate
revisions can be compared for progress without model judgment.

### `_candidate_obligation_universe` (Utils/Candidates.py:350) — function
Builds the full deterministic contract surface (set of obligation IDs) a candidate for the
given labels must satisfy: file-level policies plus per-label target presence/kind,
required dependencies, and planned helpers with their kinds and members.

### `_evaluate_phase1_candidate` (Utils/Candidates.py:399) — function
Runs the complete deterministic Phase-1 gate on candidate code and returns
`(obligation universe, violated obligations, raw findings)` — the scoring function behind
monotonic candidate transitions.

### `_lean_error_count` (Utils/Candidates.py:431) — function
Counts `:<line>:<col>: error:` occurrences in Lean output (falling back to 1 for nonempty
output), used as the progress metric between two failed compiles.

### `_candidate_transition_decision` (Utils/Candidates.py:438) — function
The core monotonicity rule: decides whether a proposed candidate may replace the stored
best for the same statement/plan epoch. Accepts on initial candidate, same-hash evidence,
deterministic improvement, semantic-rejection revisions, Lean pass, or Lean error-count
reduction; rejects deterministic regressions and no-progress changes.

### `_upgrade_candidate_entry` (Utils/Candidates.py:491) — function
Lazy migration: re-evaluates a pre-migration stored candidate through the deterministic
gate and fills in all monotonic-state fields so old saved state participates in the new
transition logic.

### `_working_candidate_payload` (Utils/Candidates.py:529) — function
Extracts the fields to persist as a "working candidate" — a deterministic-clean compiler
intermediate kept separately from the monotonic best, so corrections can continue from the
latest diagnostics without displacing the rollback point.

### `_may_retain_working_candidate` (Utils/Candidates.py:565) — function
Predicate for whether a non-best proposal qualifies as a usable compiler-transaction step:
not accepted as best, no deterministic regression, Lean-failed, from a compile-related
source, and non-empty code.

### `_store_generation_candidates` (Utils/Candidates.py:582) — function
The central Phase-1 candidate persistence routine (~480 lines): parses proposed code,
groups labels into atomic components via shared helper ownership, checks plan-epoch
staleness, evaluates each component with the deterministic gate, and applies
`_candidate_transition_decision` per label — installing accepted improvements as the new
best, recording rejections, optionally keeping a working intermediate, and writing
semantic/compiler/deterministic evidence into the diagnostic ledger with correct
lifetimes. Returns the labels actually stored.

### `_reusable_uncompiled_candidate` (Utils/Candidates.py:1068) — function
Rehydrates a complete pre-audit `Phase1LayerCandidate` from stored candidates without a
model call: every requested label must have deterministically valid persisted
code/imports/preamble, delivered target names must match exactly, and the recomposed
module must pass all skeleton findings; otherwise returns None and generation runs.

### `_retained_generation_candidate_code` (Utils/Candidates.py:1179) — function
Composes the exact best stored candidate module for the given labels, including ones that
still have deterministic or Lean failures — correction loops need the exact retained text
so a rejected patch can't become their editing baseline.

### `_salvage_partial_phase1_response` (Utils/Candidates.py:1224) — function
When a model response omits some requested targets, stores the delivered declarations as
candidates, then re-validates each fully-delivered component and marks it reusable —
preserving independently valid work from an incomplete response.

### `_semantic_repair_candidate` (Utils/Candidates.py:1314) — function
Mandatory continuation after a semantic (statement-alignment) rejection: rehydrates the
exact rejected compiling candidate, gathers per-label critic evidence, and calls
`_revise_semantic_candidates` to produce a corrected candidate before ordinary generation
is allowed — so precise critic feedback never becomes a cold restart.

### `_generation_candidates_for` (Utils/Candidates.py:1416) — function
Returns the latest usable rejected candidate code for labels as one compact annotated text
block for prompt injection, preferring the working (compiler-intermediate) code over the
monotonic best because it carries the newest diagnostics.

### `_clear_generation_candidates` (Utils/Candidates.py:1457) — function
Forgets stored candidate Lean for the given labels (normally on statement acceptance);
with `include_shared_components=True` it also clears every candidate sharing helper code
with a changed label, since that stored code is one atomic unit.

### `_retry_lifecycle_key` (Utils/Candidates.py:1501) — function
Trivial key builder `"{stage}:{label}"` for the retry-lifecycle store.

### `_retry_next_tier` (Utils/Candidates.py:1505) — function
Returns which model tier ("base" or "escalation") the next attempt for a label/stage
should use, based on the recorded lifecycle state for the current statement fingerprint —
so batching can't reset a node's escalation provenance.

### `_record_retry_failure` (Utils/Candidates.py:1516) — function
Advances each label's retry lifecycle monotonically through base → escalation → exhausted
for its exact statement version; returns the set of labels that reached "exhausted". A
later base-tier report cannot demote a node already at escalation.

### `_clear_retry_lifecycle` (Utils/Candidates.py:1588) — function
Removes retry-lifecycle entries for the given labels (optionally restricted to one stage),
e.g. after acceptance.

### `_prune_stale_retry_lifecycle` (Utils/Candidates.py:1601) — function
Discards retry history whose label is gone or whose statement fingerprint no longer
matches, so a changed statement restarts at base tier.

---

## 2.14 `scripts/Utils/ModelCalls.py`

Model runner construction, cancellation, and the `_call_model` choke point.

### `_default_fast_runner_specs` (Utils/ModelCalls.py:15) — function
Chooses the default two-tier model policy (cheap batched tier + stronger escalation tier):
OpenAI mini/nano vs. full models if `OPENAI_API_KEY` is set, else Anthropic haiku vs.
sonnet/opus, else local Codex models — so the command works with no API billing.

### `_make_runner` (Utils/ModelCalls.py:49) — function
Thin factory around `get_runner`: builds a model-backend runner from a spec string with
timeout/readonly/effort/skill-file/resume-session options.

### `_ModelCallControl` (Utils/ModelCalls.py:71) — class
Thread-safe handle to cancel one in-flight model call: `attach(runner)`,
`detach(runner)`, `cancel()`.

### `_call_model` (Utils/ModelCalls.py:99) — function
The single choke point for every model invocation: picks base vs. escalation runner spec,
resolves/records resumable backend sessions (resuming after timeouts, dropping on other
failures), runs the prompt, and emits full `model_call` telemetry with stored
prompt/response artifacts. Environment errors and exhausted transport retries propagate so
the run halts with saved state instead of burning repair budget against a dead backend;
other failures return an error/timeout `CallResult`.

---

## 2.15 `scripts/Utils/Sections.py`

Generated-section paths, compile fingerprints, the olean cache, and object probes.

### `_state_path` (Utils/Sections.py:15) — function
Returns the path `SCRATCH_DIR/<name>/skeleton_state.json` where run state is persisted.

### `_section_module` (Utils/Sections.py:19) — function
Maps a blueprint name and section number to its Lean module name
(`AutoBlueprint.Generated.<Base>.SkeletonNN`) and source file path.

### `_lake_olean_path` (Utils/Sections.py:26) — function
Computes the `.lake/build/lib/lean/...olean` path corresponding to a generated source.

### `_lean_environment_fingerprint` (Utils/Sections.py:31) — function
Hashes the Lean command plus `lean-toolchain`, `lakefile.lean`, and `lake-manifest.json`
contents, so cached compiled objects are invalidated when the toolchain or dependency
environment changes.

### `_section_exact_source_fingerprint` (Utils/Sections.py:44) — function
SHA-256 of a section file's exact bytes; used for state restoration and final publication
where every source byte matters.

### `_section_object_source_fingerprint` (Utils/Sections.py:54) — function
Hashes only the parts of a section's source that can affect its importable Lean object:
theorem/lemma proof bodies are reduced to their headers while definitions, structures,
imports, options, and preamble stay exact; falls back to the exact-source hash if parsing
fails, keeping reuse conservative.

### `_section_compile_fingerprint` (Utils/Sections.py:98) — function
Combines the Lean environment fingerprint, the section's object-source fingerprint, and
the compile fingerprints of every imported generated module into one cache key — so an
opaque proof edit doesn't cascade rebuilds through importers, but statement/definition
edits do.

### `_migrate_section_compile_fingerprints` (Utils/Sections.py:121) — function
On resume, upgrades pre-v2 compile-fingerprint keys by recomputing the whole section graph
topologically for sections whose objects exist, avoiding a one-time full rebuild on
`--continue`.

### `_section_objects_exist` (Utils/Sections.py:171) — function
True iff both the sibling `.olean` and the `.lake` build `.olean` for a section exist.

### `_mark_section_compiled` (Utils/Sections.py:175) — function
Stamps a section's `compile_fingerprint` with the current environment/source/imports
fingerprint after a successful build.

### `_compile_section_olean` (Utils/Sections.py:183) — function
Compiles one section to an olean via `_compile_module_olean`, marking the section compiled
on success or clearing its fingerprint on failure; returns the attempt object.

### `_phase1_integration_gate_path` (Utils/Sections.py:194) — function
Returns the scratch path for the run's Phase-1 integration gate file.

### `_generated_lake_module_dir` (Utils/Sections.py:198) — function
Returns the `.lake` build directory holding compiled objects for one blueprint's generated
modules.

### `_discard_section_objects` (Utils/Sections.py:211) — function
Deletes both compiled `.olean` objects for a generated source while keeping the source.

### `_discard_section_artifacts` (Utils/Sections.py:219) — function
Deletes an abandoned (never frozen) section's source file and its objects, so later
generation calls that glob the generated directory can't pick up an orphan and resolve
imports against a stale `.olean` from an earlier run.

### `_statement_surface_probe_code` (Utils/Sections.py:234) — function
Builds a disposable diagnostic variant of a module in which only target
theorem/def/instance bodies are replaced by `sorry` (structures left intact); returns the
probe code and the changed names. Never accepted or persisted — it isolates whether
compile cost lives in the interface or the body.

### `_run_statement_surface_object_probe` (Utils/Sections.py:275) — function
Writes the statement-surface probe to a uniquely named scratch file, object-compiles it
under the usability timeout, and always cleans up the probe artifacts. Used after an
object-build timeout to run the statement-only control.

### `_object_gate_evidence` (Utils/Sections.py:304) — function
Classifies an object-build failure deterministically into `(failure_class, evidence)`
without model guessing: non-timeouts are `object_compile`; a Phase-1 timeout (bodies
already deferred) is `interface_usability`; for a completed Phase-2 node it runs the
statement-only control probe — probe passes → `implementation_object`, probe also times
out → `interface_usability`, inconclusive → `object_compile`.

### `_phase1_interface_usability_evidence` (Utils/Sections.py:388) — function
Normalizes Phase-1 plain-check timeouts/heartbeat exhaustion (where bodies were already
`sorry`) into a canonical interface-usability evidence block instructing bounded named
representations rather than harder proving or blueprint decomposition.

### `_phase1_interface_prompt_rule` (Utils/Sections.py:428) — function
Turns diagnosed interface-usability feedback into the prompt rule injected for the
correction call: allows same-node named structural declarations, forbids invented
blueprint lemmas, and permits an explicit NEEDS-DECOMPOSITION answer.

### `_compile_fast_candidate_object` (Utils/Sections.py:448) — function
Runs the fast pipeline's bounded object-compile gate on a candidate file, records
telemetry for the compilation and (on failure) the usability-gate classification; returns
`(attempt, failure_class, evidence)`.

---

## 2.16 `scripts/Utils/StateIO.py`

Run-state persistence: `_save_state`, `_save_ctx_state`, `_load_state`, and artifact pruning.

### `_save_state` (Utils/StateIO.py:15) — function
Serializes the entire run state to `skeleton_state.json` (schema version 29): section
entries with source hashes and per-label fingerprints, plus a large scheduler payload —
quarantine, local group partitions, generation feedback, the diagnostic-evidence ledger,
dependency observations, Phase-1 and Phase-2 candidates, exchange history, model resume
sessions, retry lifecycle, design/semantic/alternate plans, blueprint-direct-generation
records, the pending repair boundary, the Phase-2 repair queue/active entry, and workflow
flags. Every sub-payload is filtered so only entries matching current statement
fingerprints are persisted, guaranteeing a resume can't replay stale state.

### `_save_ctx_state` (Utils/StateIO.py:774) — function
Takes a single coherent snapshot of the run's mutable scheduler state under `_STATE_LOCK`
via deep copies, then delegates to `_save_state` — so a UI stop or outer retry can save
mid-flight without serializing dictionaries that Phase 1 workers are still mutating.

### `_load_state` (Utils/StateIO.py:839) — function (~830 lines)
The resume (`--continue`) loader: parses the persisted JSON state and reconstitutes every
scheduler store (quarantine, partitions, feedback, diagnostic evidence, candidates, retry
lifecycle, repair boundary/queue, plan entries, blueprint-direct flags, exchange history,
resume sessions), aggressively validating each entry against current node labels and
statement fingerprints so stale state is dropped rather than trusted. It then rebuilds the
kept `Section` list — discarding duplicate-owner sections, salvaging
modified-but-recompilable files, deferring sections whose imports went stale, and
recompiling missing `.olean`s — and returns the surviving sections.

### `_prune_stale_generated` (Utils/StateIO.py:1668) — function
The `--continue` analog of deleting the generated dir: removes `Chunk*`/`Skeleton*`
`.lean`/`.olean` artifacts (including lake-build oleans) not owned by a kept section, so
agent runners can't mine outdated implementations whose statements predate repairs.

---

## 2.17 `scripts/Utils/Prompts.py`

Prompt-context builders (digests, dependency interfaces) and the shared prompt builders.

### `_decl_interface_text` (Utils/Prompts.py:15) — function
Extracts the useful frozen interface of one declaration: strips theorem proofs and
deferred def/abbrev bodies down to the header/type, keeps completed definition bodies
(they carry definitional meaning), truncates oversized bodies.

### `_frozen_interface_digest` (Utils/Prompts.py:38) — function
Builds a module-grouped interface digest of frozen declarations for prompt inclusion.
Budgeting is module-granular: over budget, the oldest non-priority modules are dropped
whole and named explicitly — never a mid-declaration cut.

### `_minimal_dependency_interface` (Utils/Prompts.py:86) — function
Computes the smallest complete generated-dependency interface a target group needs: direct
non-Mathlib `uses` outside the group, plus generated declarations transitively referenced
from those interfaces. Raises `ValueError` if any advertised dependency is absent — the
deterministic completeness gate ensuring no model call launches with a missing dependency
context.

### `_phase1_dependency_interface_chars` (Utils/Prompts.py:187) — function
Measures (in characters) the complete frozen dependency interface for one candidate group,
feeding the group-partitioning budget logic.

### `_frozen_decl_for_label` (Utils/Prompts.py:203) — function
Looks up the frozen interface text of one label's declaration among non-deferred sections.

### `_downstream_proof_context` (Utils/Prompts.py:215) — function
For top-down proof search, builds compact read-only context showing how higher-level
(already-established) theorem consumers use the current frontier's targets — blueprint TeX
plus frozen Lean interface for up to 8 consumers — carrying intended usage downward
without a Lean import cycle.

### `_format_library_candidates` (Utils/Prompts.py:256) — function
Renders a subset of deterministic library-search candidates (declaration, module,
file:line, matched term, snippet) in the same shape as the global search summary, for
prompt embedding.

### `_library_context_for` (Utils/Prompts.py:279) — function
Slices the run-global library candidate list down to candidates whose matched search term
came from the target nodes or their direct dependencies (capped at 12) — repeating the
whole-blueprint list in every prompt is the largest fixed prompt cost.

### `_local_node_summary` (Utils/Prompts.py:304) — function
Node-graph orientation for prompts limited to the targets, their direct dependencies, and
their direct consumers — instead of a whole-graph summary that scales with blueprint size.

### `_conjecture_policy_prompt` (Utils/Prompts.py:322) — function
If any target label is a conjecture node, returns the policy-specific prompt block: under
`record`, express the conjecture as an exact proposition-valued `def`; under `attempt`,
treat it as an ordinary theorem-like node.

### `_text_only_budget_rule` (Utils/Prompts.py:353) — function
Shared prompt bullet stating that generation calls are text-only with a fixed wall-clock
budget: no shell/search/file tools exist, supplied context is already verified, and the
call must never end without emitting code.

### `_common_rules` (Utils/Prompts.py:380) — function
Assembles the hard-constraint block shared by generation prompts: blueprint TeX is the
sole source of truth, exact Lean names, Mathlib-owned name rules, no
`sorry`/`axiom`/invented helpers, import discipline, the `NEEDS-DECOMPOSITION` protocol,
unavailable imports, library candidates, the Lean idiom cheatsheet, and conjecture policy.

### `_design_plan_rules` (Utils/Prompts.py:426) — function
Variant of the constraint block for JSON interface-planning calls: return JSON only, one
contract per label, no bodies/proofs, helpers restricted to structure/inductive/class
type interfaces.

### `_initial_declaration_prompt` (Utils/Prompts.py:461) — function
Prompt for the provisional declaration-environment pass that bootstraps Phase 1: create
every requested Lean name with a faithful provisional signature (`:= by sorry` bodies) so
consumers can elaborate; explicitly not a statement-acceptance call and never allowed to
return `NEEDS-DECOMPOSITION`.

### `_skeleton_prompt` (Utils/Prompts.py:569) — function
The main Phase-1 statement-generation prompt (`BLUEPRINT-SKELETON-SECTION`): one
statement-only declaration per target, with feedback block, minimal dependency interface,
dependency contract table, design-plan block, and local node summary; delegates to
`_initial_declaration_prompt` when `initial_only`.

### `_targeted_skeleton_patch_prompt` (Utils/Prompts.py:700) — function
Prompt for replacing only specific failing declarations inside a large generated section:
replacement-only rules, plan-owned-helper allowances, persisted unresolved rejection
constraints, the deterministic audit findings, and the current focused declarations.

### `_proof_prompt` (Utils/Prompts.py:884) — function
The Phase-2 prompt (`IMPLEMENT-FROZEN-DECLARATION-BODIES`) asking the model to replace
terminal `sorry`s with real bodies: headers immutable, bodies self-contained tactic
blocks, must visibly use listed dependency names and follow the blueprint proof structure,
with frozen interface digest and downstream-consumer context attached.

---

## 2.18 `scripts/phase1.py`

Phase 1: interface planning, statement generation, freezing, audits, and failure escalation.

### `_phase1_context_atomic_units` (phase1.py:15) — function
Splits a scheduling group into atomic units, keeping persisted shared-helper candidate
components indivisible so partitioning never splits a component that must be generated
together.

### `_partition_phase1_groups_by_dependency_context` (phase1.py:32) — function
Deterministic, model-free pre-dispatch pass that greedily splits Phase-1 candidate groups
so each part's exact dependency-interface size fits the soft budget; atomic
components/singletons that exceed it still get their complete interface, with telemetry
recording the overage.

### `_coalesce_phase1_semantic_correction_waves` (phase1.py:115) — function
The opposite optimization: batches compatible `semantic_rejected` singleton corrections
(same dependency imports, same next retry tier, mutually independent statements) into
shared correction waves up to a cap, saving model calls while keeping per-label evidence.

### `_patchable_skeleton_labels` (phase1.py:204) — function
Decides whether findings are declaration-local enough for in-place targeted repair:
returns the ordered failing labels, or empty when any finding is unattributed, none target
section labels, or the set exceeds `TARGETED_DECL_PATCH_MAX_LABELS`.

### `_isolated_deterministic_failure_labels` (phase1.py:222) — function
Returns the attributable failing labels only when they form a proper subset of the
section — empty for section-wide or unattributable failures — enabling isolation of just
the bad members.

### `_apply_skeleton_replacements` (phase1.py:235) — function
Merges a patch response's replacement declarations into an existing parsed section:
swaps/inserts declarations for the patch labels, preserves accepted plan-owned helpers
unless explicitly replaced, discards omitted unplanned helpers, deduplicates module-global
names, and validates/strips unavailable imports post-merge. Returns `None` if required
replacements are missing.

### `_targeted_patch_skeleton_decls` (phase1.py:375) — function
The full targeted-patch transaction: identifies patchable labels, builds the patch prompt,
runs the model call through the Phase-1 exchange dedup/sample-limit ledger (with a single
escalation retry on singleton timeout and byte-identical-replay detection), canonicalizes
the returned Lean, and applies it via `_apply_skeleton_replacements`.

### `_retry_statement_patch_compile_once` (phase1.py:564) — function
Gives one failed semantic statement correction exactly one base-tier retry with its
precise Lean compiler errors: attributes findings to corrected declarations, runs the
targeted patch, normalizes deferred bodies, re-runs the deterministic audit and Lean
compile; never expands into the hard-timeout ladder.

### `_design_plan_order` (phase1.py:663) — function
Orders labels root-first using the top-down statement layering, giving a
traversal-independent planning order.

### `_sync_design_plan` (phase1.py:675) — function
Rebuilds `ctx.design_plan`, the compatibility text rendering of the structured design-plan
contracts.

### `_transition_phase1_generation_epoch` (phase1.py:686) — function
The single atomic invalidation point when a node's authoritative interface epoch changes:
under `_STATE_LOCK` clears generation candidates (including shared components), Phase-1
retry lifecycle and exchange history, releases quarantine and local partitions, resyncs
the plan, and prunes candidate/plan-scoped diagnostics while retaining statement-scoped
semantic facts; records telemetry.

### `_invalidate_descendant_design_plans_for_changed_interfaces` (phase1.py:740) — function
When a dependency's interface becomes untrusted, drops the design plans, alternates,
candidates, and retry state of all dependency descendants planned against the old surface,
forcing them to re-plan against the new provider contract.

### `_invalidate_blueprint_direct_descendants_after_freeze` (phase1.py:785) — function
Checks whether a blueprint-direct-generated node's accepted public interface fingerprint
changed after freezing, and if so invalidates the design plans of its descendants so they
replan against the new interface.

### `_uses_blueprint_direct_generation` (phase1.py:824) — function
Predicate: has this label's exact current statement version activated the
"blueprint-direct" strategy (stopped trusting its interface plan and generates Lean
straight from the blueprint)? Used throughout as a guard to skip plan-based checks.

### `_activate_blueprint_direct_generation` (phase1.py:833) — function
The interface-plan circuit breaker: switches a set of labels to blueprint-direct
generation, storing per-label failure evidence, clearing plan audit/rejection metadata,
transitioning the generation epoch, and logging the activation. Idempotent per statement
fingerprint.

### `_prune_stale_blueprint_direct_generation` (phase1.py:978) — function
Drops blueprint-direct entries whose node vanished or whose statement fingerprint changed,
and repairs a pre-v8 persistence bug where one shared multi-node audit was copied into
every activated entry.

### `_preserve_plan_entry_progress` (phase1.py:1023) — function
When a plan entry is replaced for an unchanged blueprint statement, carries forward the
`origin` provenance marker and the max of bounded retry counters, preventing corrections
from resetting a repeatedly-rejected node to revision zero and looping forever.

### `_prune_stale_design_plan` (phase1.py:1052) — function
Continuation/startup hygiene: removes design-plan entries, alternates, and semantic-plan
entries whose node disappeared, statement fingerprint changed, or schema version is
outdated; also prunes stale blueprint-direct state and transitions the generation epoch
for everything invalidated.

### `_render_semantic_plan_entry` (phase1.py:1108) — function
Renders one advisory semantic-plan entry (representation, stable vocabulary, obligations,
provider capabilities) as compact non-Lean prompt text used to keep independently
generated frontiers semantically coherent.

### `_repair_json_string_backslashes` (phase1.py:1154) — function
Scans model-emitted JSON and escapes lone TeX backslashes (e.g. `\dagger`) inside quoted
strings without touching valid escapes or structure. Protects against JSON parse failures
and silent control-escape corruption of math.

### `_extract_json_object_with_key` (phase1.py:1213) — function
Robust JSON extractor that decodes the first top-level object containing a required key
(trying backslash-repaired text first, and fenced code blocks), avoiding the shared loose
extractor's failure mode of picking up a nested object from a malformed outer one.

### `_parse_semantic_plan_entries` (phase1.py:1254) — function
Parses and mechanically sanitizes the model's compact global semantic plan: validates
labels, vocabulary names, obligations, readiness values, and provider requirements against
statement `\uses` authorization; drops ambiguous vocabulary owned by multiple nodes.
Malformed entries never block Phase 1 (callers fall back to deterministic guidance).

### `_semantic_plan_fallback_entry` (phase1.py:1393) — function
Builds the deterministic blueprint-only advisory entry used when semantic-planning output
is incomplete for a label.

### `_render_design_plan_entry` (phase1.py:1414) — function
Canonical prompt rendering of one typed interface contract: target signature, owned
helpers with exact declarations or typed members, and design decisions.

### `_normalize_plan_helper` (phase1.py:1456) — function
Validates and normalizes one raw helper dict from a plan response: enforces identifier
syntax, an allowed kind, nonempty typed members with size/uniqueness bounds; returns
`None` (rejecting the helper) otherwise.

### `_normalize_plan_mathlib_aliases` (phase1.py:1502) — function
Deterministically rewrites generated spellings for Mathlib-settled nodes into their
authoritative `\lean` declaration names at ingestion, avoiding a paid correction call for
an exact, mechanical translation.

### `_parse_design_plan_entries` (phase1.py:1528) — function
Parses a versioned contract-plan JSON response into per-label entries: requires the target
Lean name to appear in the signature, normalizes helpers and Mathlib aliases, and rejects
entries with invalid/duplicate helpers or helpers owned by multiple labels or colliding
with target names.

### `_design_plan_audit_fingerprint` (phase1.py:1609) — function
SHA-256 identity of one blueprint contract (label, statement fingerprint, versioned
contract payload, paper text hash). Used to cache audit acceptance/rejection and detect
unchanged correction attempts.

### `_findings_require_plan_revision` (phase1.py:1630) — function
Predicate over skeleton findings deciding whether candidate errors originate in the
accepted interface plan versus generation errors, so contract closure failures are routed
to plan correction instead of compiler patching.

### `_mentions_lean_symbol` (phase1.py:1659) — function
Regex check for whether text mentions a generated Lean name as a standalone identifier or
namespace prefix. Core primitive for closure and dependency-surface analysis.

### `_design_plan_public_interface_fragments` (phase1.py:1670) — function
Collects the Lean-aware text fragments constituting one plan's public interface: parsed
target declarations, exact helper declarations, and typed member types. Prose excluded —
prose cannot satisfy a declaration-level dependency.

### `_design_plan_dependency_closure_details` (phase1.py:1700) — function
For one label, classifies every statement dependency as represented or missing on the
typed plan surface, returning required/represented/missing lists plus which missing
providers are pipeline-generated.

### `_design_plan_owner_helper_cycle_paths` (phase1.py:1738) — function
Builds a mention-graph among a plan's target and its helpers and searches for
target→helper→target declaration-order cycles that would make the planned declarations
impossible to order.

### `_planned_target_members` (phase1.py:1790) — function
Extracts the deterministic dotted public surface of a planned
`structure`/`class`/`inductive` target declaration — field or constructor names after
`where` — without guessing methods from prose.

### `_planned_target_result_type` (phase1.py:1820) — function
Returns the top-level result type of a planned target declaration by scanning for the
first colon outside brackets. Used to connect a target value to a plan-owned interface
helper so the helper's members count as target surface.

### `_lean_surface_tokens` (phase1.py:1866) — function
Tokenizes a declaration surface (comments stripped) into a tuple for conservative exact
comparison — stricter than Lean equivalence, so false negatives just keep the normal retry
route while positives prove a plan defect.

### `_contains_token_sequence` (phase1.py:1885) — function
Whether one exact Lean token sequence occurs contiguously inside another token tuple; used
to verify a planned typed member appears verbatim in an emitted helper.

### `_candidate_exactly_realizes_plan` (phase1.py:1898) — function
Proves an emitted Phase-1 interface is a faithful copy of its accepted plan: token-exact
target header match plus, for every plan-owned helper, matching kind, complete member set,
and verbatim typed member declarations. A positive result means regeneration under the
unchanged plan cannot fix a semantic failure — the plan must change.

### `_candidate_target_exactly_realizes_plan` (phase1.py:2013) — function
Narrower variant checking only that the emitted target header token-exactly copies the
planned target signature — sufficient for diagnosing a compiler-rejected identifier that
the plan itself mandates.

### `_plan_owned_unknown_lean_names` (phase1.py:2063) — function
Intersects compiler-unknown names with the tokens of the plan's target signature and full
planned surface, attributing compile failures to the plan.

### `_phase1_compile_plan_defects` (phase1.py:2089) — function
Classifies compile failures that regeneration cannot fix under the current plan: a
plan-copied unknown Lean name in an exactly-realized target/interface, or an identical
error shape recurring under the same plan fingerprint with an exact realization. Returns
per-label defect descriptions routed to plan correction.

### `_plan_realized_semantic_rejections` (phase1.py:2157) — function
Returns the semantically-rejected labels whose emitted code exactly realizes a
non-candidate-origin plan — rejections regeneration cannot fix, which must go to plan
revision instead.

### `_revise_audit_reported_plan_defects` (phase1.py:2175) — function
When the independent statement critic attributes a failure to the plan (origin
`plan`/`both`) with concrete missing blueprint obligations, revises those plan-owned
contracts before retrying Lean generation.

### `_activate_audit_reported_candidate_plan_defects` (phase1.py:2257) — function
The sibling path for candidate-owned contracts (`origin == phase1_candidate`): since
there is no independent plan object to repair, audit-reported plan omissions switch those
labels to blueprint-direct generation instead.

### `_audit_plan_revision_request` (phase1.py:2336) — function
Convenience builder: runs `_revise_audit_reported_plan_defects` and, if anything was
revised, packages the retry as a `RepairRequest` with `plan_revision_required` set.

### `_design_plan_symbol_surfaces` (phase1.py:2365) — function
Builds the global symbol table of planned generated declarations: maps each target/helper
name (original and canonical namespaced spelling) to its exposed member set, and each
symbol to its owning blueprint label. Foundation for closure validation.

### `_design_plan_closure_fingerprint` (phase1.py:2402) — function
Fingerprints one contract against the complete planned symbol surface, so cached closure
validation is invalidated when any relevant plan changes.

### `_design_plan_contract_closure_issues` (phase1.py:2418) — function
The core deterministic symbol-table check over plan entries: per label it verifies exactly
one canonical target declaration, no extra public targets, no interface references to
generated nodes outside the statement-dependency closure, no out-of-closure helper
references, every dotted member reference resolvable on the planned owner's surface, and
no target/helper declaration cycles. Returns structured `PlanClosureFinding`s.

### `_design_plan_contract_closure_findings` (phase1.py:2559) — function
Compatibility wrapper grouping structured closure issues into a
`{consumer label: [deduped messages]}` dict.

### `_design_plan_unauthorized_reference_findings` (phase1.py:2572) — function
Filters closure issues down to just the messages for unauthorized dependency references.

### `_design_plan_invalid_mathlib_alias_findings` (phase1.py:2583) — function
Rejects contracts that mention a Mathlib-settled node via its generated label-derived
spelling instead of the authoritative `\lean` declaration name.

### `_design_plan_dependency_findings` (phase1.py:2624) — function
Deterministic dependency gate exposed to the audit: only mechanically conclusive
unauthorized references are rejected; missing `\uses` representation is left to the
semantic alignment audit since it isn't mechanically decidable.

### `_validate_design_plan_contract_closure` (phase1.py:2636) — function
Validates and fingerprints the deterministic plan-to-generation handoff for a label set:
skips labels whose cached `closure_fp` matches, runs closure + Mathlib-alias checks on the
rest, stamps or clears `closure_fp` per result, persists the plan, and records telemetry.

### `_design_plan_closure_repair_components` (phase1.py:2702) — function
Groups closure findings into connected provider–consumer components that must be corrected
atomically. Components come out in plan order.

### `_closure_blocked_labels` (phase1.py:2755) — function
Flattens the repair components into the set of labels that cannot freeze while current
closure findings remain.

### `_closure_findings_for_scope` (phase1.py:2766) — function
Selects the closure findings belonging to every complete repair component that touches a
requested label scope, so corrections always see whole components.

### `_evaluate_design_plan_candidate` (phase1.py:2784) — function
Scores a candidate plan with the live closure rules against an isolated shallow-copied
context, so evaluation can never mutate the run's real plan state; returns a
`DesignPlanCandidate`.

### `_initial_plan_admission` (phase1.py:2821) — function
Decides whether a complete candidate plan is safe to start Phase 1 with: every requested
contract must exist and the entire initial bottom-up-ready frontier must be closure-clean.

### `_initial_plan_repair_costs` (phase1.py:2849) — function
Estimates, in abstract contract-work units, the cost of bounded local closure repair
versus rerunning a full two-lane planning tournament, for the repair-admission decision.

### `_initial_plan_repair_admission` (phase1.py:2871) — function
Fallback admission after both tournament lanes settle: admits a complete near-good plan
whose frontier is nonempty but blocked, only when the estimated scoped repair is cheaper
than a fresh tournament.

### `_merge_design_plan_candidates` (phase1.py:2900) — function
Greedily improves the primary tournament candidate by swapping in the alternate's version
of whole defective closure components, rescoring the full plan after each trial and
accepting only strict score improvements that don't shrink the ready frontier.

### `_design_plan_audit_prompt` (phase1.py:2958) — function
Builds the independent-critic prompt for the interface-plan audit: per-node blueprint TeX,
dependency lists, and rendered contract, plus nearby untrusted contracts and paper
context, with strict JSON output instructions distinguishing `lean_translation_issue`,
`blueprint_issue`, and `needs_decomposition`.

### `_audit_phase1_design_plan` (phase1.py:3051) — function (~290 lines)
Runs the semantic plan audit for uncached entries: reuses cached rejections at the same
fingerprint, applies deterministic dependency rejections first, otherwise calls the model
(with single-label escalation retry), then routes acceptance or per-issue rejection kinds
into an `AlignmentAuditResult`, persisting rejection metadata on each entry.

### `_try_alternate_design_plan_component` (phase1.py:3338) — function
Zero-cost first correction attempt: swaps in retained alternate-plan entries for the
failed labels (preserving retry progress), applying the swap only if the score improves or
closure stays clean; transitions the generation epoch on success.

### `_correct_phase1_design_plan` (phase1.py:3388) — function
The paid plan-correction transaction for one connected contract set: optionally tries the
retained alternate first, deduplicates attempts by an evidence+contract fingerprint per
tier, prompts the model under the lossless contract schema, then applies parsed
corrections only if the contract fingerprints actually changed, preserving progress
counters and transitioning the generation epoch.

### `_phase1_frontier_plan_gateway` (phase1.py:3590) — function (~340 lines)
The just-in-time gate admitting one dependency-ready plan slice to statement generation:
repairs frontier-owned deterministic closure defects (base then escalation), runs the
semantic audit, routes blueprint/decomposition rejections to blueprint repair, corrects
`lean-generation` rejections (with re-closure and re-audit), and raises routed
`RepairRequest`s whenever correction is exhausted. Accepted audits are fingerprint-cached
so an unchanged frontier pays this gate once.

### `_closure_component_evidence` (phase1.py:3927) — function
Renders the complete correction evidence string for one connected closure component —
findings, editable providers with missing members, and read-only provider context.

### `_closure_component_score` (phase1.py:3971) — function
Monotonic 3-tuple score for one closure component's health: (total finding messages,
blocked labels, affected consumers). Lower is better.

### `_closure_correction_stage` (phase1.py:3986) — function
Chooses the next provider-aware edit set for a component: missing-member defects are fixed
first with the provider plus only the consumers imposing requirements on it; then
remaining authorization/alias/cycle defects edit consumers only.

### `_correct_plan_closure_component_from_snapshot` (phase1.py:4018) — function
Makes one bounded base-tier closure correction for a component against an isolated
deep-copied plan snapshot (never mutating the live plan), scoring before/after; returns a
`PlanClosureCorrectionResult`. Designed so parallel per-component corrections on the
initial-plan critical path can't interfere.

### `_repair_phase1_design_plan_closure` (phase1.py:4134) — function
Repairs disjoint closure defects in the Phase-1 design plan by fixing each connected
component concurrently from one immutable plan snapshot, so a failed component cannot roll
back a successful sibling: apply zero-cost retained alternates and rescore; correct each
remaining component via model calls in a thread pool; merge only accepted component
entries; re-validate; retain improved-but-failing candidates as alternates and raise a
`RepairRequest` demanding fresh planning for the rest.

### `_design_plan_context_labels` (phase1.py:4361) — function
Computes the small complete plan slice for a set of target labels: the targets plus their
direct providers and direct consumers. Bounds how much of the plan is injected into
prompts.

### `_design_plan_block` (phase1.py:4375) — function
Renders the best available per-node guidance text for a prompt: exact typed contracts when
present, else compact semantic-plan entries, target labels first under a hard character
budget. Appends a "PLAN CIRCUIT BREAKER" block for nodes flagged for blueprint-direct
generation.

### `_compact_dependency_contract_table` (phase1.py:4465) — function
Emits the authoritative dependency graph as compact JSON Lines (label, Lean name,
statement-deps, proof-only deps) for the semantic planner.

### `_semantic_plan_prompt` (phase1.py:4496) — function
Builds the prompt for the compact advisory semantic plan: JSON `contracts` with
representation choices, vocabulary, obligations, provider requirements, and readiness
flags — explicitly forbidding Lean signatures, and stressing that proof-only deps must not
shape public signatures.

### `_ensure_phase1_semantic_plan` (phase1.py:4580) — function (~260 lines)
Creates (or reuses) the one bounded advisory semantic plan for pending nodes with no
pre-Phase-1 repair loop: prunes stale entries; short-circuits for lightweight test
contexts; otherwise fires the planner call with a hedge lane (a second parallel fresh call
if the primary exceeds the hedge threshold or returns incomplete coverage), merges
coverage across lanes, cancels the loser, and fills still-missing labels with
blueprint-only fallback entries.

### `_readiness_repair_components` (phase1.py:4836) — function
Partitions readiness-repair labels into independent connected components (via
transitive-dependency relatedness) so blueprint repairs can proceed concurrently.

### `_phase1_readiness_repair_request` (phase1.py:4877) — function
Wraps confirmed blueprint-source defects (missing proofs, `\notready` markers) into a
`RepairRequest` that authorizes a blueprint TeX edit through the normal repair
transaction.

### `_phase1_source_readiness_request` (phase1.py:4913) — function
Gate run before planning: honors source-authoritative unresolved markers. Flags nodes
carrying `\notready`, conjectures lacking a proof under the `attempt` policy, and
theorem-like nodes without a blueprint proof; records "recorded" open conjectures without
blocking.

### `_readiness_repair_postcondition_findings` (phase1.py:4964) — function
Validates a readiness blueprint repair after the fact: rejects repairs that deleted the
target node, left `\notready` in place, or erased a marker without adding the required
blueprint proof. Pure function over before/after node and TeX-block maps.

### `_phase1_readiness_confirmation_prompt` (phase1.py:5012) — function
Prompt asking a separate critic model to independently confirm planner-reported readiness
gaps from the blueprint source (and a paper excerpt), judging the source rather than
Lean-encoding difficulty.

### `_parse_phase1_readiness_confirmation` (phase1.py:5060) — function
Parses the readiness-confirmation JSON reply into `{label: {readiness, gap}}`, dropping
unknown labels, invalid readiness values, and non-ready verdicts lacking a concrete gap.

### `_phase1_advisory_readiness_request` (phase1.py:5088) — function
Runs the one-shot readiness confirmation for nodes the semantic planner flagged as
non-ready, updates each semantic-plan entry with the verdict, and returns a
blueprint-repair `RepairRequest` only for independently confirmed defects.

### `_blueprint_roots` (phase1.py:5182) — function
Returns the theorem-like labels nothing else depends on — the paper's public results —
used as root obligations for root-first planning.

### `_design_plan_prompt` (phase1.py:5193) — function
Builds the typed interface-plan prompt: a JSON plan of one `target_signature` per node
plus typed structure/inductive/class helpers and semantic decisions — no bodies, no
proofs — with hard rules (root-first design, no assuming conclusions in definitions, only
statement-deps in signatures, one declaration per node).

### `_generate_design_plan_candidate` (phase1.py:5324) — function
Generates one independent full-context plan candidate: loops over label batches, calls the
model, parses entries, retries once on a zero-contract reply with completeness feedback,
and returns the candidate scored via `_evaluate_design_plan_candidate`.

### `_initial_design_plan_tournament` (phase1.py:5404) — function (~280 lines)
Runs the two-lane planning tournament: two independent full-context plan candidates
concurrently, admitting the first whose entire initial dependency-ready frontier is
mechanically closed (cancelling its sibling); else merges the two candidates
component-wise and checks admission; else picks the candidate with the cheapest
scoped-closure-repair estimate; else raises a `RepairRequest` restarting the tournament.
Also computes a per-node alternate fallback plan from the losing lane.

### `_ensure_phase1_design_plan` (phase1.py:5680) — function
Creates or extends the shared root-first typed contract plan for Phase 1: prunes stale
entries; if the plan is empty runs the initial tournament; loops scoped model calls for
still-missing contracts; activates blueprint-direct generation for anything the planner
never delivered; validates contract closure and either defers, repairs, or returns the
closure findings.

### `_bulk_skeleton_prompt` (phase1.py:5906) — function
The one-chunk skeleton-emission prompt: emit the exact Lean statement of every target node
(statements ending in `:= sorry`, no proofs, no auxiliary declarations beyond same-node
structure/class/inductive helpers), given imports, the frozen interface digest, the
dependency-contract table, the design-plan block, and root obligations.

### `_delivered_decl_texts` (phase1.py:6016) — function
Selects from a parsed model reply the complete set of declaration texts covering one
part's labels plus the helpers those targets consume, returning `None` if a shared
helper's target component would be split across parts or any target is missing.

### `_salvage_timeout_declarations` (phase1.py:6061) — function
Recovers syntactically complete target declarations from the partial output of a timed-out
model call (timeouts being the largest wasted-time category); returns the parsed module
and the labels it actually delivered, or `None`.

### `_freeze_section_from_code` (phase1.py:6096) — function (~620 lines)
The central "freeze one section from already-delivered declarations" transaction: runs the
same gates as fresh generation — deterministic checks, Lean compile, alignment audit,
.olean build — and returns the new `Section` list or `None` (caller regenerates), raising
`RepairRequest` when the audit blames the blueprint. Steps: compose/parse module and
normalize `sorry` bodies; deterministic findings (one in-place patch if `allow_patch`);
Lean check with interface-usability short-circuit; broad-Mathlib/narrow-import environment
fallback diagnosis; plan-defect short-circuit; up to `COMPILER_CORRECTION_ROUNDS` targeted
compile patches with candidate retention; optional alignment audit; object-compile gate;
then record the frozen or candidate section state.

### `_parallel_initial_emission` (phase1.py:6713) — function
Stage-zero optimization: emits provisional declaration chunks concurrently with a thread
pool, then compiles/installs them sequentially in topological order so Lean sees providers
first, falling back per-chunk to `_freeze_section` on failure.

### `_bulk_skeleton_pass` (phase1.py:6841) — function
One cheap "design pass" that tries to state the whole pending graph in big chunks before
the per-section loop: ensure the semantic plan; delegate to parallel initial emission when
applicable; per chunk call the model (one hard-timeout retry), bail out to the section
loop on refusals or non-Lean replies, freeze each delivered chunk atomically, and on a
failed initial broad chunk shrink the adaptive section size and end the sweep early.

### `_freeze_parts` (phase1.py:7024) — function
Freezes an ordered list of label subgroups, carrying partial success through repairs:
parts fully covered by already-delivered declarations try a no-generation freeze first;
excluded parts are reordered last so healthy work lands before a `RepairRequest` bubbles
up. When Phase-1 alignment is deferred and fragments are independent, freezes them
concurrently.

### `_note_frozen_section` (phase1.py:7195) — function
Advances the persistent adaptive-capacity controller after an accepted section: releases
quarantine/partitions/feedback/candidates/retry state for the labels, records closure-wave
outcomes, and after two clean full-size sections doubles (bounded) the effective section
size.

### `_next_phase1_group` (phase1.py:7245) — function
Chooses the next generation group from the topological order without remixing
known-problematic scopes: quarantined labels go alone, persisted local partitions stay
intact, and otherwise a size-bounded prefix is taken stopping at any
quarantined/protected label.

### `_candidate_component_labels` (phase1.py:7277) — function
Returns the persisted shared-helper atomic component containing a label, validated against
the current frontier; falls back to the singleton on any mismatch.

### `_coalesce_candidate_components` (phase1.py:7300) — function
Reorders a layer's labels so members of each persisted atomic candidate component appear
contiguously, without adding or removing labels.

### `_freeze_section` (phase1.py:7316) — function (~1,330 lines; the largest worker in the file)
The main per-section generation transaction: generate, deterministically check,
compile-fix, audit, and freeze one section (bisecting when needed); attempt 1 at base
tier, attempt 2 escalated. Steps: prompt build and exchange-sample-limit gating; model
call with timeout salvage or router-driven bisection; duplicate-exchange detection with
one-time escalation; decomposition-refusal handling (invalid-Mathlib rejection, isolation
of the refused node, escalation before blueprint repair); ingest + deterministic findings
with plan-revision routing or targeted patch; Lean compile with targeted patch and failure
routing/quarantine; alignment audit with one escalated targeted correction and one
re-audit; object compile; freeze and record. A `finally` discards artifacts on any
non-frozen exit.

### `_run_initial_declaration_pass` (phase1.py:8650) — function
Stage zero: creates one boilerplate file containing every provisional Lean name (so
root-first Phase 1 can elaborate root interfaces) with a single model call; omitted names
are filled with deterministic placeholders. Deliberately runs no Lean, no audits, no
retries.

### `_add_phase1_boilerplate_names` (phase1.py:8771) — function
After a blueprint repair introduces new nodes, appends their deterministic placeholder
declarations to the existing provisional-environment section, updates its labels, rewrites
the file, and discards its stale objects.

### `_generate_phase1_statement_group` (phase1.py:8829) — function
Replaces stage-zero boilerplate with exact Phase-1 statements for a label group before any
checks run: tries base then escalated tier, handles decomposition refusals via a
forced-fresh independent adjudication, ingests the reply, strips self-imports, splices the
replacements into the section's parsed module, salvages partial coverage, and routes
multi-node failures through the shared failure router.

### `_phase1_layer_candidate_code` (phase1.py:9076) — function
Composes a `Phase1LayerCandidate`'s full module code string for compiling or persisting.

### `_phase1_layer_candidates_code` (phase1.py:9085) — function
Concatenates all declarations across several layer candidates into one text block for a
single batched semantic judgment.

### `_subset_phase1_candidate` (phase1.py:9094) — function
Extracts a sub-candidate containing only selected target labels plus their owned local
helpers, in original order; `None` when a clean extraction is impossible.

### `_generate_uncompiled_phase1_candidate` (phase1.py:9130) — function
Generates and deterministically validates a statement candidate without running Lean (the
"semantic-first" lane): reuses a pending semantic-repair or persisted reusable candidate
when available; otherwise generates against a fake section of placeholders, records
candidate plan fingerprints, runs deterministic checks with one targeted patch (or plan
revision), persists the result as a reusable pre-audit candidate, and raises a routed
`RepairRequest` on unresolved findings.

### `_revise_semantic_candidates` (phase1.py:9301) — function
Applies exactly one exact-feedback targeted revision to audit-rejected candidates only:
subsets each candidate to its rejected labels, runs a targeted patch with the audit reason
as findings, re-runs deterministic checks, escalates confirmed missing-dependency findings
into an authorized blueprint dependency-edge repair, and raises on any residual
deterministic errors.

### `_revise_unusable_interface_plan` (phase1.py:9450) — function
When an exact interface can't build efficiently (operational, not mathematical, evidence):
tries the retained alternate plus one focused base-tier plan correction; failing that,
invalidates only the affected plan entries so the next frontier gets fresh scoped
planning.

### `_route_phase1_compile_failure` (phase1.py:9503) — function (~390 lines)
Classifies and routes one completed Phase-1 compile failure into a `RepairRequest`,
immediately and independently of sibling workers: interface-usability failures walk an
escalation ladder (persist evidence → first-time plan revision → switch to
blueprint-direct generation → bounded retry); otherwise detect plan-realized defects and
revise those contracts; attribute compiler evidence per label so unattributed siblings
don't burn retries; record retry-lifecycle failures and, on exhaustion, route via
`_route_exhausted_phase1_semantics`.

### `_finalize_phase1_accepted_sections` (phase1.py:9889) — function
Runs the expensive steps only after semantic acceptance: builds .olean objects for
accepted candidate sections in parallel (reusing valid fingerprints), routes object
failures through the compile-failure router, then runs the integrated-import gate (a
synthetic module importing every accepted section) — discarding everything if joint import
fails — and finally marks sections refined/frozen.

### `_compile_semantic_phase1_candidate` (phase1.py:10001) — function
Typechecks one generated contract candidate through `_freeze_section_from_code` (with
patching, plan-defect routing, and the object gate deferred), without auditing it.

### `_materialized_phase1_candidate` (phase1.py:10037) — function
Rebuilds a `Phase1LayerCandidate` from the exact post-patch module text Lean actually saw,
so later attribution/subsetting operates on the real failing code.

### `_compile_phase1_candidate_preserving_attributed_siblings` (phase1.py:10064) — function
Compiles one candidate and, on failure, splits the exact post-patch module at
declaration/helper ownership boundaries: recursively re-compiles the subset not attributed
to the failure through all gates, returning accepted sections plus a list of true
failure-owner subsets.

### `_compile_semantic_phase1_candidates` (phase1.py:10140) — function
Typechecks a layer's contract candidates in parallel (with alignment deferred), collecting
per-candidate accepted sections and routed compile failures; on any failure aggregates the
requests (preferring blueprint-authorized ones) and raises with the compiled sections
attached.

### `_compile_and_finalize_semantic_candidates` (phase1.py:10231) — function
Convenience wrapper chaining `_compile_semantic_phase1_candidates` and
`_audit_phase1_layer_candidates`: typecheck, audit, object-build, and integrate; on a
compile-side `RepairRequest` it still audits the partial successes so preservable siblings
pass the same integrated gates.

### `_refine_statement_group` (phase1.py:10270) — function (~430 lines)
Top-down Phase-1 path: refines selected declarations inside the shared provisional
environment without ever exposing failed candidates — all gates run against a disposable
attempt file and the canonical skeleton is replaced atomically only after everything
passes: heal legacy state; generate exact statements; deterministic checks with base then
escalated targeted patches; Lean compile with a loop repairing malformed provisional lower
scaffolding in owned batches; alignment audit with one escalated correction, compile
retry, and re-audit; atomic publish via `os.replace`, object build with rollback, then
mark refined and record.

### `_phase1_candidate_code` (phase1.py:10697) — function
Collects all target declaration texts from a list of candidate `Section`s into one block
for the layer-wide semantic audit.

### `_patch_phase1_candidate_section` (phase1.py:10706) — function
Patches only audit-rejected declarations inside one already-compiled candidate section:
targeted escalated patch, `sorry` normalization, deterministic re-check, Lean re-check
with one compile-retry, and object rebuild — restoring the original file on any failure.

### `_expand_rejected_section_components` (phase1.py:10782) — function
Expands a critic's rejected-label set so every shared-helper component stays atomic: if
any member of a helper-connected component is rejected, the whole component is.

### `_audit_phase1_layer_candidates` (phase1.py:10802) — function (~460 lines)
The layer-wide semantic audit and integration step for typechecked candidates (audit
verdicts are cache-keyed so unchanged declarations are free): run the alignment audit (on
pass: finalize/object-build and return); classify rejections into confirmed dependency
repairs, lean-generation, decomposition, and blueprint buckets; try one-time plan
revisions; expand shared-helper components; persist candidates/feedback/quarantine and
retry lifecycles, routing exhausted labels through `_route_exhausted_phase1_semantics`;
retain accepted siblings from partially rejected sections; then finalize accepted sections
and raise a single richly annotated semantic `RepairRequest`.

### `_semantic_first_failure_request` (phase1.py:11260) — function
The semantic-first-lane analogue of the rejection half of `_audit_phase1_layer_candidates`:
classifies an audit rejection of uncompiled candidates, persists candidates/feedback/retry
lifecycles, and builds (returns, not raises) the routed `RepairRequest` while keeping
independently accepted frozen sections attached.

### `_revise_exhausted_phase1_contracts` (phase1.py:11512) — function
When both generation tiers produced a compiling statement that the critic still rejects,
revises the untrusted plan contract instead of regenerating under the identical plan:
snapshots the rejected candidates as explicit semantic-correction seeds, applies one
evidence-driven plan correction, bumps `semantic_revision_count`, transitions the
generation epoch, and reattaches the seeds as rejected candidates.

### `_revise_decomposition_plans_once` (phase1.py:11648) — function
Before a decomposition verdict is allowed to edit the blueprint, spends the plan's one
unconsumed evidence-driven revision on labels whose plan hasn't been revised yet; a second
decomposition verdict under the revised plan then proceeds to real blueprint
decomposition.

### `_semantic_exhaustion_policy` (phase1.py:11695) — function
Pure policy classifier for what happens next when a label's retry lifecycle is exhausted:
`decomposition` (already blueprint-direct), `blueprint-direct` (candidate-origin plan or
already revised once), or `plan-revision` (unrevised legacy plan). Kept side-effect-free
so historical traces can validate lifecycle changes.

### `_route_exhausted_phase1_semantics` (phase1.py:11714) — function
The unified exhaustion router for every Phase-1 failure source (semantic, compile,
deterministic): scopes evidence and failure identities per label, applies
`_semantic_exhaustion_policy`, activates blueprint-direct generation or plan revision
accordingly, and returns `(decomposition, revised, unresolved)` label sets — first
exhaustion revises the plan, second goes blueprint-direct, only the third routes to
decomposition.

### `_route_phase1_precompile_deterministic_failure` (phase1.py:11855) — function
Coordinator-side routing for deterministic (pre-compile) generation failures: records
retry-lifecycle failures per label and, on exhaustion, splits the original `RepairRequest`
into up to three routed requests — an authorized decomposition request, a plan-revision
request, and an ordinary bounded-retry request.

### `_run_validated_contract_phase1_layer` (phase1.py:12016) — function
Orchestrates one Phase-1 layer in the validated-contract order: generate uncompiled
candidates from the untrusted plan, compile them, then audit final statements exactly
once. A thread pool runs generate-then-compile per group (streaming compile starts as soon
as each group generates); on failures it corrects plan-closure defects, routes
deterministic failures through the shared lifecycle, persists incomplete candidates as
reusable, audits and finalizes the successful siblings, and raises an aggregated request;
on full success hands all compiled sections to `_audit_phase1_layer_candidates`.

### `_run_phase1` (phase1.py:12253) — function (~380 lines)
Runs the one-time Phase 1 statement-skeleton generation for all pending blueprint nodes,
refusing to run once Phase 2 has started: source/advisory readiness gating and
semantic-plan setup; then, for the bottom-up order, an iterative dependency-ready-frontier
loop (grouping/coalescing candidates, running validated-contract layers, draining
independent branches past localized failures, aggregating deferred RepairRequests); or,
for top-down order, layer-by-layer statement refinement per owning section with recursive
failure routing and retry-tier bookkeeping.

### `_phase1_recompile_environment` (phase1.py:12635) — function
The Phase 1 "integration gate": topologically orders all active frozen sections, reuses
compiled `.olean` objects whose fingerprints still match, rebuilds dirty ones, and finally
runs one aggregate import check to prove the reused objects coexist. Sections that fail
have their labels returned to refinement.

---

## 2.19 `scripts/phase2.py`

Phase 2: whole-node repair transactions, the tactic ladder, and proof implementation.

### `_phase2_whole_node_prompt` (phase2.py:19) — function
Model prompt for a Phase 2 whole-node transaction: one complete Lean declaration
(statement + proof/body together, no `sorry`) for a repaired blueprint node, embedding the
dependency contract table, frozen interface digest, the full TeX block, and prior failure
evidence.

### `_phase2_complete_node_correction_prompt` (phase2.py:94) — function
Focused correction prompt for a rejected complete Phase 2 candidate, telling the model to
fix only what the exact rejection requires; policy text adapts to whether the failure was
an interface-usability timeout, implementation-object timeout, or ordinary rejection.

### `_phase2_complete_candidate` (phase2.py:189) — function
Canonicalizes one model response into an owned complete-node module: ingests the Lean,
checks the required declaration is present with no unowned helpers, and composes the
module code; raises `ValueError` otherwise.

### `_phase2_candidate_failure_kind` (phase2.py:210) — function
Classifies a failure-evidence string into a coarse failure kind (`interface_usability`,
`implementation_object`, `deterministic`, `object_compile`, `lean_compile`,
`semantic_alignment`, or `validation`) by prefix matching, used to fingerprint retries.

### `_run_phase2_whole_node_transaction` (phase2.py:226) — function (~330 lines)
Generates/corrects, validates, and freezes one repaired Phase 2 node atomically, retaining
a rejected candidate as the next correction seed: load/re-classify any stored candidate;
choose an attempt sequence (correction-first vs. generation+correction, with
duplicate-correction fingerprint skipping); call the model; handle decomposition refusals
as authorized RepairRequests; ingest and gate via `_freeze_section_from_code`; on failure
store the candidate/evidence and loop; finally raise a non-blueprint-authorizing
RepairRequest when exhausted.

### `_run_phase2_whole_node_repairs` (phase2.py:560) — function
Drives all Phase-2-changed nodes through whole-node transactions bottom-up over
dependency-ready frontiers, running workers in a thread pool; blueprint-authorized worker
failures are enqueued as independent Phase 2 repair transactions while ordinary failures
are aggregated as Lean retries; detects cyclic/stalled graphs.

### `SectionProofOutcome` (phase2.py:677) — dataclass
Per-section result record for Phase 2 proof work: `section`, `proved`, `failed`
(label → evidence), `decomposition` (label → requested helper names),
`decomposition_evidence`.

### `_phase2_unimplemented_body_kinds` (phase2.py:685) — function
Maps definition labels whose Phase 2 implementation is unavailable — a frozen declaration
still ending in terminal `sorry`, or a definition-like node whose declaration was removed
by a repair — so the scheduler treats both alike.

### `_phase2_implemented_definition_labels` (phase2.py:722) — function
Filters accepted Phase 2 labels down to non-theorem-like kinds — the definitions whose
implemented bodies affect reduction and therefore require rebuilding the section's
`.olean` (theorem proofs are opaque to importers).

### `_persist_phase2_section_outcome` (phase2.py:741) — function
Publishes accepted Phase 2 work under the state lock: rebuilds the section object when
definition bodies changed, and on a failed rebuild rolls back the source/object
transactionally, converting the "proved" labels into failures.

### `_phase2_definition_prerequisites` (phase2.py:804) — function
Evidence-bound detector for deferred `def`/`abbrev`/`instance` bodies that a blocked
Phase 2 proof needs unfolded: only selects unimplemented definitions in the blocked node's
dependency closure that the diagnostic explicitly names (or a unique direct one when the
evidence cites opacity/unfolding); never infers new dependency edges.

### `_schedule_phase2_definition_prerequisites` (phase2.py:861) — function
Persists a local implementation-order override (into `ctx.phase2_prerequisite_labels`) for
the found prerequisites, extending them with their missing non-frozen closure, without
editing the blueprint TeX.

### `_phase2_prerequisite_frontier` (phase2.py:917) — function
Returns the next bottom-up implementation frontier drawn from the persisted prerequisite
label set, or `None` when no local override is pending.

### `_prioritized_phase2_declaration_work` (phase2.py:933) — function
During Phase 2, narrows a pending-declaration set to the persisted local prerequisite
closure when it intersects, so prerequisite work preempts unrelated repairs.

### `_phase2_declaration_work_labels` (phase2.py:945) — function
Selects which contract-pending labels the complete-node declaration path should regenerate
now: missing/invalidated prerequisite providers first; if a prerequisite is already frozen
(just body-deferred) it returns empty so the normal body scheduler handles it instead of
creating a duplicate declaration.

### `_route_phase2_proof_outcomes` (phase2.py:978) — function
Routes one Phase 2 proof frontier's collected `SectionProofOutcome`s without widening
blueprint-edit authority: decomposition findings become independent authorized
RepairRequests (or scheduling-only prerequisite requests when the evidence names a
deferred definition body), while ordinary failures become a non-authorizing Lean-retry
RepairRequest.

### `_phase2_prerequisite_request_for_repair` (phase2.py:1103) — function
Converts a misrouted blueprint-repair request into a scheduling-only RepairRequest when
its evidence actually identifies deferred definition bodies, so the pipeline implements
those dependencies instead of editing the blueprint again.

### `_proof_base_round_limit` (phase2.py:1139) — function
Computes the number of base-tier proof rounds a section is allowed: enough for one
feedback retry plus deterministic bisection of the actual batch size down to singletons.

### `_module_decl_texts` (phase2.py:1148) — function
Parses a section's Lean file into a `ParsedModule` plus a name→index map over its
declarations; the shared read primitive for all in-place proof splicing.

### `_write_section` (phase2.py:1154) — function
Recomposes a section's Lean module from its parsed imports/preamble/decls, writes it to
disk, and returns the per-declaration line ranges used for error attribution.

### `_ladder_tactic` (phase2.py:1160) — function
Chooses the free tactic-ladder attempt for one label: a
`first | rfl | omega | norm_num | ring | simp ... | aesop` chain, or a simp call
explicitly naming non-Mathlib dependencies when the dependency-mention contract requires
them to appear in the declaration.

### `_run_tactic_ladder` (phase2.py:1177) — function
Tries to close a section's `sorry`s with zero model calls by splicing ladder tactics into
every candidate, compiling once, keeping only the declarations that pass, reverting
failures (and recompiling to confirm any mixed-outcome kept subset).

### `_apply_proof_batch` (phase2.py:1240) — function
Splices model-returned `:= by` proof bodies into the frozen declarations of a section,
then runs the acceptance gauntlet: full compile with per-declaration error attribution and
rollback, a recompile of any kept subset, the dependency-mention contract (each
non-Mathlib `\uses` name must be visible in the finished declaration), and a semantic
definition-body alignment audit for non-theorem kinds with rollback.

### `_prove_section` (phase2.py:1406) — function (~440 lines)
The main Phase 2 per-section proof driver: fills every terminal-`sorry` body among the
requested labels of one section and returns a `SectionProofOutcome`: add missing
dependency imports; run the free tactic ladder; batched base-tier model rounds with
timeout/failure bisection routing and decomposition-refusal handling; escalated singleton
retries for the residue; error/decomposition bookkeeping; finally
`_persist_phase2_section_outcome` to publish or roll back.

---

## 2.20 `scripts/Utils/BlueprintRepair.py`

Transactional blueprint repair, the boundary audit, dependency edges, and section normalization.

### `_invalidate_after_repair` (Utils/BlueprintRepair.py:19) — function
After a blueprint repair, invalidates directly-changed contracts and defers unchanged
dependency descendants: provisional-environment sections keep their scaffolding with
deleted nodes pruned, directly-hit sections try to retain untouched labels, and pure
descendants are marked `deferred` with their objects discarded.

### `_generated_skeleton_import` (Utils/BlueprintRepair.py:121) — function
Predicate: is an import line one of this blueprint's generated skeleton modules? Used when
rebinding a deferred section's imports.

### `_reactivate_deferred_sections` (Utils/BlueprintRepair.py:126) — function
Rebinds imports and recompiles deferred (unchanged-fingerprint) sections after a repair,
without any model call: sections whose external dependencies are all owned again are
rewritten with fresh generated imports and compiled; passing sections become active,
failing ones drop back to regeneration; with `drop_unready` the still-blocked remainder is
dropped too.

### `_paper_excerpt_for` (Utils/BlueprintRepair.py:248) — function
Builds a deterministic, budget-bounded slice of the source paper for repair prompts: the
paper head plus the paragraphs sharing the rarest terms with the failing nodes' TeX
(scored by inverse token frequency), replacing the earlier practice of sending the whole
paper.

### `_repair_node_context` (Utils/BlueprintRepair.py:289) — function
Assembles the blueprint slice a repair prompt needs: the failing nodes' full TeX,
budget-limited statements of their dependency closure, and statements of up to 8 immediate
consumers (marked as must-keep-compiling).

### `_phase2_component_repair_rules` (Utils/BlueprintRepair.py:351) — function
Returns extra prompt rules (empty before Phase 2) requiring a Phase 2 repair to deliver
the complete dependency-closed helper component for each failing root in one transaction.

### `_scoped_blueprint_repair_prompt` (Utils/BlueprintRepair.py:378) — function
Builds the full RETURN-SCOPED-BLUEPRINT-REPAIR prompt: a JSON `replacements` object
(complete replacement TeX per failing node, new helpers allowed immediately before their
target), with detailed scope/strength rules, the harness note, node context, deterministic
paper excerpt, and the Lean critic evidence.

### `_insert_statement_dependencies` (Utils/BlueprintRepair.py:474) — function
Narrow deterministic TeX transformation adding direct `\uses{...}` edges to one node —
merging into an existing `\uses` or inserting one after `\label` — without touching prose;
returns the updated text plus the set actually added.

### `_dependency_path` (Utils/BlueprintRepair.py:516) — function
BFS over the `uses` graph returning one existing dependency path from `start` to `target`;
used to explain why a proposed edge would close a cycle.

### `_cyclic_dependency_repair_findings` (Utils/BlueprintRepair.py:540) — function
For each proposed dependency edge, checks whether an existing path already runs the other
way and, if so, produces a rejection message describing the cycle it would close.

### `_mark_repair_boundary_pending` (Utils/BlueprintRepair.py:562) — function
Persists a `ctx.repair_boundary_pending` record after a blueprint mutation so a scoped
pre-generation audit runs first: for Phase 1 it targets statement-changed labels; for
Phase 2 component repairs the whole changed component plus original roots, retaining
pre-edit statement text/fingerprints and the original failure evidence.

### `_post_repair_boundary_prompt` (Utils/BlueprintRepair.py:635) — function
Builds the AUDIT-MODEL-BLUEPRINT-REPAIR-BOUNDARY prompt: previous vs. repaired statements,
the dependency/consumer boundary, eligible provider contracts, the label inventory, and a
paper excerpt, asking for a JSON accept/reject with classified issues.

### `_phase2_provider_contract_candidates` (Utils/BlueprintRepair.py:779) — function
Computes which existing dependencies may legally be named as owning a Phase 2 boundary
defect: only non-Mathlib transitive dependencies of the original repair roots —
consumers, siblings, and invented labels never gain edit authority via this route.

### `_audit_post_repair_boundary` (Utils/BlueprintRepair.py:798) — function
Runs the boundary-audit model call once for a repaired component, parses its JSON verdict,
and converts rejections into a `RepairBoundaryAuditOutcome` with routed repair labels,
required dependency edges, decomposition helpers, and provider-repair labels;
unavailable/garbled audits fall back to later gates.

### `_pending_repair_boundary_request` (Utils/BlueprintRepair.py:953) — function
Resumes or performs the persisted post-repair boundary transaction: in `repair` mode it
reconstructs the appropriate RepairRequest (provider-owned transaction, model repair, or
deterministic dependency-edge-only, with fingerprint checks for idempotent resumption); in
`audit` mode it runs `_audit_post_repair_boundary` and either clears the state or stores
the rejection and recurses.

### `_apply_required_dependency_edges` (Utils/BlueprintRepair.py:1116) — function
Transactionally applies critic-confirmed statement `\uses` edges to the TeX draft: rejects
cycle-closing edges up front, edits the files, revalidates the draft, verifies the
validator parsed each new edge, and rolls everything back on any failure.

### `_ScopedBlueprintRepairProposal` (Utils/BlueprintRepair.py:1230) — frozen dataclass
Carrier for one read-only parallel repair proposal: `labels`, `response_text`,
`duration_s`, `repaired_json_backslashes`.

### `_run_scoped_blueprint_repair_proposal` (Utils/BlueprintRepair.py:1237) — function
Runs one read-only scoped-repair model call for one component (escalation runner, no draft
mutation), records telemetry, parses the `replacements` JSON, and enforces that the
returned target set exactly matches the requested labels.

### `_normalized_parallel_repair_components` (Utils/BlueprintRepair.py:1332) — function
Validates a proposed partition of a repair transaction into components: returns them only
when they are non-overlapping, at least two, and exactly cover the transaction's labels;
otherwise `[]` to force the single-repair path.

### `_repair_blueprint_components` (Utils/BlueprintRepair.py:1361) — function
Parallel front-end to blueprint repair: when a valid component partition exists, proposes
each component's repair concurrently in a thread pool, merges the JSON replacements
(rejecting overlaps), and commits once atomically via
`_repair_blueprint(prepared_response=...)`; otherwise delegates directly.

### `_repair_blueprint` (Utils/BlueprintRepair.py:1492) — function (~315 lines)
Runs one transactional blueprint-repair attempt — the only route that edits the
unpublished TeX draft: snapshot content/nodes/fingerprints; run the read-only repair model
(or use a prepared merged response), with timeout bisection into label halves; apply the
scoped replacements via `_write_scoped_blueprint_repair_to`; validate the draft, enforce
readiness-repair postconditions and decomposition helper-orientation (attempting a
deterministic edge fix first); roll everything back on any violation; finally diff
contract fingerprints to report the changed label set.

### `_stuck_state_for` (Utils/BlueprintRepair.py:1806) — function
Finds or creates the `SectionStuckState` for one exact failing label set — deliberately
not merging overlapping sets, so edit/normalization authority stays tied to the precise
scope that exhausted its retries.

### `_section_normalization_prompt` (Utils/BlueprintRepair.py:1825) — function
Builds the NORMALIZE-STUCK-BLUEPRINT-SECTION prompt asking for a single constrained
normalization pass making a repeatedly-failing section's nodes easier to state in Lean
without weakening content; supports agent mode (edit the draft in place) and API mode
(return full replacement `content_tex` JSON).

### `_normalize_stuck_section` (Utils/BlueprintRepair.py:1931) — function
Executes one section-normalization pass with a writable runner: applies/validates the
result, diffs contract fingerprints, rejects the edit (raising
`SectionNormalizationRejected`) and rolls back the draft when validation fails or too many
contracts changed.

---

## 2.21 `scripts/Utils/Reporting.py`

Final assembly, verified-label accounting, and the pipeline progress card.

### `_assemble_final` (Utils/Reporting.py:19) — function
Concatenates all sections (sorted by number) into one final standalone Lean file: dedupes
non-generated imports, strips `AutoBlueprint` imports, and composes preambles plus
declaration bodies for the final from-scratch check.

### `_record_proof_graph_telemetry` (Utils/Reporting.py:35) — function
Records the current proof-scheduling graph into telemetry: top-down layers, per-node
proof/traversal depth, immediate theorem dependencies/consumers, and per-node structural
features.

### `_verified_node_labels` (Utils/Reporting.py:98) — function
Returns nodes whose current contract is fully discharged: Mathlib-satisfied, proved, or
frozen non-theorem-like declarations — excluding recorded conjectures. Feeds progress
reporting.

### `_recorded_conjecture_labels` (Utils/Reporting.py:114) — function
Returns open-conjecture labels faithfully encoded as complete `def`/`abbrev ... : Prop :=`
declarations (no `sorry`) in frozen sections — "recorded but not proved" for the
completeness gate and progress card.

### `_phase2_body_progress` (Utils/Reporting.py:140) — function
Scans frozen sections and returns `(implemented, required)` label sets for Phase 2 body
work: only declaration kinds with replaceable bodies count, with implemented meaning no
terminal `sorry`.

### `_contract_work_stage` (Utils/Reporting.py:175) — function
Returns the user-visible name of the current declaration-work owner: "Phase 2 whole-node
repair" once Phase 2 has started, else "Phase 1"; used pervasively in logs.

### `_run_pending_declaration_work` (Utils/Reporting.py:184) — function
Enforces the one-way Phase 1/Phase 2 boundary for pending declarations: dispatches to
`_run_phase2_whole_node_repairs` after Phase 2 starts, otherwise to `_run_phase1`.

### `_begin_phase2` (Utils/Reporting.py:195) — function
Performs the one-way transition into Phase 2 once every non-Mathlib node is frozen:
records the Phase 1 baseline label set, sets `ctx.phase2_started`, and returns `True` only
for the transition itself.

### `_print_pipeline_progress` (Utils/Reporting.py:223) — function
Prints and records the pipeline progress card: Phase 1 contracts frozen, Phase 2 bodies
implemented, overall verified/recorded-conjecture completion, and repair-trial usage.

---

## 2.22 `scripts/formalize_blueprint.py`

The entry point: module docstring, import block, the part-file loader, `main`, `logged_main`, and the `__main__` guard.

**Module docstring (lines 1–72).** The "statements-first" Lean formalization pipeline
(fast successor to `refine_blueprint_with_lean.py`): Phase 1 freezes exact Lean statements
bottom-up from the blueprint dependency graph; Phase 2 fills deferred `sorry` bodies
top-down via a deterministic tactic ladder, batched model calls, escalation, and bounded
blueprint repair.

**Imports of note (lines 95–144).** Heavy reuse of sibling modules: `generate_blueprint`
(`_extract_json`, `read_paper`), `lean_preflight`, `model_runners` (runner selection), a
~45-symbol import block from `refine_blueprint_with_lean` (Lean compilation, audits,
declaration parsing, module composition), `telemetry` (`TelemetryRun`), and
`validate_blueprint` (`Node`, `validate_blueprint`).


### `main` (formalize_blueprint.py:188) — function (~1,555 lines); CLI entrypoint
Parses all CLI arguments (`name`, runner/escalation/planner tiers, `--paper`,
`--max-trials`, timeouts, section/batch sizes, `--conjecture-policy`, `--workers`, effort
levels, the `--continue`/`--continue-phase1`/`--fresh` resume group, `--no-ladder`,
`--no-build`, `--lean-command`) and then runs the entire statements-first formalization
pipeline to completion or budget exhaustion: telemetry/config setup and Lean environment
preflight; blueprint draft preparation, validation, and library search; `Ctx` construction
and state load/reset; then the giant outer loop — completing verified Phase 2 repairs,
servicing boundary-audit and queued Phase 2 repair requests, reactivating deferred
sections, running pending declaration work and the integration gate, conjecture-proof
policy enforcement, crossing into Phase 2, scheduling and running proof frontiers in
parallel, the final assembly/coverage check and publish on success, and otherwise routing
evidence into either a no-blueprint-edit generation retry or the blueprint-repair path
(dependency edges, section normalization, or scoped repair) with scope-violation
rollback, invalidation, and no-op escalation — plus RunnerError/ValueError terminal
handling that writes the report.

### `logged_main` (formalize_blueprint.py:1743) — function
Wrapper entrypoint that pre-parses the blueprint name, tees stdout/stderr into a
persistent per-blueprint run log via `TeeStream`, installs a SIGTERM handler that logs
pid/stage before exiting, runs `main`, and converts unhandled exceptions into logged exit
codes (2 for environment/runner errors, 1 otherwise).

### `if __name__ == "__main__"` (formalize_blueprint.py) — module entry guard
Invokes `raise SystemExit(logged_main())` — the script's actual process entrypoint.

---

## 3. The subsystem map (what the file already is, implicitly)

The catalog above shows the file is not unstructured — it is ~20 coherent subsystems
concatenated in one namespace, mostly in a sensible order, with three cross-cutting
patterns applied uniformly:

- **Fingerprint/epoch discipline** — every persistent store is keyed by
  statement/plan/candidate fingerprints and has a `_prune_stale_*` partner wired into
  `Ctx.refresh_nodes` and the save/load boundary.
- **Transactionality** — snapshot → model call → deterministic validation → commit or
  byte-exact rollback, everywhere.
- **Evidence-scoped authority** — edit authority is never wider than the labels whose
  failure evidence authorized it, carried by the `RepairRequest` exception.

The problem is purely organizational: 466 definitions share one flat namespace; the only
navigation aid is grep; the dependency structure between subsystems is invisible; and
every change produces a diff in the same 31k-line file. Nothing below proposes changing
what any function does.

The subsystems, with their current line homes:

| # | Subsystem | Monolith home (lines, historical) | New home |
|---|-----------|-----------------------------------|----------|
| 1 | Policy constants, regexes, kind predicates, default runner tiers | 146–341 | `Utils/Constants.py` (+ runner tiers in `Utils/ModelCalls.py`) |
| 2 | Logging / telemetry wrappers / thread-stage tracking / global locks | 222–366 | `Utils/Logging.py` |
| 3 | Blueprint fingerprints + dependency-graph scheduling (topo, layers, frontiers) | 372–758 | `Utils/Graph.py` |
| 4 | Shared dataclasses (parsed-module types, audit/plan verdict types) | 766–983 | `Utils/Types.py` |
| 5 | Lean module parsing + model-output canonicalization (helper namespacing) | 986–2001 | `Utils/LeanSource.py` |
| 6 | Phase-1 interface/body contract enforcement (defer/splice/extract) | 2002–2307 | `Utils/LeanSource.py` |
| 7 | Lean compilation, error attribution, import resolution | 2310–2502 | `Utils/LeanCheck.py` |
| 8 | Deterministic skeleton audit + finding classification | 2505–2775, 12229–12488, 6355–6490 | `Utils/Audits.py` (obligation IDs in `Utils/Candidates.py`) |
| 9 | Failure routing: `CallResult`, `FailureScopeDecision`, `RepairRequest`, aggregation | 2782–3327 | `Utils/FailureRouting.py` |
| 10 | Transactions: Phase-1 checkpoint, Phase-2 repair queue/lifecycle | 3330–4290 | `Utils/Transactions.py` |
| 11 | `Ctx` (run context) + conjecture predicates | 4291–4547 | `Utils/Types.py` (`Ctx`) + `Utils/Draft.py` (predicates) |
| 12 | Blueprint draft lifecycle + scoped TeX repair validator | 4548–4770 | `Utils/Draft.py` |
| 13 | Evidence stores: quarantine, bisection, diagnostic ledger, generation feedback, dependency observations | 4772–5847 | `Utils/Evidence.py` |
| 14 | Model-call economy: exchange sample budget, resume sessions | 5848–6075 | `Utils/Exchange.py` |
| 15 | Candidate state machines (Phase-1 monotonic store, Phase-2 node candidates), retry lifecycle | 6076–7673 | `Utils/Candidates.py` |
| 16 | Model-call infrastructure (`_make_runner`, `_ModelCallControl`, `_call_model`) | 7676–7950 | `Utils/ModelCalls.py` |
| 17 | Sections, compile-fingerprint cache, object probes, usability gate | 7952–8490 | `Utils/Types.py` (dataclasses) + `Utils/Sections.py` |
| 18 | State persistence (`_save_state`, `_save_ctx_state`, `_load_state`, artifact pruning) | 8493–10194 | `Utils/StateIO.py` |
| 19 | Graph queries, repair-scope gates, prompt-context builders, prompt builders | 10196–12222 | `Utils/Graph.py` + `Utils/Prompts.py` (patch machinery in `phase1.py`) |
| 20 | Alignment audit (model critic) + design-plan lifecycle/epoch invalidation | 12229–13166 | `Utils/Audits.py` + `phase1.py` (plan lifecycle) |
| 21 | Design-plan machinery: circuit breaker, schemas/parsing, closure, tournament, corrections, frontier gateway | 13169–18313 | `phase1.py` |
| 22 | Phase-1 generation/freezing engine + escalation routing + `_run_phase1` | 18316–25045 | `phase1.py` |
| 23 | Phase-2: whole-node transactions, proof driver, tactic ladder, prerequisites | 25186–27015 | `phase2.py` |
| 24 | Blueprint repair + boundary audit + section normalization | 27017–29102 | `Utils/BlueprintRepair.py` |
| 25 | Final assembly, progress reporting, phase bookkeeping | 29104–29366 | `Utils/Reporting.py` |
| 26 | CLI: `main`, `logged_main`, `__main__` guard | 29367–30971 | `formalize_blueprint.py` |

## 4. Why the monolithic shape was not sustainable (organizationally)

- **One namespace, 466 names.** Understanding any call site requires knowing which of the
  ~20 subsystems the callee belongs to; the file offers no boundary that says so.
- **The unit of review is the whole file.** Every branch merge conflicts in
  `formalize_blueprint.py`; git blame/annotate is slow; editors and code-intel tools
  struggle with a 1.2 MB source file.
- **Layering exists but is unenforced.** Data types, pure policy functions, stateful
  stores, and orchestration are interleaved; nothing prevents a low-level helper from
  calling into an orchestrator.
- **The legacy module is a hidden shared library.** ~45 private (`_`-prefixed) names are
  imported from `refine_blueprint_with_lean.py`, so the "fast successor" is permanently
  coupled to the internals of the module it succeeded, without any file naming that fact.
- **External consumers bind to private internals.** Tests, `benchmark_lean_candidate.py`,
  and `replay_phase1_plans.py` import `_`-prefixed names directly from
  `formalize_blueprint`, so today there is no place where "the stable surface" is written
  down.

## 5. Organization — implemented layout

> **Status: implemented.** The split described below was carried out (2026-09-02) with a
> different mechanism than the package-facade sketch in 5.1, for one decisive reason
> discovered during implementation: the test suite patches ~120 private names **as
> attributes of the `formalize_blueprint` module** (about 300 `patch("formalize_blueprint.<name>")`
> call sites, e.g. `_call_model` x70, `_check_lean` x30, plus `SCRATCH_DIR`/`REPO_ROOT`).
> A conventional package split binds names per-module at import time, so those patches
> would stop reaching internal call sites — silently changing behavior under test. The
> implemented split therefore keeps ONE runtime namespace: `formalize_blueprint.py`
> retains the docstring, the import block, `main`, `logged_main`, and the `__main__`
> guard, and assembles the rest of itself by compiling and executing each part file into
> its own module globals, in a mechanically checked definition order:
>
> ```
> scripts/
>   formalize_blueprint.py      # entry point + imports + parts loader + main/logged_main
>   phase1.py                   # Phase 1: planning, generation, freezing, escalation routing
>   phase2.py                   # Phase 2: whole-node transactions, tactic ladder, proofs
>   Utils/
>     Constants.py  Logging.py  Types.py  Graph.py  LeanSource.py  LeanCheck.py
>     Audits.py  FailureRouting.py  Transactions.py  Draft.py  Evidence.py
>     Exchange.py  Candidates.py  ModelCalls.py  Sections.py  StateIO.py
>     Prompts.py  BlueprintRepair.py  Reporting.py
> ```
>
> Every definition moved byte-for-byte (comments included; the splitter asserted the
> concatenation of all parts equals the original body). Functions still resolve
> collaborators through `formalize_blueprint`'s globals, so patch seams, private imports
> (tests, replays, the benchmark), pickling/`__module__`, and the CLI path are all
> unchanged. Verified: identical test-suite results (498 tests, same single pre-existing
> fixture error), identical `dir()` surface (623 names, +2 loader constants), CLI
> `--help`, and the replay/benchmark tools.
>
> The original package-facade proposal is kept below for reference — it remains the
> right *next* step if the patch seams are ever migrated to dependency injection.

### 5.0 Original proposal (superseded, kept for reference)

### 5.1 Shape: a package with a compatibility facade

Split the module into a package while keeping `scripts/formalize_blueprint.py` in place as
a **facade** that re-exports every name the outside world uses and keeps the CLI entry:

```
scripts/
  formalize_blueprint.py        # FACADE + CLI entry — path, name, and behavior unchanged
  formalize/                    # new package (name illustrative)
    __init__.py                 # empty, or docstring only — no import side effects
    config.py                   # subsystem 1: constants, regexes, kind predicates,
                                #   _default_fast_runner_specs, EVIDENCE_LIFETIMES, schema versions
    runlog.py                   # subsystem 2: _PRINT/_TELEMETRY/_STATE locks, _ACTIVE_STAGES,
                                #   _stage, _log, _record, _store_text
    types.py                    # subsystem 4 + CallResult/FailureScopeDecision/RepairRequest (9)
                                #   + Section/Phase1LayerCandidate/SectionProofOutcome +
                                #   Ctx, SectionStuckState (11) — the data model, no policy
    graph.py                    # subsystem 3 + graph queries from 19: fingerprints, topo order,
                                #   layers, frontiers, _statement_uses/_proof_uses, closures,
                                #   repair-scope gates
    lean_source.py              # subsystems 5–6: parsing, canonicalization, helper namespacing,
                                #   defer/splice/extract, _compose_module
    lean_check.py               # subsystem 7 + object probes/usability gate from 17:
                                #   _check_lean, error attribution, import resolution,
                                #   compile fingerprints, olean cache
    audits.py                   # subsystem 8 + 20's _model_alignment_audit: deterministic
                                #   skeleton audit, obligations, alignment audit + identities
    evidence.py                 # subsystem 13: quarantine, bisection, diagnostic ledger,
                                #   generation feedback, dependency observations
    exchange.py                 # subsystem 14 + 16: exchange budget, resume sessions,
                                #   _make_runner, _ModelCallControl, _call_model
    candidates.py               # subsystem 15: both candidate stores + retry lifecycle
    draft.py                    # subsystem 12: blueprint draft lifecycle, scoped TeX repair
                                #   validator, promote
    state_io.py                 # subsystem 18: _save_state/_save_ctx_state/_load_state,
                                #   _prune_stale_generated
    transactions.py             # subsystem 10: Phase-1 checkpoint, Phase-2 repair queue
    prompts.py                  # the shared prompt-context builders and rule blocks from 19
                                #   (digests, minimal dependency interface, _common_rules, ...)
    plan/                       # subsystem 21, itself large enough for a subpackage:
      __init__.py
      schema.py                 #   schemas, parsing, JSON repair, rendering
      closure.py                #   symbol surfaces, closure issues, components, scores
      lifecycle.py              #   circuit breaker, epoch transitions, staleness pruning
      tournament.py             #   candidates, admission, merging, semantic plan
      correction.py             #   audit prompt/runner, corrections, frontier gateway
    phase1/                     # subsystem 22:
      __init__.py
      generate.py               #   prompts + generation groups + salvage
      freeze.py                 #   _freeze_section, _freeze_section_from_code, _freeze_parts
      layers.py                 #   validated-contract layer runner, compile/audit pipeline
      routing.py                #   compile/exhaustion/deterministic failure routers
      driver.py                 #   _run_phase1, _phase1_recompile_environment
    phase2/                     # subsystem 23:
      __init__.py
      whole_node.py             #   whole-node prompts + transactions + driver
      proofs.py                 #   tactic ladder, proof batches, _prove_section
      prerequisites.py          #   definition-prerequisite scheduling and routing
    repair.py                   # subsystem 24: invalidation/reactivation, repair prompts,
                                #   dependency-edge editing, _repair_blueprint(+components),
                                #   boundary audit, section normalization
    reporting.py                # subsystem 25: _assemble_final, progress, verified labels
    cli.py                      # subsystem 26: main, logged_main
```

The facade then reads, in full:

```python
# formalize_blueprint.py — compatibility facade + CLI entry.
from formalize.config import *            # noqa: F401,F403  (see 5.3 on underscore names)
from formalize.config import _is_theorem_like_kind, _default_fast_runner_specs, ...
from formalize.types import Ctx, RepairRequest, CallResult, ...
from formalize.exchange import _call_model, _runner_failure_status, ...
...
from formalize.cli import main, logged_main

if __name__ == "__main__":
    raise SystemExit(logged_main())
```

Why a facade rather than moving consumers:

- `python scripts/formalize_blueprint.py ...` keeps working — README commands,
  `webui.py`'s subprocess invocations, *and* `webui.py`'s permission allowlist entry
  (`"scripts/formalize_blueprint.py"`) are untouched.
- Every existing import (`tests/`, `benchmark_lean_candidate.py`,
  `replay_phase1_plans.py`) keeps working unchanged.
- The facade doubles as the written-down public surface: the explicit re-export list *is*
  the list of names outsiders may use.

### 5.2 Layering rule the split makes enforceable

The modules above form a DAG (arrows = "may import"):

```
config ─┐
runlog ─┼─→ types ─→ graph / lean_source ─→ lean_check / audits ─→ evidence /
        │            candidates / exchange / draft / prompts ─→ plan ─→ phase1 / phase2
        └───────────────────────────→ transactions / state_io ─→ repair ─→ cli
```

The exact arrows can be settled during extraction (the catalog's cluster notes say who
calls whom); the invariant worth adopting is just: **types and config at the bottom, cli
at the top, no cycles.** Today that layering exists by discipline only; after the split
the import graph enforces it, and any accidental upward call becomes an ImportError
instead of silent coupling.

### 5.3 Hard constraints that protect functionality

These are the rules that make the reorganization a pure code *move*. Each one exists
because violating it would silently change behavior:

1. **Move, don't touch.** Function bodies, names, signatures, defaults, and docstrings are
   copied byte-for-byte. No renames, no "while I'm here" cleanups, no splitting of large
   functions (`main`, `_freeze_section`, `_load_state` move whole). Splitting big
   functions is a separate, later project with its own tests.

2. **Underscore names don't survive `import *`.** Almost every name in this file is
   `_`-prefixed, and `from formalize.x import *` skips underscore names unless the source
   module defines `__all__`. The facade must therefore use **explicit** re-import lists
   (or per-module `__all__` including the underscore names). Generate the list
   mechanically from `grep -E '^(def |class |[A-Z_]+ =|_[A-Za-z]+ =)' ` output and assert
   at the end of the migration that `dir(formalize_blueprint)` before == after.

3. **Mutable module state moves to exactly one home.** `_ACTIVE_STAGES`,
   `_ACTIVE_STAGE_LOCK`, `_PRINT_LOCK`, `_TELEMETRY_LOCK`, `_STATE_LOCK` are shared
   mutable objects. Each must be defined once (in `runlog.py`) and imported everywhere
   else — never re-created per module, or Phase-1 workers would synchronize on different
   locks (a real, silent concurrency bug). In-place mutation through an imported binding
   is safe; *rebinding* a module global from another module is not. (Good news: the file
   contains no `global` statements, so no function rebinds a module global today — the
   locks and stores are only mutated in place.)

4. **Patch seams must stay real.** Tests import `_call_model`, `_runner_failure_status`,
   `_compose_module`, `PHASE2_COMPLETE_CORRECTION_TIMEOUT`, etc. from
   `formalize_blueprint`. Re-exporting keeps the *imports* working, but if any test (or
   future test) monkeypatches `formalize_blueprint._call_model`, internal call sites in
   `formalize/phase1/...` would no longer see the patch — they'd call
   `formalize.exchange._call_model` directly. Before the split, grep the tests for
   `patch.object`/`setattr` targets on `formalize_blueprint` (today the tests patch
   `lean_libs`, `new_blueprint`, and `refine_blueprint_with_lean` — not
   `formalize_blueprint` — so this is currently safe, but it must be re-checked at
   migration time and documented in the facade).

5. **The legacy import block becomes explicit.** The ~45 names imported from
   `refine_blueprint_with_lean` should be funneled through one new module (e.g.
   `formalize/legacy.py`) that contains nothing but
   `from refine_blueprint_with_lean import _run_lean, _lean_env, ...` and re-exports them.
   Zero behavior change — but the coupling gets a single, visible, documented home, and a
   future "actually move the shared code out of the legacy module" step touches one file.

6. **No import-time side effects in the package.** The current module only defines things
   at import time (constants, locks, regexes); keep it that way — `formalize/__init__.py`
   stays empty so importing a leaf module never drags in the CLI or model runners.

7. **Import mechanics stay path-based.** Tests, webui, and the replay scripts put
   `scripts/` on `sys.path` and import flat top-level names. The `formalize/` package
   lives inside `scripts/`, so `import formalize.config` resolves through the same
   mechanism; use absolute imports (`from formalize import config`), not relative ones,
   inside the package — relative imports would break if a module were ever run directly.

8. **One assertion of equivalence per step.** After each extraction step:
   `uv run pytest tests/` plus an import-surface check
   (`python -c "import formalize_blueprint as m; print(sorted(dir(m)))"` diffed against
   the pre-split output). The test suite already exercises the private surface heavily
   (routing, orchestration replay, semantic planner, trajectory replays), which is what
   makes a mechanical split verifiable.

### 5.4 Suggested migration order (lowest risk first)

Each step is independently shippable and leaves the facade complete:

1. `config.py` + `runlog.py` (constants, locks, logging) — no logic, easiest to verify.
2. `types.py` (all dataclasses + `RepairRequest` + `Ctx`) — everything depends on these,
   they depend on almost nothing.
3. Pure functions: `graph.py`, `lean_source.py` — deterministic, well covered by tests.
4. `lean_check.py`, `audits.py`, `prompts.py`.
5. Stateful stores: `evidence.py`, `candidates.py`, `exchange.py`, `draft.py`,
   `transactions.py`, `state_io.py` (these mutate `Ctx` under `_STATE_LOCK`; move them as
   whole clusters so a store and its `_prune_stale_*` partner never straddle a step).
6. `plan/`, then `phase1/`, then `phase2/`, then `repair.py` (orchestrators last).
7. `reporting.py` + `cli.py`; the original file shrinks to the facade.
8. Only after everything is green: add `formalize/legacy.py` for the
   `refine_blueprint_with_lean` imports (step 5.3.5).

### 5.5 What NOT to do

- **Don't split `main` / `_freeze_section` / `_load_state` as part of this.** Decomposing
  1,000+-line orchestrators changes control flow around `try/except RepairRequest`
  boundaries and `finally` cleanup; it is behavior-risk work, not organization work.
- **Don't rename anything**, including "ugly" names — every `_`-name is a potential
  import/patch target of tests, replay tooling, and persisted-state readers.
- **Don't change persisted formats or schema versions** (`skeleton_state.json` v29,
  `DESIGN_PLAN_SCHEMA_VERSION`, evidence ledger versions). File moves must not touch any
  serialization code path.
- **Don't move code *out of* `refine_blueprint_with_lean.py`** in the same effort. The
  legacy loop is a separately documented, working pipeline; extracting the shared ~45
  helpers into a real common module is worthwhile but is a second project with its own
  verification (both pipelines' tests).
- **Don't reorder within-module definitions "for readability"** during the move; keeping
  file order identical to the original line order makes every step diffable against the
  monolith (`git diff --color-moved` verifies pure moves).

### 5.6 Cheaper fallback (if the package split is deferred)

If even a mechanical split is more churn than wanted right now, two zero-risk
improvements still help:

1. **A table of contents.** Add one banner comment per subsystem boundary (the 26 rows of
   the table in section 3) plus a top-of-file index with line anchors. Pure comments;
   zero functional surface.
2. **Region markers matching the catalog.** Adopt this document's section numbers in
   those banners so `organize.md` doubles as the file's index.

These don't fix the namespace problem but make the monolith navigable until the split
lands.
