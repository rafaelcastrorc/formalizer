# Catalogue.md — every file under `scripts/`

What each file in the `scripts/` tree does, one entry per file. Function-level detail for
the formalization pipeline lives in `organize.md`; this is the file-level map.

Two structural facts to know up front:

- **`formalize_blueprint.py` is a composite module.** Its source is physically organized
  into `Utils/*.py`, `phase1.py`, and `phase2.py`, but at import time it compiles and
  executes those part files into its own namespace, in a fixed order. The part files are
  therefore *not* importable modules on their own — every name in them belongs to the
  `formalize_blueprint` module at runtime. This preserves the single namespace that the
  test suite's `patch("formalize_blueprint.<name>")` seams and the replay/benchmark
  tools' private imports depend on.
- **Entry points stay at `scripts/` top level** (their paths are documented in the README
  and hard-coded in `webui.py`'s subprocess commands and allowlist); environment tooling
  lives in `env_setup/`, ad-hoc measurement tools in `diagnostics/`, and the historical
  replay harnesses in `tests/replay/` next to their fixtures.

---

## Top-level entry points

### `formalize_blueprint.py`
The statements-first Lean formalization pipeline — the recommended way to formalize a
blueprint (`python scripts/formalize_blueprint.py <name> --paper ... --runner ...`).
Phase 1 freezes exact Lean statement contracts bottom-up from dependency leaves; Phase 2
implements deferred bodies top-down from public results. The blueprint is the only
mathematical source of truth and Lean is the critic; all edits are transactional against
an unpublished draft. The file itself holds the module docstring, the import block, the
part-file loader (see above), the `main` orchestration loop (~1,550 lines: trial budget,
repair routing, phase transitions, final assembly and publication), `logged_main`
(run-log teeing, SIGTERM handling, exit codes), and the `__main__` guard.

### `refine_blueprint_with_lean.py`
The legacy per-chunk author/critic refinement loop (`## Legacy Lean-Guided Refinement` in
the README): validates the blueprint, picks dependency-closed chunks from the `\uses`
graph, asks a model for disposable Lean, compiles, audits, and repairs the blueprint per
chunk. Kept working as documented — and it doubles as a de facto shared library: the fast
pipeline imports ~45 of its helpers (Lean running, module composition, statement audits,
library search, report writing).

### `generate_blueprint.py`
Paper → blueprint generation entry point. Agent mode (`--runner codex`/`claude-code`)
lets a local coding agent edit files and run scripts; API mode
(`--runner openai:...`/`anthropic:...`) accepts JSON only, then this script scaffolds
files, validates, and builds. Also exports `read_paper`/`_extract_json`, reused by the
formalization pipelines.

### `new_blueprint.py`
Scaffolds `blueprints/<name>/` from `templates/blueprint-skeleton/` and writes
`meta.yml`. The deterministic first step of both generation modes.

### `validate_blueprint.py`
Deterministic structural validator for blueprint sources (labels present and unique,
theorem-like environments labeled, `\uses` targets exist, layout contract). Exports the
`Node` dataclass and `validate_blueprint`, the shared parsed representation used by every
other pipeline script. Model output must pass this gate before anything is accepted.

### `build.py`
Builds every blueprint plus the landing page into `site/` by running plasTeX the way
`leanblueprint web` does internally. Deliberately never invokes Lean — the website build
and the formalization loop are separate layers.

### `webui.py`
Local stdlib-only browser dashboard (`python scripts/webui.py`) wrapping the CLI scripts
(generate, formalize/refine, validate, build, `env_setup/setup_lean.py`,
`env_setup/lean_libs.py`) behind a job runner with live logs, an allowlist of exact
script paths, and single-job locking.

### `phase1.py` *(part file of formalize_blueprint.py)*
Phase 1 in full: the advisory semantic planner and the typed interface-plan machinery
(two-lane tournament, deterministic contract-closure validation, plan corrections, the
blueprint-direct circuit breaker), source-readiness gating (`\notready`, conjecture
policy), statement generation and timeout salvage, the two freeze transaction workhorses
(`_freeze_section`, `_freeze_section_from_code`), the validated-contract layer pipeline
(generate → typecheck → batched audit with sibling preservation), and the graduated
failure-escalation ladder (targeted revision → plan revision → blueprint-direct →
decomposition), ending in the `_run_phase1` driver and the Phase-1 integration gate.

### `phase2.py` *(part file of formalize_blueprint.py)*
Phase 2 in full: whole-node repair transactions (complete statement+body regeneration
for repaired nodes), the free tactic ladder, batched proof implementation with
per-declaration rollback (`_apply_proof_batch`, `_prove_section`), definition-body
prerequisite scheduling, and the routing of proof outcomes into scheduling-only or
blueprint-authorized repair requests.

### `lean_preflight.py` *(shared library)*
Deterministic Lean/Lake readiness checks used by the CLI scripts and the web UI before
any model is consulted: the repo must declare Lean, `lake` must run, and a tiny Mathlib
probe must compile. Error messages point at `scripts/env_setup/setup_lean.py`.

### `telemetry.py` *(shared library)*
Append-only, raw-observation telemetry under `.auto-blueprint/telemetry/` (events plus
content-addressed text artifacts), with optional best-effort upload when
`AUTO_BLUEPRINT_TELEMETRY_URL` is set. No guessed labels at collection time — dataset
builders derive labels later from outcomes. Exports `TelemetryRun` and
`node_structural_features`.

---

## `Utils/` — part files of formalize_blueprint.py

Grouped utilities of the statements-first pipeline. Executed into the
`formalize_blueprint` namespace in the order below (constants first, orchestrable
subsystems later); none is importable on its own.

### `Utils/Constants.py`
Every module-level constant of the pipeline: filesystem anchors (`SCRIPTS_DIR`,
`REPO_ROOT`, `SCRATCH_DIR`), node-kind sets and the theorem-likeness predicates,
traversal/batch/worker defaults, retry/timeout/budget knobs, evidence-ledger and
design-plan schema versions, prompt boilerplate blocks (frozen-interface note, harness
conventions, repair-scope rules), and all shared compiled regexes (declaration heads,
terminal `sorry`, diagnostics locations, model wrappers, missing-name errors, …).

### `Utils/Logging.py`
The process-wide mutable coordination state — `_PRINT_LOCK`, `_TELEMETRY_LOCK`, the
reentrant `_STATE_LOCK`, and the per-thread stage map — plus the `_stage` context
manager and the thread-safe `_log` / `_record` / `_store_text` primitives.

### `Utils/Types.py`
The shared data model: parsed-Lean types (`DeclBlock`, `ParsedModule`,
`CanonicalModelModule`), audit/plan verdict types (`SkeletonFinding`,
`PlanClosureFinding`, `DesignPlanCandidate`, `PlanClosureCorrectionResult`,
`AlignmentAuditResult`, `RepairBoundaryAuditOutcome`), the section records (`Section`,
`Phase1LayerCandidate`), stuck-section state, the `_SectionNumberAllocator`, and the
central `Ctx` run context whose `refresh_nodes` re-fingerprints the blueprint and prunes
every stale evidence store.

### `Utils/Graph.py`
Blueprint statement/contract fingerprints; dependency-graph scheduling (topological
order, static bottom-up/top-down layers, dynamic ready frontiers, proof layers); label
bookkeeping over sections (frozen/reserved/proved); statement-vs-proof-scoped `\uses`
accessors and transitive closures; and the deterministic repair-scope gates
(scope-violation detection, decomposition-helper orientation, Mathlib-refusal mappings,
failure fingerprint/shape hashing).

### `Utils/LeanSource.py`
The model-output boundary: comment-aware Lean parsing into `ParsedModule`, wrapper
stripping, theorem-keyword normalization, helper ownership and deterministic
`_autobp_` namespacing, `_canonicalize_model_lean` / `_ingest_model_lean`, Phase-1
body deferral to terminal `:= sorry` (with the structural-alias exception), Phase-2
proof splicing/extraction, and `_compose_module`.

### `Utils/LeanCheck.py`
Running the Lean compiler on a module (`_check_lean`, with timeout process-group kill
and the universe-level auto-repair retry), grouping diagnostics per declaration, and
deterministically resolving missing names to narrow local-library imports instead of a
persisted broad `import Mathlib`.

### `Utils/Audits.py`
Both correctness gates: the deterministic skeleton audit (`_skeleton_code_findings`,
`_skeleton_deterministic_findings` — sorry placement, kinds, closure references,
plan-owned helper surfaces, finding classification and stagnation fingerprints) and the
independent model alignment audit (`_model_alignment_audit`) with its canonical
failure-identity plumbing.

### `Utils/FailureRouting.py`
The shared failure vocabulary and policy: `CallResult` and runner-failure
classification, `FailureScopeDecision` and the isolate/bisect/singleton routing rule,
the `RepairRequest` control-flow exception, aggregation of parallel failures into single
outer transactions, and payload (de)serialization for persisted routes.

### `Utils/Transactions.py`
Durable transaction machinery: the immutable Phase-1 checkpoint
(create/restore/availability), and the full Phase-2 repair transaction lifecycle —
content-addressed request payloads and context fingerprints, the persisted queue,
activation/verify/complete stages, pre-edit snapshots with rollback, interrupted-repair
recovery, follow-up merging, and provider rerouting.

### `Utils/Draft.py`
The unpublished blueprint draft: conjecture-policy predicates, canonical/draft
directory mapping, draft creation and validation, blueprint-source reading for prompts,
the scoped TeX repair validator (`_scoped_blueprint_repair_content` — per-label
replacements only, atomic write), and `_promote_blueprint_draft` publication.

### `Utils/Evidence.py`
Fingerprint-scoped failure memory: quarantine and local bisection partitions for
scheduling, the typed diagnostic-evidence ledger (statement/plan/candidate lifetimes,
dedup by failure signature, consume/prune), per-label generation feedback and compiler
evidence attribution, and the two-party dependency-edge observation/confirmation store.

### `Utils/Exchange.py`
The model-call economy: persisted per-context exchange sample budgets
(`_phase1_exchange_start/_finish`, duplicate-response detection) and the
resume-session store that lets an outer retry resume a timed-out backend conversation.

### `Utils/Candidates.py`
The candidate state machines: the monotonic Phase-1 generation-candidate store
(obligation universe, transition decision, `_store_generation_candidates`, reuse and
partial-response salvage, semantic-repair continuation), the epoch-keyed Phase-2
complete-node candidate store, and the base → escalation → exhausted retry lifecycle.

### `Utils/ModelCalls.py`
Everything that talks to a model backend: `_default_fast_runner_specs` (two-tier model
policy), `_make_runner`, the `_ModelCallControl` cancellation handle, and `_call_model`
— the single choke point with session resume, telemetry, and fail-fast on dead
backends.

### `Utils/Sections.py`
Generated-section artifact management: state/module/olean path helpers, the
environment+opaque-theorem-v2 compile-fingerprint scheme with resume migration, olean
compilation and cache stamping, artifact discard, and the object-build usability gate
(statement-surface probes classifying timeouts as interface vs. implementation cost).

### `Utils/StateIO.py`
Run-state persistence: the fingerprint-filtered `_save_state` serializer (schema v29),
the lock-coherent `_save_ctx_state` snapshot, the heavily validating `_load_state`
resume path (per-store staleness checks, section salvage/dedup/deferral), and
`_prune_stale_generated` artifact cleanup.

### `Utils/Prompts.py`
Prompt construction shared across phases: frozen-interface digests with module-granular
budgets, the minimal complete dependency interface and its completeness gate, the
dependency contract table, library/node-summary context slicing, downstream proof
context, the shared rule blocks (`_common_rules`, `_design_plan_rules`, text-only
budget, conjecture policy), and the concrete task prompts (initial declarations,
skeleton statements, targeted patch, Phase-2 proof bodies).

### `Utils/BlueprintRepair.py`
Evidence-driven blueprint TeX editing: post-repair invalidation and deferred-section
reactivation, deterministic paper excerpts and repair node context, the scoped-repair
prompt, deterministic `\uses` edge insertion with cycle rejection, the transactional
`_repair_blueprint` core with parallel component proposals, the post-repair boundary
audit (persisted, resumable), and the stuck-section normalization escape hatch.

### `Utils/Reporting.py`
End-of-run accounting: `_assemble_final` (one standalone Lean file for the final check),
proof-graph telemetry, verified/recorded-conjecture label sets, Phase-2 body progress,
the one-way Phase-1→Phase-2 transition, and the pipeline progress card.

---

## `env_setup/` — Lean environment tooling

### `env_setup/setup_lean.py`
Installs/checks the Lean toolchain the repo declares: elan bootstrap
(`--install-elan`), `lake exe cache get`, and the deterministic preflight. The
project-level equivalent of `requirements.txt` for Lean. Run after checkout in CI and
locally.

### `env_setup/lean_libs.py`
Resolves and applies a mutually-compatible set of Lean libraries (mathlib, cslib,
physlib): reads each library's `lean-toolchain` history to find a common toolchain,
rewrites the managed block of `lakefile.lean`, snapshots/restores on failure, tracks
per-library build/import readiness stamps, and caches resolutions
(`resolve` / `apply` / `status`). Imported at runtime by `webui.py` and
`refine_blueprint_with_lean.py` as `from env_setup import lean_libs`.

### `env_setup/__init__.py`
Empty package marker so the runtime imports above resolve with `scripts/` on `sys.path`.

---

## `diagnostics/` — ad-hoc measurement tools

### `diagnostics/benchmark_lean_candidate.py`
Measures where one generated single-declaration Lean module spends compilation time:
copies it to a temp dir, derives imports-only and statement-with-`sorry` controls, and
times plain checking vs `.olean` generation. Read-only with respect to generated
modules and Lake artifacts.

### `diagnostics/build_classifier_dataset.py`
Flattens the append-only run telemetry into JSONL example tables (progress, routing,
candidate transitions, repair scopes, …) under `.auto-blueprint/telemetry/datasets/`.
Labels derive from observed outcomes; it does not train anything.

---

## `model_runners/` — model backend abstraction (importable package)

### `model_runners/__init__.py`
The runner registry: maps stable CLI-facing backend names (`codex`, `claude-code`,
`openai`, `anthropic`, `mock`) to concrete classes via `get_runner`, and re-exports the
error types.

### `model_runners/base.py`
The shared runner contract: `ModelRunner` base class (context-file loading,
retry/backoff, timing, cancellation), the common `RunResult` shape, and the error
taxonomy (`RunnerError`, transient vs environment classification helpers).

### `model_runners/api.py`
HTTP API backends (OpenAI, Anthropic) using only the stdlib: return text/JSON, never
edit files or run commands. Also model-listing/choice helpers used by the CLIs and web
UI. Credentials from environment variables.

### `model_runners/cli.py`
Local coding-agent backends (Codex CLI, Claude Code CLI): the model behaves like a repo
collaborator that may inspect and edit files, with `validate_blueprint.py` as the
deterministic safety gate. Includes codex model selection/escalation helpers.

### `model_runners/mock.py`
Offline test double returning a tiny valid blueprint payload in the API-mode JSON shape
— lets generation and validation be tested without credentials or network.

---

## `templates/`

### `templates/landing.html.j2`
Jinja2 template for the `site/` landing page listing all built blueprints; rendered by
`build.py`.

---

## Related (outside `scripts/`, for orientation)

- `tests/replay/replay_phase1_plans.py` — replays committed historical Phase-1 planner
  responses through today's deterministic closure/scheduling gates (regression tool for
  orchestration changes; no model calls).
- `tests/replay/replay_phase1_scheduler_latency.py` — replays committed task traces
  through a logical scheduler to measure Phase-1 scheduling headroom (no model, no
  Lean).
- `tests/replay/replay_phase2_latency.py` — deterministic legacy-vs-retained-candidate
  Phase-2 latency comparison over a committed fixture with a logical clock.
