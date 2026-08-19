# Phase 1 orchestration replay fixtures

These fixtures preserve minimal, provider-neutral observations from historical
Phase 1 runs that exposed retry and scheduling regressions. They are committed
test resources: the tests do not need local `.auto-blueprint/` telemetry, R2,
network access, or a model account.

`blueprint_direct_candidate_epoch.json` records the Simplex transition where
an ordinary-plan declaration exhausted compiler correction, activated
blueprint-direct generation, and was then incorrectly persisted as reusable
under the new strategy epoch. The regression requires the old candidate to
remain diagnostic evidence only; blueprint-direct generation must produce new
code before another compiler-correction lifecycle can begin.

`semantic_compiler_feedback_handoff.json` captures a statement-audit rejection
followed by several compiler-only declaration patches. It protects the
invariant that a compiler correction cannot forget an unresolved semantic
constraint and recreate the same rejected public contract.

`unknown_universe_retry.json` preserves the repeated mechanical Lean failure
from `run-20260802-221127`: independently generated interfaces used `Type u`
without declaring `u`. The regression requires the compiler boundary to add
only the universe level named by Lean, retry the same command, and spend no
model call or blueprint-repair trial.

`correction_sampling.json` records exact prompt/plan/tier epochs and the
candidate outcome produced by each stochastic sample. It deliberately includes
cases where sample two or three was the first one to compile, plus the
`lem:claim6` case where the same epoch was sampled six times without compiling.

`streaming_transactions.json` records the event boundary that made a completed
`def:decimal-affine-map` candidate wait behind an independent
`lem:claim6` escalation. It is sufficient to test that generation can stream
into compilation without splitting or bypassing the one final semantic audit.

`transport_outage.json` preserves the exact failure class from
`run-20260731-061030`: Codex websocket reconnect failures were incorrectly
counted as seven mathematical repair trials. The regression requires the
shared runner to retry that failure as infrastructure and assign it zero repair
budget.

`compile_reuse_loop.json` preserves the exact singleton loop from
`run-20260731-095949`: a deterministically clean candidate failed Lean, retained
its zero-call reuse permission, and was recompiled unchanged 91 times without a
model revision. The regression requires Lean rejection to keep the candidate as
feedback while making it ineligible for another zero-call reuse.

`semantic_candidate_dominance.json` preserves the candidate-selection failure
from `run-20260731-114400`: a compiling but semantically rejected interface
continued to dominate distinct deterministic-clean revisions, including one
that compiled. The regression requires such a revision to replace the rejected
candidate and proceed to the normal semantic gate.

`post_repair_boundary.json` preserves the five-contract key-generation repair
from `run-20260731-114400` and the continuation segment in
`run-20260731-131011`. The repaired support contract omitted a direct public
dependency, but the old pipeline spent seven generation/patch/audit calls and
324 seconds before discovering it. The regression requires the repaired
component audit to precede every Lean-generation call and route the exact edge
through the existing deterministic dependency transaction.

The same fixture also preserves the UUE pending-boundary lifecycle regression
from `run-20260802-233439`, where an applied certified edge retained stale
state and reauthorized six model blueprint repairs totaling about 520 seconds.
The regression requires the completed edge to resume Phase 1 without another
model repair or redundant boundary audit.

The fixture also preserves the compound transaction from
`run-20260803-003136`. A deterministic edge for
`def:local-basis-unitary` and a valid four-contract decomposition of
`def:finite-register-operators` were merged before scope checking. The old
scope check attributed the deterministic edit to the model, falsely rejected
it as downstream, and discarded both authorized operations. The regression
requires scope validation to inspect only the model-authored delta while the
complete five-contract transaction remains committed.

`immediate_dependency_edge.json` preserves the `def:local-basis-unitary`
failure from `run-20260731-133708`. The statement auditor identified an
existing required dependency while correctly classifying the remaining issue
as Lean translation, but the outer loop discarded the edge because a model
blueprint rewrite was not authorized. Eleven model calls and 275 model-seconds
ran before the edge transaction. The regression requires dependency evidence
to enter the deterministic, cycle-checked edge transaction immediately without
authorizing a model blueprint rewrite.

`semantic_origin_serialization.json` preserves three historical cases where
the statement critic saw that Lean was semantically wrong but, without the
current plan, could not identify that the plan was wrong too. The timestamps
measure the stale-plan generation work performed before the pipeline
eventually corrected the plan or decomposed the blueprint node.

`frontier_gateway_trajectories.json` preserves multi-step Phase 1 trajectories
from two different papers. The `simplex` case references an exact committed
historical planner response by SHA-256 and follows four dependency frontiers.
The `unconditional-unclonable-encryption` case preserves an adapted,
provider-neutral sequence in which two under-specified contracts are rejected,
corrected with exact feedback, re-audited, and then frozen before the next
frontier advances. `tests/test_phase1_trajectory_replay.py` injects those
responses at the real model-call boundary and drives the actual Phase 1
coordinator; only Lean generation itself is replaced by deterministic recorded
freeze outcomes.

The `20260801-014205` trajectory preserves the startup regression where a
future consumer's missing-member finding blocked a ready provider and delayed
the first frontier gateway until 913 seconds. This case uses the real closure
checker. It requires the provider frontier to freeze without editing the future
consumer, then requires that consumer alone to be corrected when it becomes
dependency-ready.

`frontier_gateway_exhaustion.json` preserves the failure later in that same
run: both correction tiers had already failed for
`def:finite-register-operators`, but the unchanged rejected plan stayed
installed and consumed 98 additional repair trials in roughly two seconds. The
regression requires exhausted entries to be invalidated so the next bounded
outer retry performs fresh scoped planning.

`mixed_plan_audit_routing.json` preserves the mixed plan-audit response from
`run-20260801-022052`. One issue supplied concrete evidence authorizing a
blueprint edit, while its sibling explicitly supplied no such evidence. The
old batch-level route sent both nodes to blueprint repair. The regression
requires per-node authorization: only the first node may mutate the blueprint,
and the sibling must remain a scoped plan/Lean correction.

`compile_plan_defect_head_of_line.json` preserves the compile-worker ordering
from `run-20260801-030727`. Lean had already proved that
`def:finite-register-operators` copied a compiler-invalid plan at `+1265s`, but
its plan correction waited until `+1631s` for unrelated sibling model calls.
The regression drives the real parallel compile coordinator and requires a
completed failure to enter its existing routing transaction before the slowest
sibling finishes. It does not change how the failure is classified.

`uue_repeated_compile_failure_lifecycle.json` preserves the repeated
`thm:security` compiler failures from `run-20260803-031013`. Ordinary compile
failures bypassed the persisted per-node retry lifecycle and regenerated
malformed Lean through retries 51-55. The paired executable regression requires
base and escalated compiler failures to use the same bounded lifecycle as
statement-audit failures, switch once to blueprint-direct generation, and route
only exhaustion of that direct lifecycle to scoped decomposition.

`simplex_precompile_deterministic_failure_lifecycle.json` preserves the
`remark:geometric-recursion-gap` loop from `run-20260813-235136`. A
pre-compilation deterministic rejection bypassed that same lifecycle and
restarted ordinary generation from retries 28 through at least 57. The paired
regression requires deterministic generation failures to escalate once,
switch once to blueprint-direct generation, and route only exhaustion of that
direct lifecycle to scoped decomposition. A separate executable check protects
the immediate root cause: canonical blueprint target names are exempt from the
helper-name placeholder heuristic.

`parallel_retry_state.json` preserves the three-worker Phase 1 overlap from
`run-20260801-041251`. Three generation calls began together at `+1051s`, while
another call entered the same wave at `+1070s`. Those workers share retained
candidate and rejection-feedback dictionaries. The fixture records the
historical concurrency boundary; the paired threaded unit regression requires
candidate transitions, cumulative feedback, and continuation snapshots to be
atomic at that boundary.

`empty_tournament_serial_fallback.json` preserves the failed initial-plan
tournament from `run-20260801-051352`. Candidate A returned an explicit empty
contract set twice by `+35s`, but its worker then remained idle until candidate
B timed out at `+309s`. Only then did the required 292-second recovery begin.
The regression requires that unchanged recovery to start in the freed worker
slot while B is still running, removing at least 274 seconds from the recorded
critical path without adding work to a healthy tournament.

`repairable_tournament_admission.json` preserves tournament 2 from
`run-20260801-180629`. Candidate B covered all 52 contracts and had only four
closure findings in four isolated components; only
`def:finite-register-operators` blocked the three-node initial frontier. The
strict frontier policy discarded it and ran three more complete tournaments.
The regression requires the deterministic cost boundary to retain this plan
for existing scoped closure repair while the catastrophic-plan fixture remains
ineligible.

`repeated_plan_semantic_exhaustion.json` preserves the
`def:finite-register-operators` loop from `run-20260801-054159`. The same
statement fingerprint received three interface-plan correction calls while the
critic continued to reject an opaque placeholder interface. The regression
drives the real shared semantic-exhaustion router and requires one plan
correction, one blueprint-direct generation lifecycle, and decomposition only
if that blueprint-direct lifecycle also exhausts.

`invalid_patch_import.json` preserves the obsolete Mathlib import emitted in
`run-20260801-070856`. The import detector correctly rejected
`Mathlib.Data.Polynomial.Basic`, but the patch merge had already copied it into
the persistent skeleton. The regression requires import filtering on the final
merged module, before Lean compilation or retry state can retain the bad import.

`planned_member_shadowing.json` preserves the repeated
`def:positive-loewner-density` compiler failure from `run-20260801-074355`.
The interface declared a local field named `DensityOperator` and later fields
depended on it, while a separate planned helper had the same name. Bare-helper
canonicalization incorrectly rewrote the local dependent references to the
global helper. The paired executable regression requires local member
shadowing while retaining the earlier downstream bare-alias behavior.

The fixtures contain hashes, outcomes, durations, timestamps, and minimal
synthetic compiler inputs needed by the policy tests. They do not contain paper
text, model prompts, or full generated formalizations.

`blueprint_direct_sibling_evidence.json` preserves the circuit-breaker state
corruption from Simplex `run-20260814-235036`. One unchanged statement acquired
audit findings owned by two sibling nodes, so unrelated sibling corrections
changed its plan fingerprint and discarded its retained candidate. The paired
regression requires blueprint-direct evidence and fingerprints to remain
declaration-owned while still allowing each sibling's own evidence to evolve.

`integration_gate_reuse.json` preserves the 699-second boundary between the
last frozen Phase 1 contract and Phase 2 in the Simplex snapshot
`run-20260802-115840`. All 39 generated modules had already compiled when they
froze. The regression requires the final integration gate to reuse all 39
matching objects, perform no section recompilation, and retain one aggregate
import check over the complete environment.
