# Phase 1 orchestration replay fixtures

These fixtures preserve minimal, provider-neutral observations from historical
Phase 1 runs that exposed retry and scheduling regressions. They are committed
test resources: the tests do not need local `.auto-blueprint/` telemetry, R2,
network access, or a model account.

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

The fixtures contain hashes, outcomes, durations, and timestamps needed by the
policy tests. They do not contain paper text, prompts, or generated Lean source.
