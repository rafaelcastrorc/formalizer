# Phase 1 orchestration replay fixtures

These fixtures preserve minimal, provider-neutral observations from historical
Phase 1 runs that exposed retry and scheduling regressions. They are committed
test resources: the tests do not need local `.auto-blueprint/` telemetry, R2,
network access, or a model account.

`extension_certificate_scope_mismatch.json` preserves the Claim Five
oscillation from `run-20260902-200908-ec9c6470`. One candidate omitted the
restrictions on newly introduced extension data; its replacement incorrectly
applied those restrictions to inherited data too. The executable regression
requires a complete, structured extension certificate to route directly to the
existing transactional blueprint-decomposition boundary. It also requires an
incomplete certificate to remain an ordinary Lean/plan correction, so free text
or a partial model suggestion cannot authorize a blueprint edit.

`theorem_like_contract_poisoning.json` preserves the terminal Simplex loop from
`run-20260827-131622`. A rejected theorem-like candidate was emitted as
`def ... : Prop := sorry`, rewrote its own authoritative contract before the
same deterministic transaction rejected it, and then lost its producing tier
when targeted correction exhausted. Retries 33--100 consequently consumed the
shared outer budget in ten seconds with no model call or state progress. The
paired executable regressions require theorem-like targets to remain theorem or
lemma declarations with a concrete proposition, make candidate contract
realization atomic with deterministic acceptance, and preserve the producing
tier so the existing bounded exhaustion router changes strategy immediately.

`terminal_sorry_outer_let.json` preserves two legal Phase-1 declaration shapes
observed in Simplex and unconditional-unclonable-encryption: the theorem result
type contains an unparenthesized `let` or `letI` assignment before the final
`:= sorry`. The regression requires ingestion and frozen-interface extraction
to remove only the final Phase-1 marker. It also retains a completed-definition
control proving that actual implementation bodies are still deferred.

`structured_statement_audit_routing.json` preserves the exact three-node
statement-audit response from Simplex telemetry sequence 827/829. The critic
classified every issue as a plan-origin `lean_translation_issue`, named the
existing required dependencies, and requested no helper or missing blueprint
information. The former prose-keyword override nevertheless routed two labels
to decomposition. The executable regression requires all three labels to stay
on plan/Lean correction while retaining their deterministic dependency-edge
evidence.

`scoped_blueprint_repair.json` preserves the response shapes needed by the
provider-neutral blueprint-repair boundary: a singleton repair, a multi-target
Simplex-style repair with target-owned helpers, and invalid responses that try
to edit a pre-existing sibling, omit a requested target, or assign one helper
to two targets. The executable regression also proves that Python applies the
response to the immutable pre-call source even if a backend somehow changes
the draft path before returning.

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

The fourth case preserves the Simplex `prop:newton-pieces` boundary failure
from `run-20260903-021411`. The repaired proposition claimed a correspondence
under a "suitable affine isomorphism" without exposing the witness, its source
and target, or the action needed by consumers. The historical audit accepted
that component, after which Phase 1 spent repeated generation and audit calls
inventing incompatible representations. The regression requires this defect
to return to the existing blueprint-repair transaction before Lean generation;
ordinary complete existential theorems remain accepted.

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

`simplex_interface_usability_lifecycle.json` preserves the Phase 1 interface
elaboration failures from `run-20260831-022739`. Lean timed out even after the
pipeline had replaced every target implementation and proof by `sorry`, but the
old generic compile-failure route treated those timeouts as evidence for adding
new mathematical helper nodes. The paired regressions require one bounded plan
correction, one switch to blueprint-direct statement generation, and then only
ordinary bounded retries for that unchanged statement. A compiler timeout by
itself must never authorize blueprint repair or decomposition. Recognition is
required at the first local Lean check, before any compiler-patch model call;
malformed Lean continues through the existing compiler-failure lifecycle.

`scoped_compile_failure_attribution.json` preserves the twelve-contract
Simplex compiler group from `run-20260820-032411`. Lean diagnostics identified
only `def:relu-network`, but the old router advanced all eleven unrelated
siblings through their retry lifecycle and later spent 706.4 model-seconds on
three of them. The paired regressions require only the diagnostic owner to
advance *and* require the exact generated declarations for the other eleven
siblings to survive the failed all-or-nothing compile. Those siblings are
isolated with their owned helpers, rechecked through the ordinary deterministic
and Lean gates, and frozen without another generation call. Truly unattributed
compiler output still uses the existing group isolation route.

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

`explicit_open_claim.json` preserves the Simplex source shape that exposed an
open mathematical question inside a generic `proposition` environment labeled
`remark:open-depth-questions`. The paired negative control uses the topological
phrase "open set". The regression requires only the explicit question to enter
the configured conjecture policy.

`blueprint_direct_sibling_evidence.json` preserves the circuit-breaker state
corruption from Simplex `run-20260814-235036`. One unchanged statement acquired
audit findings owned by two sibling nodes, so unrelated sibling corrections
changed its plan fingerprint and discarded its retained candidate. The paired
regression requires blueprint-direct evidence and fingerprints to remain
declaration-owned. Once a statement is already blueprint-direct, later findings
are cumulative retry feedback and cannot reactivate the strategy or redefine its
fingerprint.

The Phase-2 fixture
`../phase2_orchestration_replay/provider_contract_ownership.json` preserves two
later Simplex failures from run `20260823-001604`: a caught queued repair that
was activated without its required rollback snapshot, and two scoped boundary
audits that repeatedly blamed changed consumer helpers even though both named
the same missing capability in the unchanged dependency provider. Regressions
require every activation path to cross the snapshot gate and require a
provider diagnosis to remain inside the original root's existing dependency
closure, roll back the consumer transaction, and queue the provider separately.

`blueprint_direct_reactivation.json` records the repeated
`prop:linear-size` activation from Simplex `run-20260823-001604`. The statement
fingerprint did not change between the candidate semantic exhaustion and the
later integrated-audit finding, but the old implementation crossed the
generation-epoch boundary again and erased its retry state. The paired
regression requires one activation, a continuous base/escalation lifecycle, and
a genuinely new activation only after the blueprint statement changes.

`integration_gate_reuse.json` preserves the 699-second boundary between the
last frozen Phase 1 contract and Phase 2 in the Simplex snapshot
`run-20260802-115840`. All 39 generated modules had already compiled when they
froze. The regression requires the final integration gate to reuse all 39
matching objects, perform no section recompilation, and retain one aggregate
import check over the complete environment.

`candidate_contract_refresh_lifecycle.json` preserves the 282 candidate-header
epoch transitions in Simplex `run-20260825-194345`. The paired executable
regression requires a candidate-owned typed-contract refresh to preserve the
same candidate, retry lifecycle, and exchange history. Only a genuine
blueprint, plan-authority, or generation-strategy change may cross the full
Phase 1 epoch boundary.

`evidence_lifecycle_matrix.json` unifies the validity boundaries demonstrated
by the semantic/compiler handoff, immediate dependency-edge, blueprint-direct
reactivation, sibling-isolation, and candidate contract-refresh fixtures.
Executable regressions require statement facts to survive plan/candidate
replacement, plan facts to expire with a changed plan, candidate diagnostics
to expire with replaced Lean, and dependency observations to be consumed only
by the exact graph transaction that uses them.
