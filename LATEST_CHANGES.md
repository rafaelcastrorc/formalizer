# Latest Changes

## 2026-08-22: Replace the Read-Only Exploration Allowance With a Text-Only Call Contract

### Confirmed failure

Every generation call is read-only by design (README: read-only model calls):
`claude-code` removes all tools, `codex` disables execution, and API backends
never receive tools; the harness alone inspects the repository, searches
libraries, and compiles. The Phase-1 statement, Phase-1 patch, and Phase-2
proof prompts nevertheless told the model to "Spend AT MOST half of it
verifying library APIs or exploring" — an activity no backend can perform.
Because readonly Claude Code removes the tools from the schema rather than
denying calls at runtime, the model received no "tool unavailable" feedback:
recorded calls emitted tool-invocation markup, bare shell commands, or
investigation narration as plain assistant text — sometimes hallucinating the
file contents they claimed to have read — and that text was stored as the
model's answer.

Across the stored telemetry corpus, 62 of 404 Phase-1 statement-generation
responses (15.3%) contained no Lean declaration at all (12 tool-markup, 25
shell-command, 19 narration, 6 other), wasting 66.5 minutes of model time
directly (mean 64.3s, max 488.8s at the opus escalation tier). Twenty-two were
multi-label batches, so the batch-scoped router isolated/bisected them; 61
labels were regenerated, consuming 274 follow-up calls and 105.6 minutes
before the next success, 110 of them at a changed model/effort tier. The
Phase-2 proof prompt shares the same sentence and recorded 5 of 72 such
responses.

### Correction

- The four prompts that carried the sentence — Phase-1 bulk statement
  generation, Phase-1 retry generation, Phase-1 targeted declaration patch,
  and Phase-2 proof bodies — now share one provider-neutral
  `_text_only_budget_rule`. It states the actual contract: the call is
  text-only, no shell/file/search/web tool exists, tool-invocation text is
  rejected as commentary, the supplied module paths/interfaces/API snippets
  are already verified, and the model must reason from them and never end the
  budget without the requested code.
- The original timeout protections are retained: leave time to emit, an
  imperfect reply beats no reply, the compiler and audits catch mistakes.
  Only the impossible exploration allowance is removed. This mirrors the
  contract `_initial_declaration_prompt` already used successfully.
- No retry policy, import handling, schema rule, or provider-specific branch
  changes. Specific-imports guidance ("never blanket `import Mathlib`") and
  the statements-only Phase-1 schema are untouched and now pinned by tests.
- Follow-up evidence, deliberately not changed here: `phase2_whole_node_repair`
  prompts never contained the exploration sentence yet recorded 45/157 (29%)
  tool-narration responses, confirming the root cause is the model never being
  told its tools are gone. Extending the text-only contract to those prompts
  needs its own validation pass.

### Validation

A/B validation used the production `claude-code` read-only runner, ingestion
boundary, deterministic skeleton gates, Lean compiler, and statement-alignment
audit on four recorded failing prompts from Simplex telemetry run
`20260821-181032` (seq 447, 449, 591 at sonnet/medium/300s; seq 2236 at
opus/high/600s — the call that historically wasted 488.8s). Control was the
exact recorded prompt; treatment replaced only the budget bullet. Three
repetitions per arm per case (24 calls):

- recorded tool/narration no-Lean failures: control 6/12, treatment 0/12;
- tool pantomime anywhere in the response: control 6/12, treatment 0/12;
- responses reaching the deterministic gates: control 6/12, treatment 11/12
  (the one exception was an empty 300s timeout on the hardest batch, matched
  by an equal control timeout on the same case);
- compiled candidates 3 vs 2; audit-accepted declarations 2 vs 1; model time
  per audit-accepted declaration 18.6 min (treatment) vs 25.5 min (control);
- conditional on reaching the gates, deterministic-finding rates were
  equivalent (4/6 vs 7/11), and the two partial-coverage treatment responses
  are exactly the shape the partial-response salvage path retains.

The Codex CLI and API backends are not installed or configured on this
machine (the complete local telemetry corpus is `claude-code`/`anthropic`),
so the mandated Codex cross-check could not run; the change is one shared
provider-neutral sentence with no Claude-only branching, and Codex validation
should be repeated on a codex-equipped machine before relying on that runner.

Committed regression fixtures under `tests/fixtures/phase1_tool_narration/`
preserve the four recorded responses; `tests/test_phase1_text_only_contract.py`
verifies they stay deterministic format rejections and that all four prompts
carry the text-only contract with the exploration wording gone and the
specific-import rule intact. The full suite ran 427 tests with one
pre-existing, unrelated error: `opaque_theorem_object_reuse.json`, cited by
the 2026-08-21 fast-path entry below, was never actually committed, so its
test fails on a clean checkout. Every committed Phase-1 plan replay passed
with `--require-progress`, the scheduler-latency replay reproduced its
documented bounds, the Phase-2 retained-candidate replay retained its
`2.741x` result, and Python compilation and `git diff --check` passed.

## 2026-08-21: Keep Opaque Theorem Proofs on the Phase-2 Object Fast Path

### Confirmed failure

Phase 2 intentionally retained Phase-1 `.olean` files after theorem-only proof
updates because theorem proofs are opaque to importers. The later integration
gate nevertheless hashed the complete edited `.lean` source. It therefore
declared the retained object stale and propagated that false invalidation into
importers. The historical transaction rebuilt 43 of 51 modules after 42
theorem proof-body edits, contradicting the documented fast path.

### Correction

- Reusable-object fingerprints now erase only theorem/lemma proof bodies.
- Exact theorem statements, complete definition-like bodies, structures,
  instances, imports, options, preamble commands, imported object interfaces,
  and Lean environment files remain fingerprinted.
- Exact source SHA-256 remains a separate persisted state check, and final
  publication still compiles the fully assembled exact source from scratch.
- `--continue` migrates old object keys deterministically without rebuilding
  known-good objects. No model prompt, blueprint edge, or provider behavior
  changes.

### Validation

The committed historical-shape replay contains 51 modules, 42 theorem proof
updates, and the downstream importer that made the old key rebuild 43 modules.
It requires zero rebuilds under the object-semantic key. Focused regressions
also require theorem statement edits and definition-body edits to invalidate
their objects, while an exact-source hash still changes for a theorem proof
edit. Validation completed with all 420 Python tests passing, every committed
Phase-1 plan replay passing with progress required, both scheduler-latency
fixtures passing, the Phase-2 retained-candidate replay retaining its `2.741x`
logical speedup, Python compilation, and `git diff --check`.

## 2026-08-21: Enforce Header-Only Phase-1 Model Output

### Confirmed failure

The Phase-1 prompt told models to end ordinary definitions in `:= sorry`, but
also allowed a definition node to become a structure. In Simplex
`run-20260821-105325`, `def:cpwl-function` was described by both the blueprint
and compact plan as a predicate, yet generation emitted a `Prop`-valued
structure with data fields. Lean rejected that structure. The first targeted
repair correctly translated its fields into a completed predicate body, but
the pipeline then persisted that entire body as the candidate-derived "exact
typed contract" while simultaneously asking the next repair to end in
`:= sorry`. The next response satisfied both contradictory instructions by
moving the predicate formula into the result type, corrupting the public
contract and triggering downstream correction work.

### Correction

- Phase-1 generation and patch prompts now distinguish an ordinary predicate
  (`def ... : Prop := sorry`) from a genuinely bundled data object. A structure
  cannot be used merely to package predicate conditions or witnesses.
- Every Phase-1 model-response path now passes through one provider-neutral
  ingestion boundary. Completed ordinary definition bodies and theorem proofs
  are reduced to their public header plus terminal `:= sorry` before contract
  realization, deterministic checking, timeout salvage, or targeted patching.
- The exact historical malformed form `structure NAME ... : Prop where ...`
  is normalized at that same boundary to `def NAME ... : Prop := sorry`.
  This preserves the already-emitted public binders and result sort without a
  Lean failure or model repair. Type-valued structures are not rewritten.
- Candidate-derived typed contracts strip ordinary bodies independently, so a
  missed or historical unnormalised candidate cannot feed implementation text
  back to a model as an authoritative target signature.
- The existing transparent alias to a same-node, candidate-owned structural
  interface remains unchanged.

### Validation

The regression fixture contains the actual completed CPWL predicate returned
by the historical repair. It verifies deterministic deferral to
`def ... : Prop := sorry`, header-only contract extraction, telemetry, and
preservation of the structural-alias exception.

Validation completed on 2026-08-21:

- the full Python suite passed: 416 tests;
- the committed historical Phase-1 plan replay passed with progress required;
- the committed scheduler-latency replay passed for both historical fixtures;
- a real `codex:gpt-5.5` call through the production read-only runner returned
  an ordinary CPWL predicate ending in `:= sorry` in 14.4 seconds, with no
  completed body or predicate-as-structure substitution;
- that exact declaration compiled with the repository's Lean/Mathlib
  toolchain; Lean emitted only the expected `declaration uses sorry` warning.

## 2026-08-21: Publish Implemented Phase-2 Definition Bodies to Importers

### Confirmed failure

Phase 2 correctly wrote completed definition bodies to generated `.lean`
files, but deliberately retained the Phase-1 `.olean` objects. That shortcut
is valid for theorem proofs because their bodies are opaque and their public
types do not change. It is invalid for `def`/`abbrev` implementations that a
downstream proof must unfold. In the current Simplex run,
`Skeleton08.lean` contained the completed recursive body of
`def_polytope_classes`, while its older `Skeleton08.olean` still printed and
reduced that declaration as `fun ... => sorry`. The downstream delta-four
proof therefore could not use the accepted recursive definition and repeatedly
requested blueprint helpers.

This also explains the measured helper churn without blaming missing planning.
All 21 helper nodes retained in the current draft have direct consumers and are
transitively reachable from original blueprint nodes, but telemetry contains
49 earlier repair-added helper labels that no longer exist in the draft.
Phase-1 model time does not support amplifying the initial planner for helpers:
original-node calls averaged 25.8 seconds (20.8-second median), while introduced
helper calls averaged 23.4 seconds (22.5-second median), with no timeout in
either group. Phase 2 was the divergence point: introduced-node calls averaged
122.4 seconds and recorded twelve timeouts, concentrated in the repeatedly
repaired delta-four component.

### Correction

- A Phase-2 section that accepts at least one definition-like body now rebuilds
  and publishes its importable `.olean` before progress is persisted.
- The existing theorem-only fast path remains unchanged; replacing an opaque
  theorem proof does not rebuild its object.
- Object publication and state persistence share the existing state lock. If
  publication unexpectedly fails, the complete section source and its previous
  object are restored, and none of that section's tentative completions count
  as accepted.
- No blueprint edge or helper is inferred, no model prompt changes, and no
  provider-specific behavior is introduced.

### Validation

Three focused regressions cover definition refresh, theorem-only object reuse,
and transactional rollback. A real Lean integration reproduction first built a
Phase-1 provider with a `sorry` definition and confirmed that an importing
module could not prove its concrete value; after the Phase-2 source change and
object refresh, the same import compiled successfully. The full suite passed
all 413 tests, every committed Phase-1 plan replay, the Phase-1 scheduler
latency replay, and the Phase-2 retained-candidate replay (`2.741x` simulated
speedup), followed by `git diff --check`.

## 2026-08-21: Make the Compact Planner Model Tier Configurable

The compact Phase-1 semantic planner previously always used the base runner.
The Refine UI now offers **Base model** (the unchanged default) and
**Escalation model** for that call, backed by `--planner-tier
base|escalation`. The selected tier applies to both the primary planner call
and its hedge; it does not alter statement generation, repair, or Phase-2 model
routing. Telemetry and the generated report record the selected tier and
runner. Routing tests cover both choices and the Web UI command mapping.

## 2026-08-21: Preserve Semantic Guidance for Newly Introduced Helpers

### Confirmed failure

Simplex `run-20260821-001641` recorded compact semantic plans for every helper
before statement generation, but `_design_plan_block` selected its source
globally: if any candidate-derived typed contract existed, it rendered only
typed entries. A helper introduced by decomposition normally has semantic
guidance before it has a typed candidate, so neighboring typed contracts hid
the new helper's own obligations. For
`lem:geometric-recursion-edge-realization-preservation`, the stored plan
required the ambient dimension, the one-hidden-layer compression block, and
preservation of the represented function. None of those plan requirements
appeared in its first generation prompt, and the returned statement was
rejected for exactly those omissions.

This was a mixed-state prompt-rendering bug, not evidence that helpers are
intrinsically slower. Across 125 stored Simplex runs, helper-only Phase 1
generation calls had a 25.4-second mean and 19.4-second median, compared with
28.5 seconds and 21.5 seconds for original-node calls. In the affected run,
added nodes cost more only after repeated generation, audit, and repair work.
The geometric-recursion component accumulated 101 model calls and about 2,881
seconds of allocated model time.

### Correction

- Prompt guidance is now selected independently per node. A nonempty typed
  candidate contract wins for that node; otherwise its compact semantic plan
  is rendered even when neighboring nodes already have typed contracts.
- Current targets are rendered before surrounding context so their guidance
  cannot be truncated by the existing 9,000-character prompt budget.
- Blueprint-direct generation still suppresses both plan forms for the exact
  target fingerprint, preserving the existing plan circuit breaker.
- The compact planner remains advisory and untyped. This change does not
  restore the retired global typed-planning pass or make a model plan an
  authority over the blueprint.

### Validation

The regression reproduces the historical mixed state with an existing typed
`def:relu-network` contract and only semantic guidance for the newly introduced
geometric-recursion helper. It fails on the old all-or-nothing renderer and
passes only when both the provider's typed interface and the helper's own
semantic obligations reach generation.

All 409 discovered tests passed, along with every committed Phase 1 plan
replay, the Phase 1 scheduler-latency replay, Python compilation, and
`git diff --check`. A production call through `codex:gpt-5.5` at medium effort
using the current Simplex draft, exact frozen dependency interfaces, and the
corrected mixed plan completed in 27.8 seconds. It returned a statement that
quantifies the ambient dimension, consumes the later ReLU network and all
three compression/containment dependencies, and concludes that a composed
network computes exactly `T_{a,b+4}`. A standalone recompilation of that
response was blocked before elaboration by a missing stale generated
`Skeleton59.olean`; this is an existing local generated-artifact condition,
not a diagnostic against the returned declaration.

## 2026-08-20: Recover Silent Planning, Preserve Compiling Siblings, and Narrow Imports

### Confirmed failures

- In Simplex `run-20260820-124446`, the compact semantic-planning call emitted
  no response for 600 seconds. The exact 57,564-character prompt had completed
  in 246-372 seconds in the preceding recorded runs, and a real replay completed
  successfully, so accepting an all-node fallback after that silent execution
  outlier discarded useful coordination.
- The same run generated twelve contracts at once and Lean diagnostics belonged
  to only five. Telemetry reported seven preserved siblings, but the
  all-or-nothing freezer had already deleted their generated module; all twelve
  were later regenerated. Six of those seven historical sibling declarations
  independently passed the production statement audit.
- A successful broad `import Mathlib` diagnosis was persisted permanently.
  The current generated Simplex module compiled in 13.0 seconds with the broad
  import versus 7.1 seconds with the exact required module, and historical
  object checks showed a 6.36-second median without broad fallback versus
  15.06 seconds with it.

### Corrections

- A completely silent semantic-plan timeout gets exactly one fresh call using
  the same base runner and timeout. Partial or malformed output still follows
  the existing deterministic parser/fallback path; this is not a new semantic
  repair loop.
- Attributed compiler failures now split the exact post-correction candidate at
  existing target/helper ownership boundaries. Unaffected siblings rerun every
  normal deterministic and Lean gate and freeze without generation; only true
  diagnostic owners enter the existing provider-neutral failure router.
  Ambiguous diagnostics retain the whole-component route.
- Broad Mathlib compilation remains a diagnostic correctness fallback. After it
  succeeds, unresolved names are matched against selected, ready local library
  declarations and the unchanged candidate is compiled with exact prefixed
  module imports. Broad Mathlib is retained only if that narrower compile fails.

### Validation

The compact-planner suite covers the one-call silent recovery boundary. The
committed `scoped_compile_failure_attribution.json` historical fixture now
checks preservation of the generated sibling declarations themselves, not only
their retry counters. Import tests cover qualified-name extraction, source-root
prefixing for any selected Lean library, and narrow module persistence.

All 403 discovered tests passed, as did every committed Phase 1 plan replay,
the Phase 1 scheduler-latency replay, the Phase 2 latency replay, Python
compilation, and `git diff --check`. Post-implementation production validation
used the exact 57,564-character historical semantic-plan prompt with
`codex:gpt-5.5` at medium effort: the first call reproduced the silent timeout,
while the single fresh recovery returned 107/107 unique requested entries in
413.9 seconds, with no unauthorized provider requirements. The seven
historically discarded sibling declarations all compiled with the real project
Lean/Mathlib toolchain. A fresh production statement audit accepted six of
those seven and isolated the one actual semantic defect, confirming that
candidate preservation retains usable work without bypassing alignment.

## 2026-08-20: Scope Phase 1 Compiler Retries to Diagnostic Owners

### Confirmed failure

In Simplex `run-20260820-032411`, one twelve-contract compiler command failed
with diagnostics owned only by `def:relu-network`. Diagnostic attribution was
already declaration-aware, but `_route_phase1_compile_failure` subsequently
advanced all twelve nodes through the retry lifecycle by falling back to the
complete compiler group. Eleven unrelated siblings therefore inherited the
same error and escalation tier. Three of those unnecessary model calls alone
consumed 706.4 seconds. A scan of recorded compiler-failure groups found 65
unsupported sibling advances in 20 cases across nine runs.

### Correction

- When compiler diagnostics are attributed to declaration ranges, only those
  owning labels consume a retry or enter escalation/exhaustion routing.
- Unrelated siblings retain their candidates and current retry tiers so the
  scheduler can recheck them independently.
- When compiler output has no attributable source location, the existing
  whole-group isolation/bisection route remains unchanged. The fix therefore
  does not suppress ambiguous failures.
- The behavior is provider-neutral: it operates on Lean diagnostics after
  generation and does not depend on Codex, Claude, or API response formats.
- Telemetry now records both the diagnostic owners and preserved siblings in
  `phase1_compile_unattributed_siblings_preserved`.

### Validation

Added the committed historical fixture
`scoped_compile_failure_attribution.json` and executable regressions for both
attributed and genuinely unattributed compiler failures. All 398 tests, the
committed Phase 1 plan replay, scheduler-latency replay, Phase 2 latency replay,
and `git diff --check` pass. The exact stored historical
`lem:claim-five-q-membership` prompt was also replayed through the production
`codex:gpt-5.5` runner at medium effort: the model returned a declaration in
20.5 seconds and the project Lean/Mathlib toolchain compiled it successfully.

## 2026-08-20: Give Every Phase 2 Repair Activation a Fresh Rollback Baseline

### Confirmed failure

The Simplex run `run-20260820-032411` activated the queued repair for
`thm:previous-cpwl-bound` but emitted no matching
`phase2_repair_transaction_snapshot` event. When another Phase 2 worker later
requested decomposition during verification, rollback failed with
`active Phase 2 blueprint repair has no pre-edit transaction snapshot` and
terminated the run after 19,158 seconds. Repair queue IDs are content-derived,
so an old directory for the same diagnosis could make transaction startup
silently reuse an earlier lifecycle instead of recording the current pre-edit
state.

### Correction

- A newly activated queued repair now replaces any transaction directory for
  that request ID with the current pre-edit blueprint, generated Lean, Lake
  artifacts, and scheduler state.
- An already-active transaction, including one restored by `--continue`, keeps
  its original rollback baseline instead of overwriting it.
- Snapshot creation verifies that its manifest was committed durably.
- A repair cannot enter the verification stage unless its pre-edit snapshot is
  present. This catches any future lifecycle violation before another repair
  can depend on unverified edits.

### Regression

Added a regression that leaves a stale snapshot for a content-derived request
ID, reactivates the request against a new blueprint baseline, rejects the
provisional edit, and verifies rollback restores the new baseline. A second
regression enforces the verification-stage snapshot invariant. All 396 tests,
the committed Phase 1 plan replay, scheduler-latency replay, Phase 2 latency
replay, and `git diff --check` pass.

## 2026-08-20: Independently Adjudicate Phase 1 Decomposition Refusals

### Confirmed failure

Across 33 recorded first-refusal/follow-up pairs, the initial Phase 1
`NEEDS-DECOMPOSITION` response took a median 18.3 seconds, while the forced
follow-up took a median 75.2 seconds and consumed 2,642.9 seconds in total.
Thirty-two follow-ups resumed the producer session, received the refusal as
prior candidate code, and were instructed to make a stronger attempt. That
biased the second call toward defending or overturning its own diagnosis rather
than independently deciding whether the blueprint actually lacked an
interface.

### Correction

- The first refusal remains a generator claim and cannot mutate the blueprint.
- The escalation call is now a neutral adjudication: it may emit the exact
  Phase 1 declarations or independently confirm the structured decomposition
  finding.
- That adjudication explicitly ignores lifecycle-local and persisted producer
  sessions. Its newly created session is still retained for later corrections.
- The refusal is no longer passed as previous Lean code. Telemetry records the
  fresh-session adjudication explicitly.
- The change is provider-neutral. Session-capable CLIs start fresh; API and
  other sessionless runners receive the same neutral adjudication prompt.

### Regression

Added focused tests proving that forced-fresh calls ignore both local and
persisted sessions while retaining the new session, and that a base refusal is
followed by exactly one fresh, neutral escalation adjudication. Historical
four-case real-model probes reduced the adjudication total from 743.4 seconds
under forced resumed retries to 74.5 seconds with independent calls, while all
four retained the same missing-interface diagnosis.

## 2026-08-17: Candidate-Owned Audit Defects Switch to Blueprint-Direct Generation

### Confirmed failure

Real-model validation found a Phase 1 case where generated Lean compiled but
the statement-alignment audit rejected the candidate-owned contract itself. The
`def:relu-network` example stored arbitrary functions instead of the affine
layer/composition semantics required by the blueprint. The old route treated
that as ordinary Lean-generation failure, so the next call could keep trying to
repair Lean against the same rejected local contract.

### Correction

- If a semantic audit rejects a declaration whose plan entry originated from a
  Phase 1 candidate (`origin == phase1_candidate`) and the audit names concrete
  missing blueprint requirements, the node no longer retries under that stale
  candidate-owned plan.
- The node switches to the existing blueprint-direct generation lifecycle with
  the exact audit evidence attached.
- Dependency-edge findings still use the deterministic dependency-repair path;
  accepted audit verdicts still freeze normally.

### Regression

Added focused regressions for both integrated-audit and semantic-first routing.
Real-model spot checks covered an accepted case, a dependency-edge case, and the
candidate-owned `def:relu-network` defect. Full unit tests and Phase 1
historical replays pass.

## 2026-08-17: Invalidate Downstream Plans Only After Interface Fingerprint Changes

### Confirmed failure

Switching a child node to blueprint-direct generation safely abandoned the
child's bad local plan, but downstream plans could still have been written
against that child's old public surface. An immediate downstream invalidation
would be safe but too aggressive: if the regenerated child exposed the same
interface, it would force unnecessary model calls.

### Correction

- Blueprint-direct activation records the child node's previous public
  interface fingerprint.
- The run persists that fingerprint through `--continue`.
- When the child contract later freezes, the accepted public interface
  fingerprint is computed from the frozen typed contract surface.
- Downstream cached plans, alternates, candidates, and retry state are cleared
  only if the accepted interface fingerprint differs from the previous one.
- If the public interface is unchanged, upstream cached work remains reusable.

### Regression

Added a regression proving that activation alone does not clear an upstream
plan, freezing with the same interface still preserves it, and freezing with a
changed interface invalidates only the downstream stale state. Full unit tests,
Phase 1 historical replays, scheduler latency replay, and `git diff --check`
pass.

## 2026-08-17: Route Missing Named Object Audit Failures to Decomposition

### Confirmed failure

The Simplex telemetry showed `lem:claim-five-r-membership` repeatedly failing
Phase 1 statement alignment because the generated declaration did not expose
the four concrete lifted `R13`, `R14`, `R23`, and `R24` terms and their
half-sum formulas. The critic evidence identified missing concrete mathematical
objects, but the router treated the finding as ordinary Lean-generation failure,
which allowed repeated statement retries and eventual long model-call timeouts.

### Correction

- Statement-audit routing now recognizes reject evidence that explicitly says a
  declaration is missing concrete, named, lifted, bundled, displayed, or
  explicit mathematical objects, terms, formulas, operations, relations, or
  interfaces.
- Only that narrow evidence class is rerouted to the existing blueprint
  decomposition path; generic representation complaints and ordinary Lean
  translation failures still remain Lean-generation issues.
- The change adds no model call. It changes the destination of an already
  required audit verdict so the existing scoped decomposition transaction can
  create the missing helper nodes instead of retrying the same under-exposed
  statement.

### Regression

Added a focused regression for the historical lifted-`R13`/`R14`/`R23`/`R24`
shape and kept the existing guard that representation-style audit complaints do
not authorize blueprint repair. Full unit tests and Phase 1 historical replays
pass.

## 2026-08-15: Keep Deferred Predicate Bodies Out of Phase 1 Contracts

The Simplex refinement generated a correct predicate header for
`def:common-face`, but the statement critic rejected it because its terminal
`sorry` did not yet implement the exposed-face and intersection clauses. A
subsequent Phase-1 correction moved those body semantics into the result type,
turning a predicate into a proposition asserted for every input.

- The shared statement-audit schema now distinguishes concrete public-interface
  defects from deferred body obligations.
- For a typed Phase-1 `def`/`abbrev` ending in `sorry`, body-only findings are
  carried as Phase-2 obligations and cannot trigger statement regeneration.
- Missing or wrongly typed parameters, wrong result types, and genuinely
  required public helpers still reject the Phase-1 contract.
- Added regressions for the exact deferred `common-face` predicate and for a
  malformed version that omits its public `F` parameter.

This changes no persisted-state migration policy. A run containing the earlier
reshaped contract must be restarted fresh; future fresh runs preserve the
correct predicate skeleton and audit its completed body in Phase 2.

## 2026-08-15: Centralize Phase 1 Generation-Epoch Transitions

### Problem

Plan correction, retained-alternate activation, closure repair, plan
invalidation, and blueprint-direct activation all change the contract under
which Phase 1 code is generated. These branches previously duplicated parts of
the required cleanup. One branch could clear the retry lifecycle but leave a
candidate, while another could prune candidates but retain an obsolete local
partition or exchange ledger. The stale-candidate bug below was one concrete
result of that split ownership.

### Correction

- One atomic transition now owns every scheduler store tied to the replaced
  Phase 1 generation epoch: candidate code, Phase 1 retry provenance, exact
  exchange history, quarantine, and local group partitions.
- The transition is a coordinator, not a second cleanup implementation. It
  composes the existing candidate, retry, quarantine, and partition primitives;
  only exchange-history clearing needed a new store-specific primitive.
- Semantic-plan revision now defers its transition until the full retained
  shared-candidate component is known, so that path crosses the epoch exactly
  once instead of first resetting the target and then resetting the component.
- Every live plan replacement, plan deletion, and strategy switch calls that
  transition at the mutation boundary. Downstream callers no longer repeat
  their own `_clear_retry_lifecycle`/candidate-pruning pairs.
- Shared-helper candidate components are removed atomically when any member's
  plan changes. Unaffected nodes keep their independent retry tier.
- Exact compiler and critic feedback is intentionally preserved. The one path
  that revises a semantically rejected contract captures the old compiling
  declaration before the transition and restores it afterwards only as an
  explicitly rejected correction seed.
- Parallel closure evaluation is non-committing. It changes only its isolated
  plan copy; the live transition happens once, after the accepted component is
  merged.

### Regression

The routing suite now verifies the transition across all owned scheduler
stores, including shared-helper candidate removal, while proving that Phase 2
retry state and exact Phase 1 feedback remain intact.

## 2026-08-15: Keep Phase 1 Candidates in Their Producing Strategy Epoch

### Confirmed failure

Simplex `run-20260815-013516` exhausted three compiler corrections for
`def:paper-claim-seven-block` and activated blueprint-direct generation at
`+1360s`. At `+1403s`, however, the next transaction launched no statement
generation call: the failed ordinary-plan candidate had been saved again as a
reusable candidate after the strategy changed. The pipeline then spent three
more compiler-correction calls on the same stale declaration before routing to
decomposition at `+1569s`.

### Correction

- Every in-memory Phase 1 candidate now carries the exact plan/strategy
  fingerprint under which its declarations were generated.
- Candidate persistence rejects code when that producing fingerprint differs
  from the current contract or blueprint-direct strategy. The code remains
  failure evidence, but cannot be relabelled as fresh output from a strategy
  that never generated it.
- The same epoch boundary now applies to the interface-usability route: its
  failed declaration is recorded before plan revision and is then pruned by
  the centralized transition. If correction is unavailable and the plan is
  invalidated, the same transition starts fresh scoped planning. Old code
  cannot be saved under either replacement.
- This does not reduce the documented three-sample stochastic allowance. A
  genuinely fresh blueprint-direct candidate retains its normal correction
  lifecycle; only the duplicate lifecycle over stale code is removed.

### Regression

The committed `blueprint_direct_candidate_epoch.json` fixture preserves the
observed transition and verifies that an ordinary-plan candidate cannot cross
the blueprint-direct epoch boundary as reusable code.

## 2026-08-15: Isolate Circuit-Breaker Evidence by Blueprint Node

### Confirmed failure

Simplex `run-20260814-235036` initially froze contracts quickly, then spent its
tail repeatedly regenerating the same declarations. The persisted scheduler
state showed that `def:reported-best-wang-sun-upper-bound` had retained audit
findings owned by `def:paper-max-construction` and
`remark:open-depth-questions`. Because blueprint-direct evidence participates
in the candidate plan fingerprint, every unrelated sibling finding made the
unchanged Wang-Sun candidate look stale and restarted its correction work.

### Correction

- The shared blueprint-direct circuit breaker now accepts declaration-owned
  evidence and stores only the slice belonging to each activated node.
- Compiler, semantic-audit, and deterministic-precompile exhaustion all pass
  their existing structured per-node evidence through the shared router.
- Genuinely shared operational findings, such as a planner omitting several
  requested contracts, must opt in explicitly to shared evidence. An
  unattributed multi-node diagnostic is no longer copied into every node.
- Continuation deterministically migrates already-saved circuit-breaker state:
  structured sibling findings are removed before evidence is fingerprinted,
  while unmarked singleton/shared operational evidence remains intact.
- Candidate fingerprinting remains strict: a node's own changed evidence still
  invalidates its candidate, while a sibling's evidence cannot do so. This
  changes no model-call budget, dependency order, or acceptance gate.

### Regression

The committed `blueprint_direct_sibling_evidence.json` fixture reproduces the
real statement fingerprints and mixed rejection shape from the run. Its test
proves that changing only the paper-construction finding changes only that
node's fingerprint; the unchanged Wang-Sun node retains its evidence,
fingerprint, and candidate eligibility.

## 2026-08-14: Persist Phase 1 Sampling and Stream Candidate Typechecking

### Confirmed latency

Historical Phase 1 telemetry showed two general orchestration costs unrelated
to mathematical difficulty. First, the three compiler-correction samples
allowed inside one transaction reset after an outer retry. Across the committed
corpus, persisting that allowance at three suppresses 27 repeated calls and
594.5 model-seconds without losing any recorded first-compiling outcome; caps
of one or two do lose successful historical samples. Second, completed
generation workers waited behind slower sibling model calls before any Lean
typechecking began. The committed trace includes a 477-second idle interval for
work whose subsequent typecheck took 46 seconds.

The latest Simplex run also spent roughly 7,200 model-seconds across 190 Phase 1
calls before proof work: 65 declaration patches, 59 statement generations, 39
statement audits, 11 plan calls, and 10 blueprint repairs. These measurements
show that repeated correction and serialized orchestration, not one unusually
slow node, dominated the run.

### Implemented correction

- The exact Phase 1 exchange key now includes statement and plan fingerprints,
  candidate input, runner/model, tier, purpose, and prompt hash.
- Its three-sample allowance persists across inner corrections, outer retries,
  process restart, and `--continue`. Exhaustion launches no model and returns
  the retained evidence to the existing failure router. A changed statement,
  plan, candidate, model, tier, or prompt creates a new eligible epoch.
- Each dependency-independent worker now performs generation, deterministic
  checks, and Lean typechecking as one streamed transaction. A completed worker
  starts typechecking while slower siblings remain in generation.
- Every typechecked candidate still waits for the same one batched statement
  audit. Object generation, import integration, partial-sibling preservation,
  dependency order, and every blueprint/Lean acceptance rule are unchanged.

### Related correctness fix

The post-repair boundary now compares repaired TeX with an immutable pre-edit
statement snapshot. `Node` objects contain source locations rather than frozen
text, so rereading a pre-repair `Node` after the edit previously compared the
new file with itself. An existing-node statement edit could therefore miss the
early boundary audit and spend another generation/compile/audit cycle before
the mandatory final audit caught it.

### Verification

- Added an executable synchronization regression that blocks one generation
  worker and proves a fast sibling enters typechecking before the blocked worker
  returns, while the final audit still runs exactly once after both settle.
- Added persisted sampling regressions for the third allowed sample, blocked
  fourth sample, model-key invalidation, state pruning, and immutable repair
  snapshots.
- All `295` Phase 1 routing tests and all `367` repository tests passed.
- All committed Simplex planner replays passed `--require-progress`; the
  dependency scheduler replay retained its existing timing and eligibility
  results because this change does not weaken or reorder graph dependencies.

## 2026-08-14: Snapshot Direct Phase 2 Repairs Before Blueprint Edits

### Confirmed failure

Simplex `run-20260814-043118` completed Phase 1 and accepted 13 Phase 2
implementations before a legitimate decomposition request repaired
`cor:geometric-signed-simplex`. The repair added a provisional five-node
component. Verification then requested another decomposition for
`lem:simplex-face-polytope`, but rollback crashed because the active repair had
no pre-edit transaction snapshot.

The transaction snapshot existed only on the orchestration path that consumed
a repair at the beginning of a later queue iteration. A repair returned
directly by the current parallel proof frontier was queued and activated in the
same iteration, but that path skipped snapshot creation before mutating the
draft.

### Implemented correction

- One transaction gate now performs repair activation, scheduler-state
  persistence, and durable blueprint/Lean snapshot creation together.
- Both queued repairs and repairs returned directly by proof outcomes use that
  same gate. A Phase 2 blueprint repair without a persisted queue identity is
  rejected before any mutation.
- Nested decomposition during complete-node verification can therefore restore
  the exact pre-edit draft and retry the original repair roots with the new
  evidence, as documented. No Lean, semantic, or blueprint acceptance gate was
  changed.

### Regression

- Added a committed fixture extracted from `run-20260814-043118` and a test
  that routes the direct decomposition, creates the transaction, mutates the
  draft provisionally, and verifies exact restoration of the baseline.
- The focused snapshot/rollback tests passed, full discovery passed `366`
  tests, every committed Simplex Phase 1 plan replay passed
  `--require-progress`, and the Phase 2 latency replay retained its `2.741x`
  deterministic result.

## 2026-08-14: Defer Phase 1 Objects and Drain Independent Branches

### Measured opportunity

Two committed Phase 1 task traces were replayed without a model or Lean. The
replay preserves recorded model/object durations, worker counts, and per-label
causal order. Allowing graph-independent work to advance reduced the current
trace from 3,320s to 3,011s (`1.103x`) and the earlier best trace from 2,379s to
1,568s (`1.517x`). Even an optimistic zero-eligibility replay with all rejected
object work removed reached only `2.083x` and `1.736x`, respectively. The
change is therefore useful but is not represented as a complete 2x solution.

### Implemented correction

- Phase 1 still performs deterministic validation and ordinary Lean checking
  before the statement-alignment audit.
- `.olean` generation now occurs only for declarations accepted by that audit.
  Accepted declarations still pass the same object-generation and integrated
  import gates before they count as frozen.
- A rejected sibling is removed before object generation. Accepted siblings
  are extracted, rechecked, object-built, integrated, and retained exactly as
  before.
- When a Phase 1 failure blocks only one dependency closure, the scheduler
  advances other already-ready graph branches before returning the failure to
  the serialized repair loop. Blueprint edits remain serialized; generation
  never races an edit to the unpublished draft.
- Telemetry distinguishes typechecked candidates, post-audit object builds,
  and the start/completion of independent-branch draining.

### Regression

- Added portable scheduler timing fixtures for the current and historical-best
  Simplex traces plus a deterministic replay CLI.
- Added tests proving that pre-audit compilation requests defer object builds,
  semantic acceptance still requires object generation, rejected nodes never
  reach the post-audit object set, and an independent child branch advances
  before a local failure returns to repair.
- Full discovery passed `365` tests. Every committed Simplex Phase 1 plan
  replay passed `--require-progress`, the Phase 1 scheduler replay reproduced
  the timing bounds above, the Phase 2 latency replay retained its `2.741x`
  deterministic result, Python compilation passed, and `git diff --check`
  passed.

## 2026-08-14: Do Not Reject Blueprint-Owned Names as Placeholders

### Confirmed failure

Simplex `run-20260813-235136` repeatedly rejected the required declaration
`remark_geometric_recursion_gap` as a placeholder because the generic helper
name heuristic treats `_gap` as suspicious. The model could not repair that
finding: one-to-one coverage requires the declaration to keep the canonical
name derived from `remark:geometric-recursion-gap`. The run consequently made
repeated generation and patch calls for an unchangeable deterministic finding.

### Implemented correction

- The placeholder-name heuristic now exempts only exact blueprint target names
  supplied by the deterministic target table.
- Plan-owned and invented helper names remain subject to the same placeholder
  heuristic, including helpers containing `gap`, `stub`, `todo`, `sorry`, or
  `trivial`.
- No statement, dependency, Lean compilation, or semantic-alignment gate was
  weakened.

### Regression

- Added a regression proving that the exact required target
  `remark_geometric_recursion_gap` is accepted.
- Added the inverse regression proving that a plan-owned helper named
  `local_gap_helper` is still rejected.
- The complete Phase 1 routing module passed (`289` tests).
- Every committed Simplex Phase 1 plan replay passed `--require-progress`.
- The deterministic Phase 2 latency replay passed its improvement and
  equal-correctness-gate assertions.
- Full discovery ran `357` tests; its only failures were the existing ten
  historical-plan fixture mismatches caused by comparing 14-contract recorded
  responses with the currently modified 107-target Simplex blueprint.

## 2026-08-13: Make Phase 2 Blueprint Repairs Truly Atomic

### Confirmed failure

The Phase 2 queue prevented two independent repairs from editing the blueprint
at the same time, but it did not provide rollback across the edit-and-verify
boundary. A repair mutated the unpublished draft immediately. If complete Lean
verification then requested another decomposition, the next repair extended
that already-unverified draft. Across continued Simplex runs, the Phase-1
baseline of 75 labels consequently reached 145 draft labels even though the
later helper components had never all passed Lean and alignment together.

This violated the documented meaning of a Phase 2 whole-node transaction. The
one-to-one blueprint/Lean checks were still present; the scheduler was feeding
them an accumulated provisional graph.

### Implemented correction

- Activating a Phase 2 blueprint repair now creates a durable pre-edit snapshot
  of the unpublished blueprint, scheduler state, generated Lean sources, and
  generated compiled objects before the model can write.
- If verification of the staged changed/new nodes exposes another authorized
  blueprint defect, the scheduler restores that exact snapshot. The rejected
  provisional helper component disappears from both the blueprint and Lean.
- The new diagnostic and helper requirements are merged into the original
  repair request. The repair model must replace the original component from
  the clean graph; it cannot incrementally extend rejected helper nodes.
- The snapshot is removed only after every replacement blueprint node has a
  complete compiled and alignment-audited Lean declaration. Successful repairs
  incur no additional model call.
- A process interrupted while the repair model is writing restores the pre-edit
  snapshot before blueprint validation on continuation. Older active states
  without snapshots establish one migration baseline to prevent any further
  accumulation; they cannot reconstruct already-discarded historical state.

### Regression

The committed Phase 2 replay now records the observed 75-to-145 Simplex
expansion and the `def:finite-indexed-minkowski-sum` provisional helper
component. Tests verify exact restoration of the draft, generated Lean,
compiled objects, and scheduler state, and verify that follow-up evidence
returns edit authority to the original blueprint root rather than a discarded
helper label.

- Full repository suite: `353` tests passed.
- Every committed Simplex Phase 1 plan replay passed `--require-progress`.
- The Phase 2 retained-candidate latency replay passed its equal-gate and
  deterministic-improvement assertions.
- Python compilation and `git diff --check` passed.

## 2026-08-13: Resume Invalidated Phase 2 Providers Without Blueprint Repair

### Confirmed failure

In Simplex `run-20260813-125126`, an extraordinary Phase 2 repair had
legitimately invalidated generated declarations while preserving the repaired
blueprint draft. On continuation, the saved audit evidence still identified
`def:m-function` as the incomplete Lean provider. Because that declaration was
now absent rather than present with a terminal `sorry`, the prerequisite route
did not recognize it and repeatedly sent the consumer back to blueprint repair.

The invalidation itself was expected. The bug was interpreting missing
generated Lean after that invalidation as evidence that the already-repaired
blueprint needed another edit.

### Implemented correction

- The existing Phase 2 provider detector now recognizes evidence-named
  definition providers that are either deferred or absent after invalidation.
- It schedules only the provider's missing, existing blueprint dependency
  closure. It does not infer dependencies, reopen Phase 1, edit TeX, or consume
  a blueprint-repair trial.
- Pending declaration work prioritizes that local closure; the existing
  complete-node Phase 2 executor rebuilds it dependency-first. Unrelated
  invalidated nodes remain pending for normal scheduling.
- The persisted post-repair boundary takes the same route, so `--continue`
  escapes the stale blueprint-repair loop immediately.

### Regression

The committed Simplex orchestration fixture now includes the exact saved-state
shape from `run-20260813-125126`: a frozen consumer, a missing two-definition
provider closure, and unrelated invalidated work. The regression requires the
public readout definition to run first, `def:m-function` second, and no
blueprint edit or repair-trial consumption.

## 2026-08-13: Route Opaque Definition Blockers Inside Phase 2

### Confirmed failure

In Simplex `run-20260813-030629`, Phase 2 repeatedly repaired the same two
`m-function` helper lemmas from repair 60 through repair 98. The repair model
kept trying to change `def:m-function`; the Phase 2 scope guard correctly
rolled that provider edit back, but the scheduler then issued the same repair
again. The generated `def_m_function` still had a terminal `sorry`, while the
audit evidence explicitly said the consumer needed to unfold that definition.

The blueprint was not the blocker. Top-down Phase 2 can assume lower theorem
statements, but it cannot reduce an unimplemented definition body. Treating
that condition as blueprint decomposition consumed 39 repeated repair calls
without changing the relevant Lean state.

### Implemented correction

- Phase 2 now detects only evidence-named, still-deferred `def`/`abbrev`/
  `instance` declarations in the blocked node's existing dependency closure.
- Those declarations become persisted local implementation prerequisites and
  run dependency-first before the blocked consumer is retried.
- Normal Phase 2 order remains top-down everywhere else. The route does not
  mutate TeX, infer a new dependency edge, reopen Phase 1, or consume a repair
  trial.
- The same conversion applies at the post-repair boundary, so `--continue`
  states already caught in this loop escape without another blueprint edit.
- Active Phase 2 repair transactions are acknowledged once all replacement
  declarations have real bodies, preventing a completed prerequisite route
  from leaving the repair queue permanently active.
- Telemetry records the blocked labels, selected prerequisites, exact evidence,
  normal order, override order, and the fact that no blueprint edit/trial was
  consumed.

### Regression

The committed fixture
`tests/fixtures/phase2_orchestration_replay/simplex_opaque_definition_prerequisite.json`
captures the real `m-function` graph and rejection. Tests require the scheduler
to select only `def:m-function`, leave the repair queue empty, preserve the
blueprint, persist the override, and resume ordinary top-down scheduling after
the body is complete.

## 2026-08-13: Diagnose Public-Interface Object Timeouts Before Model Retry

### Measured failure

In Simplex `run-20260813-010635`, the same complete Phase 2 node reached
`lean -o` repeatedly and consumed six 600-second object-build waits. Direct
controls separated three costs:

- imports-only objects completed in roughly 15-17 seconds;
- ordinary Lean checking of the real declaration and of the same statement
  with a `sorry` body completed in roughly 47-61 seconds;
- object generation for both the real declaration and the statement-only
  control exceeded 90-120 seconds, and the canonical path repeatedly exhausted
  600 seconds.

The proof body was therefore not the measured bottleneck. The expensive part
was the public dependent interface itself: repeated casts, anonymous nested
products, and long projection chains. The old pipeline labeled every object
timeout as generic Lean generation and paid for another proof rewrite, which
could not change that result.

### Implemented correction

- Fast-pipeline candidate object builds now use a 90-second usability budget;
  legacy callers and final from-scratch integration retain their existing
  longer budgets.
- A timed-out complete Phase 2 candidate gets exactly one disposable
  statement-only control compile. If it passes, correction preserves the
  public interface byte-for-byte and simplifies only the body. If it also
  times out, correction preserves the exact blueprint mathematics but may
  replace the costly anonymous Lean representation with bounded named
  same-node structures and fields.
- A Phase 1 timeout is already a statement-only control because all bodies are
  deferred. It revises or invalidates only the affected advisory interface-plan
  entries and regenerates those exact contracts. It does not authorize a
  blueprint edit.
- Saved pre-change Phase 2 candidates whose 600-second timeout was recorded as
  generic object compilation are diagnosed once on `--continue` before any
  model call.
- Failed object builds remove partial or stale `.olean` files, and telemetry
  records the duration, phase, timeout, and deterministic classification.

### Correctness boundary and regression

The blueprint remains the mathematical source of truth. No timeout changes the
blueprint, weakens a statement, skips an audit, or accepts a candidate. Every
replacement still passes deterministic ownership/dependency checks, ordinary
Lean checking, independent statement/body alignment, object generation, and
integration.

The committed fixture
`tests/fixtures/phase2_orchestration_replay/simplex_object_interface_timeout.json`
preserves the real timings and repeated-timeout exposure. Executable tests
verify both diagnostic outcomes, the 90-second bound, retained mathematical
source-of-truth instructions, and the historical interface-timeout route.

- Full repository suite: `347` tests passed.
- Phase 1 historical plan replay passed with `--require-progress`.
- Phase 2 retained-candidate replay passed with the same four acceptance gates
  and a `2.741x` deterministic logical-clock improvement.
- Python compilation and `git diff --check` passed.

## 2026-08-13: Retain and Correct Complete Phase 2 Candidates

### Confirmed bottleneck

Historical telemetry from Simplex run `20260810-025600-bfe3d503` records 164
Phase 2 complete-node model calls consuming 38,387 model-seconds. Forty-five
calls timed out, 57 complete-node transactions exhausted, and only 20
transactions committed. Three nodes alone consumed 101 calls and roughly
28,822 model-seconds. A rejected complete declaration was discarded, so an
outer retry usually paid for another full generation instead of correcting the
existing statement-and-body candidate.

The telemetry also separates backend-session cost: successful resumed Phase 2
calls averaged 221.9 seconds, while successful fresh calls averaged 71.7
seconds. Thirty-three resumed calls reached the 600-second timeout. This
evidence applies specifically to self-contained complete-node correction;
Phase 1's anchored statement-patch sessions remain unchanged.

### Implemented correction

- A failed Phase 2 statement-and-body candidate is retained with its exact
  deterministic, compiler, object-compilation, or alignment rejection.
- The next model call receives that complete candidate, the complete blueprint
  node and proof, frozen dependency interfaces, and only the current rejection.
  It must return a corrected complete node. It cannot route through the Phase 1
  patcher, which intentionally emits terminal `sorry` bodies.
- `allow_patch=False` therefore remains deliberate at the shared freeze gate:
  acceptance is still atomic over the whole statement and real body. The new
  correction happens outside that gate and re-runs every gate afterward.
- Complete-node corrections use fresh backend sessions and are capped at 300
  seconds. The candidate is fingerprinted by its blueprint statement,
  contract, and dependency context and survives bounded outer retries and
  `--continue`. Exact no-progress corrections are not replayed.
- Disposable candidate Lean checks are capped at 90 seconds; the final
  assembled integration check retains its longer timeout. The broad
  `import Mathlib` diagnostic retry now runs only for missing-name errors, not
  for type mismatches, unfinished tactics, or heartbeat exhaustion.
- Phase 1 declaration-local correction prompts now include only the affected
  targets and their plan-owned structural declarations. The authoritative
  dependency-contract table remains present, but unrelated declarations from
  a large section are no longer repeated in the model prompt.

### Correctness boundary

Nothing is accepted from the retained candidate merely because it is cheaper
to edit. Every corrected node still passes deterministic coverage, Lean,
object compilation, statement alignment against the complete blueprint node,
and ordinary integration. A blueprint or dependency-contract change
invalidates the candidate automatically. Compiler failure alone still cannot
authorize a blueprint edit, and Phase 2 never reopens Phase 1.

### Regression coverage

The committed replay fixture
`tests/fixtures/phase2_orchestration_replay/simplex_complete_node_candidate_loop.json`
preserves the measured call counts, time, timeout, and session data from the
historical run. Executable regressions verify fresh-session correction,
retained-candidate reuse across outer retries, the 300-second correction cap,
complete-body atomic validation, candidate-state persistence, focused Phase 1
patch prompts, and selective broad-import diagnosis.

- Full repository suite: `339` tests passed.
- Phase 1 orchestration, trajectory, and recorded-plan replay tests passed.
- Every committed Simplex plan replay passed `--require-progress`.
- The deterministic Phase 2 logical-clock benchmark reduces the committed
  scenario from seven full generations and 443.102 observed model-seconds to
  one generation plus one correction and 161.67 simulated model-seconds
  (`2.741x`), while requiring the same four acceptance gates.
- Python compilation and `git diff --check` passed.

## 2026-08-10: Verify Each Phase 2 Repair Before Applying the Next

### Confirmed failure

In Simplex `run-20260809-223432`, independent repair scopes were correctly
queued, but the scheduler acknowledged each scope immediately after editing the
blueprint. It then drained the rest of the queue before generating replacement
Lean. The unpublished draft grew from 65 to 173 nodes, consumed 54 repairs, and
completed only 16 Phase 2 implementations. The queue therefore prevented one
broad edit but still accumulated many unverified edits.

### Implemented correction

- Phase 2 now persists one active repair with explicit `repair` and `verify`
  stages. A later queued blueprint edit cannot start while replacement Lean for
  the active repair is pending.
- A repair is acknowledged only after its changed/new nodes complete the
  existing whole-node generation, deterministic checks, compilation, statement
  alignment, and integration gates. Phase 1 is never reopened.
- Queue entries include a deterministic fingerprint of the target statements
  and their transitive statement/proof dependency environment. After a repair
  verifies, diagnoses based on a changed environment are superseded instead of
  being applied to stale graph state.
- If verification discovers another genuine helper defect, it extends the
  active transaction; independent sibling findings remain queued.
- State schema 27 persists the active transaction and retained complete-node
  correction candidates across interruption and
  `--continue`.

### Latency boundary and regression coverage

The correction adds no model-call stage. Queue activation, context
fingerprinting, staleness checks, and acknowledgment are deterministic; the
existing repair, boundary-audit, complete-node generation, compilation, and
alignment calls are merely ordered transactionally. The committed historical
fixture records the 65-to-173 failure and tests that at most one unverified edit
exists, stale dependency-context evidence is removed, active state survives
save/resume even after its statement changes, and the scheduling transition
invokes no model. The full repository suite passes (`333` tests), the complete
committed Simplex planner replay passes with `--require-progress`, and
`git diff --check` is clean.

## 2026-08-09: Stop Phase 2 Proof-Frontier Node Explosion

### Confirmed failure

In Simplex `run-20260809-010031`, six independent Phase 2 proof workers
requested decomposition. The proof-frontier scheduler merged all six labels and
all helper suggestions into one blueprint-repair prompt. Repair 1 consequently
changed 21 contracts and added 15 helpers, expanding the unpublished draft from
81 to 96 nodes; later repairs reached 106 nodes. This bypassed the independent
repair queue already used by Phase 2 whole-node workers.

The same run also exposed a second authorization bug. The decomposition parser
used a greedy regular expression and returned a repair payload even when JSON
parsing failed. Two responses containing the prompt's literal example values
(``<node label>``, ``<each needed helper statement>``, and ``<why>``) were
therefore treated as mathematical evidence for blueprint decomposition.

### Implemented correction

- Every decomposition response must now consist solely of
  `NEEDS-DECOMPOSITION:` followed by valid JSON. The payload must contain a
  concrete non-placeholder label, at least one concrete helper statement, and
  a reason. Its label must be one of the nodes assigned to that exact model
  call. Malformed JSON, trailing prompt text, placeholders, and wrong-label
  responses are ordinary generation failures and cannot edit the blueprint.
- The strict parser is shared by the legacy loop, Phase 1 statement generation,
  Phase 2 proof batches/singletons, and Phase 2 whole-node generation.
- Phase 2 proof-frontier decomposition findings now enter the same persisted
  independent repair queue as whole-node findings. Six refusals produce six
  one-node transactions, not one six-root edit scope.
- Ordinary Lean/compiler failures remain non-blueprint retries even when a
  sibling worker produces valid decomposition evidence. Their node-owned
  diagnostics are retained separately and never inherit the sibling's edit
  authority.

### Regression coverage

The committed replay fixture records the exact 81-to-96-to-106 Simplex
expansion. Tests verify the six independent queue scopes, rejection of malformed
and placeholder refusals, target-label enforcement, and the non-blueprint route
for ordinary Phase 2 generation failures. Full repository suite: `331` tests
passed.

## 2026-08-09: Do Not Convert Phase 2 Generation Exhaustion Into Blueprint Repair

### Confirmed failure

In Simplex `run-20260808-032618`, ordinary Phase 2 whole-node failures
(timeouts, malformed Lean, compilation failures, and deterministic/alignment
generation failures) exhausted the base and escalation attempts. The terminal
fallback incorrectly marked that exhaustion as blueprint-authorized. Repair 36
then changed 34 contracts without mathematical evidence that those contracts
were defective, contributing to later invalidation of 50 accepted dependents
and regeneration of 176 nodes.

### Implemented correction

- Whole-node generation exhaustion now returns a non-blueprint retry request.
  Its exact per-node evidence is retained and the unpublished blueprint remains
  unchanged.
- Only explicit decomposition, semantic blueprint/decomposition evidence, or
  certified required dependency edges can enter the blueprint transaction.
- Outer retry telemetry, reports, and logs now identify Phase 2 generation
  retries as Phase 2 rather than incorrectly calling them Phase 1 retries.

### Regression coverage

The committed historical fixture records the exact Simplex failure class and
verifies that two exhausted model tiers route to the bounded Phase 2 generation
retry lifecycle with `blueprint_edit_authorized = false`. The existing replay
continues to verify that explicit `NEEDS-DECOMPOSITION` evidence immediately
authorizes the independent Phase 2 repair queue.

## 2026-08-08: Keep Independent Phase 2 Repair Authority Separate

### Observed issue

In Simplex `run-20260808-032618`, parallel Phase 2 complete-node workers
reported independent blueprint defects. The scheduler unioned those requests
into one repair prompt. Repair 36 consequently changed 34 contracts; the next
repair changed foundational interfaces and invalidated 50 accepted dependents,
eventually expanding complete-node regeneration to 176 nodes. Successful
sibling worker results were preserved, but the merged edit authority erased
the latency benefit.

### Implemented solution

- Authorized Phase 2 worker failures are now persisted as an ordered queue of
  independent repair transactions. The original labels, exact evidence,
  decomposition request, required dependency edges, and failure route remain
  attached to their own transaction.
- The outer loop processes one queued repair at a time. Post-repair boundary
  validation completes before the next queue item, and accepted sibling
  sections remain frozen.
- A Phase 2 model repair may modify only pre-existing nodes explicitly named
  by that transaction. Dependencies and neighbors are read-only. Newly added
  helper nodes remain allowed and continue through the existing connectivity,
  orientation, and scoped semantic boundary checks.
- Queue state is statement-fingerprinted and saved in `skeleton_state.json`, so
  interruption and `--continue` do not merge or lose pending repairs.
- Telemetry records queue scopes and completion instead of only the former
  combined repair.

### Correctness boundary

This does not suppress any failure or accept partial mathematics. It narrows
who may edit existing blueprint contracts. If a foundational dependency is
itself defective, the auditor must name it in its own repair request; merely
being supplied as context no longer grants edit authority. Every changed or
new node still passes blueprint validation, graph checks, post-repair semantic
audit, Lean compilation, statement alignment, and the final assembled check.

### Regression coverage

The committed Phase 2 replay fixture records the exact Simplex blast-radius
case and verifies that three worker failures remain three queue items while
accepted siblings survive. Focused tests also verify the Phase 2 existing-node
scope guard and persisted queue restoration. Full repository suite: `327`
tests passed.

## 2026-08-03: Close Phase 2 Helper Components Before Lean Regeneration

### Confirmed failure

In UUE `run-20260803-224713`, Phase 2 repaired
`lem:security-winning-probability-transport` by adding
`lem:security-concrete-package-final-bound`. The existing post-repair boundary
audit examined that helper in isolation and accepted it. A costly complete Lean
attempt then exposed another missing helper,
`lem:security-final-reduction-unpacked-main-construction`. After roughly 18
minutes the run had completed only two net nodes because it was discovering one
helper per Lean/repair cycle.

### Implemented correction

- Every Phase 2 blueprint-repair prompt now requires the complete finite helper
  component needed by the original failing root in the same edit. A helper may
  not merely rename or postpone an unresolved obligation.
- The existing post-repair boundary transaction persists the original root,
  exact failure evidence, and every changed or added component node. Proof-only
  helper edits are included during Phase 2; Phase 1 behavior is unchanged.
- That same existing boundary-audit call now examines the complete root/helper
  blueprint proofs and rejects an incomplete decomposition before another Lean
  generation call. It requests all foreseeable missing helpers together and
  carries the original evidence and boundary findings into the next repair.
- Component state is persisted in state schema version 24. Telemetry records
  roots, changed component labels, closure requirements, and verdicts for future
  repair/decomposition classifiers.

### Regression coverage

- Added the exact serial UUE helper chain to the committed Phase 2 orchestration
  replay fixture.
- Added coverage for Phase 1 proof-only behavior, Phase 2 root/component prompt
  construction, multi-helper routing, evidence preservation, and save/load
  continuity.

## 2026-08-03: Repair Complete Nodes Inside Phase 2

### Confirmed failure

After Phase 2 repaired or decomposed a blueprint node, the main loop computed
the resulting missing declaration and called `_run_phase1(...)`. That produced
and froze a statement-only contract with `:= sorry`; a later Phase 2 model call
then implemented its body. This reopened Phase 1 machinery semantically even
though the UI called it “Phase 2 contract repair,” duplicated model work, and
violated the intended boundary: Phase 1 is the one-time initial skeleton, while
Phase 2 owns complete repaired nodes.

The historical UUE run `run-20260803-214911` exercised this path for
`lem:security-operator-data-package`, `lem:security-final-reduction`, and
`thm:security`.

### Implemented correction

- Pending declarations dispatch through an explicit one-way boundary. Before
  `phase2_started`, they use Phase 1 statement freezing. Afterward, `_run_phase1`
  is unreachable and they use Phase 2 whole-node transactions.
- Each Phase 2 transaction receives the complete current blueprint node,
  dependency contracts, frozen Lean interfaces, and exact retry evidence. It
  returns one complete Lean declaration containing both the current statement
  and its proof or definition body.
- The shared freezer has an explicit complete-body mode. It preserves real
  bodies instead of normalizing them to `:= sorry`, rejects every remaining
  `sorry`, and applies the existing deterministic, Lean, semantic-alignment,
  object-compilation, and integration gates to the complete declaration.
- Independent dependency-ready repaired nodes run across the configured worker
  pool. Successful Lean nodes are accepted against the unpublished draft
  immediately; failed nodes retain exact evidence
  and retry once through the escalation tier before ordinary evidence-driven
  Phase 2 repair/decomposition.
- Unaffected frozen declarations and accepted proofs remain reusable. Phase 1
  progress remains the immutable baseline and repaired nodes already count as
  completed Phase 2 work when committed.
- Web UI stages and telemetry now say “Phase 2 whole-node repair”; the obsolete
  repaired-contract stages and event names were removed.

### Regression coverage

- Added a committed UUE historical replay case proving pending work after the
  Phase 2 boundary cannot call `_run_phase1`.
- Added focused coverage proving a Phase 2 whole-node call enables complete-body
  mode and proving that mode accepts a real definition body but rejects `sorry`.
- Added the follow-up UUE replay from `run-20260803-223132`: two parallel
  whole-node repairs completed, while a third produced a valid
  blueprint-authorized request. The coordinator now retains the accepted
  siblings and propagates that request through the authorized Phase 2 repair
  aggregator instead of stopping in the non-blueprint aggregator.

## 2026-08-03: Bound Repeated Phase 1 Compiler Failures

### Confirmed failure

In `unconditional-unclonable-encryption/run-20260803-031013`,
`thm:security` repeatedly emitted malformed Lean during retries 51-55. The
semantic-audit routes advanced the persisted per-node retry lifecycle, but the
ordinary Phase 1 compile-failure route bypassed it and returned directly to
statement generation. The same statement version could therefore consume the
global repair budget without reaching the existing strategy changes.

### Implemented correction

- Every ordinary Phase 1 compile failure now advances the same
  statement-fingerprinted `base -> escalation -> exhausted` lifecycle used by
  statement-audit failures. Compiler and audit evidence remain separately
  scoped to their owning node.
- Exhausted compiler correction uses the existing bounded sequence: revise an
  eligible legacy interface plan once, switch candidate-owned or repeatedly
  rejected contracts to blueprint-direct generation, and route only a contract
  that exhausts that direct lifecycle to decomposition.
- Parallel compilation now aggregates an authorized decomposition route from
  one failed worker while retaining independently compiled siblings. It no
  longer assumes every compiler failure is a non-authorized generation retry.
- Exhaustion bookkeeping cannot terminate the whole run with an internal
  impossible-state exception; any unresolved label remains in the bounded
  retry route.

### Regression coverage

- Added a committed replay fixture for the repeated `thm:security` compiler
  failure and verified that prior statement-audit state carries into compiler
  exhaustion, blueprint-direct generation, and eventual decomposition.
- Added coordinator coverage for authorized exhaustion returned by a parallel
  compiler worker.
- Phase 1 routing suite: 244 tests passed.
- Historical orchestration, trajectory, and planner replay suites: 25 tests
  passed.
- Full repository suite: 308 tests passed.

## 2026-08-03: Keep Blueprint Corrections Owned by Phase 2

### Confirmed failure

The main loop inferred the active phase only from `current blueprint nodes -
frozen Lean declarations`. When Phase 2 decomposition added helper nodes or
changed a contract, that set became nonempty and the workflow visibly reopened
Phase 1. The scoped regeneration was necessary, but its ownership was wrong:
Phase 1 is the one-time initial skeleton stage, while corrections discovered
during proof implementation belong to Phase 2.

### Implemented correction

- The workflow now persists a one-way `phase2_started` milestone and the exact
  Phase 1 baseline labels in `skeleton_state.json`.
- Once the initial skeleton and integration gate complete, Phase 1 remains
  complete. This change originally labeled later scoped regeneration as a
  “Phase 2 contract repair.” The subsequent whole-node correction documented
  above removed that two-step implementation: Phase 2 now generates the
  repaired statement and body together.
- Unaffected frozen contracts and accepted proofs remain reusable. Complete
  repaired nodes return directly to top-down Phase 2 proof scheduling.
- Progress keeps the historical Phase 1 skeleton complete instead of dropping
  its numerator when Phase 2 adds helpers. Telemetry separately records Phase 2
  whole-node repair start/completion and the pending node labels.
- The Web UI labels these operations as Phase 2 whole-node work rather than
  displaying a second Phase 1.

### Regression coverage

- Added a one-way phase-transition regression proving that adding a node after
  Phase 2 begins does not reopen Phase 1 or change its baseline.
- Extended persisted-state coverage for the Phase 2 milestone and Phase 1
  baseline so `--continue` preserves the same ownership.

## 2026-08-03: Scope Retry Evidence and Persist Exact Phase 1 Exchanges

### Confirmed failure

Phase 1 retained compiler and semantic feedback across retries, but an
aggregated multi-node failure could copy the complete combined evidence into
every sibling's next prompt. A node could therefore be asked to repair another
node's compiler or audit failure. Separately, exact prompt/response detection
was local to one section attempt. Crossing the outer repair loop or restarting
with `--continue` reset that memory and allowed an identical response to be
compiled and audited again.

### Implemented correction

- Retry requests now carry an explicit `evidence_by_label` map. Deterministic
  findings, Lean diagnostics, and semantic-audit findings are assigned only to
  their owning node before requests are aggregated.
- Unattributed evidence is retained automatically only for a singleton. A
  multi-node failure without deterministic ownership is routed without copying
  the blob into every node's prompt.
- Phase 1 now fingerprints each exact model exchange from its labels, statement
  and plan epochs, candidate input, purpose, tier, and prompt. Response hashes
  are persisted in `skeleton_state.json`, so the same byte-identical result is
  recognized across outer retries and `--continue`.
- A distinct response to the same prompt remains a valid stochastic sample.
  The existing bounded multi-sample policy is unchanged because historical
  replay fixtures contain cases where sample two or three is the first result
  that compiles.
- Blueprint statement or plan changes prune the corresponding exchange history,
  allowing the corrected contract to start a fresh retry epoch.

### Regression coverage

- Added a regression proving two sibling audit failures produce separate stored
  evidence and separate correction prompts.
- Added a regression proving exact duplicate responses are recognized after an
  outer retry while a different response remains admissible.
- Extended state persistence coverage through save/load and statement-epoch
  invalidation.
- Phase 1 routing suite: 240 tests passed.
- Historical orchestration and trajectory replay suites: 23 tests passed.
- Full repository suite: 304 tests passed.

## 2026-08-03: Preserve Both Sides of a Compound Repair Transaction

### Confirmed failure

In `unconditional-unclonable-encryption/run-20260803-003136`, one Phase 1
frontier authorized two independent changes: the deterministic dependency edge
for `def:local-basis-unitary` and model decomposition of
`def:finite-register-operators` into three concrete provider interfaces. Both
operations succeeded. The final scope guard nevertheless checked their merged
five-label delta only against the model target, misclassified the separately
authorized deterministic edit as a downstream model edit, and rolled back the
entire transaction. Phase 1 then regenerated the original monolithic contract
and later attempted a cyclic dependency repair.

### Implemented correction

- Compound transactions now retain a snapshot immediately after validated
  deterministic dependency insertion.
- Only the model-authored delta is checked against the model repair scope.
- If that delta exceeds its scope, it is rolled back to the post-edge snapshot;
  already validated deterministic changes remain committed.
- Successful compound transactions still invalidate and recheck the union of
  deterministic and model-authored statement changes.
- Telemetry records the complete committed delta, the separately checked model
  delta, and the retained deterministic labels.

### Regression coverage

- Added the exact five-label UUE transaction to the committed historical replay
  fixture.
- Added focused graph-scope coverage for an upstream decomposition beside an
  independently validated dependency edge.
- Existing downstream-consumer and disconnected-change protections remain in
  place.

## 2026-08-03: Consume Certified Boundary Repairs Exactly Once

### Confirmed failure

In `unconditional-unclonable-encryption/run-20260802-233439`, the scoped
post-repair audit authorized only the deterministic statement dependency
`def:reduced-operator -> def:density-operator-interface`. The edge was applied,
but the persisted request retained its old statement fingerprints. On the next
iteration the target disappeared from the request while unchanged siblings
remained, an explicitly empty model-repair scope was replaced by those sibling
labels, and the already-satisfied edge was treated as failed insertion. The
pipeline spent six unnecessary blueprint-repair calls and about 520 model
seconds before repeatedly rolling the edits back as out of scope.

### Implemented correction

- Pending boundary repair state now distinguishes an explicitly empty model
  scope from legacy state that did not store a scope.
- Certified dependency obligations are reconciled against the current
  statement graph. Already-present edges complete idempotently, including
  after interruption between the TeX edit and state persistence.
- A no-op edge authorizes model repair only when the required edge remains
  absent after the deterministic transaction. An already-satisfied edge cannot
  fall through to a model call.
- Dependency-only edits invalidate affected Lean normally but do not trigger a
  redundant second boundary audit. Actual model-authored statement changes
  still queue the existing scoped audit.
- Mixed transactions retain explicit model/decomposition work when their
  certified dependency edge completes; cycle rejection and scoped rollback are
  unchanged.

### Regression coverage

- Added the exact UUE historical case to the committed post-repair boundary
  fixture, including the six calls and 519.7 seconds of avoidable work.
- Added focused lifecycle tests for edge-only completion and interruption of a
  mixed edge/model transaction.

## 2026-08-02: Preserve Semantic Constraints Through Compiler Patches

### Confirmed failure

In `unconditional-unclonable-encryption/run-20260802-224805`, statement audits
rejected `def:finite-register-operators` and `def:key-space` for erasing
blueprint semantics. The semantic correction call received that evidence, but
later targeted Lean compiler patches received only the newest compiler error.
Those patches could therefore restore the same weakening, causing another
semantic rejection after several otherwise useful compiler corrections.

### Implemented correction

- Every targeted Phase 1 declaration patch now receives the unresolved,
  statement-fingerprint-scoped semantic/compiler history for exactly the
  declarations it edits.
- The current compiler error supplements that history instead of replacing it.
- Prompt evidence is bounded and preserves both ends of each history: the
  original semantic requirement and the latest compiler diagnostics.
- The behavior is implemented in the shared prompt path, so it applies equally
  to Codex, Claude, and API runners.
- A committed historical replay fixture reproduces the audit rejection followed
  by three compiler-only patches and requires the semantic constraint to remain
  present throughout the correction transaction.
- Verification passed: 297 repository tests, Python compilation, focused Phase
  1 orchestration and trajectory replays, the standalone committed historical
  plan replay with `--require-progress`, and `git diff --check`.

## 2026-08-02: Preserve Complete Blueprint Nodes with Nested LaTeX

### Confirmed failure

The source-contract extractor ended a blueprint node at the first
`\\end{...}` after its label. In
`unconditional-unclonable-encryption/run-20260802-213402`, the 531-character
`def:single-qubit-paulis-cliffords` definition was reduced to 200 characters
because `\\end{pmatrix}` was mistaken for `\\end{definition}`. Phase 1 model
calls and alignment audits could therefore receive an incomplete blueprint
contract.

### Implemented correction

- Node extraction now finds the environment that encloses the label and
  balances that exact environment's begin/end tokens.
- Nested matrices, aligned equations, and nested same-name environments no
  longer truncate the node.
- Commented-out environment tokens are ignored without changing source offsets.
- An immediately following proof remains part of the extracted full-node
  contract, as before.
- Verification passed: 292 repository tests, Python compilation, the complete
  committed historical Phase 1 plan replay, and `git diff --check`.

## 2026-08-02: Preserve Semantic Plans Containing TeX Backslashes

### Confirmed failure

In `unconditional-unclonable-encryption/run-20260802-210758`, the compact
semantic planner returned all 52 requested contracts, but mathematical prose
contained a single JSON-invalid TeX escape such as `\dagger`. Strict decoding
failed, after which the loose shared extractor selected one valid nested
contract object. The semantic-plan parser therefore reported that the response
omitted `contracts` and replaced all 52 entries with blueprint-only fallbacks,
wasting the 220-second planning call.

### Implemented correction

- Semantic-plan ingestion now requires the intended top-level `contracts` key;
  it can never substitute a nested object for a malformed outer response.
- A schema-local recovery pass escapes malformed TeX backslashes only inside
  JSON strings. Existing JSON escapes and all structural text remain unchanged.
- Recovery is recorded in semantic-plan findings for telemetry.
- The historical malformed response shape is committed as a regression fixture.

## 2026-08-02: Conjecture Policy and Incremental Phase 1 Integration

### Confirmed problems

- The pipeline treated every theorem-like environment identically. A paper
  conjecture therefore became a Phase 2 proof obligation even when the desired
  publication was an honest formal record of an open claim. There was also no
  safe opt-in path for asking the model to prove a conjecture while preserving
  the blueprint as the source of truth.
- In the Simplex snapshot `run-20260802-115840`, Phase 1 froze its last contract
  at `+8603s` but Phase 2 did not begin until `+9302s`. The 699-second gap was a
  serial recompilation of 39 generated modules that had already compiled when
  they froze.

### Implemented correction

- Added `--conjecture-policy record|attempt` and a matching Web UI selector.
  `record` is the default: each conjecture is encoded as its exact
  proposition-valued Lean `def`, contains no `sorry`, is skipped by Phase 2,
  and is reported as recorded rather than proved.
- `attempt` cannot let Lean invent an independent proof. If the blueprint has
  no proof for a conjecture, the ordinary transactional author repair must add
  that proof to the unpublished blueprint draft first. Phase 2 then formalizes
  the blueprint proof under the existing compiler and alignment gates.
- Progress, telemetry, reports, and final publication distinguish verified
  nodes from recorded open conjectures. Changing policy invalidates incompatible
  resumed skeleton state.
- Each generated section now persists a compile fingerprint covering its Lean
  source, checker command, toolchain/manifest, and imported generated-interface
  fingerprints. The final Phase 1 gate reuses matching `.olean` files, rebuilds
  only dirty or missing modules in dependency order, and then compiles one
  aggregate file importing every active section.
- The optimization removes duplicate compilation only. It does not weaken the
  final assembled from-scratch Lean check or any deterministic/model alignment
  audit, and it does not introduce node-owned declarations outside the
  blueprint graph.
- Verification passed: 289 repository tests, Python compilation, and the
  complete committed Simplex historical-plan replay with `--require-progress`.

## 2026-08-02: Keep Fresh Phase 1 Candidates Out of the Legacy Plan Loop

### Confirmed failure

In `unconditional-unclonable-encryption/run-20260802-043131`, fresh
candidate-derived contracts for `def:finite-register-operators` and
`def:local-basis-unitary` entered repeated `phase1_design_plan_correction` and
`phase1_design_plan_audit` calls. The correction parser omitted the immutable
`phase1_candidate` origin marker, and the shared semantic-exhaustion router
treated every unmarked contract as legacy typed-plan state.

### Implemented correction

- Contract replacement now preserves immutable origin provenance when a model
  response omits it.
- Candidate-derived contracts are excluded from both semantic and decomposition
  plan-correction entry points.
- After the existing exact-evidence candidate correction is exhausted, a fresh
  contract moves directly to one blueprint-direct lifecycle. Only exhaustion of
  that lifecycle routes to blueprint decomposition.
- Resumed legacy typed-plan contracts retain their historical
  plan-revision/blueprint-direct/decomposition compatibility path.
- A committed UUE replay fixture covers both affected nodes and requires zero
  legacy plan-correction calls.
- Complete verification passed: 281 repository tests, Python compilation,
  `git diff --check`, and the standalone committed Simplex historical replay
  with `--require-progress`.

## 2026-08-02: Make Phase 1 Dependency Context Limits Non-Fatal

### Confirmed failure

In `unconditional-unclonable-encryption/run-20260802-033800`, Phase 1 had frozen
15 of 52 contracts when a five-node retry required 12,349 characters of exact
generated dependency interfaces. The prompt builder treated its 10,000-character
batching target as a hard correctness limit and stopped the autonomous run at
`+1898s`, even though every required declaration existed.

### Implemented correction

- The 10,000-character value is now a soft grouping target. It cannot remove a
  required declaration or terminate refinement.
- Before model dispatch, the scheduler measures the exact transitive generated
  interface and greedily partitions ordinary groups into maximal fitting
  prefixes. The recorded UUE retry deterministically becomes `2 + 1 + 2`, with
  measured interfaces of 8,812, 9,809, and 7,247 characters.
- Persisted candidates that share structural helper code remain atomic. If an
  atomic component or singleton itself exceeds the target, it receives the
  complete context and telemetry records the soft overflow.
- The same partitioner is used by bottom-up and top-down Phase 1 dispatch. It is
  model- and provider-independent and adds no model call.
- A committed historical fixture records the exact UUE labels and measured
  interface sizes. Focused tests cover lossless oversized context, historical
  partitioning, and oversized atomic components.
- Complete verification passed: 278 repository tests, Python compilation,
  `git diff --check`, and the standalone committed Simplex historical-plan
  replay with `--require-progress`.

## 2026-08-02: Derive Typed Contracts Atomically from Phase 1 Candidates

### Confirmed problem

The original shared plan was introduced to keep independently generated
frontiers consistent, but it accumulated exact Lean signatures, helper kinds,
member types, constructors, semantic decisions, and provider requirements. In
`unconditional-unclonable-encryption/run-20260731-095949`, its prompt was about
63,000 characters and its two responses were about 58,000 and 67,000
characters. Those calls took roughly 309 and 350 seconds before Phase 1 had
generated any Lean. Defective typed entries then entered separate plan-repair
calls, making the planning aid an expensive pre-Phase-1 formalization stage.

Historical runs also showed that a globally perfect typed plan was unnecessary:
Phase 1 could advance quickly from a near-good plan because the generated Lean,
compiler, deterministic gates, and statement-alignment audit were already the
authoritative checks. The latency came from asking one model response to predict
every exact Lean interface and then forcing later generation to obey that
independently generated prediction.

### Implemented architecture

- The global planner now returns only compact semantic coordination: a
  representation choice, stable vocabulary, mathematical obligations, and
  direct-provider capabilities. It cannot return Lean signatures, binder
  types, helper member types, constructors, imports, bodies, or proofs.
- The semantic prompt includes the authoritative deterministic dependency table.
  Statement dependencies may shape public interfaces; proof-only dependencies
  are reserved for Phase 2; root context cannot invent graph edges.
- Planning is one advisory call with no planner-repair loop. Missing, malformed,
  duplicate, or unauthorized entries are sanitized or replaced by a
  deterministic blueprint-only fallback. A bad advisory response therefore
  cannot block Phase 1 or consume repeated planning calls.
- Each Phase 1 generation response now emits the canonical target and any owned
  structural interface together. Canonical ingestion extracts their exact Lean
  headers and persists that same candidate as its typed contract. No separate
  typed-contract model call exists.
- Compiler, deterministic, and statement-audit corrections refresh the typed
  contract from the same replacement candidate. Generated code can no longer be
  trapped under a stale independently produced typed plan.
- Candidate-owned typed contracts do not enter the former independent
  plan-correction route. Legacy `--continue` state from the typed planner remains
  readable and retains its historical validation behavior.

### Preserved safeguards

This is a boundary change, not a weakening of Phase 1. Before a statement can
freeze, the existing canonical and deterministic checks still enforce:

- one canonical target per blueprint node and complete target coverage;
- authorized statement dependencies and separate proof-only dependencies;
- exact structural helper ownership, declarations, members, and member types;
- target/helper and dependency-cycle rejection;
- Mathlib-owned alias normalization and rejection of unresolved aliases;
- rejection of executable helper definitions or theorems not represented by
  blueprint nodes;
- Lean compilation/integration and the independent statement-alignment audit
  against the blueprint.

Blueprint repair remains evidence-only and transactional. Accepted siblings and
unrelated branches remain reusable. Phase 1 remains bottom-up, Phase 2 remains
top-down, and publication still requires the complete final Lean and correctness
audits.

### State, telemetry, and regression coverage

- Refinement state version 20 stores compact semantic entries separately from
  exact candidate-derived typed contracts. Statement fingerprints invalidate
  either representation when its blueprint node changes.
- Telemetry records semantic-plan coverage/fallback/sanitization and exact
  candidate contract realization with `typed_contract_model_calls=0`.
- Added focused regressions for dependency sanitization, semantic-prompt scope,
  atomic target/helper realization, and routing candidate-owned closure failures
  back to candidate correction rather than independent plan repair.
- Added committed historical-shape fixtures for the UUE unauthorized-provider
  regression and the Simplex atomic structural-helper contract. They require no
  model, network, telemetry service, or local run artifacts.
- Existing committed historical Phase 1 trajectory fixtures still exercise the
  legacy typed-plan compatibility path and preserve their recorded routing.
- Complete repository verification: 272 tests passed; the standalone committed
  Simplex historical-plan replay passed with `--require-progress`; Python
  compilation and `git diff --check` passed.

## 2026-08-01: Balance Initial Plan Repair Against Full Replanning

### Confirmed regression

Tournament 2 in `run-20260801-180629` produced a complete 52-contract candidate
with only four closure findings in four isolated components. Only
`def:finite-register-operators` blocked the three-node initial frontier. The
strict admission rule discarded all 52 contracts and ran three more complete
tournaments before selecting a clean plan at `+1572s`.

### Implemented solution

- A clean complete initial frontier retains the existing fast path and starts
  immediately without waiting for the sibling lane.
- After both lanes finish, a complete near-good candidate may be retained when
  its deterministic bounded-repair estimate is strictly lower than another
  two-lane full-plan tournament.
- The estimate is provider-neutral contract work, not guessed model pricing:
  `2 * blocked contracts + closure findings + repair components`, compared with
  `2 * total contracts` for another tournament.
- Retention does not bypass validation. The existing frontier closure gateway
  repairs and revalidates affected contracts before statement generation.
- Incomplete candidates remain ineligible, and the existing blueprint-repair
  authorization rules are unchanged.

### Historical replay

- Added `repairable_tournament_admission.json` from `run-20260801-180629`; its
  observed candidate scores `16` repair units versus `104` replan units and
  must be retained for scoped repair.
- The existing catastrophic `run-20260801-083320` fixture scores `231` repair
  units versus `104` replan units and must still restart.

### Verification

- Added a unit regression that drives the actual tournament selection path and
  requires `cheaper_scoped_repair` rather than a restart.
- Added a regression proving selection uses repair cost rather than the older
  lexicographic plan score when those order candidates differently.
- Full repository suite, including committed historical plan, trajectory, and
  orchestration replays: 266 tests passed.

## 2026-08-01: Make Blueprint Dependencies Authoritative During Initial Planning

### Problem

The Phase-1 section writer already received the deterministic dependency table,
but the earlier shared design-planner prompt did not. It showed informal
statement/proof dependency lists while also referring to a dependency table
that was absent. A planner could therefore infer a generated dependency from
root context or place a proof-only dependency in a public target signature,
creating avoidable closure repair before statement generation.

### Implemented solution

- The initial design planner now receives the existing deterministic direct
  dependency-contract table; no new table or model call was added.
- The table is explicitly the sole authority for generated dependency symbols.
- Statement-interface dependencies may appear in `target_signature`.
- Proof-only dependencies may guide Phase 2 but may not be added to the public
  signature merely because the proof uses them.
- Root context may shape interface semantics but cannot invent dependency edges
  absent from the blueprint graph.

### Verification

- Added a focused prompt regression covering statement-interface and proof-only
  dependencies, the authoritative-table rule, and the root-context boundary.
- Full repository suite, including committed Phase-1 historical replay
  fixtures: 261 tests passed.

## 2026-08-01: Reject Catastrophic Initial Plans Before Phase 1

### Confirmed regression

In `run-20260801-083320`, candidate A returned all 52 requested contracts in
282 seconds, but deterministic closure found 124 violations blocking all 52
nodes, including every node in the three-node initial frontier. Candidate B
timed out at the ordinary 300-second base-call limit, and the recovery returned
16 characters with zero usable contracts. The tournament selected A merely
because it was the least-bad available candidate. Full closure repair was
correctly deferred to dependency-ready frontiers, but no admission threshold
prevented a plan with `0/3` initially runnable contracts from entering that
incremental path.

### Implemented correction

- The two full-context candidates use the configured hard timeout. Ordinary
  Phase 1 and Phase 2 calls continue using the base timeout.
- Each candidate is scored as soon as it finishes. Admission requires complete
  contract coverage and a mechanically closed entire initial bottom-up
  dependency frontier. This gate is deterministic and contains no blocked-ratio
  or paper-specific threshold.
- The first qualifying candidate may begin Phase 1 immediately. Selection does
  not wait for a redundant sibling; cancellation is requested for unfinished
  futures, whose isolated deterministic scoring can no longer swap temporary
  plan state into the live run.
- If neither candidate qualifies, component-safe merging gets one deterministic
  chance. If the merged plan still blocks the initial frontier, every candidate
  is discarded and a non-blueprint repair request restarts the complete
  tournament through the existing bounded repair budget. A timeout or malformed
  candidate can no longer authorize degraded planning guidance.
- The next tournament receives the exact prior admission evidence. No planner
  prompt expansion, global semantic audit, or serial global closure-correction
  wave was added.

### Regression coverage

- A coordinator test proves an admissible lane returns without waiting for a
  stalled sibling.
- A routing test requires two catastrophic candidates to request a complete
  tournament restart without authorizing a blueprint edit.
- The committed `run-20260801-083320` fixture records the exact 52-node score,
  three blocked initial providers, timeout, and malformed recovery response.
- Historical replay remains the guard against over-strengthening admission:
  the fastest recorded plan retains `5/5` initial-frontier eligibility even
  though future consumers still receive their existing just-in-time checks.

## 2026-08-01: Respect Planned Member Shadowing During Helper Canonicalization

### Confirmed regression

The July 31 unique bare-helper optimization fixed unresolved downstream helper
names, but it treated every bare spelling as a global helper reference. In
`run-20260801-074355`, `PositiveLoewnerDensityInterface` declared its own
`DensityOperator : Register -> Type` field and later members referred to
`DensityOperator R`. Canonicalization rewrote those local dependent references
to the separate global `_autobp_..._DensityOperator`, which has additional
parameters. Lean then rejected the same malformed type through at least four
outer retries and repeated targeted patches.

### Implemented correction

Canonicalization now computes the member namespace of each planned
`structure` or `class`. Bare global-helper aliases that are shadowed by those
members are not rewritten anywhere in that declaration body. Qualified and
unshadowed aliases still resolve to their canonical global declarations, so
the original downstream `MaxNInterface` optimization remains active.

### Regression coverage

- The executable regression includes both a global `DensityOperator` helper
  and an interface-local `DensityOperator` field used by a later dependent
  member. It requires the global declaration and downstream target type to be
  canonicalized while the local field references remain local.
- The original unique downstream bare-helper and same-named field regressions
  remain in the suite.
- A committed historical fixture records the exact paper, node, repeated
  interval, and required shadowing invariant from `run-20260801-074355`.

## 2026-08-01: Validate Imports After Every Phase 1 Patch Merge

### Confirmed regression

In `run-20260801-070856`, a model patch imported the obsolete module
`Mathlib.Data.Polynomial.Basic`; the installed module is
`Mathlib.Algebra.Polynomial.Basic`. The existing detector identified the import
as unavailable, but only after `_apply_skeleton_replacements` had already
copied it into the merged skeleton. The later filter applied only to an
additional append, so the bad import remained and Lean failed at `+979s`.

### Implemented correction

Import validation now runs inside the shared skeleton-replacement merge
boundary. The final deduplicated import list is checked, unavailable imports
are removed before the merged module is returned, and their names are recorded
in run state so subsequent prompts do not repeat them. This applies to normal
Phase 1 generation and every targeted patch caller, independent of model
provider.

### Regression coverage

- A unit regression merges the exact obsolete import into a valid skeleton and
  requires the declaration to survive while the import is removed and recorded.
- A committed historical fixture records the failure from
  `run-20260801-070856` and requires zero mathematical repair trials.

## 2026-08-01: Bound Rejected-Plan Control With Blueprint-Direct Generation

### Confirmed regression

In `run-20260801-054159`, `def:finite-register-operators` received interface-plan
corrections at `+457s`, `+614s`, and `+926s`, while the statement critic kept
rejecting the same opaque placeholder interface. The untrusted planning
artifact continued controlling generation after its evidence-driven correction
had already failed.

### Implemented correction

The shared semantic-exhaustion router now has one statement-fingerprinted,
monotonic lifecycle:

1. Correct the interface plan once from exact rejection evidence.
2. If the corrected plan exhausts, disable it for that statement and generate
   directly from the blueprint, frozen dependency interfaces, and evidence.
3. Route to blueprint decomposition only if the blueprint-direct lifecycle also
   exhausts.

Blueprint-direct generation does not bypass acceptance: deterministic checks,
Lean compilation, and the independent statement-alignment audit remain
mandatory. The lifecycle is persisted for `--continue` and resets when the
blueprint statement fingerprint changes.

### Regression coverage

- A committed fixture records the exact three-correction trajectory from
  `run-20260801-054159`.
- The integration regression drives the real shared router through plan
  correction, blueprint-direct generation, and final decomposition.
- Persistence coverage verifies the new state survives save/load only for the
  matching statement fingerprint.
- The complete suite passes: 253 tests, including all historical Phase 1 replay
  fixtures.

## 2026-08-01: Overlap Failed-Tournament Recovery With the Surviving Lane

### Confirmed regression

In `run-20260801-051352`, tournament candidate A returned the explicit response
`{"contracts":[]}` at 16 seconds and repeated it by `+35s`. Its worker then sat
idle while candidate B ran to the 300-second timeout. The pipeline started the
already-required full-context recovery only at `+309s`; that call and its
two-contract tail finished at `+633s`. The bad-plan fallback therefore
serialized two complete model-call windows before Phase 1 could start.

### Implemented correction

- The two healthy tournament lanes and their prompts remain unchanged.
- When a lane finishes with zero usable contracts, the single existing
  full-context recovery starts immediately in that freed worker slot while the
  other candidate continues.
- The recovery is still scored with the complete deterministic plan closure and
  participates in the same component-safe selection and merge. It adds no call
  to a healthy tournament and does not alter any Phase 1 acceptance gate.
- Concurrent candidate scoring now makes its temporary plan-state swap atomic;
  deterministic scoring is locked, while all model calls remain parallel.

Using the recorded call durations, this moves complete-plan availability from
`+633s` to approximately `+359s`, removing at least 274 seconds from this
historical critical path without making the planner more elaborate.

### Regression coverage

- A threaded coordinator test proves recovery starts before the still-running
  sibling finishes.
- A committed historical fixture preserves the exact empty responses, timeout,
  fallback durations, and required critical-path reduction.

## 2026-08-01: Make Parallel Phase 1 Retry State Transactional

### Observed issue

Phase 1 generates and compiles independent contract groups concurrently, but
its retained Lean candidates and rejection evidence were only partially
protected. Candidate replacement used a lock while feedback accumulation,
stale-entry pruning, prompt reads, accepted-entry clearing, and state-file
snapshots accessed the same dictionaries without that lock. Overlapping workers
could therefore lose one worker's evidence or compose a retry from candidate
state and feedback belonging to different moments in the transaction.

### Implemented correction

- The shared Phase 1 state lock is reentrant so state readers can prune stale
  entries and snapshot the result in one transaction.
- Candidate and feedback reads now use immutable snapshots. Prompt construction,
  compiler-plan classification, shared-helper scheduling, semantic repair, and
  persisted continuation state cannot observe dictionaries while another
  worker mutates them.
- Feedback accumulation and accepted-entry clearing are atomic. A rejected
  candidate transition stores its exact rejection evidence before another
  worker can consume that candidate epoch.
- Parsing, deterministic candidate evaluation, Lean compilation, and model
  calls remain outside the state lock, so independent workers are not
  serialized by this fix.

### Regression coverage

- Added a concurrent regression that forces six workers to update rejection
  evidence for one statement simultaneously and requires every finding to
  survive in the next prompt.
- Existing Phase 1 routing and historical orchestration behavior remains
  unchanged; the fix affects only consistency of shared run state.

## 2026-08-01: Route Completed Phase 1 Compile Failures Without a Sibling Barrier

### Observed issue

In
`.auto-blueprint/formalization/unconditional-unclonable-encryption/run-20260801-030727.log`,
Lean identified at `+1265s` that `def:finite-register-operators` exactly copied
a compiler-invalid plan. The existing deterministic classifier had already
selected plan correction as the next action. That correction did not start
until `+1631s`, after unrelated sibling compiler-patch calls completed or timed
out. The batch barrier added 366 seconds after the required route was known.

### Root cause

The parallel compile coordinator collected all worker results first and routed
failures only after every future completed. Candidate persistence and failure
aggregation were correct, but the ordering forced fast failures to wait for the
slowest independent worker. The committed historical plan replay exercised
initial planner responses and frontier eligibility; it did not exercise this
compile-worker completion boundary.

### Implemented solution

- Per-candidate compile-failure persistence and classification now live in one
  shared routing function.
- The coordinator invokes that function as each compile future completes, while
  unrelated workers keep running.
- Plan correction, ordinary Lean-generation retry, exact evidence persistence,
  and telemetry retain their existing rules. This change does not add a model
  call or change which artifact is authoritative.
- The coordinator still waits for every sibling before returning and aggregates
  all failures plus compiled siblings exactly as before.
- `phase1_compile_failure_routed` records the completion-time classification
  and route, allowing future replay data to measure this boundary directly.
- A committed `20260801-030727` orchestration fixture reproduces the completion
  ordering. Its test drives the real coordinator and requires plan correction
  to begin before the slow sibling can finish, which the former batch barrier
  could not satisfy.

### Correctness effect

There is none at the acceptance boundary. A contract still freezes only after
deterministic checks, Lean compilation, integration, and statement alignment.
The change overlaps already-required independent work; it neither weakens the
blueprint contract nor accepts a failed candidate.

## 2026-08-01: Route Mixed Contract-Plan Audit Findings Per Node

### Confirmed live regression

In `run-20260801-022052.log`, one batched Phase 1 contract-plan audit rejected
`def:security-parameter-negligible` and `def:channel-povm`. Only the first issue
identified mathematical information absent from the blueprint. The second
reported no missing blueprint information and required plan/Lean correction.
The router nevertheless applied the batch-level `blueprint_issue`
classification to both nodes and widened the blueprint repair transaction.

### Implemented correction

- Contract-plan audit issues are authorized and routed independently. A
  sibling's missing-blueprint evidence cannot authorize mutation of another
  node.
- Mixed audit results carry per-label classification, reason, and decomposition
  helpers through the rejection cache and frontier gateway.
- The gateway sends only independently authorized labels to blueprint repair.
  Remaining rejected labels preserve their plan/Lean correction route for the
  next transaction; no additional audit or classifier call was added.
- Telemetry records the repair-now and deferred-plan-correction subsets so this
  routing decision remains available for classifier training.

### Regression coverage

- Added `mixed_plan_audit_routing.json`, derived from the exact audit response
  in run `20260801-022052`.
- Added a focused test that drives the real audit parser and frontier gateway
  and requires only `def:security-parameter-negligible` to authorize blueprint
  repair.
- Added a historical orchestration replay assertion preserving the observed
  incorrect scope and the expected per-node routes.

## 2026-08-01: Do Not Let Future Consumers Block the Ready Frontier

### Confirmed live regression

The first frontier-gateway implementation was wired after the old global
closure-component scheduler. In
`run-20260801-014205.log`, a selected 52-node plan had future consumers that
invented members on lower providers. The scheduler connected those consumers
to the ready providers, ran 10- and 16-node plan-correction waves, and consumed
two generation retries. The first scoped gateway did not run until `+913s`, so
the enhancement was active but could not improve startup latency.

### Implemented correction

- Global closure findings remain available for telemetry and future
  scheduling, but they are no longer a generation barrier.
- Only closure defects whose consumer belongs to the current dependency-ready
  frontier can block that frontier. A defective future consumer cannot rewrite
  or delay a ready lower provider.
- Current-frontier correction edits only the affected current contracts. Direct
  providers and future consumers are passed as read-only context. After the
  correction, the complete closure table is recomputed and the current
  frontier must be closed before its semantic gateway runs.
- A provider that already froze remains stable. If a later consumer reveals a
  real blueprint-level inconsistency, the existing semantic audit and
  fingerprint invalidation path handles it from concrete evidence rather than
  speculative global plan closure.
- If both correction tiers are exhausted, the rejected frontier entries and
  stale alternates are removed before returning to the bounded outer loop. The
  next retry therefore performs fresh scoped planning instead of replaying a
  cached rejection while consuming the entire repair budget.

### Regression coverage

- Added the `20260801-014205` multi-frontier trajectory using the real closure
  checker. It reproduces the missing-provider-member shape and the historical
  913-second pre-gateway stall.
- The regression requires the provider to freeze first, correction of only the
  consumer when it becomes ready, and complete progress across both frontiers.
- Added a focused scheduler test proving that a future consumer cannot block an
  independent ready-provider wave.
- Added the later `def:finite-register-operators` exhaustion fixture from the
  same run. It records 98 no-work retries in about two seconds and verifies the
  new invalidate-and-replan transition.

## 2026-08-01: Gate Each Ready Frontier With a Good-Enough Plan Audit

### Confirmed problem

Historical runs showed both sides of the planning tradeoff. A coherent initial
plan let Phase 1 advance quickly, while an under-specified plan could serialize
many statement-generation, compiler, and final-audit calls before the plan was
eventually corrected. Making the complete initial planner more elaborate had
already increased startup latency and timeout risk. The missing boundary was a
bounded check of the contracts that were actually about to generate Lean.

### Implemented correction

- The initial plan remains lightweight, global, and untrusted. Mechanical
  contract closure is still computed for the complete plan.
- Immediately before a dependency-ready frontier enters statement generation,
  a scoped semantic gateway audits only that frontier. Direct providers and
  consumers are included as read-only context.
- A rejection corrects only the rejected contract slice, reruns the existing
  deterministic closure checker for the affected component, and re-audits only
  changed contracts. Unrelated plan entries and graph branches are preserved.
- Accepted audit fingerprints persist with the plan entry, so an unchanged
  contract is not charged again. Audit transport failure cannot invent a plan
  defect or trigger an arbitrary correction.
- Generated Lean remains subject to every existing deterministic gate,
  compilation, and the independent blueprint/statement alignment audit. The
  new gateway decides only whether the untrusted plan is good enough to begin
  generation.

### Regression coverage

- Added a committed multi-frontier trajectory corpus for `simplex` and
  `unconditional-unclonable-encryption`.
- The replay substitutes historical responses at the real model-call boundary
  and drives the actual Phase 1 coordinator across several frontiers. It checks
  audit order, scoped correction, frozen contracts, and complete response
  consumption without a network or model account.
- Added focused routing tests for correction scope and deterministic closure
  rechecking after a semantic plan correction.

## 2026-07-31: Route Plan-Owned Audit Failures Before Retrying Lean

### Confirmed regression

The mandatory statement audit previously saw the blueprint and compiling Lean,
but not the Phase 1 design-plan entry that generated that Lean. When the plan
and generated declaration omitted the same blueprint requirement, the critic
could describe the semantic defect but the router treated it as Lean-only. In
`run-20260731-151554.log`, this serialized 921 seconds around
`def:finite-register` and 197 seconds around `def:key-space` before the existing
plan-correction path was finally reached. The best comparable
`def:finite-register` transaction in `run-20260731-133708.log` took 158 seconds.

### Implemented correction

- The existing statement-audit call now receives the blueprint node, current
  design-plan entry, and compiling Lean declaration together. The blueprint
  remains the source of truth; the plan is explicitly marked as untrusted.
- Every rejection reports whether the missing content originates in Lean, the
  plan, or both. A `plan`/`both` route is honored only when the critic names the
  exact missing plan requirements; unsupported classifications fall back to the
  ordinary Lean-generation lifecycle.
- Evidence-backed plan defects enter the existing scoped plan-revision
  transaction before another statement-generation call. Lean-only failures,
  blueprint defects, decomposition, compiler correction, and Phase 2 routing
  retain their existing behavior.
- The audit cache now includes the design-plan entry, so a corrected plan cannot
  reuse an origin classification produced for an older plan.
- This adds no model call: it enriches the mandatory audit and changes only the
  route taken after a rejection.

### Historical validation

- Added `semantic_origin_serialization.json` with the two delayed current-run
  cases and the best comparable historical transaction.
- Added regressions for plan-only, combined plan/Lean, missing-evidence fallback,
  audit-cache invalidation, and both active Phase 1 transaction paths.

## 2026-07-31: Apply Certified Statement Dependencies Before Retrying Lean

### Confirmed regression

In `run-20260731-133708.log`, the statement audit for
`def:local-basis-unitary` identified a required existing dependency while
classifying the remaining defect as Lean translation. The request preserved
the edge, but the outer loop checked model blueprint-repair authorization
first and entered the generation retry path. It spent eleven additional model
calls and 275 model-seconds before applying an edge already present in the
first audit result.

### Implemented correction

- Existing-label dependency evidence independently enters the deterministic,
  cycle-checked blueprint transaction before any generation retry.
- The edge does not authorize a model blueprint rewrite. Any residual Lean
  translation issue returns through the existing Phase 1 gates after the graph
  and statement fingerprint have been updated.
- Dependency-only requests do not advance the rejected candidate's escalation
  lifecycle before the graph correction is attempted.
- Added `statement_dependency_edge_routed` telemetry and a committed replay
  fixture containing the exact current-run classification, edge, eleven calls,
  and 275 model-seconds of avoidable work.

## 2026-07-31: Audit Model Repairs Before Regenerating Lean

### Confirmed regression

In `run-20260731-114400.log`, blueprint repair 20 changed five key-generation
contracts. The repaired `lem:key-generation-support` statement semantically
used `def:key-generation-free-coordinate-sampler` but omitted that direct
statement dependency. In the continuation `run-20260731-131011.log`, the old
pipeline spent seven generation, compiler-patch, and statement-audit model
calls and 324 seconds before the final auditor identified the missing edge.
The complete node did not freeze until 518 seconds.

### Implemented correction

- Every model repair that changes a public statement or statement-scoped
  dependency queues one scoped blueprint-only semantic audit before Lean
  generation.
- The audit sees only the changed statements, their previous versions, their
  immediate dependency/consumer boundary, a bounded paper excerpt, and the
  label inventory. It runs once as a batch, not once per node.
- Missing existing public-statement dependencies enter the existing
  deterministic, cycle-safe edge transaction. Concrete statement defects and
  required decomposition enter the existing bounded blueprint-repair loop with
  the exact audit evidence.
- Proof-prose-only repairs and ordinary Phase 1 work add no call. Auditor
  transport/JSON failure falls through once to the mandatory later Lean
  statement-alignment audit and cannot stop the run.
- Pending audit or corrective-repair state is stored in
  `skeleton_state.json`; fresh and continued runs therefore use the same
  boundary and interruption cannot silently skip it.
- Audit outcomes and their associated model-call timing are exported to
  `post_repair_boundary_examples.jsonl`, including the observed routing label,
  required dependency edges, repair labels, and requested decomposition
  helpers for future classifier training.

### Historical validation

- Added `post_repair_boundary.json`, a committed fixture preserving the exact
  five-contract repair, seven avoidable calls, and 324-second discovery delay.
- Added regressions for early dependency-edge routing, accepted healthy
  repairs, one-shot unavailable-auditor fallback, and persisted boundary state.

## 2026-07-31: Let Semantic Revisions Replace a Compiling Rejected Candidate

### Confirmed regression

In `run-20260731-114400.log`, the retained candidate for
`def:security-parameter-negligible` compiled but failed statement alignment.
Later deterministic-clean revisions were generated and some compiled, but the
monotonic candidate selector rejected every different revision as
`no_measurable_progress`: the old candidate's successful Lean status dominated
the revisions even though that old candidate was already known to be
semantically unacceptable. This kept Phase 1 at 1/52 contracts while repeatedly
regenerating the same node.

### Implemented correction

- A semantically rejected candidate is no longer considered a valid rollback
  winner solely because it compiles.
- A different candidate with no deterministic contract violations may replace
  it and continue through the existing Lean and statement-alignment gates.
- Deterministic regressions remain rejected, and the revision is not frozen
  until all normal Phase 1 checks pass.
- Added a regression covering the complete rejected-compiling candidate to
  deterministic-clean revision to successful compilation transition.

## 2026-07-31: Stop Zero-Call Recompilation After Lean Rejects a Candidate

### Confirmed regression

In `run-20260731-095949.log`, `def:uniform-finite-sampling` passed the
deterministic Phase 1 generation gate and was stored as a reusable uncompiled
candidate. Lean then rejected the exact bytes with `unknown namespace
BigOperators` and `expected token`. Recording that compiler result retained the
reuse bit, so retries 10 through 100 recompiled the same candidate without a
single model call. The loop consumed 91 repair trials and about 20 minutes
without any possibility of changing the code.

### Implemented correction

- A candidate whose exact stored bytes have `lean_status=failed` is never
  eligible for zero-call uncompiled reuse, including migrated sibling state.
- Recording failed Lean evidence for the same candidate explicitly revokes its
  reuse bit.
- The failed code, compiler output, statement fingerprint, plan fingerprint,
  and deterministic obligations remain stored. The next statement-generation
  call receives them as exact revision context instead of starting over.
- Healthy deterministically valid candidates retain the existing first-compile
  reuse path; no extra call is added before their first Lean check.

### Historical validation

- Added a committed orchestration fixture for the exact July 31 loop: 91
  identical retries, zero model calls, and 91 incorrectly consumed trials.
- Added regressions proving that Lean rejection disables zero-call reuse while
  preserving revision context, healthy candidate reuse still works, and
  historical migrated siblings cannot bypass a recorded Lean failure.

## 2026-07-31: Keep Provider Transport Failures Out of Mathematical Repair

### Confirmed regression

In `run-20260731-061030.log`, 19 Codex calls exited while reconnecting to the
responses websocket. The shared transient classifier did not recognize that
provider-specific wording. Phase 1 therefore treated seven outage waves as
failed Lean generation, reran unchanged `.dim`/`.layer` compiler errors, and
consumed repair trials 9 through 15 despite receiving no model output.

### Implemented correction

- The shared runner now recognizes websocket/reconnect failures, dropped or
  refused connections, temporary overloads, rate limits, and HTTP
  429/502/503/504 failures as transient transport errors for every CLI and API
  backend.
- Transient calls retry internally with `30/60/90` second backoff. Attempt
  reporting now counts those calls accurately.
- If transport remains unavailable, the model boundary records
  `transport_exhausted` and propagates the outage. It cannot return an ordinary
  generation error to Phase 1 or Phase 2, consume a repair trial, trigger
  decomposition, or edit the blueprint.

### Historical validation

- Added a committed replay fixture for the exact July 31 outage signature and
  its seven incorrectly consumed trials; the corrected repair-budget delta is
  zero.
- Added shared-runner tests for transient recovery, exhausted transport,
  permanent model-output failure, and the formalization boundary.
- All 219 tests pass, including the existing historical plan and orchestration
  replay suites.

## 2026-07-31: Make Optional Lean-Library Readiness Repairable

### Confirmed gap

The library resolver treated matching checkout revisions as fully up to date.
CSLib and PhysLib source trees could therefore be present and searchable while
their selected `lean_lib` targets had no compiled `.olean` artifacts. The
`apply` command then returned early because the pins matched, so the existing UI
button could not repair the state. Refinement could offer a declaration found
in source even though Lean could not import its module.

### Implemented correction

- Library status now distinguishes source/pin readiness from compile readiness.
- Optional libraries are ready only when a representative compiled artifact
  exists and a successful import probe is recorded for the exact checkout and
  active toolchain.
- Matching pins no longer bypass a missing build. The repair path builds only
  missing optional `lean_lib` targets and verifies an import; it skips
  `lake update`, the Mathlib cache fetch, and the Auto-Blueprint package build.
- The Lean status panel and **Lean libraries** tab show **build required** and a
  **Build / repair libraries** action.
- Refinement excludes unready optional source checkouts from deterministic
  candidate search. Mathlib-only behavior and per-blueprint opt-in priorities
  remain unchanged.

### Validation

- Added portable regressions for a matching-but-unbuilt checkout, a verified
  artifact/stamp pair, repair routing with current pins, candidate-search
  filtering, and the Web UI status payload.
- The complete automated suite passes (`213` tests).

## 2026-07-31: Route Plan-Owned Lean Compiler Failures to Plan Correction

### Confirmed wasted work

In `run-20260731-041307.log`, the accepted contract for
`lem:ahm-lower-bound` required `Nat.ceilLog`, but the local Mathlib API exposes
the ceiling logarithm as `Nat.clog`. Statement generation faithfully copied the
invalid planned name. Lean rejected it at `+657s`, `+894s`, `+1086s`,
`+1312s`, `+1717s`, and later retries, while ordinary compiler correction kept
the unchanged plan in force. Generated-only errors in the same candidates,
including the `BigOperators` namespace and a missing `Nonempty (Fin m)`
instance, are separate translation problems and are not evidence against the
plan.

### Implemented correction

- Parallel Phase 1 compiler failures now pass through one conservative,
  deterministic plan-defect check before ordinary retry routing.
- An unknown Lean identifier routes directly to plan correction only when the
  emitted target header exactly copies a target signature containing that
  identifier. An identifier found only in a planned helper type requires the
  complete target/helper public interface to match the plan exactly.
- Ambiguous compiler failures still receive one ordinary correction. They
  become plan defects only if the same normalized compiler error recurs under
  the same plan fingerprint and the complete emitted interface exactly
  realizes that plan.
- Generated-only names are never routed merely because Lean reports them as
  unknown. In a mixed parallel failure, only proven plan-defect labels leave
  ordinary retry routing; unrelated labels retain their existing compiler
  correction and scheduling behavior.
- Plan correction reuses the existing evidence-driven correction call and
  retained candidate seed. The blueprint remains unchanged, and the corrected
  contract must still compile and pass the mandatory statement-alignment audit.

### Validation

- The exact saved current-run candidate classifies
  `lem:ahm-lower-bound -> Nat.ceilLog` as a plan defect while excluding
  `BigOperators`.
- The complete automated suite passes (`202` tests), including mixed-wave,
  generated-only, repeated-error, and already-revised-plan cases.
- Deterministic planning replay passes for the fastest prior run
  `20260730-204628`, the prior slow run `20260731-032040`, and the current run
  `20260731-041307`; every selected complete plan retains runnable initial
  frontier work.

## 2026-07-31: Route Exact-Plan Semantic Omissions Directly to Plan Revision

### Confirmed wasted work

In `run-20260731-032040.log`, the accepted plan for
`def:polyhedral-cell` explicitly excluded the blueprint's public
full-dimensionality notion. Statement generation copied that plan exactly and
Lean compiled it. The semantic audit correctly rejected the omission, but the
pipeline classified it as a generation problem and retried under the unchanged
plan. It spent roughly another two minutes on an escalated statement patch,
two compiler-feedback patches, and an identical second audit before finally
revising the plan. The same pattern then recurred for
`def:minkowski-join`, whose generated helper included exactly the unrelated
fields required by its faulty plan.

### Implemented correction

- After Lean compilation and the mandatory independent semantic audit, the
  pipeline mechanically compares each rejected declaration with its accepted
  plan.
- The direct plan route is allowed only when the target header and every
  plan-owned helper kind, member set, and typed member declaration match
  exactly, modulo formatting and deterministic helper namespacing.
- On that proof of plan realization, the existing plan-correction call runs
  immediately with the audit evidence. No additional model call is introduced;
  it replaces the unchanged-plan generation retry that could not satisfy the
  audit without violating the plan.
- Ambiguous, incomplete, or differently typed candidates keep the existing
  generation-retry route. A plan already revised once cannot take this shortcut
  again, preserving the existing bounded decomposition fallback.

### Historical validation

- Accepted semantic audits do not execute the new comparison or change route.
- The current `def:polyhedral-cell` artifact matches the conservative trigger;
  its first rejection would skip the four intervening model calls and repeated
  compilation work before the observed plan correction.
- Candidates that change a target type or a helper member type do not trigger.
- Regression coverage checks the exact current failure shape, an exact typed
  helper interface, type mismatch, one-revision bound, and that retry accounting
  is bypassed on this route.

## 2026-07-31: Preserve Same-Named Fields During Helper Namespacing

### Confirmed regression

`run-20260731-025106.log` repeatedly rejected `lem:ahm-lower-bound` because
its plan-owned class and field were both named `weightOf`. Canonical helper
namespacing correctly renamed the global class, but the bare-helper alias pass
also renamed the field. The deterministic audit then searched for the planned
field name, reported it missing, and repeated the same singleton generation and
patch cycle 18 times without freezing another contract.

The historical plan replay did not catch this because it ended after plan
closure and frontier selection. It did not send generated declarations through
helper canonicalization and the deterministic skeleton audit.

### Implemented correction

- Global helper declarations and consumer references still receive stable,
  collision-safe `_autobp_...` names.
- Planned structure, class, and inductive member declarations retain their
  contract names even when a member has the same spelling as its helper.
- A regression test reproduces the exact `class weightOf where weightOf : ...`
  shape and runs canonicalization followed by deterministic skeleton auditing.
- Replaying the saved `lem:ahm-lower-bound` plan and candidate now produces the
  canonical class `_autobp_8865fe72d5d6_weightOf` with field `weightOf` and zero
  deterministic findings.

## 2026-07-31: Stop Treating Every Dependency Edge as a Public Type Obligation

### Confirmed regression

At roughly 15 minutes, `run-20260731-020506.log` had frozen 3 of 62 Phase 1
contracts. The comparable best run, `run-20260730-204628.log`, had frozen 32.
Replaying the exact stored response selected by that best run through the new
closure code changed its score from 6 findings at runtime to 43 findings. The
same Lean-ish plan had not become worse; a later deterministic rule had
reclassified dependency edges as missing public-signature names.

That rule was not sound for this blueprint format. A `\uses` edge may identify
a theorem used by the proof, and such a theorem normally must not appear in the
public proposition being proved. Name absence alone cannot distinguish that
case from a definition omitted from a defining equation. Blocking both cases
manufactured dozens of plan-correction calls before statement generation.

### Implemented correction

- Required, represented, and missing dependency names remain recorded in
  closure telemetry, but absence alone no longer blocks a plan contract.
- Generated references outside the authorized dependency closure, authorized
  missing provider members, invalid declaration surfaces, and helper cycles
  remain blocking mechanical findings.
- An unauthorized consumer reference no longer produces a second
  missing-member finding against its provider, so it cannot drag a healthy
  provider into the repair component.
- Exact generated aliases for `\mathlibok` nodes are rewritten to their
  authoritative `\lean` names during plan ingestion, including typed helper
  member types. The defensive alias rejection remains for stale or manually
  constructed entries.
- Tournament component substitution must improve the global mechanical score
  without reducing the currently runnable dependency frontier. A globally
  cleaner alternate can no longer delay a contract that was already ready.
- Every declaration still must compile and pass the independent semantic
  statement-alignment audit before its Phase 1 contract freezes. That audit,
  not dependency-name presence, checks whether the contract preserves the
  blueprint statement and defining equations.

### Deterministic replay

- The best run's selected response now exposes all `5/5` initial frontier
  contracts instead of `2/5` under the regressed rules.
- For the current slow run's exact responses, the selected and safely merged
  plan exposes `4/5` initial contracts; the regressed code exposed only one
  before paying for closure corrections.
- The full test suite passes: 190 tests.

## 2026-07-31: Keep Consumer Omissions From Blocking Healthy Providers

### Observed regression

Historical replay exposed a deterministic scheduling regression. Under the
current closure code, the exact planner response from the fastest recent run,
`run-20260730-204628.log`, changed from five blocked contracts at runtime to 51
blocked contracts when replayed. `run-20260731-013144.log` then spent 746
seconds to freeze one contract. The closure component builder joined every
provider named by a consumer's missing-dependency finding, despite its own
docstring and correction stage treating that provider as read-only context.
This connected distant consumers through healthy dependency leaves and could
block the complete initial frontier.

### Implemented solution

- Missing-dependency observations no longer block either contract; they remain
  telemetry for semantic auditing and future classifier work.
- A true missing-member finding still joins provider and consumer into one
  atomic repair component, because that defect may require changing both
  surfaces coherently.
- `scripts/replay_phase1_plans.py` replays content-addressed planner responses
  through the current parser, closure scorer, and initial frontier scheduler
  without making model calls or changing generated state. Ten historical
  tournaments and their exact response bytes now live under
  `tests/fixtures/phase1_plan_replay/`, so this regression runs from a clean
  clone without local telemetry or R2 access. Local telemetry remains a
  fallback for investigating runs not yet promoted to fixtures.
  `--require-progress` makes a complete historical candidate that blocks the
  whole initial frontier a regression failure.

Every contract still passes canonical ingestion, deterministic mechanical
closure, Lean compilation, and semantic statement alignment before freezing.

### Verification

- The full test suite passes: 204 tests, including two hermetic historical
  replay tests over the committed fixture corpus.
- Historical replay covered ten recent fresh planning tournaments from
  `run-20260730-152056` through `run-20260731-013144`, using their exact stored
  model responses. Every selected candidate retained at least one runnable
  initial dependency-frontier contract.
- The pathological selected candidate from `run-20260731-013144` changed from
  three broadly connected repair components, including one roughly 50-label
  component, to 29 local components with a largest component of ten labels.
- The fastest selected candidate from `run-20260730-204628` retains all five
  immediately runnable initial contracts under the current closure rules.

This replay validates deterministic routing, not model latency. A fresh run is
still required to measure end-to-end wall time, but the known graph-wide stall
cannot recur through this ownership path.

## 2026-07-31: Resolve Unique Bare Plan Helpers Before Lean Compilation

### Observed regression

In `run-20260731-010545.log`, `def:maxn` froze its planned helper under the
canonical global name `_autobp_..._MaxNInterface`. The next eight planned
consumer contracts used the model-facing name `MaxNInterface`. Canonical
ingestion recognized qualified aliases such as `def_maxn.MaxNInterface` but
left this unambiguous bare name unchanged. Lean then reported the same unknown
identifier throughout the batch, and Phase 1 paid for repeated singleton patch
calls.

### Implemented solution

- Canonical ingestion now builds the complete plan's bare-helper ownership
  table once per response.
- A bare helper spelling with exactly one canonical owner is rewritten before
  deterministic checks, persistence, or Lean compilation.
- A spelling owned by multiple plan contracts remains untouched and is rejected
  normally; the pipeline never guesses between ambiguous interfaces.
- Qualified aliases, helper ownership, namespacing, and every existing Phase 1
  acceptance gate remain unchanged.

This is deterministic and backend-independent. It adds no model call and would
have converted the observed `MaxNInterface` batch directly to the already
frozen provider interface instead of entering compiler-repair retries.

## 2026-07-31: Bound Bad-Plan Closure Repair to One Paid Call

### Observed regression

`run-20260730-204628.log`, the fastest recent fresh run, selected a plan with
five blocked contracts and froze 20 contracts by 397 seconds, 28 by 573
seconds, and 32 by 927 seconds. `run-20260731-003655.log` selected a plan with
49 blocked contracts, then spent from 222 to 575 seconds in contract-closure
repair. It had frozen zero contracts at 927 seconds and only two at 1,055
seconds.

### Root cause

The monotonic closure-correction transaction had reintroduced up to two base
calls plus one escalation call for each blocked component. That contradicted
the existing tournament policy below, which intentionally removed automatic
pre-generation escalation. A partially improving response could therefore keep
an unusable initial plan on Phase 1's critical path for several serial model
calls before any statement was generated. In the observed run, one escalation
call alone consumed 254 seconds.

### Implemented solution

- Retained alternate components remain the zero-call first choice.
- Each unresolved disjoint component now gets at most one paid base-model
  correction with its complete deterministic evidence and read-only provider
  context.
- The response is still rescored globally. A fully closed component merges;
  a strict partial improvement is retained as an alternate.
- Any component still open after that call is selectively replanned by the
  existing bounded outer transaction. Initial-plan closure never invokes the
  escalation runner.
- Disjoint components remain parallel, and successful siblings cannot be
  rolled back by a failed component.

This change removes model calls only from the bad-plan path. Closed plans and
zero-call alternate repairs behave exactly as before, and every generated Lean
declaration still passes deterministic checks, compilation, and independent
statement alignment before a Phase 1 contract freezes.

## 2026-07-31: Preserve Semantic Retry Progress Across Plan Corrections

### Observed issue

In `run-20260731-000449.log`, `def:cpwl` repeatedly compiled and then received
the same semantic rejection: its generated `CPWLInterface` abstracted away the
concrete finite-polyhedral-subdivision definition. The run consumed seven
global repairs without freezing a contract.

### Root cause

The Phase 1 lifecycle already bounds this case correctly: after both model
tiers fail, it revises the untrusted interface plan once; if both tiers reject
the revised plan too, it routes the node to blueprint decomposition. However,
contract-closure correction and retained-alternate replacement replace the
entire plan-entry dictionary. That replacement discarded
`semantic_revision_count`, resetting the unchanged blueprint statement to its
first semantic revision and allowing the same contract strategy to repeat.

### Implemented solution

- Plan replacements now preserve statement-lifecycle progress metadata.
- Both model-produced plan correction and retained-alternate replacement use
  the same preservation boundary.
- Mathematical plan content is still replaced normally; rejection and
  correction fingerprints remain tied to the exact candidate and are not
  carried onto changed contracts.
- A genuinely changed blueprint statement still resets the lifecycle through
  the existing statement-fingerprint invalidation path.

This is an orchestration fix only. It does not add a model call, change the
planner prompt, weaken semantic auditing, or add paper-specific behavior.

This file records the most recent behavioral changes to Auto-Blueprint. Each
entry states the observed problem, its root cause, the implemented solution,
and the verification performed. New changes should be added above older ones.

## 2026-07-30: Preserve Progress Inside Contract-Closure Corrections

### Observed issue

The first complete-closure run executed correction waves concurrently, but
every returned component retained at least one deterministic finding. The
transaction returned an empty result for `still_rejected`, discarded all
improvements, invalidated 12 and later 31 connected entries, and then paid for
generic planning calls. It reached ten frozen contracts at 1095 seconds,
compared with 570 seconds in the preceding run.

### Implemented solution

- Closure correction distinguishes editable owners from read-only context.
  Rejected consumers are editable; providers are edited only for missing-member
  findings, not merely because a consumer omitted their dependency.
- Every response is deterministically rescored against the exact component.
  Strictly improving candidates remain inside the isolated transaction and the
  next call receives only residual findings.
- An unchanged base result skips a redundant second base attempt and advances
  to the configured escalation runner. Healthy closed plans add no call.
- Fully closed components still merge atomically. If bounded correction cannot
  close an improving component, its best candidate is retained as an alternate
  before only the unresolved closure component is invalidated.
- Telemetry records editable labels, read-only context, model tier, pre/post
  score, and residual findings for every correction attempt.

### Verification

- Regression coverage proves that a two-step correction retains the first
  fixed provider member and sends only the remaining member to the second call.
- Existing concurrency, failed-sibling isolation, deferred-frontier, alias,
  dependency-coverage, and cycle tests remain active.

## 2026-07-30: Complete Contract Closure Before Statement Generation

### Observed issue

The existing closure gate rejected unauthorized generated references and
missing provider members, but it did not enforce the converse: every direct
statement-level blueprint dependency had to appear somewhere in the planned
target or its typed helper interface. A mechanically incomplete plan could
therefore reach statement generation and reveal omitted dependencies one at a
time through generation, compilation, and semantic-audit retries. Independent
blocked closure components were also corrected serially even though the graph
already proved they shared no provider or consumer.

### Implemented solution

- The existing closure evaluation now resolves every direct statement
  dependency to its canonical generated declaration or settled Mathlib name.
- Exact Lean identifier matching scans the parsed target declaration and every
  typed helper field or constructor. Proof-only dependencies and free-form plan
  prose do not constrain this check.
- One structured finding reports the complete missing set and joins the
  consumer to every implicated generated provider in the existing closure
  graph. Existing member, ownership, alias, duplicate-target, unauthorized
  reference, and target/helper-cycle checks remain active.
- Retained alternates are still tried first without a model call. Remaining
  disjoint components are corrected concurrently, bounded by `--workers`, from
  one immutable selected-plan snapshot. Each response is parsed and rescored
  independently; successful components merge deterministically, while a failed
  component discards only itself.
- The closure fingerprint version was incremented so continuation revalidates
  old plans. Healthy closed plans incur no new model or critic call.

### Telemetry and verification

- Closure events now include complete required, represented, and missing
  dependency sets. Correction waves record component/provider labels,
  concurrency, timing, pre/post scores, merge results, and later statement-
  freeze outcomes.
- Classifier dataset export includes closure-wave and closure-outcome events.
- Regressions cover aggregate missing dependencies, proof-only exclusion,
  Mathlib names, typed helper coverage, pre-generation cycles, concurrent
  disjoint repair, and failed-component isolation.

## 2026-07-30: Reject Generated Aliases for Mathlib-Owned Plan Dependencies

### Observed issue

The design-plan prompt correctly told models that `def:affine-map` is
Mathlib-owned as `AffineMap`, but the deterministic plan-closure validator did
not enforce that rule. In `run-20260730-191253.log`, `def_affine_map` therefore
survived planning and reached Lean, which reported it as an unknown identifier.
The later refusal handler could diagnose this mapping, but only after generation
and compilation time had already been spent.

### Implemented solution

- The existing deterministic plan-closure gate now rejects a generated label
  alias whenever the corresponding blueprint node is marked `\mathlibok` and
  has a different settled `\lean{...}` declaration.
- The check covers both canonical target signatures and types of members in
  plan-owned helper interfaces.
- It does not require proof-only Mathlib dependencies to appear in public
  contracts; it only rejects the wrong name when the plan actually uses it.
- The closure fingerprint version was incremented so persisted plans are
  revalidated on continuation. No model call was added.

### Verification

- Regression coverage rejects `def_affine_map` in a target signature and in a
  helper member type, while accepting the settled `AffineMap` spelling.
- The complete repository suite passes.

## 2026-07-30: Keep Failure Bisection Local to Its Contract Group

### Observed issue

In `run-20260730-191253.log`, Phase 1 had recovered its adaptive section size
to six. An unresolved two-contract group containing `lem:faces-preserve-Pk`
and `constr:delta3-rhombic` was then bisected into two singletons. The scheduler
copied that local part size into the run-global capacity, so the next unrelated
17-contract frontier was scheduled entirely as singleton calls. Only four of
those contracts were quarantined.

### Implemented solution

- A non-timeout `bisect` route no longer changes `effective_section_size`.
- The resulting parts are stored as local, statement-fingerprinted scheduling
  constraints for only the failed group.
- Broad groups stop at a local-part boundary; each failed part is retried as
  routed while unrelated contracts retain the current global capacity.
- Local parts persist through `--continue` and are released after they freeze
  or any participating statement changes.
- Genuine batch timeouts retain the existing adaptive capacity behavior because
  they are measured evidence that the requested batch did not fit its timeout.

### Verification

- Regression coverage reproduces the two-node bisection with global capacity
  six and verifies that unrelated neighbors remain broadly grouped.
- Persistence and statement-fingerprint invalidation are covered.
- The complete repository suite passes: 172 tests.

## 2026-07-30: Preserve Compiler Transactions Without Weakening Phase 1

### Observed issue

The monotonic candidate lifecycle used one saved slot both for the best rollback
candidate and for the compiler's current correction. A deterministic-clean
patch that changed the Lean diagnostics but did not immediately reduce their
count was rejected as `no_measurable_progress`. The next call therefore edited
the older failure again. Logs showed repeated corrections of the same contracts
even though later patches depended on the preceding compiler rewrite.

### Implemented solution

- The persisted lifecycle now has two explicit roles: a stable monotonic
  best candidate and a separate deterministic-clean compiler transaction.
- A compiler intermediate may seed the next correction without replacing the
  best candidate, counting as frozen, or bypassing any Phase 1 gate.
- A compiling or measurably improved intermediate is promoted normally and
  clears the transaction; a deterministic regression is still discarded.
- Semantic correction that exposes a mechanically invalid plan-owned interface
  now routes to the existing scoped plan-revision transaction with its exact
  finding instead of restarting Lean generation under the stale plan.
- State persistence, telemetry, and classifier export distinguish
  `accepted_as_working` from `accepted_as_best`.

### Why this preserves the documented workflow

Phase 1 still freezes exact statements bottom-up only after deterministic
checks, Lean compilation and integration, and the independent statement audit.
The working compiler candidate is untrusted scratch state. Phase 2 remains the
only phase that fills proofs and deferred bodies.

### Verification

- Added regressions for retaining a same-error-count compiler intermediate,
  promoting it only after compilation, persisting it through `--continue`,
  exporting its telemetry state, and routing a semantic plan-closure conflict
  to scoped plan revision.
- The complete test suite passes: 170 tests.

## 2026-07-30: Make Phase 1 Candidate Refinement Monotonic

### Observed issue

Long Phase 1 runs repeatedly corrected the same declarations without retaining
all prior progress. A patch could fix one deterministic requirement while
dropping another, and individual deterministic, compiler, salvage, or semantic
branches could overwrite the saved candidate differently. Outer retries then
paid for another generation call under the same statement and plan.

### Implemented solution

- The existing per-node candidate cache is now the single persisted candidate
  lifecycle; no second cache or provider-specific path was added.
- Every proposed candidate is canonically ingested and evaluated by the full
  existing deterministic Phase 1 gate. Shared-helper components move atomically.
- Candidate replacement requires monotonic deterministic progress: no newly
  violated obligation and at least one removed violation. Identical candidates
  only merge new evidence. A compiler-success transition and a targeted
  semantic-correction transition are tracked explicitly without bypassing their
  later Lean and critic gates.
- Compiler failure stores the actual post-patch code and exact Lean output.
  Semantic failure stores the compiling code and exact critic evidence.
- Deterministically regressing proposals remain telemetry/evidence records.
  The previous best remains the rollback seed; a deterministic-clean compiler
  intermediate may continue as an untrusted working transaction until it
  compiles or makes measurable progress. Feedback is cumulative and
  deduplicated for the current statement fingerprint.
- A plan revision starts a new plan-fingerprint epoch and re-evaluates the old
  compiling code only as an untrusted correction seed. A statement edit prunes
  stale state. `--continue` restores the lifecycle; `--fresh` removes it.
- Generation can no longer choose the blank bulk prompt merely because the
  separate feedback map is empty when a retained candidate exists.

### Telemetry and verification

- `phase1_candidate_transition` records parent/candidate hashes, statement and
  plan fingerprints, complete obligation sets, newly satisfied and regressed
  obligations, selection outcome, source, tier, and Lean/semantic status.
- Dataset export now writes
  `fast_phase1_candidate_transition_examples.jsonl` for future ranking and
  routing classifiers without invented confidence labels.
- Added regression coverage for deterministic regression rejection, monotonic
  replacement, and exact compiler/semantic evidence retention. The existing
  Phase 1 routing suite remains green.

## 2026-07-30: Select and Merge Two Independent Initial Plans

### Observed issue

Repeated fresh runs could receive materially different plans from the same
full-context planning prompt. A coherent response let Phase 1 advance, while an
under-specified or mechanically inconsistent response sent the same paper into
long component-correction chains. Treating one nondeterministic response as the
only initial plan made run time depend too heavily on that single sample.

### Implemented solution

- A fresh multi-node run now generates exactly two complete root-first plan
  candidates concurrently with the configured base runner. The planner prompt
  and schema are unchanged.
- Existing deterministic coverage, helper ownership, dependency authorization,
  and contract-closure checks score both candidates globally.
- The better complete plan is selected. Rejected provider-consumer components
  may be replaced from the alternate candidate only when rescoring the complete
  merged plan proves a strict mechanical improvement. Plans are never mixed
  arbitrarily node by node.
- The non-selected contract for each node is retained. A later rejected
  component tries that alternate once, with zero model calls, before the
  existing correction path runs.
- If neither candidate supplies a closed component, only that component gets
  one base-model correction with exact findings. The previous automatic second
  escalation correction was removed; unresolved entries are replanned by the
  existing bounded outer transaction.
- Selective replanning after blueprint edits remains single-candidate, so the
  tournament cost is paid only for a fresh shared plan.
- Telemetry records both raw model calls, candidate scores and findings,
  selected and merged components, alternate substitutions, and their downstream
  acceptance. The selected plan and unused alternates are persisted for
  `--continue`.
- The existing pre-edit dependency-cycle guard is unchanged.

### Why this preserves correctness

Candidate scoring and merging accept no Lean statement. The selected plan is
still untrusted generation guidance. Every emitted declaration must pass the
same deterministic gates, Lean compilation, and independent blueprint
statement-alignment audit before Phase 1 freezes it.

## 2026-07-30: Separate Plan Defects from Blueprint Decomposition

### Observed issue

A Phase 1 statement could be semantically rejected because its untried design
plan omitted a required interface, yet the first rejection immediately edited
the blueprint. Structural contracts could then loop: generation emitted a
plan-owned structure plus the canonical target as a transparent type alias,
the generic deferred-body gate rejected the alias, and replacing it with an
opaque `sorry` target lost the structure required by consumers. Separately, a
critic-requested dependency edge could close a cycle and was discovered only
after editing and revalidating the draft.

### Root cause

- `needs_decomposition` bypassed the existing evidence-driven plan-revision
  lifecycle even when the current plan had never been revised.
- Phase 1 treated every completed target `def` as implementation work, including
  a definition whose entire purpose was to expose its plan-owned structural
  type interface.
- Dependency repairs and decomposition direction were validated too late and
  reported only as generic blueprint failures.

### Implemented solution

- The first decomposition verdict for an untried plan now performs one scoped
  plan revision using the exact statement-audit evidence. Only a repeated
  verdict under that revised plan can mutate the blueprint.
- Phase 1 accepts one narrow completed-definition form: a canonical type-valued
  target may transparently alias its own plan-owned `structure`, `inductive`,
  or `class`. Arbitrary completed definitions remain rejected.
- Proposed `\uses` repairs are checked against the existing graph before any
  source edit. Cycle rejection includes the exact path and is passed into the
  bounded blueprint-repair call.
- Decomposition is accepted only when each newly introduced helper is upstream
  of a repaired target. Reversed or disconnected helpers roll back with exact
  deterministic evidence.
- Healthy runs gain no model calls and the initial planner schema is unchanged.

### Verification

- Added regressions for structural aliases, arbitrary completed definitions,
  plan-first decomposition routing, cyclic edge rejection, and decomposition
  orientation.
- Targeted Phase 1 routing tests pass: 156 tests.

## 2026-07-30: Require Typed Phase 1 Helper Contracts

### Observed issue

Phase 1 interface plans stored only the names of fields and constructors owned
by auxiliary `structure`, `inductive`, and `class` helpers. The closure check
therefore accepted a helper surface such as `p1_linear_map`, `p1_rewrite`, and
`p1_mem` without deciding their Lean types. Statement generation had to invent
those types and repeatedly mistranslated index-sensitive coordinate maps even
though the blueprint and later critic feedback were concrete.

### Implemented solution

- The design-plan schema now requires every helper member to provide both its
  stable name and complete Lean-ish type.
- Untyped, malformed, duplicate, or excessively large helper-member contracts
  invalidate that plan response instead of being silently discarded.
- Generation and compiler-repair prompts render the accepted typed members
  verbatim. Persisted plans retain the same typed representation.
- Contract closure now recognizes that a canonical target returning an owned
  helper interface exposes that helper's fields as value projections. For
  example, `def def_Pk : PkInterface` exposes `def_Pk.inPk` when `inPk` is a
  declared `PkInterface` member; this prevents unrelated consumers from being
  grouped into a false repair.
- The schema version was increased, so older untyped cached plans are replanned
  automatically.
- Refinement routing, compilation order, and semantic-audit order are unchanged.

### Verification

- Added regression coverage for typed helper-member parsing/rendering and for
  rejecting name-only or otherwise unimplementable helper contracts.
- The complete test suite passes: 156 tests.

## 2026-07-30: Make Phase 1 Design Planning JSON-Only and Complete

### Observed issue

In `.auto-blueprint/formalization/simplex/run-20260730-005058.log`, the first
two design-plan calls each returned `{"contracts":[]}`. Telemetry showed the
same prompt and response hashes both times. They consumed two outer retries
without producing any Phase 1 contract. The third response contained all 62
contracts, but the contradictory prompt had also asked the planning model to
follow Lean-code and decomposition output rules.

### Root cause

The JSON-only design-plan prompt reused `_common_rules`, which is written for
Lean generation and instructs the model to return a Lean code block or an
alternate decomposition response. The planner therefore received mutually
exclusive output contracts. A zero-contract JSON response was parsed as a
successful response, and its exact rejection was not included in the next
prompt.

### Implemented solution

- Design planning now uses dedicated JSON-only rules. It contains no Lean-code
  or alternate-output instructions.
- A successful-status response containing zero usable contracts is recorded as
  `invalid_empty_contracts`, not `ok`.
- The planner retries that malformed response once inside the same planning
  transaction with explicit completeness feedback. The retry prompt therefore
  cannot be byte-identical to the rejected prompt.
- Regression tests verify both prompt consistency and the zero-contract retry.

## 2026-07-30: Preserve Every Authorized Repair from a Parallel Frontier

### Observed issue

In `.auto-blueprint/formalization/simplex/run-20260729-235906.log`, Phase 1
twice logged that `def:relu-network` had exhausted statement translation and
was being routed to blueprint decomposition. The next frontier nevertheless
scheduled the same contract for statement generation again. A simultaneous
deterministic dependency repair was executed while the decomposition request
disappeared.

### Root cause

The parallel-frontier handoff collected every failure but selected only the
first request authorized to edit the blueprint. When dependency-edge,
blueprint, or decomposition failures arrived together, list order could
silently discard the other authorized actions even though their evidence and
routing decisions were correct.

### Implemented solution

- All authorized requests from the frontier are now aggregated with their
  labels, exact evidence, accepted sibling sections, decomposition helpers,
  and required dependency edges intact.
- The aggregate distinguishes dependency-only labels from labels requiring a
  model-driven blueprint repair. The outer transaction applies deterministic
  edges and still executes simultaneous blueprint/decomposition work instead
  of treating those actions as mutually exclusive.
- Telemetry records the combined request count and both resulting scopes.
- A regression test reproduces a decomposition request arriving beside a
  dependency-edge repair and verifies that neither action is lost.

## 2026-07-29: Route Repeated Phase 1 Semantic Failure to Decomposition

### Observed issue

In `.auto-blueprint/formalization/simplex/run-20260729-221008.log`, a small
set of contracts repeatedly consumed most of Phase 1. Three labels alone
accounted for 37 statement-patch calls and about 1,906 seconds of model time.
Their rejected declarations repeatedly expanded concrete mathematical
constructions inline or hid them behind arbitrary witnesses because the
blueprint exposed no reusable declaration-level interface for those objects.

### Root cause

The statement critic returned one classification for an entire audited batch,
and both Phase 1 audit consumers treated semantic exhaustion differently. One
path revised an interface plan once; the semantic-first path could revise it
again indefinitely. A missing blueprint interface could therefore be routed as
another Lean translation attempt, especially when its audit batch also
contained an ordinary Lean encoding error.

### Implemented solution

- Every rejected issue now carries its own routing classification. Mixed audit
  batches preserve Lean-only candidates while sending only independently
  justified blueprint/decomposition labels to repair.
- Both Phase 1 audit consumers now share one exhaustion transition. The first
  exhaustion revises the saved interface plan from the exact critic evidence.
  The later 2026-08-01 circuit-breaker change extends this transition: a second
  exhaustion first tries blueprint-direct generation, and only exhaustion of
  that direct lifecycle enters the blueprint-decomposition transaction.
- Decomposition covers missing named mathematical objects, operations,
  relations, and substantial intermediate statements, including contracts
  otherwise expressible only by duplicating a large executable term or using
  an arbitrary witness. Ordinary Lean syntax, typing, and API errors remain
  Lean-generation corrections.
- The plan-revision count is bound to the blueprint statement fingerprint and
  persisted across `--continue`; a real blueprint statement change resets the
  lifecycle naturally.

### Correctness, latency, and telemetry

This changes routing, not acceptance. Every resulting blueprint draft is still
validated, and every regenerated declaration still passes deterministic gates,
Lean compilation, integration, and the independent statement audit before it
freezes. No additional model call is introduced: routing consumes the existing
statement-audit result and prevents repeated generation under an interface
already rejected after revision.

Telemetry now records per-label `routed_kinds`, mixed-batch repair/deferred
subsets, the statement fingerprint, source audit path, and exact evidence when
semantic exhaustion enters decomposition. Regression tests cover mixed routing,
one-revision exhaustion, and persistence of the revision count.

## 2026-07-29: Preserve Dependency Repairs Across Phase 1 Audit Routing

### Observed issue

In `.auto-blueprint/formalization/simplex/run-20260729-205822.log`, the
statement critic correctly reported the deterministic dependency correction
`lem:claim5 -> def:tab`. The outer loop nevertheless regenerated the statement
and revised its plan repeatedly instead of applying the existing transactional
dependency-edge repair.

### Root cause

Both Phase 1 final-audit rejection paths extracted the critic's structured
`required_dependencies` map and stored it with the candidate, but omitted that
map when constructing the `RepairRequest` returned to the outer transaction.
The outer repair logic therefore received the rejection text but not the
structured authorization needed to invoke deterministic edge repair. Earlier
runs sometimes reached a later semantic-correction path that preserved the
map, which made the defect intermittent and sensitive to batching.

### Implemented solution

- Compile-then-audit and semantic-first rejection requests now both carry the
  complete certified dependency map.
- The existing outer transaction remains responsible for validating and
  applying the edge; the critic still cannot edit arbitrary dependencies.
- Regression tests cover both rejection paths, including the singleton route
  that looped on `lem:claim5`.

## 2026-07-29: Run Phase 2 Proofs Top-Down Independently of Phase 1

### Intended behavior

Once Phase 1 has frozen the complete one-to-one Lean statement skeleton,
Phase 2 should validate the blueprint's public results first. Higher theorem
proofs may use the exact frozen statements of lower lemmas while those lower
bodies remain deferred. Filling a lower theorem body later does not alter its
public type and therefore does not require regenerating an accepted higher
proof.

### Implemented solution

- Phase 1 statement traversal is fixed bottom-up and Phase 2 body traversal is
  fixed top-down. The obsolete `--proof-order` CLI flag and Web UI selector
  were removed so runs cannot select a contradictory pipeline combination.
- Phase 2 always selects implementation frontiers with the existing root-first
  scheduler.
- Phase 2 logs, reports, graph telemetry, frontier telemetry, and repair
  telemetry record `top-down` explicitly while retaining the Phase 1 order as
  a separate field.
- The Web UI displays the fixed two-phase policy without a traversal control.
- Existing accepted proofs remain reusable because the persisted statement
  traversal identifies the fixed Phase 1 state; proof scheduling does not mutate
  any frozen declaration.

### Correctness boundary

This changes scheduling only. Phase 2 still compiles every completed body,
audits completed definitions, preserves successful siblings, and performs the
strict no-`sorry` final check. Blueprint repairs retain the existing
fingerprint and deterministic revalidation behavior.

## 2026-07-29: Schedule Closed Contracts Before Provider-Aware Repair

### Observed issue

The first run after contract-closure validation was repaired,
`.auto-blueprint/formalization/simplex/run-20260729-194423.log`, still reached
its first statement-generation call at 671 seconds and froze 31 contracts at
2495 seconds. The pre-closure baseline, `run-20260729-031415.log`, started
generation at 252 seconds and had frozen 46 contracts by 2346 seconds.
Although 49 of 62 planned contracts had no closure finding at 178 seconds, the
global closure barrier held all of them while 13 rejected consumers went
through correction, escalation, and replanning.

The repair calls also received only the consumer that mentioned a missing
member. For example, consumers of `def_relu_network.represents` were asked to
change while the provider contract `def:relu-network` was absent from the
correction request. The model consequently substituted other missing member
names instead of making the provider and consumers agree.

### Root cause

Closure findings were stored as consumer-keyed strings. Provider ownership was
available while constructing the symbol table but discarded before repair.
`_ensure_phase1_design_plan` then treated any finding anywhere in the pending
graph as a prerequisite for all Phase 1 generation.

### Implemented solution

- Closure findings now retain their consumer and implicated provider as
  structured data while preserving the existing grouped-string API.
- Missing-member repairs operate on connected provider-consumer components.
  Consumers sharing a provider are corrected with that provider in one
  coherent contract transaction.
- Phase 1 records all findings after the shared plan but defers model-backed
  closure repair until a blocked component reaches the selected traversal
  frontier.
- Dependency-ready contracts outside blocked components proceed through the
  unchanged generation, compilation, and semantic-audit transaction
  immediately.
- In bottom-up mode an implicated provider is blocked before it can freeze, so
  a later consumer correction cannot silently change an already-frozen public
  interface. Top-down mode repairs a blocked component before refining its
  current layer.
- If both correction tiers fail, the whole unresolved connected component is
  invalidated for fresh planning. Unrelated closed contracts, closure cache
  entries, accepted sections, adaptive section size, and quarantine remain
  untouched.

### Correctness and performance effect

No contract bypasses closure validation. The scheduler only advances a node
when its contract is closed and it is dependency-ready; blocked providers and
their consumers wait together. The change removes the global startup barrier
and the consumer-only renaming loop without weakening canonical-declaration,
compilation, or independent statement-alignment checks.

### Verification

- Provider-aware correction receives both provider and consumer contracts.
- Exhausted correction invalidates both sides of the unresolved component but
  preserves unrelated entries.
- Deferred closure leaves an unrelated closed contract schedulable.
- Bottom-up Phase 1 freezes unrelated closed work before invoking repair for a
  blocked provider-consumer component.
- The complete test suite passes (`145` tests).

## 2026-07-29: Close the Multi-Target Plan Regression

### Observed issue

After the two preceding Phase 1 changes,
`.auto-blueprint/formalization/simplex/run-20260729-140024.log` froze only 25 of
62 contracts after roughly 59 minutes; the preceding
`run-20260729-031415.log` had frozen 48 contracts at the same elapsed time.
`def:relu-function` and `def:minkowski-join` repeatedly alternated between
statement generation and plan correction.

### Root cause

The contract-closure validator checked generated references and member
surfaces, but did not check the declarations contained in a target signature.
Those two plans each declared two public `def`s for one blueprint node. Model
output canonicalization correctly treated the noncanonical declaration as a
node-owned helper, and Phase 1 correctly rejected executable helpers, but then
misclassified every unplanned helper as a plan defect. Partial-failure
preservation kept that unresolved work alive, magnifying the contradiction
into repeated plan calls on every frontier. The ordinary failure router also
treated two pre-generation closure rejections as statement-batch failures,
reducing the global section size from 12 to 2 and then 1 before statement
generation began. That is why the regressed run launched singleton calls while
the earlier run advanced in broad groups.

### Implemented solution

- Contract closure now requires exactly one top-level declaration in every
  target signature, named with that node's canonical generated Lean name.
- The closure-check version is part of its cache fingerprint, so `--continue`
  rechecks plans accepted by the older incomplete validator instead of reusing
  their stale acceptance markers.
- A blueprint node that defines several related operations must package them
  in one plan-owned `structure` or `class` interface returned by the canonical
  target. Planning and correction prompts state this rule explicitly.
- An unplanned executable helper is no longer automatically classified as a
  plan defect. If a closed plan did not request it, the existing targeted
  generation-repair path receives the exact deterministic rejection.
- Genuine symbol/member/declaration closure failures still use targeted plan
  correction before statement generation.
- A plan-revision retry no longer modifies statement-generation quarantine or
  adaptive section size. Plan shape is not evidence that a model batch was too
  large; only actual generation failures may reduce that capacity.

### Correctness and performance effect

The change does not weaken statement alignment or accept additional Lean
declarations. It moves an objectively invalid one-node/multiple-target plan to
the pre-generation boundary and removes repeated plan correction for output
that diverged from an otherwise valid plan. Partial sibling preservation
remains enabled without continuously rescheduling this contradictory state.

### Verification

- Regression coverage rejects a second public target in one node's contract.
- Regression coverage accepts the same bundled operations behind one
  plan-owned type interface and canonical target.
- Regression coverage distinguishes model-invented helpers from actual plan
  closure failures when routing repair.

## 2026-07-29: Validate Contract Closure Before Statement Generation

### Observed issue

In `.auto-blueprint/formalization/simplex/run-20260729-031415.log`, the shared
Phase 1 plan proposed contracts that could not be realized as Lean
declarations. For example, one target required
`def_relu_network.Representable` even though the planned `def_relu_network`
structure exposed no `Representable` member. Another target/helper pair formed
a declaration cycle: the target's type required its helper while the helper's
field type required the target. These plans survived until statement
generation and then consumed repeated compiler-patch and plan-correction calls.

The first live run of the closure gate,
`.auto-blueprint/formalization/simplex/run-20260729-041359.log`, exposed a
second orchestration bug. One base correction remained invalid, after which
the correction fingerprint correctly suppressed the identical model call but
the outer loop still counted each cache hit as a new retry. It consumed retries
3 through 100 without performing work and stopped after 537 seconds.

### Root cause

The plan boundary checked coverage and schema shape but did not build a symbol
table for the complete planned interface. Candidate-time routing recognized
only unplanned executable helpers as plan failures. Missing generated members
and owner/helper cycles therefore looked like ordinary Lean-generation errors,
even though no emitted declaration text could satisfy the plan.

### Implemented solution

- Immediately after planning, a deterministic closure validator builds the
  generated target/helper symbol table and their declared member surfaces.
- Dotted generated references must name an exposed field or constructor.
- Plan-owned helpers may be consumed through their owning blueprint node, but
  the owner and all generated target dependencies must remain inside the
  consumer's statement dependency closure.
- Accepted closure results are cached by a fingerprint of the contract and the
  complete planned symbol surface. A valid plan adds no model call.
- Only rejected entries are sent to the existing targeted
  `phase1_design_plan_correction` call with the exact mechanical findings.
- A still-invalid base correction advances once to the escalation correction
  tier. If that also remains invalid, only those rejected plan entries are
  removed so the next bounded outer retry performs fresh planning. Valid plan
  entries and their closure fingerprints remain intact.
- An unchanged correction-cache hit therefore cannot be returned repeatedly as
  new work or drain the repair budget.
- Canonical candidate ingestion performs the corresponding declaration-graph
  check. A target/helper cycle is classified as the same plan-closure failure
  and returns to plan correction instead of spending compiler-patch rounds.
- Top-down and bottom-up Phase 1 use one shared plan-revision predicate, so the
  routing does not depend on which stage discovered the impossible contract.

### Correctness invariants preserved

- The closure validator makes no mathematical judgment and does not replace the
  independent statement-alignment audit.
- The plan remains untrusted generation guidance. Generated Lean must still
  pass deterministic checks, compilation, integration, and semantic alignment
  before a contract freezes.
- The blueprint dependency graph continues to authorize generated references;
  the validator does not invent dependencies or weaken blueprint statements.
- Blueprint content is not edited by a mechanical plan-closure rejection.

### Telemetry added

- `phase1_design_plan_closure` records accepted, rejected, and cached closure
  decisions with exact findings.
- `phase1_outline_plan_closure_correction` now uses the general
  `deterministic_contract_closure` reason for both pre-generation and
  candidate-time closure failures.

### Verification

- Regression coverage rejects a missing generated member and accepts the same
  reference when the member is exposed.
- Regression coverage detects a generated owner/helper declaration cycle.
- Regression coverage verifies that closure failure invokes targeted plan
  correction before statement generation and fingerprints the corrected plan.
- Regression coverage verifies that unchanged base and escalation corrections
  invalidate only the rejected entries for fresh planning instead of looping.

## 2026-07-29: Preserve Partial Phase 1 Work and Aggregate Parallel Failures

### Observed issue

The Phase 1 run in
`.auto-blueprint/formalization/simplex/run-20260729-022719.log` reached 23 frozen
contracts faster than the preceding run, but then repeated substantial work.
The clearest example was:

```text
The response omitted required Phase 1 declarations:
lem:ahm-lower-bound -> `lem_ahm_lower_bound`.
```

The model had returned the other declarations in the 11-node request. Despite
the failure being attributable to one missing declaration, the pipeline routed
eight nodes as affected and later regenerated groups of six and five nodes.

The same run also had several candidate groups executing concurrently. When
more than one group failed, the compile transaction retained and reported only
the first failure. A semantic rejection from a successfully compiled sibling
could also replace the original compile failure while unwinding the partial
transaction. The unselected failures resurfaced in later outer iterations,
causing repeated generation and correction calls.

### Root cause

The existing shared failure router operated only after the caller had selected
one failure. Two lower-level transaction boundaries still discarded
information:

1. Incomplete model responses were treated as unattributed whole-group
   failures. The code knew exactly which declarations were missing but did not
   preserve independently valid declarations returned beside them.
2. Parallel generation/compilation collected multiple failures but selected a
   single exception for the outer loop. Code and evidence for the other failed
   candidates could be stored, but their retry scopes were not applied in the
   same transaction.

This is why earlier retry-isolation changes did not fix this case: the router
could not route successful output or failures that its caller had already
dropped.

### Implemented solution

Phase 1 now treats a frontier operation as one transaction with multiple
independent outcomes:

- An incomplete response is parsed before routing. Every complete target or
  shared-helper component that passes the existing deterministic Phase 1 gates
  is stored as a reusable uncompiled candidate.
- Only missing or deterministically invalid declarations are unresolved.
  Explicitly missing declarations are passed to the failure router as the
  attributable subset.
- A reusable singleton/component is scheduled separately from fresh work. It
  proceeds directly to Lean compilation and the existing statement-alignment
  audit without another generation-model call.
- Parallel compile failures are all persisted with their exact Lean evidence.
  Their independent retry routes are aggregated into one outer transaction
  instead of selecting `failures[0]`.
- If auditing successfully compiled siblings produces another non-blueprint
  rejection, that rejection is aggregated with the original compile failures
  rather than masking them.
- The outer orchestrator applies every retained route independently. Isolation,
  bisection, and singleton escalation therefore retain their original behavior
  for each failed candidate group.

### Correctness invariants preserved

- A salvaged declaration is not frozen merely because the model returned it.
  It must pass deterministic statement checks, Lean compilation, integration,
  and the statement-alignment audit before its Phase 1 contract is accepted.
- Blueprint repair remains available only when evidence explicitly authorizes
  a blueprint contract change.
- The blueprint remains the specification being verified; no Lean statement is
  accepted by weakening or replacing its blueprint claim.
- Shared helpers remain atomic with their owning target component. The pipeline
  does not preserve a helper fragment that cannot be compiled independently.
- Phase 2 behavior is unchanged.

### Telemetry added

- `phase1_partial_response_salvaged` records requested, delivered, salvaged, and
  unresolved labels.
- `phase1_parallel_compile_failures` records every failed candidate group and
  the siblings that compiled.
- `phase1_failure_routes_applied` records every independent route applied by
  the outer orchestrator.

These events retain the distinction between model omission, deterministic
rejection, Lean compilation failure, and accepted reusable work for future
classifier training.

### Verification

- Added regressions for salvaging an independently valid declaration from an
  incomplete response.
- Added a regression proving that only the omitted declaration is routed.
- Added a regression proving reusable singleton candidates are not rebundled
  with fresh generation work.
- Added a regression proving every parallel compile failure and its evidence is
  retained.
- Updated the partial-frontier regression to require simultaneous generation
  and semantic failures to be aggregated.
- `tests.test_formalize_phase1_routing`: 123 tests passed.
- Full repository suite: 133 tests passed.

## 2026-08-02: Repair Missing Lean Universe Binders Without a Model Call

### Problem

In `run-20260802-221127`, independently generated Phase 1 candidates repeatedly
used types such as `Type u` without emitting the mechanical top-level binder
`universe u`. Lean reported the exact same `unknown universe level` diagnostic
at 279s, 394s, and 538s. The general failure router then paid for fresh model
corrections even though the mathematical interface was not in question.

### Implemented solution

Every shared Lean compile boundary now recognizes only Lean's exact
`unknown universe level` diagnostic for the file being compiled. It inserts a
top-level `universe` declaration containing exactly the missing identifiers and
retries the same compiler command once. Existing declarations are respected,
diagnostics from other files are ignored, and unrelated Lean errors are left to
the normal routing logic. This deterministic correction consumes neither a
model call nor a blueprint-repair trial and does not alter any target statement
or proof.

### Regression coverage

The committed historical fixture `unknown_universe_retry.json` reproduces the
UUE failure without requiring telemetry or a model account. Unit coverage also
checks multiple levels, idempotence, cross-file diagnostics, and unrelated Lean
errors. The behavior is shared by the statements-first compiler, legacy/final
Lean verification, and generated `.olean` compilation.

- A production-path smoke test repaired and compiled an actual Lean file with
  `Type u` and no original binder.
- Full repository suite: 296 tests passed.
- Focused orchestration and trajectory replay suite: 25 tests passed.
- Complete committed Simplex planner replay passed with `--require-progress`.
- `git diff --check` passed.

## 2026-08-03: Route Repeated Phase 1 Compile Failures Through the Node Lifecycle

### Observed issue

In
`.auto-blueprint/formalization/unconditional-unclonable-encryption/run-20260803-031013.log`,
`thm:security` repeatedly produced compiler-invalid Lean during Phase 1. The
node had already received a statement-alignment rejection, but compile failures
from retries 51 through 55 bypassed the persisted per-node retry lifecycle.
Each outer iteration therefore treated the compiler failure as fresh work,
repeated local correction calls, and consumed the global repair budget without
reaching the existing exhausted strategy.

### Root cause

Statement-audit failures advanced `phase1_statement:<label>` through the
existing base, escalation, and exhausted states. The parallel compilation path
stored its candidate and compiler output, but returned an ordinary Lean
generation failure without advancing that same lifecycle. In addition, the
parallel coordinator aggregated ordinary retry requests but did not preserve
an authorized blueprint-decomposition request produced by an exhausted compile
failure.

### Implemented solution

- Every completed Phase 1 compile failure now stores candidate code and
  node-scoped compiler evidence, then advances the same persisted
  `phase1_statement` lifecycle used by semantic rejections.
- Exhaustion first invokes the existing strategy change: revise an invalid
  plan when justified or switch once to blueprint-direct generation.
- If compiler-invalid output survives the blueprint-direct base and escalation
  lifecycle, the existing scoped decomposition route is authorized for only
  the exhausted node. It no longer regenerates indefinitely under the same
  strategy.
- Parallel compilation still preserves independently compiled siblings. When
  one worker reaches an authorized exhaustion route, the coordinator now
  propagates that authorization instead of flattening it into an ordinary
  retry request.
- The routing uses the runner-independent model tier recorded on the candidate;
  it does not depend on Codex-specific output or reasoning controls.

### Correctness invariants preserved

- A compiler failure alone does not edit the blueprint. Blueprint repair is
  authorized only after the existing plan-revision and blueprint-direct
  strategies are exhausted.
- Candidate statements still pass deterministic checks, Lean compilation,
  integration, and statement alignment before freezing.
- Accepted sibling declarations remain preserved during a scoped failure.
- Phase 2 behavior and the Phase 1/Phase 2 boundary are unchanged.

### Regression coverage

The committed fixture
`tests/fixtures/phase1_orchestration_replay/uue_repeated_compile_failure_lifecycle.json`
captures the real `thm:security` retries and compiler error. Its executable
regression verifies the complete transition from the prior semantic rejection,
through compiler escalation and blueprint-direct generation, to scoped
decomposition. A second regression verifies that the parallel coordinator
preserves an authorized exhaustion request and its helper evidence.

- Full repository suite: `308` tests passed.
- Python compilation and `git diff --check` passed.

## 2026-08-03: Discover Codex Models From the ChatGPT App Bundle

### Observed issue

The Web UI's model fields became empty even though `codex debug models` worked
in an interactive terminal. The running `/api/state` response confirmed that
the server returned an empty Codex catalog.

### Root cause and fix

The Web UI had been launched with a GUI-style `PATH` that did not contain the
`codex` executable. The runner fallback still pointed only to the obsolete
standalone path `/Applications/Codex.app/Contents/Resources/codex`, while the
installed executable now lives at
`/Applications/ChatGPT.app/Contents/Resources/codex`.

Runner discovery now checks `PATH` first, then the current ChatGPT app bundle,
then the older standalone Codex app bundle. This is shared by model discovery
and actual Codex runner execution, so the Web UI and terminal resolve the same
installation.

### Verification

- A regression simulates a GUI process with no `codex` entry on `PATH` and
  verifies selection of the ChatGPT-bundled executable.
- An integration check with `PATH=/usr/bin:/bin` discovered all seven visible
  models from the local Codex catalog.
- The restarted Web UI returned the populated catalog from `/api/state`.
- Full repository suite: `309` tests passed.

## 2026-08-03: Keep Independent Phase 2 Branches Running

### Observed issue

Phase 2 selected only the first incomplete static top-down graph layer. In the
unconditional-unclonable-encryption run, that layer contained one unresolved
node even though three additional nodes in independent branches were already
safe to implement. The three-worker pool therefore had only one task while the
other branches waited behind an unrelated static-layer barrier.

### Implemented solution

- Phase 2 now recomputes a branch-local ready frontier after every proof wave.
- In top-down mode, a node is ready when none of its generated consumers remain
  unresolved. In bottom-up mode, the symmetric dependency-ready rule applies.
- Static layers still prioritize public roots and provide the diagnostic layer
  number, but they no longer synchronize independent graph branches.
- Frontier telemetry records `dynamic_branch_ready_frontier`, and the Web UI
  identifies the dynamically ready root-first wave.
- A regression proves that an unresolved root in one component does not block
  a lower node whose own consumer has already completed in another component.

### Correctness boundary

This changes scheduling only. A dependency cannot run before an unresolved
consumer in its own branch, and all existing compilation, semantic audit,
repair, fingerprint invalidation, and final no-`sorry` checks remain unchanged.

### Verification

- The committed UUE replay exposes four safe nodes where the former static
  scheduler exposed only the single root.
- The newer saved UUE state exposes six safe nodes to the patched scheduler,
  enough to occupy all three configured proof workers.
- Full repository suite: `310` tests passed.

## 2026-08-03: Bound Phase 2 Base Retries by Actual Unit Size

### Observed issue

In `unconditional-unclonable-encryption/run-20260803-205950`, the singleton
`lem:main-construction-security-field` made five sequential base-tier proof
calls before escalation. The retry allowance was derived from the configured
proof-batch capacity of 12 even though the section contained only one target.
Those extra bisection rounds could not split any work and consumed roughly
three and a half minutes in that one section.

### Implemented solution

- The base-round allowance now uses `min(configured capacity, actual labels)`.
- A singleton receives two base calls: an initial attempt and one retry with
  exact compiler/audit feedback.
- A genuine 12-node batch still receives five rounds, preserving the existing
  deterministic bisection path before singleton escalation.
- The committed UUE Phase 2 replay fixture records the observed five-attempt
  singleton and verifies the corrected two-attempt policy.

### Correctness boundary

This changes only how many impossible singleton bisection rounds are attempted.
The same model prompts, feedback, local Lean checks, escalation retries,
decomposition routing, blueprint repairs, and final audits remain mandatory.

### Verification

- The complete Phase 2 worker regression observes exactly two base calls and
  then the unchanged singleton escalation route.
- The 12-node case still receives five base rounds for deterministic bisection.
- Full repository suite: `312` tests passed.
# 2026-08-03: Preserve Phase 2 decomposition diagnoses

`run-20260803-232002` returned a precise `NEEDS-DECOMPOSITION` diagnosis from
the base Phase 2 whole-node call in 17 seconds. The transaction discarded it,
paid 204 seconds for escalated generation, and then spent multiple repair loops
rediscovering the same missing package interface. Phase 2 whole-node responses
now route a valid decomposition diagnosis immediately to the authorized,
bounded blueprint-repair transaction with the exact helper list. This does not
change Phase 1's stricter policy for statement-only refusals.
## 2026-08-14: Historical Phase 1 Replays Use Immutable Graph Snapshots

**Problem.** The committed planner responses were recorded against a historical
65-node Simplex graph (62 generated contracts), but the replay harness rebuilt
the graph from the mutable working blueprint. After the working draft grew to
107 generated targets, only 14 historical labels overlapped. Full test discovery
therefore reported ten false failures by comparing 14 parsed contracts with 107
live targets.

**Change.** Each committed run is now bound through
`tests/fixtures/phase1_plan_replay/manifest.json` to a content-addressed,
committed graph snapshot. The replay reconstructs node order, statement/proof
dependencies, Mathlib ownership, Lean mappings, and statement identities from
that snapshot. Current-blueprint reconstruction remains available only for ad
hoc local telemetry that has not been promoted to the fixture corpus.

**Invariant.** A historical regression is evaluated against the exact graph it
recorded, so editing a live blueprint cannot make a portable fixture pass or
fail. Missing context or a context hash mismatch is a hard test error.

## 2026-08-14: Bound Pre-Compilation Deterministic Retries

**Problem.** In `simplex/run-20260813-235136`, the canonical target
`remark_geometric_recursion_gap` matched the helper-name placeholder heuristic.
That false deterministic rejection occurred before Lean compilation, where the
request did not carry its producing model tier and therefore bypassed the
persisted retry lifecycle. The same node restarted ordinary generation from
repair 28 through at least repair 57 while Phase 1 remained at 118/119.

**Change.** Canonical names required by blueprint labels are exempt from the
helper-name placeholder heuristic; planned and model-invented helpers remain
checked. Every non-plan-closure deterministic generation failure now carries
its producing tier to the Phase-1 coordinator. The coordinator advances the
same bounded lifecycle used by compiler and semantic failures: base,
escalation, blueprint-direct generation, then scoped decomposition. Plan state
is changed only by the coordinator after parallel workers settle.

**Regression.** A committed replay records the exact Simplex label, statement
fingerprint, rejection, and observed retry range. Tests cover the immediate
canonical-name case, retain rejection for placeholder-like helper names, drive
the failure through the real parallel coordinator, and verify the complete
bounded lifecycle through terminal decomposition.

## 2026-08-20: Apply Blueprint Repairs as Scoped Returned Data

**Problem.** Blueprint-repair prompts were scoped in prose but not at the
mutation boundary. Codex and Claude Code were given the draft path, write
permission, and instructions to edit `content.tex` in place. API providers
received the entire file and returned a full-file replacement. In the recorded
Simplex Claim 5 component, a four-target repair therefore carried a roughly
31.7K-character prompt, took about 430.6 model-seconds, and returned only a
short edit summary while the actual mutation remained outside the response.
The later scope checks could roll back unrelated edits, but only after paying
for an unconstrained repair and losing a trial.

**Change.** Every provider now receives the same dependency-sliced,
return-only prompt and runs read-only. The response is a JSON map from each
requested label to that node's complete replacement TeX. A value may prepend
brand-new, uniquely owned helper nodes; it may not contain another
pre-existing label. Python applies all replacements to the immutable pre-call
source in one transaction, then runs the existing validator, graph
orientation/cycle checks, phase-specific edit-scope checks, post-repair
boundary audit, Lean checks, and semantic audit. The separate section
normalization path still uses its existing full-draft transaction and is not
part of this change.

**Correctness boundary.** The model still receives the complete failing nodes,
dependency statements, immediate consumer statements, deterministic paper
excerpt, harness rules, and exact evidence. Only mutation authority changed:
non-target blueprint text is now mechanically immutable rather than merely
protected by a later rollback.

**Regression.** Committed fixtures cover a singleton, a multi-target repair
with cross-referenced new helpers, an attempted sibling rewrite, a missing
target, and duplicate helper ownership. A coordinator-level regression runs
both the former agent and API branches and requires both to construct a
read-only runner and use the same scoped response protocol.

## 2026-08-20: Hedge Slow Compact Semantic Planning Without Killing It

**Problem.** The compact planner emits one large all-node JSON response. A
recorded 107-contract Codex call was still generating when the local 600-second
timeout killed it, so `--output-last-message` exposed no usable partial plan. An
identical fresh call then completed in about 414 seconds. Sequential recovery
therefore discarded potentially useful work and paid the two calls end to end.

**Change.** For the compact semantic planner only, `--hard-timeout` now marks
the point at which one fresh identical call starts in parallel. The original
call remains alive. The first complete successful result wins; the other call
is explicitly cancelled. A failed lane cannot cancel a still-running lane, and
each call retains a final safety ceiling of twice the hedge threshold. Other
model-call stages keep their existing timeout and retry semantics.

**Provider boundary.** Codex and Claude Code cancellation terminates the exact
losing process group. API runners receive the same coordinator race and discard
the losing response; synchronous provider APIs may continue server-side work
when their protocol offers no cancellation endpoint.

**Regression.** Tests cover a primary response that completes before the hedge
threshold, a hedge that wins while the original remains alive, explicit loser
cancellation, and the existing immediate silent-failure recovery path.
