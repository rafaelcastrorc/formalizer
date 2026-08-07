# Latest Changes

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
