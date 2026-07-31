# Latest Changes

This file records the most recent behavioral changes to Auto-Blueprint. Each
entry states the observed problem, its root cause, the implemented solution,
and the verification performed. New changes should be added above older ones.

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
  If the same statement exhausts both model tiers again under that revised
  plan, only that node enters the existing blueprint-decomposition transaction.
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
