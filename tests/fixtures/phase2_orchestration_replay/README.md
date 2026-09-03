# Phase 2 Orchestration Replay Fixtures

These fixtures preserve scheduler states extracted from real formalization
runs. They test graph eligibility and worker utilization without replaying
model calls. Each fixture records only dependency edges, unresolved labels,
and the expected dynamically ready frontier needed to reproduce the observed
scheduling decision.

The Simplex `run-20260813-030629` fixture records a top-down consumer whose
exact audit evidence names a dependency definition that still has a terminal
`sorry` body. It requires the scheduler to implement that definition as a
local dependency-first prerequisite instead of repeatedly editing the
blueprint. The override consumes no blueprint-repair trial and normal top-down
Phase 2 order resumes afterward.

The same fixture records `run-20260813-125126`, where a legitimate Phase 2
repair invalidated and removed the stale provider declaration. Continuation
must rebuild the smallest missing dependency closure for that provider before
resuming unrelated invalidated work; it must not reinterpret missing Lean as
another blueprint defect.

The UUE fixture also records the Phase 2 repair-boundary regression observed in
`run-20260803-214911`: once Phase 2 has started, a changed blueprint node must
be regenerated as one complete statement-and-body transaction. It may not be
routed through Phase 1 statement freezing and a later proof call.

The same fixture records the parallel authorized-repair failure observed in
`run-20260803-223132`: accepted whole-node siblings must remain frozen while a
sibling blueprint-authorized request is propagated to the outer Phase 2 repair
transaction. Such a request must never enter the non-blueprint aggregator.

The `run-20260803-224713` replay records serial helper discovery during Phase 2:
the boundary audit accepted each new helper by itself, and only a later costly
Lean attempt exposed the next helper. The boundary must retain the original
failing root and evidence and audit the complete changed helper component before
another Lean-generation call.

The `run-20260803-232002` replay records a valid Phase 2 whole-node
`NEEDS-DECOMPOSITION` response that was incorrectly discarded before an
escalated generation call. Phase 2 already supplies the complete node, proof,
and frozen dependency interfaces, so this signal must enter the authorized
blueprint-repair transaction immediately. The different Phase 1 policy, which
confirms a statement-only refusal at escalation tier, remains unchanged.

The Simplex `run-20260809-223432` replay records the transactional queue
regression: the scheduler applied many independent blueprint edits before
generating replacement Lean for the first edit, growing the draft from 65 to
173 nodes while only 16 Phase 2 implementations completed. The regression
requires one active repair at a time, blocks the next queued edit until complete
Lean verification, invalidates diagnoses whose dependency context changed, and
asserts that the deterministic scheduler transition makes no model call.

The Simplex `run-20260813-131224` replay covers the remaining transaction
boundary: replacement Lean for an already-staged blueprint edit requested a
further decomposition, and the scheduler extended the unverified helper graph.
The regression starts from the observed 75-node Phase-1 baseline and 145-node
continued draft. It requires exact restoration of the pre-edit blueprint,
generated Lean, compiled objects, and scheduler state, followed by a retry of
the original repair roots carrying the new verification evidence. A rejected
provisional helper label cannot become the next edit root.

The Simplex `run-20260814-043118` fixture covers the other entry path into that
same transaction boundary. A decomposition request returned directly by the
current Phase 2 proof frontier must persist its rollback snapshot in the same
iteration, before the repair model edits the unpublished draft. It may not wait
for a later queue iteration to create that snapshot. The regression mutates a
provisional helper component and verifies exact restoration of the pre-edit
blueprint.

The Simplex `20260810-025600-bfe3d503` telemetry replay records the complete-node
regeneration loop: 164 Phase 2 model calls consumed 38,387 model-seconds, with
45 timeouts and only 20 committed transactions. Its regression requires the
latest rejected statement-and-body candidate to survive, receive its exact
rejection in one fresh targeted correction, and pass all ordinary gates before
commit. It also records the observed resumed-versus-fresh session timings that
justify disabling backend session continuation only for this self-contained
Phase 2 correction path.

Run the deterministic logical-clock comparison with:

```bash
uv run python tests/replay/replay_phase2_latency.py --assert-improvement
```

The replay deliberately labels the retained-correction result as a
counterfactual. It validates orchestration savings and equal acceptance gates;
only a live model run can measure future wall-clock behavior.

The Simplex `run-20260813-010635` object-interface fixture records a different
failure class. A complete Phase 2 node passed ordinary Lean checking but six
separate `lean -o` attempts each consumed the old 600-second budget. Independent
controls showed that the same public statement still timed out with its body
replaced by `sorry`, while imports alone compiled quickly. The regression
therefore requires a bounded object-usability gate and a disposable
statement-only control: a statement timeout revises the Lean interface plan,
whereas a passing statement control preserves the interface and corrects only
the implementation. Neither route may weaken or edit the blueprint, and both
must rerun the normal deterministic, Lean, semantic, and integration gates.

The `run-20260821-105325` opaque-theorem fixture records a 51-module Phase-2
integration transaction in which the old whole-source cache key rebuilt 43
modules after 42 theorem proof-body edits reached one importer. Its regression
requires the reusable-object key to ignore only opaque theorem/lemma bodies.
Exact theorem statements, definition bodies, imports, the Lean environment,
and final assembled source remain invalidating and are checked separately.

`graph_scoped_invalidation.json` preserves the `Skeleton48.lean` declaration
order from Simplex `run-20260825-194345`. Repairing
`cor:geometric-signed-simplex` has no blueprint-graph descendants in that file,
yet the old source-prefix policy discarded two later independent declarations.
The regression requires graph-scoped invalidation, recompilation of retained
declarations, and strict separation between repaired-label authority and
cache-only recheck evidence.

`equivalent_failure_feedback.json` preserves two differently worded statement-
audit reports of the same missing dependency, plus a genuinely different
missing-helper report. The regression requires the equivalent reports to share
one retry/correction identity while the different obligation remains distinct.
Raw report text is retained for model feedback and telemetry.
