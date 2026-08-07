# Phase 2 Orchestration Replay Fixtures

These fixtures preserve scheduler states extracted from real formalization
runs. They test graph eligibility and worker utilization without replaying
model calls. Each fixture records only dependency edges, unresolved labels,
and the expected dynamically ready frontier needed to reproduce the observed
scheduling decision.

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
