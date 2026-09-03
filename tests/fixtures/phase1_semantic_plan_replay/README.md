# Compact Phase 1 Planning Replay Fixtures

These fixtures preserve small, non-paper-text reproductions of failure shapes
observed in historical refinement runs. They are committed so the compact
semantic-planner and candidate-derived typed-contract boundary can be replayed
on any machine without local telemetry, R2 access, a model call, or Lean.

- `uue_unauthorized_provider_edge` reproduces a planner inventing a provider
  edge absent from the blueprint graph. The edge must be removed
  deterministically while the otherwise useful semantic entry survives.
- `simplex_atomic_structural_contract` reproduces a blueprint target whose
  structural helper must be owned, typed, and persisted from the same Phase 1
  response as the canonical target.
- `invalid_tex_escape.txt` preserves the malformed JSON shape returned in
  `unconditional-unclonable-encryption/run-20260802-210758`: the complete outer
  `contracts` array contained a TeX command such as `\dagger` with one
  JSON-invalid backslash. The parser must recover the outer payload instead of
  accepting a nested contract object and discarding the complete plan.
- `partial_nonempty_20260827.json` preserves the production 1-of-107 compact
  plan shape from `simplex/run-20260827-170917`. A nonempty partial response
  must retain its valid entry, start at most one fresh recovery call for the
  missing coverage, merge both responses, and fall back only for labels still
  absent after that bounded recovery.
- `readiness_cases.json` preserves the source-authoritative unresolved-node
  shapes from historical Simplex runs. It verifies that a non-open `\notready`
  node is repaired before Phase 1, a recorded open conjecture remains open, and
  attempt mode requires a blueprint proof before formalization.

The fixtures intentionally contain only synthetic statements and the minimum
historical labels needed to identify the regression shape.
