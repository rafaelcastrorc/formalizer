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

The fixtures intentionally contain only synthetic statements and the minimum
historical labels needed to identify the regression shape.
