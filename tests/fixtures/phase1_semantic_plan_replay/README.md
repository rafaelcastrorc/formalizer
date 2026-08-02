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

The fixtures intentionally contain only synthetic statements and the minimum
historical labels needed to identify the regression shape.
