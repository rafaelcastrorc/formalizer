# Phase 1 planner replay fixtures

These fixtures are the minimal immutable inputs needed by
`scripts/replay_phase1_plans.py`. They preserve exact historical model response
bytes plus the candidate selection, score, requested-label, content-hash, and
dependency-graph context consumed by the deterministic replay. `manifest.json`
binds each recorded run to a content-addressed graph snapshot under `contexts/`.
The replay never combines a committed response with the mutable live blueprint.

The files deliberately exclude prompts, timing data, logs, and unrelated
telemetry events. Those observations remain in telemetry storage but do not
affect planner parsing, closure scoring, or initial-frontier scheduling.

`tests/test_phase1_plan_replay.py` verifies every response hash and requires the
selected candidate from every committed run to retain runnable work on the
initial dependency frontier. The suite therefore runs from a clean clone and
does not require `.auto-blueprint/`, R2, or network access.

Replay the complete committed corpus manually with:

```bash
uv run python scripts/replay_phase1_plans.py simplex --require-progress
```
