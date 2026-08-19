# Phase 1 scheduler latency replay

These fixtures contain compact task traces extracted from real Phase 1
telemetry. They intentionally omit prompts, responses, paper text, and Lean
source. Each task retains only its resource pool, duration, purpose, labels,
source sequence, and observed start time.

`scripts/replay_phase1_scheduler_latency.py` compares the observed milestone
against branch-local scheduling while preserving every recorded model call and
the causal order of calls that touch the same blueprint label. The `eligible`
policy also preserves the first observed eligibility time of every label.

The `unbounded-without-objects` policy is deliberately unrealistic: all labels
are eligible at time zero and every object build is free. It is an upper bound
for the proposed combination of branch-local scheduling and moving mandatory
object generation after semantic acceptance. It is not a prediction of live
model performance.

The fixtures protect a negative result: the proposed scheduling change does
not provide a twofold speedup across both the current August 14 Simplex run and
the best comparable August 13 run, even under the optimistic bound. Production
scheduling must not be rewritten on the claim that this proposal alone meets
the twofold target.
