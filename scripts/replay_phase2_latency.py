#!/usr/bin/env python3
"""Compare legacy and retained-candidate Phase 2 latency without a model call.

The benchmark consumes a committed historical fixture.  Its legacy trace uses
the exact call durations and validation outcomes observed in a real run.  The
retained-candidate trace is a deterministic counterfactual: the same first
candidate is rejected, then a focused correction succeeds and passes every
acceptance gate.  A logical clock makes the comparison instant and repeatable.

This proves orchestration properties and timeout exposure; it does not predict
how long an unseen model response will take.  Use a live run for that final
wall-clock measurement.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_FIXTURE = (
    REPO_ROOT
    / "tests"
    / "fixtures"
    / "phase2_orchestration_replay"
    / "simplex_complete_node_candidate_loop.json"
)


@dataclass(frozen=True)
class ReplayResult:
    policy: str
    accepted: bool
    calls: int
    full_generation_calls: int
    correction_calls: int
    model_seconds: float
    acceptance_gates: tuple[str, ...]


def _run_trace(
    policy: str,
    trace: list[dict[str, Any]],
    required_gates: set[str],
) -> ReplayResult:
    """Advance a logical clock until a candidate is accepted or trace ends."""
    elapsed = 0.0
    full_generations = 0
    corrections = 0
    accepted = False
    accepted_gates: tuple[str, ...] = ()
    for step in trace:
        action = str(step.get("action") or "")
        duration = float(step.get("duration_s") or 0.0)
        if duration < 0:
            raise ValueError(f"{policy}: negative call duration")
        if action == "full_generation":
            full_generations += 1
        elif action == "targeted_correction":
            corrections += 1
        else:
            raise ValueError(f"{policy}: unsupported action {action!r}")
        elapsed += duration
        if step.get("outcome") != "accepted":
            continue
        gates = tuple(str(item) for item in step.get("gates") or [])
        missing = required_gates - set(gates)
        if missing:
            raise ValueError(
                f"{policy}: accepted candidate skipped gates: "
                + ", ".join(sorted(missing))
            )
        accepted = True
        accepted_gates = gates
        break
    return ReplayResult(
        policy=policy,
        accepted=accepted,
        calls=full_generations + corrections,
        full_generation_calls=full_generations,
        correction_calls=corrections,
        model_seconds=round(elapsed, 3),
        acceptance_gates=accepted_gates,
    )


def replay_fixture(payload: dict[str, Any]) -> dict[str, Any]:
    """Replay both policies and return machine-checkable comparison metrics."""
    benchmark = payload.get("deterministic_latency_benchmark") or {}
    required = {str(item) for item in benchmark.get("required_gates") or []}
    if not required:
        raise ValueError("fixture has no required acceptance gates")
    legacy = _run_trace(
        "legacy_discard_and_regenerate",
        list(benchmark.get("legacy_observed_trace") or []),
        required,
    )
    retained = _run_trace(
        "retain_and_correct",
        list(benchmark.get("retained_candidate_counterfactual") or []),
        required,
    )
    timeout_limits = benchmark.get("timeout_limits_s") or {}
    old_timeout = float(timeout_limits.get("legacy_full_generation") or 0.0)
    correction_timeout = float(
        timeout_limits.get("retained_candidate_correction") or 0.0
    )
    return {
        "source_run": payload.get("source_run"),
        "source_blueprint": payload.get("source_blueprint"),
        "label": benchmark.get("label"),
        "legacy": asdict(legacy),
        "retained": asdict(retained),
        "improvement": {
            "full_generation_calls_saved": (
                legacy.full_generation_calls - retained.full_generation_calls
            ),
            "simulated_model_seconds_saved": round(
                legacy.model_seconds - retained.model_seconds, 3
            ),
            "simulated_speedup": round(
                legacy.model_seconds / retained.model_seconds, 3
            )
            if retained.model_seconds
            else None,
            "per_correction_timeout_exposure_saved_s": round(
                old_timeout - correction_timeout, 3
            ),
        },
        "scope": benchmark.get("scope"),
    }


def assert_improvement(report: dict[str, Any]) -> None:
    """Fail when the replay loses correctness or does not remove known waste."""
    legacy = report["legacy"]
    retained = report["retained"]
    improvement = report["improvement"]
    if not legacy["accepted"] or not retained["accepted"]:
        raise AssertionError("both policies must reach the complete-node gates")
    if improvement["full_generation_calls_saved"] <= 0:
        raise AssertionError("retained policy did not reduce full generations")
    if improvement["simulated_model_seconds_saved"] <= 0:
        raise AssertionError("retained policy did not reduce logical model time")
    if improvement["per_correction_timeout_exposure_saved_s"] <= 0:
        raise AssertionError("correction timeout is not below full generation")
    if set(legacy["acceptance_gates"]) != set(retained["acceptance_gates"]):
        raise AssertionError("retained policy skipped an acceptance gate")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--fixture", type=Path, default=DEFAULT_FIXTURE)
    parser.add_argument("--assert-improvement", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    payload = json.loads(args.fixture.read_text(encoding="utf-8"))
    report = replay_fixture(payload)
    if args.assert_improvement:
        assert_improvement(report)
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        legacy = report["legacy"]
        retained = report["retained"]
        improvement = report["improvement"]
        print("policy\tcalls\tfull generations\tcorrections\tmodel seconds")
        print(
            f"legacy\t{legacy['calls']}\t{legacy['full_generation_calls']}\t"
            f"{legacy['correction_calls']}\t{legacy['model_seconds']}"
        )
        print(
            f"retained\t{retained['calls']}\t"
            f"{retained['full_generation_calls']}\t"
            f"{retained['correction_calls']}\t{retained['model_seconds']}"
        )
        print(
            "saved: "
            f"{improvement['full_generation_calls_saved']} full generation(s), "
            f"{improvement['simulated_model_seconds_saved']} logical model-seconds; "
            f"simulated speedup {improvement['simulated_speedup']}x"
        )
        print(
            "timeout exposure saved per correction: "
            f"{improvement['per_correction_timeout_exposure_saved_s']}s"
        )
        print(f"scope: {report['scope']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
