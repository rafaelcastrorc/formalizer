#!/usr/bin/env python3
"""Measure Phase 1 scheduler headroom from committed historical task traces.

This replay does not call a model or Lean. A fixture contains only the timing,
resource, purpose, and blueprint-label ownership of model and object-build tasks
observed before a Phase 1 progress milestone. The logical scheduler preserves
the recorded per-label causal order while allowing unrelated labels to use the
configured worker pools concurrently.

Two counterfactuals deliberately bracket the proposed optimization:

* ``eligible`` keeps the first observed eligibility time of every label. It
  measures overlap available after a branch had actually become schedulable.
* ``unbounded`` makes every label eligible at time zero. With ``--drop-objects``
  it also removes every object build, which is strictly more favorable than
  postponing object generation until after semantic acceptance. This is an
  optimistic upper bound, not an implementation forecast.

The replay therefore answers a narrow question safely: can branch-local
scheduling plus later object generation plausibly reach a requested speedup
without reducing model calls? If even the optimistic bound misses the target,
that proposal cannot satisfy the target on the recorded run.
"""
from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_FIXTURE_DIR = (
    REPO_ROOT / "tests" / "fixtures" / "phase1_scheduler_replay"
)


@dataclass(frozen=True)
class ReplayResult:
    policy: str
    observed_seconds: float
    simulated_seconds: float
    simulated_speedup: float
    task_count: int
    model_calls: int
    object_builds: int
    model_seconds: float
    object_seconds: float


def _tasks(payload: dict[str, Any], *, drop_objects: bool) -> list[dict[str, Any]]:
    tasks = []
    for raw in payload.get("tasks") or []:
        task = dict(raw)
        resource = str(task.get("resource") or "")
        if resource not in {"model", "lean"}:
            raise ValueError(f"unsupported resource {resource!r}")
        if drop_objects and resource == "lean":
            continue
        duration = float(task.get("duration_s") or 0.0)
        if duration < 0:
            raise ValueError("negative task duration")
        task["duration_s"] = duration
        task["actual_start_s"] = float(task.get("actual_start_s") or 0.0)
        task["labels"] = tuple(str(label) for label in task.get("labels") or [])
        tasks.append(task)
    tasks.sort(
        key=lambda task: (
            task["actual_start_s"],
            int(task.get("source_seq") or 0),
        )
    )
    return tasks


def replay_fixture(
    payload: dict[str, Any],
    *,
    eligibility: str,
    drop_objects: bool = False,
) -> ReplayResult:
    """Run a deterministic resource-constrained logical-clock replay."""
    if eligibility not in {"eligible", "unbounded"}:
        raise ValueError(f"unsupported eligibility policy {eligibility!r}")
    observed = float(payload.get("observed_seconds") or 0.0)
    if observed <= 0:
        raise ValueError("fixture has no positive observed_seconds")
    workers = payload.get("workers") or {}
    available = {
        "model": [0.0] * max(1, int(workers.get("model") or 1)),
        "lean": [0.0] * max(1, int(workers.get("lean") or 1)),
    }
    tasks = _tasks(payload, drop_objects=drop_objects)
    first_eligible: dict[str, float] = {}
    for task in tasks:
        for label in task["labels"]:
            first_eligible.setdefault(label, task["actual_start_s"])

    previous_by_label: dict[str, int] = {}
    completion: dict[int, float] = {}
    for index, task in enumerate(tasks):
        dependencies = {
            previous_by_label[label]
            for label in task["labels"]
            if label in previous_by_label
        }
        ready = max((completion[item] for item in dependencies), default=0.0)
        if eligibility == "eligible":
            ready = max(
                ready,
                max(
                    (first_eligible.get(label, 0.0) for label in task["labels"]),
                    default=0.0,
                ),
            )
        pool = available[task["resource"]]
        worker = min(range(len(pool)), key=pool.__getitem__)
        started = max(ready, pool[worker])
        finished = started + task["duration_s"]
        pool[worker] = finished
        completion[index] = finished
        for label in task["labels"]:
            previous_by_label[label] = index

    simulated = max(completion.values(), default=0.0)
    model_tasks = [task for task in tasks if task["resource"] == "model"]
    lean_tasks = [task for task in tasks if task["resource"] == "lean"]
    policy = eligibility + ("-without-objects" if drop_objects else "")
    return ReplayResult(
        policy=policy,
        observed_seconds=round(observed, 3),
        simulated_seconds=round(simulated, 3),
        simulated_speedup=round(observed / simulated, 3) if simulated else 0.0,
        task_count=len(tasks),
        model_calls=len(model_tasks),
        object_builds=len(lean_tasks),
        model_seconds=round(
            sum(task["duration_s"] for task in model_tasks), 3
        ),
        object_seconds=round(
            sum(task["duration_s"] for task in lean_tasks), 3
        ),
    )


def replay_path(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if int(payload.get("schema_version") or 0) != 1:
        raise ValueError(f"{path}: unsupported fixture schema")
    results = [
        replay_fixture(payload, eligibility="eligible"),
        replay_fixture(payload, eligibility="unbounded"),
        replay_fixture(
            payload, eligibility="unbounded", drop_objects=True
        ),
    ]
    return {
        "fixture": path.name,
        "source_run": payload.get("source_run"),
        "milestone": payload.get("milestone"),
        "results": [asdict(result) for result in results],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "fixtures",
        nargs="*",
        type=Path,
        default=sorted(DEFAULT_FIXTURE_DIR.glob("*.json")),
    )
    parser.add_argument("--target-speedup", type=float, default=2.0)
    parser.add_argument("--require-target", action="store_true")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    reports = [replay_path(path) for path in args.fixtures]
    if args.json:
        print(json.dumps(reports, indent=2, sort_keys=True))
    else:
        print("fixture\tpolicy\tobserved\tsimulated\tspeedup\ttasks")
        for report in reports:
            for result in report["results"]:
                print(
                    f"{report['fixture']}\t{result['policy']}\t"
                    f"{result['observed_seconds']}\t"
                    f"{result['simulated_seconds']}\t"
                    f"{result['simulated_speedup']}x\t{result['task_count']}"
                )
    if args.require_target:
        failures = []
        for report in reports:
            optimistic = report["results"][-1]
            if optimistic["simulated_speedup"] < args.target_speedup:
                failures.append(
                    f"{report['fixture']}: optimistic bound "
                    f"{optimistic['simulated_speedup']}x"
                )
        if failures:
            raise SystemExit(
                "target speedup is not supported by replay:\n- "
                + "\n- ".join(failures)
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
