#!/usr/bin/env python3
"""Replay recorded Phase 1 planner responses through today's deterministic gates.

This command is a regression tool for orchestration changes, not another model
runner. Committed fixtures preserve selected telemetry responses as content-
addressed artifacts; local telemetry remains a fallback for investigating a new
run before promoting it to the fixture corpus. This script rebuilds the current
blueprint graph, parses the exact historical responses, and reports how today's
closure/component logic would score and schedule them. It therefore
distinguishes model variability from a code change that reclassifies previously
usable work as blocked.

No model is called and no generated state is modified. Use ``--require-progress``
in CI or before accepting a scheduling change to reject a replay where a
recorded plan blocks every node on the initial bottom-up frontier. With no
``--run`` arguments, every committed fixture is replayed.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from types import SimpleNamespace
from typing import Any

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
FIXTURE_RUNS_DIR = REPO_ROOT / "tests" / "fixtures" / "phase1_plan_replay" / "runs"
sys.path.insert(0, str(SCRIPTS_DIR))

from formalize_blueprint import (  # noqa: E402
    Ctx,
    _bottom_up_ready_frontier,
    _design_plan_contract_closure_issues,
    _design_plan_order,
    _evaluate_design_plan_candidate,
    _parse_design_plan_entries,
)
from validate_blueprint import validate_blueprint  # noqa: E402


class _NoopTelemetry:
    def record(self, *_args, **_kwargs) -> None:
        pass


def _run_file(prefix: str) -> Path:
    fixture_matches = sorted(FIXTURE_RUNS_DIR.glob(f"{prefix}*.jsonl"))
    if len(fixture_matches) == 1:
        return fixture_matches[0]
    if len(fixture_matches) > 1:
        raise FileNotFoundError(
            f"expected one committed replay fixture matching {prefix!r}; "
            f"found {len(fixture_matches)}"
        )
    matches = sorted((REPO_ROOT / ".auto-blueprint/telemetry/runs").glob(f"{prefix}*.jsonl"))
    if len(matches) != 1:
        raise FileNotFoundError(
            f"expected one telemetry run matching {prefix!r}; found {len(matches)}"
        )
    return matches[0]


def _committed_run_prefixes() -> list[str]:
    return [path.name[:15] for path in sorted(FIXTURE_RUNS_DIR.glob("*.jsonl"))]


def _events(path: Path) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for line_no, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        try:
            event = json.loads(line)
        except json.JSONDecodeError as exc:
            raise ValueError(f"{path}:{line_no}: invalid JSON: {exc}") from exc
        if isinstance(event, dict):
            events.append(event)
    return events


def _context(name: str) -> tuple[Ctx, list[str], list[str]]:
    blueprint_dir = REPO_ROOT / "blueprints" / name
    result = validate_blueprint(REPO_ROOT, name, blueprint_dir=blueprint_dir)
    if not result.ok:
        raise RuntimeError(f"published blueprint {name!r} does not validate")
    ctx = Ctx(
        name=name,
        blueprint_dir=blueprint_dir,
        runner_spec="replay",
        escalation_runner_spec="replay",
        base_effort=None,
        escalation_effort=None,
        base_timeout=0,
        hard_timeout=0,
        lean_command=[],
        telemetry=_NoopTelemetry(),
        paper_text="",
        library_context="",
        section_size=12,
        proof_batch=12,
        workers=1,
        use_ladder=False,
    )
    ctx.refresh_nodes(result.nodes)
    pending = {
        label for label, node in result.nodes.items() if not node.mathlibok
    }
    ordered = _design_plan_order(ctx, pending)
    frontier = _bottom_up_ready_frontier(ctx.nodes, pending, set())
    return ctx, ordered, frontier


def _replay_run(
    ctx: Ctx, ordered: list[str], frontier: list[str], run_prefix: str
) -> list[dict[str, Any]]:
    events = _events(_run_file(run_prefix))
    entries_by_candidate: dict[str, dict[str, dict[str, Any]]] = {}
    artifact_hashes: dict[str, list[str]] = {}
    recorded_scores: dict[str, list[int]] = {}
    selected_candidates: set[str] = set()
    for event in events:
        if event.get("event") == "phase1_design_plan_candidate_scored":
            candidate_id = str(event.get("candidate_id") or "?").upper()
            recorded_scores[candidate_id] = list(event.get("score") or [])
            if event.get("selected"):
                selected_candidates.add(candidate_id)
            continue
        purpose = str(event.get("purpose") or "")
        marker = "phase1_design_plan_candidate_"
        if event.get("event") != "model_call" or not purpose.startswith(marker):
            continue
        if event.get("status") != "success":
            continue
        candidate_id = purpose.removeprefix(marker).upper()
        response = event.get("response") or {}
        artifact_path = REPO_ROOT / str(response.get("path") or "")
        if not artifact_path.is_file():
            raise FileNotFoundError(f"missing telemetry artifact: {artifact_path}")
        requested = [
            label for label in event.get("labels") or [] if label in ctx.nodes
        ]
        parsed = _parse_design_plan_entries(
            ctx, requested, artifact_path.read_text(encoding="utf-8")
        )
        entries_by_candidate.setdefault(candidate_id, {}).update(parsed)
        artifact_hashes.setdefault(candidate_id, []).append(
            str(response.get("sha256") or "")
        )

    rows: list[dict[str, Any]] = []
    for candidate_id, entries in sorted(entries_by_candidate.items()):
        candidate = _evaluate_design_plan_candidate(
            ctx, ordered, entries, f"replay-{run_prefix}-{candidate_id}"
        )
        previous_entries = ctx.design_plan_entries
        ctx.design_plan_entries = entries
        try:
            issues = _design_plan_contract_closure_issues(ctx, ordered)
        finally:
            ctx.design_plan_entries = previous_entries
        blocked = set(candidate.blocked)
        eligible = [label for label in frontier if label not in blocked]
        rows.append(
            {
                "run": run_prefix,
                "candidate": candidate_id,
                "selected": candidate_id in selected_candidates,
                "recorded_score": recorded_scores.get(candidate_id),
                "replayed_score": list(candidate.score),
                "parsed_contracts": len(entries),
                "closure_findings": len(issues),
                "initial_frontier": frontier,
                "eligible_initial_frontier": eligible,
                "blocked_initial_frontier": [
                    label for label in frontier if label in blocked
                ],
                "response_sha256": artifact_hashes[candidate_id],
            }
        )
    return rows


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("blueprint")
    parser.add_argument(
        "--run",
        action="append",
        help="Run timestamp/prefix; repeat to compare runs. Default: all committed fixtures.",
    )
    parser.add_argument(
        "--require-progress",
        action="store_true",
        help="Fail if a replayed complete candidate blocks the whole initial frontier.",
    )
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    run_prefixes = args.run or _committed_run_prefixes()
    if not run_prefixes:
        parser.error("no --run was supplied and no committed replay fixtures exist")

    ctx, ordered, frontier = _context(args.blueprint)
    rows = [
        row
        for run_prefix in run_prefixes
        for row in _replay_run(ctx, ordered, frontier, run_prefix)
    ]
    if args.json:
        print(json.dumps(rows, indent=2, sort_keys=True))
    else:
        print(
            "run\tcandidate\tselected\trecorded\treplayed\tparsed\tfindings\t"
            "initial eligible/total"
        )
        for row in rows:
            print(
                f"{row['run']}\t{row['candidate']}\t"
                f"{row['selected']}\t"
                f"{row['recorded_score']}\t{row['replayed_score']}\t"
                f"{row['parsed_contracts']}\t{row['closure_findings']}\t"
                f"{len(row['eligible_initial_frontier'])}/"
                f"{len(row['initial_frontier'])}"
            )
            print(
                "  eligible: "
                + ", ".join(row["eligible_initial_frontier"])
            )
    if args.require_progress and any(
        row["selected"]
        and row["parsed_contracts"] == len(ordered)
        and not row["eligible_initial_frontier"]
        for row in rows
    ):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
