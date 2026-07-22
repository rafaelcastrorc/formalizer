#!/usr/bin/env python3
"""Build simple JSONL datasets from Auto-Blueprint telemetry.

This script does not train classifiers. It converts append-only run telemetry
into flat examples that are easier to inspect or feed into a later training
pipeline. Labels are derived from observed outcomes, not guessed at collection
time.
"""
from __future__ import annotations

import argparse
import json
from collections import defaultdict
from pathlib import Path
from typing import Any

REPO_ROOT = Path(__file__).resolve().parent.parent
TELEMETRY_ROOT = REPO_ROOT / ".auto-blueprint" / "telemetry"


def _read_events(root: Path) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for path in sorted((root / "runs").glob("*.jsonl")):
        with path.open(encoding="utf-8") as fh:
            for line in fh:
                line = line.strip()
                if not line:
                    continue
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                event["_source_file"] = str(path)
                events.append(event)
    return events


def _write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row, ensure_ascii=False) + "\n")


def build_datasets(events: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    decisions: dict[str, dict[str, Any]] = {}
    decision_outcomes: dict[str, list[dict[str, Any]]] = defaultdict(list)
    model_calls: list[dict[str, Any]] = []
    node_features: dict[tuple[str, str, str], dict[str, Any]] = {}
    repairs: list[dict[str, Any]] = []
    pre_candidates: dict[str, list[dict[str, Any]]] = defaultdict(list)
    pre_results: dict[str, dict[str, Any]] = {}

    for event in events:
        etype = event.get("event")
        if etype == "decision_point":
            decisions[str(event.get("decision_id"))] = event
        elif etype == "decision_outcome":
            decision_outcomes[str(event.get("decision_id"))].append(event)
        elif etype == "model_call":
            model_calls.append(event)
        elif etype == "node_features":
            key = (
                str(event.get("run_id")),
                str(event.get("label")),
                str(event.get("text_sha256")),
            )
            node_features[key] = event
        elif etype in {"blueprint_repair_result", "blueprint_repair_applied", "blueprint_repair_noop"}:
            repairs.append(event)
        elif etype == "pre_decomposition_candidate":
            pre_candidates[str(event.get("decision_id"))].append(event)
        elif etype == "pre_decomposition_result":
            pre_results[str(event.get("decision_id"))] = event

    decision_rows: list[dict[str, Any]] = []
    for decision_id, decision in decisions.items():
        outcomes = decision_outcomes.get(decision_id, [])
        model_for_decision = [m for m in model_calls if m.get("decision_id") == decision_id]
        statuses = [str(m.get("status")) for m in model_for_decision]
        durations = [float(m.get("duration_s") or 0) for m in model_for_decision]
        decision_rows.append(
            {
                "run_id": decision.get("run_id"),
                "blueprint": decision.get("blueprint"),
                "decision_id": decision_id,
                "kind": decision.get("kind"),
                "target_labels": decision.get("target_labels"),
                "chosen_action": decision.get("chosen_action"),
                "scheduler_difficulty": decision.get("scheduler_difficulty"),
                "model_timeout_s": decision.get("model_timeout_s"),
                "model_call_count": len(model_for_decision),
                "model_duration_total_s": sum(durations),
                "model_duration_max_s": max(durations) if durations else 0,
                "had_model_error": "error" in statuses,
                "observed_outcomes": [o.get("outcome") for o in outcomes],
                "accepted": any(o.get("outcome") == "accepted" for o in outcomes),
                "needs_decomposition_observed": any(
                    o.get("outcome") == "needs_decomposition" for o in outcomes
                ),
                "generation_retries_exhausted": any(
                    o.get("outcome") == "generation_retries_exhausted" for o in outcomes
                ),
            }
        )

    model_rows = [
        {
            "run_id": row.get("run_id"),
            "blueprint": row.get("blueprint"),
            "decision_id": row.get("decision_id"),
            "purpose": row.get("purpose"),
            "chunk_number": row.get("chunk_number"),
            "attempt": row.get("attempt"),
            "labels": row.get("labels"),
            "backend": row.get("backend"),
            "model": row.get("model"),
            "readonly": row.get("readonly"),
            "timeout_s": row.get("timeout_s"),
            "duration_s": row.get("duration_s"),
            "status": row.get("status"),
            "environment_error": row.get("environment_error", False),
            "prompt_chars": (row.get("prompt") or {}).get("chars"),
            "response_chars": (row.get("response") or {}).get("chars"),
        }
        for row in model_calls
    ]

    pre_rows: list[dict[str, Any]] = []
    for decision_id, candidates in pre_candidates.items():
        result = pre_results.get(decision_id, {})
        changed_labels = set(result.get("changed_labels") or [])
        for candidate in candidates:
            label = str(candidate.get("label") or "")
            pre_rows.append(
                {
                    "run_id": candidate.get("run_id"),
                    "blueprint": candidate.get("blueprint"),
                    "decision_id": decision_id,
                    "label": label,
                    "reasons": candidate.get("reasons"),
                    "text_sha256": candidate.get("text_sha256"),
                    "kind": candidate.get("kind"),
                    "text_chars": candidate.get("text_chars"),
                    "proof_chars": candidate.get("proof_chars"),
                    "uses_count": candidate.get("uses_count"),
                    "display_math_count": candidate.get("display_math_count"),
                    "equation_like_count": candidate.get("equation_like_count"),
                    "sum_token_count": candidate.get("sum_token_count"),
                    "product_token_count": candidate.get("product_token_count"),
                    "reindex_token_count": candidate.get("reindex_token_count"),
                    "induction_token_count": candidate.get("induction_token_count"),
                    "node_count_before": result.get("node_count_before"),
                    "node_count_after": result.get("node_count_after"),
                    "prepass_changed_anything": bool(result.get("changed_count")),
                    "candidate_changed": label in changed_labels,
                    "changed_labels": result.get("changed_labels"),
                }
            )

    return {
        "decision_examples": decision_rows,
        "model_call_examples": model_rows,
        "node_feature_examples": list(node_features.values()),
        "repair_examples": repairs,
        "pre_decomposition_examples": pre_rows,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--telemetry-root", type=Path, default=TELEMETRY_ROOT)
    parser.add_argument("--out-dir", type=Path, default=TELEMETRY_ROOT / "datasets")
    args = parser.parse_args()

    events = _read_events(args.telemetry_root)
    datasets = build_datasets(events)
    for name, rows in datasets.items():
        out = args.out_dir / f"{name}.jsonl"
        _write_jsonl(out, rows)
        print(f"{name}: {len(rows)} row(s) -> {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
