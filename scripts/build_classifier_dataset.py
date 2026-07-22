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
    formalize_configs: dict[str, dict[str, Any]] = {}
    run_ends: dict[str, dict[str, Any]] = {}
    skeleton_sections: list[dict[str, Any]] = []
    statement_audits: list[dict[str, Any]] = []
    tactic_ladder_results: list[dict[str, Any]] = []
    proof_attempt_results: list[dict[str, Any]] = []
    proof_section_results: list[dict[str, Any]] = []
    final_check_results: list[dict[str, Any]] = []

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
        elif etype == "formalize_config":
            formalize_configs[str(event.get("run_id"))] = event
        elif etype == "run_end":
            run_ends[str(event.get("run_id"))] = event
        elif etype == "skeleton_section_frozen":
            skeleton_sections.append(event)
        elif etype == "statement_audit":
            statement_audits.append(event)
        elif etype == "tactic_ladder_result":
            tactic_ladder_results.append(event)
        elif etype == "proof_attempt_result":
            proof_attempt_results.append(event)
        elif etype == "proof_section_result":
            proof_section_results.append(event)
        elif etype == "final_check_result":
            final_check_results.append(event)

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

    def labels_overlap(left: Any, right: Any) -> bool:
        left_set = set(left or [])
        right_set = set(right or [])
        return bool(left_set and right_set and left_set.intersection(right_set))

    def is_fast_run(row: dict[str, Any]) -> bool:
        return str(row.get("run_id")) in formalize_configs

    def related_model_stats(run_id: str, purpose: str, labels: Any) -> dict[str, Any]:
        related = [
            row
            for row in model_calls
            if row.get("run_id") == run_id
            and row.get("purpose") == purpose
            and labels_overlap(row.get("labels"), labels)
        ]
        durations = [float(row.get("duration_s") or 0) for row in related]
        statuses = [str(row.get("status") or "") for row in related]
        return {
            "model_call_count": len(related),
            "model_duration_total_s": sum(durations),
            "model_duration_max_s": max(durations) if durations else 0,
            "model_had_timeout": "timeout" in statuses or any("timeout" in status for status in statuses),
            "model_had_error": "error" in statuses,
            "prompt_chars_max": max(
                [int((row.get("prompt") or {}).get("chars") or 0) for row in related],
                default=0,
            ),
            "response_chars_max": max(
                [int((row.get("response") or {}).get("chars") or 0) for row in related],
                default=0,
            ),
        }

    fast_run_rows: list[dict[str, Any]] = []
    for run_id, config in formalize_configs.items():
        end = run_ends.get(run_id, {})
        fast_run_rows.append(
            {
                "run_id": run_id,
                "blueprint": config.get("blueprint"),
                "runner": config.get("runner"),
                "escalation_runner": config.get("escalation_runner"),
                "max_trials": config.get("max_trials"),
                "timeout_s": config.get("timeout_s"),
                "hard_timeout_s": config.get("hard_timeout_s"),
                "section_size": config.get("section_size"),
                "proof_batch": config.get("proof_batch"),
                "workers": config.get("workers"),
                "base_effort": config.get("base_effort"),
                "escalation_effort": config.get("escalation_effort"),
                "continue_run": config.get("continue_run"),
                "ladder": config.get("ladder"),
                "exit_code": end.get("exit_code"),
                "final_status": end.get("status"),
                "repairs": end.get("repairs"),
                "unresolved": end.get("unresolved"),
            }
        )

    skeleton_rows: list[dict[str, Any]] = []
    for row in skeleton_sections:
        if not is_fast_run(row):
            continue
        labels = row.get("labels") or []
        stats = related_model_stats(str(row.get("run_id")), "skeleton_generation", labels)
        skeleton_rows.append(
            {
                "run_id": row.get("run_id"),
                "blueprint": row.get("blueprint"),
                "section": row.get("section"),
                "labels": labels,
                "label_count": len(labels),
                "decls": row.get("decls"),
                "frozen": True,
                **stats,
            }
        )

    statement_rows: list[dict[str, Any]] = []
    for row in statement_audits:
        if not is_fast_run(row):
            continue
        labels = row.get("labels") or row.get("rejected_labels") or []
        stats = related_model_stats(str(row.get("run_id")), "statement_audit", labels)
        statement_rows.append(
            {
                "run_id": row.get("run_id"),
                "blueprint": row.get("blueprint"),
                "labels": labels,
                "label_count": len(labels),
                "source": row.get("source"),
                "accepted": row.get("accepted"),
                "classification": row.get("classification"),
                "rejected_labels": row.get("rejected_labels"),
                "reason": row.get("reason"),
                **stats,
            }
        )

    ladder_rows = [
        {
            "run_id": row.get("run_id"),
            "blueprint": row.get("blueprint"),
            "section": row.get("section"),
            "labels": row.get("labels"),
            "candidate_count": row.get("candidate_count"),
            "proved_labels": row.get("proved_labels"),
            "proved_count": row.get("proved_count"),
            "imports": row.get("imports"),
            "success": bool(row.get("proved_count")),
        }
        for row in tactic_ladder_results
        if is_fast_run(row)
    ]

    proof_attempt_rows = []
    for row in proof_attempt_results:
        if not is_fast_run(row):
            continue
        labels = row.get("labels") or []
        purpose = "proof_singleton" if row.get("phase") == "proof_singleton" else "proof_batch"
        stats = related_model_stats(str(row.get("run_id")), purpose, labels)
        proved = row.get("proved_labels") or []
        failed = row.get("failed_labels") or []
        decomposed = row.get("decomposition_labels") or []
        proof_attempt_rows.append(
            {
                "run_id": row.get("run_id"),
                "blueprint": row.get("blueprint"),
                "section": row.get("section"),
                "phase": row.get("phase"),
                "round": row.get("round"),
                "attempt": row.get("attempt"),
                "labels": labels,
                "label_count": len(labels),
                "status": row.get("status"),
                "proved_labels": proved,
                "proved_count": len(proved),
                "failed_labels": failed,
                "failed_count": len(failed),
                "decomposition_labels": decomposed,
                "decomposition_count": len(decomposed),
                "next_batch_size": row.get("next_batch_size"),
                "missing_helpers": row.get("missing_helpers"),
                "errors": row.get("errors"),
                "error": row.get("error"),
                **stats,
            }
        )

    proof_section_rows = [
        {
            "run_id": row.get("run_id"),
            "blueprint": row.get("blueprint"),
            "section": row.get("section"),
            "labels": row.get("labels"),
            "label_count": len(row.get("labels") or []),
            "proved_labels": row.get("proved_labels"),
            "proved_count": row.get("proved_count"),
            "failed_labels": row.get("failed_labels"),
            "failed_count": row.get("failed_count"),
            "decomposition_labels": row.get("decomposition_labels"),
            "decomposition_count": row.get("decomposition_count"),
            "section_fully_proved": not row.get("failed_count") and not row.get("decomposition_count"),
        }
        for row in proof_section_results
        if is_fast_run(row)
    ]

    final_rows = [
        {
            "run_id": row.get("run_id"),
            "blueprint": row.get("blueprint"),
            "lean_ok": row.get("lean_ok"),
            "coverage_ok": row.get("coverage_ok"),
            "coverage_issue_count": len(row.get("coverage_issues") or []),
            "coverage_issues": row.get("coverage_issues"),
            "output_tail": row.get("output_tail"),
        }
        for row in final_check_results
        if is_fast_run(row)
    ]

    return {
        "decision_examples": decision_rows,
        "model_call_examples": model_rows,
        "node_feature_examples": list(node_features.values()),
        "repair_examples": repairs,
        "pre_decomposition_examples": pre_rows,
        "fast_run_examples": fast_run_rows,
        "fast_skeleton_examples": skeleton_rows,
        "fast_statement_audit_examples": statement_rows,
        "fast_tactic_ladder_examples": ladder_rows,
        "fast_proof_attempt_examples": proof_attempt_rows,
        "fast_proof_section_examples": proof_section_rows,
        "fast_final_check_examples": final_rows,
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
