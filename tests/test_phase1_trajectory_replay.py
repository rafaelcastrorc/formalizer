from __future__ import annotations

import json
import sys
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from formalize_blueprint import (  # noqa: E402
    CallResult,
    DESIGN_PLAN_SCHEMA_VERSION,
    Section,
    _extract_json,
    _frozen_labels,
    _parse_design_plan_entries,
    _run_phase1,
    _sync_design_plan,
    _validate_design_plan_contract_closure,
)
from validate_blueprint import Node  # noqa: E402


FIXTURE = (
    REPO_ROOT
    / "tests"
    / "fixtures"
    / "phase1_orchestration_replay"
    / "frontier_gateway_trajectories.json"
)
PLAN_RESPONSES = (
    REPO_ROOT / "tests" / "fixtures" / "phase1_plan_replay" / "responses"
)


class FakeTelemetry:
    def __init__(self) -> None:
        self.events: list[tuple[str, dict]] = []

    def record(self, event: str, **fields) -> None:
        self.events.append((event, fields))


def _node(raw: dict) -> Node:
    return Node(
        label=raw["label"],
        kind="definition" if raw["label"].startswith("def:") else "lemma",
        file=Path("content.tex"),
        line=1,
        uses=set(raw.get("uses") or []),
        statement_uses=set(raw.get("uses") or []),
        mathlibok=bool(raw.get("mathlibok")),
    )


class HistoricalModelReplay:
    """Return committed historical outcomes at the real model-call boundary."""

    def __init__(self, sequence: list[dict], trace: list[tuple[str, list[str]]]):
        self.sequence = list(sequence)
        self.trace = trace

    def __call__(self, _ctx, _prompt, *, purpose, labels, **_kwargs):
        if not self.sequence:
            raise AssertionError(f"unexpected model call {purpose} for {labels}")
        expected = self.sequence.pop(0)
        actual_labels = list(labels)
        if purpose != expected["purpose"] or actual_labels != expected["labels"]:
            raise AssertionError(
                "historical model sequence diverged: expected "
                f"{expected['purpose']} {expected['labels']}, got "
                f"{purpose} {actual_labels}"
            )
        self.trace.append((purpose, actual_labels))
        return CallResult(
            status="ok",
            text=json.dumps(expected["response"], separators=(",", ":")),
            duration_s=float(expected.get("duration_s") or 0.0),
        )


class PhaseOneTrajectoryReplayTests(unittest.TestCase):
    """Drive the production Phase 1 coordinator across historical frontiers."""

    def _run_case(self, case: dict) -> tuple[list[list[str]], list[str], list[tuple[str, list[str]]]]:
        nodes = {raw["label"]: _node(raw) for raw in case["nodes"]}
        pending = set(case["pending"])
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            name=f"replay-{case['blueprint']}",
            nodes=nodes,
            stmt_fps={label: f"{case['run_id']}:{label}" for label in nodes},
            tex_blocks={label: f"Historical blueprint node {label}." for label in nodes},
            design_plan_entries={},
            design_plan_alternates={},
            design_plan="",
            statement_audit_cache=set(),
            retry_lifecycle={},
            generation_candidates={},
            generation_feedback={},
            unavailable_imports=set(),
            library_candidates=[],
            paper_text="",
            base_timeout=300,
            hard_timeout=600,
            base_effort="medium",
            escalation_effort="high",
            effective_section_size=12,
            section_size=12,
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            workers=3,
            telemetry=telemetry,
        )
        model_trace: list[tuple[str, list[str]]] = []
        model = HistoricalModelReplay(case["model_sequence"], model_trace)
        frontiers: list[list[str]] = []

        def seed_plan(_ctx, _pending, _sections=None, **_kwargs):
            if case.get("plan_response_sha256"):
                response = (
                    PLAN_RESPONSES
                    / f"{case['plan_response_sha256']}.txt"
                ).read_text(encoding="utf-8")
            else:
                response = json.dumps({"contracts": case["initial_contracts"]})
            parsed = _parse_design_plan_entries(ctx, pending, response)
            self.assertEqual(set(parsed), pending)
            ctx.design_plan_entries = parsed
            _sync_design_plan(ctx)
            if case.get("use_real_closure"):
                return _validate_design_plan_contract_closure(ctx, pending)
            return {}

        def freeze_frontier(_ctx, _layer, groups, _sections, alloc):
            labels = [label for group in groups for label in group]
            frontiers.append(labels)
            number = alloc()
            return [
                Section(
                    number=number,
                    labels=labels,
                    path=Path(f"HistoricalSkeleton{number:02d}.lean"),
                    module=f"Historical.Skeleton{number:02d}",
                    import_modules=[],
                    refined_labels=set(labels),
                )
            ]

        with ExitStack() as stack:
            stack.enter_context(
                patch(
                    "formalize_blueprint._ensure_phase1_semantic_plan",
                    side_effect=seed_plan,
                )
            )
            stack.enter_context(
                patch("formalize_blueprint._call_model", side_effect=model)
            )
            stack.enter_context(
                patch(
                    "formalize_blueprint._design_plan_dependency_findings",
                    return_value=[],
                )
            )
            if not case.get("use_real_closure"):
                stack.enter_context(
                    patch(
                        "formalize_blueprint._validate_design_plan_contract_closure",
                        return_value={},
                    )
                )
            stack.enter_context(
                patch(
                    "formalize_blueprint._run_validated_contract_phase1_layer",
                    side_effect=freeze_frontier,
                )
            )
            stack.enter_context(patch("formalize_blueprint._save_ctx_state"))
            sections = _run_phase1(ctx, [], pending, "bottom-up")

        self.assertFalse(model.sequence, "not every historical model outcome was consumed")
        corrections = [
            labels[0]
            for purpose, labels in model_trace
            if purpose == "phase1_design_plan_correction"
        ]
        return frontiers, sorted(_frozen_labels(sections)), corrections

    def test_committed_trajectories_cross_multiple_frontiers(self) -> None:
        payload = json.loads(FIXTURE.read_text(encoding="utf-8"))
        self.assertEqual(payload["schema_version"], 1)
        self.assertGreaterEqual(len(payload["cases"]), 2)

        for case in payload["cases"]:
            with self.subTest(run=case["run_id"], blueprint=case["blueprint"]):
                frontiers, frozen, corrections = self._run_case(case)
                self.assertEqual(frontiers, case["expected_frontiers"])
                self.assertEqual(frozen, sorted(case["expected_frozen"]))
                self.assertEqual(corrections, case["expected_corrections"])

    def test_bad_historical_plan_is_corrected_before_statement_generation(self) -> None:
        payload = json.loads(FIXTURE.read_text(encoding="utf-8"))
        case = next(
            item for item in payload["cases"] if item["run_id"] == "20260731-233344"
        )
        frontiers, _frozen, corrections = self._run_case(case)

        self.assertGreater(case["historical_serialized_delay_s"], 1000)
        self.assertEqual(
            corrections,
            ["def:security-parameter-negligible", "def:key-space"],
        )
        self.assertEqual(
            frontiers[0], ["def:security-parameter-negligible"]
        )

    def test_future_consumer_defect_does_not_block_historical_ready_leaf(self) -> None:
        payload = json.loads(FIXTURE.read_text(encoding="utf-8"))
        case = next(
            item
            for item in payload["cases"]
            if item["run_id"] == "20260801-014205"
        )
        frontiers, frozen, corrections = self._run_case(case)

        self.assertEqual(case["historical_stall_before_first_gateway_s"], 913)
        self.assertEqual(frontiers[0], ["def:security-parameter-negligible"])
        self.assertEqual(corrections, ["def:one-time-private-key-ue"])
        self.assertEqual(frozen, sorted(case["expected_frozen"]))


if __name__ == "__main__":
    unittest.main()
