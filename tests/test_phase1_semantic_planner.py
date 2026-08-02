from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE_PATH = (
    REPO_ROOT
    / "tests"
    / "fixtures"
    / "phase1_semantic_plan_replay"
    / "historical_cases.json"
)
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from formalize_blueprint import (  # noqa: E402
    SEMANTIC_PLAN_SCHEMA_VERSION,
    _candidate_exactly_realizes_plan,
    _findings_require_plan_revision,
    _ensure_phase1_semantic_plan,
    _ingest_model_lean,
    _parse_semantic_plan_entries,
    _phase1_frontier_plan_gateway,
    _semantic_plan_prompt,
    SkeletonFinding,
)
from model_runners import RunnerError, TransientRunnerError  # noqa: E402
from validate_blueprint import Node  # noqa: E402


class FakeTelemetry:
    def __init__(self) -> None:
        self.events: list[tuple[str, dict]] = []

    def record(self, event: str, **fields) -> None:
        self.events.append((event, fields))


def node(label: str, *, uses: set[str] | None = None) -> Node:
    return Node(
        label=label,
        kind="definition",
        file=Path("content.tex"),
        line=1,
        uses=set(uses or set()),
        statement_uses=set(uses or set()),
    )


def context(nodes: dict[str, Node]) -> SimpleNamespace:
    return SimpleNamespace(
        name="semantic-smoke",
        nodes=nodes,
        stmt_fps={label: f"fp:{label}" for label in nodes},
        stmt_blocks={label: f"Blueprint statement for {label}." for label in nodes},
        semantic_plan_entries={},
        design_plan_entries={},
        design_plan_alternates={},
        blueprint_direct_generation={},
        design_plan="",
        unavailable_imports=set(),
        library_context="",
        library_candidates=[],
        telemetry=FakeTelemetry(),
    )


class CompactSemanticPlannerTests(unittest.TestCase):
    def test_transient_planner_failure_uses_complete_blueprint_fallback(self) -> None:
        nodes = {
            "def:provider": node("def:provider"),
            "def:consumer": node("def:consumer", uses={"def:provider"}),
        }
        ctx = context(nodes)
        ctx.hard_timeout = 60
        ctx.base_effort = None
        with patch(
            "formalize_blueprint._call_model",
            side_effect=TransientRunnerError("network error after retries"),
        ):
            _ensure_phase1_semantic_plan(ctx, set(nodes))

        self.assertEqual(set(ctx.semantic_plan_entries), set(nodes))
        self.assertTrue(
            all(entry["fallback"] for entry in ctx.semantic_plan_entries.values())
        )
        self.assertEqual(
            ctx.semantic_plan_entries["def:consumer"]["provider_requirements"],
            [{"provider": "def:provider", "capabilities": []}],
        )
        result_events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_semantic_plan_result"
        ]
        self.assertEqual(result_events[0]["status"], "transport_exhausted")
        self.assertEqual(result_events[0]["fallback_count"], len(nodes))

    def test_environment_planner_failure_is_not_hidden(self) -> None:
        nodes = {"def:widget": node("def:widget")}
        ctx = context(nodes)
        ctx.hard_timeout = 60
        ctx.base_effort = None
        with patch(
            "formalize_blueprint._call_model",
            side_effect=RunnerError("codex CLI not found on PATH"),
        ):
            with self.assertRaisesRegex(RunnerError, "not found on PATH"):
                _ensure_phase1_semantic_plan(ctx, set(nodes))

    def test_committed_historical_boundary_cases(self) -> None:
        fixture = json.loads(FIXTURE_PATH.read_text(encoding="utf-8"))
        self.assertEqual(fixture["schema_version"], 1)
        self.assertEqual(len(fixture["cases"]), 2)

        for case in fixture["cases"]:
            nodes = {
                label: node(
                    label,
                    uses=set(spec.get("statement_uses") or []),
                )
                for label, spec in case["nodes"].items()
            }
            ctx = context(nodes)
            with self.subTest(case=case["name"]):
                if case["kind"] == "semantic_sanitization":
                    parsed, findings = _parse_semantic_plan_entries(
                        ctx,
                        case["requested"],
                        json.dumps(case["response"]),
                    )
                    label = case["requested"][0]
                    self.assertEqual(
                        parsed[label]["provider_requirements"],
                        case["expected_provider_requirements"],
                    )
                    self.assertTrue(
                        any(
                            case["expected_finding"] in finding
                            for finding in findings[label]
                        )
                    )
                    continue

                label = case["requested"][0]
                ctx.semantic_plan_entries[label] = {
                    "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
                    "statement_fp": ctx.stmt_fps[label],
                    **case["semantic_entry"],
                }
                canonical = _ingest_model_lean(
                    ctx,
                    case["requested"],
                    case["lean_response"],
                    realize_contracts=True,
                )
                entry = ctx.design_plan_entries[label]
                self.assertIn(
                    case["expected_target_fragment"], entry["target_signature"]
                )
                self.assertIn(
                    case["expected_helper_fragment"],
                    entry["helpers"][0]["declaration"],
                )
                code = "\n\n".join(decl.text for decl in canonical.parsed.decls)
                self.assertTrue(_candidate_exactly_realizes_plan(ctx, label, code))

    def test_parser_sanitizes_unauthorized_edges_without_blocking_entry(self) -> None:
        nodes = {
            "def:provider": node("def:provider"),
            "def:other": node("def:other"),
            "def:consumer": node("def:consumer", uses={"def:provider"}),
        }
        ctx = context(nodes)
        response = json.dumps(
            {
                "contracts": [
                    {
                        "label": "def:consumer",
                        "representation": "A consumer built from the provider.",
                        "vocabulary": [
                            {"name": "ConsumerSurface", "purpose": "public data"}
                        ],
                        "obligations": ["preserve the blueprint equation"],
                        "provider_requirements": [
                            {
                                "provider": "def:provider",
                                "capabilities": ["provider value"],
                            },
                            {
                                "provider": "def:other",
                                "capabilities": ["invented edge"],
                            },
                        ],
                    }
                ]
            }
        )

        parsed, findings = _parse_semantic_plan_entries(
            ctx, ["def:consumer"], response
        )

        self.assertEqual(parsed["def:consumer"]["schema_version"], 1)
        self.assertEqual(
            parsed["def:consumer"]["provider_requirements"],
            [{"provider": "def:provider", "capabilities": ["provider value"]}],
        )
        self.assertIn("unauthorized provider", findings["def:consumer"][0])

    def test_prompt_is_semantic_and_contains_lossless_graph_authority(self) -> None:
        nodes = {
            "def:provider": node("def:provider"),
            "def:consumer": node("def:consumer", uses={"def:provider"}),
        }
        ctx = context(nodes)

        prompt = _semantic_plan_prompt(
            ctx, ["def:consumer", "def:provider"], timeout_s=600
        )

        self.assertIn("COMPACT-BLUEPRINT-SEMANTIC-PLAN", prompt)
        self.assertIn('"statement":["def:provider"]', prompt)
        self.assertIn("Do NOT write Lean signatures", prompt)
        self.assertNotIn('"target_signature"', prompt)
        self.assertNotIn('"members"', prompt)

    def test_phase1_candidate_atomically_becomes_its_typed_contract(self) -> None:
        nodes = {"def:widget": node("def:widget")}
        ctx = context(nodes)
        ctx.semantic_plan_entries = {
            "def:widget": {
                "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
                "statement_fp": "fp:def:widget",
                "representation": "A type carrying a natural value.",
                "vocabulary": [
                    {"name": "WidgetSurface", "purpose": "typed public surface"}
                ],
                "obligations": ["expose the natural value"],
                "provider_requirements": [],
            }
        }
        response = """```lean
structure WidgetSurface where
  value : Nat

def def_widget : Type := WidgetSurface
```"""

        canonical = _ingest_model_lean(
            ctx, ["def:widget"], response, realize_contracts=True
        )
        code = "\n\n".join(decl.text for decl in canonical.parsed.decls)
        entry = ctx.design_plan_entries["def:widget"]

        self.assertEqual(entry["origin"], "phase1_candidate")
        self.assertIn("def def_widget", entry["target_signature"])
        self.assertEqual(len(entry["helpers"]), 1)
        self.assertIn("value : Nat", entry["helpers"][0]["declaration"])
        self.assertTrue(_candidate_exactly_realizes_plan(ctx, "def:widget", code))

    def test_candidate_owned_closure_finding_routes_to_code_not_plan_repair(self) -> None:
        nodes = {"def:widget": node("def:widget")}
        ctx = context(nodes)
        ctx.design_plan_entries = {
            "def:widget": {
                "origin": "phase1_candidate",
                "schema_version": 6,
                "statement_fp": "fp:def:widget",
                "target_signature": "def def_widget : Type",
                "helpers": [],
                "decisions": [],
            }
        }
        finding = SkeletonFinding(
            "candidate-owned declaration cycle",
            label="def:widget",
            category="plan_contract_closure",
        )

        self.assertFalse(_findings_require_plan_revision(ctx, [finding]))

    def test_candidate_owned_contract_skips_legacy_pre_generation_gateway(self) -> None:
        nodes = {"def:widget": node("def:widget")}
        ctx = context(nodes)
        ctx.design_plan_entries = {
            "def:widget": {
                "origin": "phase1_candidate",
                "schema_version": 6,
                "statement_fp": "fp:def:widget",
                "target_signature": "def def_widget : Type",
                "helpers": [],
                "decisions": [],
            }
        }

        unchanged = _phase1_frontier_plan_gateway(
            ctx,
            ["def:widget"],
            ["def:widget"],
            {"def:widget": ["historical finding that must not trigger repair"]},
        )

        self.assertEqual(
            unchanged,
            {"def:widget": ["historical finding that must not trigger repair"]},
        )
        self.assertFalse(ctx.telemetry.events)


if __name__ == "__main__":
    unittest.main()
