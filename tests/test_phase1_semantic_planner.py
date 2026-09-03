from __future__ import annotations

import json
import sys
import threading
import time
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
INVALID_TEX_ESCAPE_FIXTURE = (
    REPO_ROOT
    / "tests"
    / "fixtures"
    / "phase1_semantic_plan_replay"
    / "invalid_tex_escape.txt"
)
PARTIAL_COVERAGE_FIXTURE = (
    REPO_ROOT
    / "tests"
    / "fixtures"
    / "phase1_semantic_plan_replay"
    / "partial_nonempty_20260827.json"
)
READINESS_FIXTURE = (
    REPO_ROOT
    / "tests"
    / "fixtures"
    / "phase1_semantic_plan_replay"
    / "readiness_cases.json"
)
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from formalize_blueprint import (  # noqa: E402
    CallResult,
    RepairRequest,
    SEMANTIC_PLAN_SCHEMA_VERSION,
    _candidate_exactly_realizes_plan,
    _findings_require_plan_revision,
    _ensure_phase1_semantic_plan,
    _ingest_model_lean,
    _parse_semantic_plan_entries,
    _phase1_advisory_readiness_request,
    _phase1_source_readiness_request,
    _readiness_repair_postcondition_findings,
    _run_phase1,
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
        paper_text="",
        telemetry=FakeTelemetry(),
    )


class CompactSemanticPlannerTests(unittest.TestCase):
    def test_source_readiness_gate_precedes_semantic_planning(self) -> None:
        label = "lem:unfinished"
        pending = Node(
            label=label,
            kind="lemma",
            file=Path("content.tex"),
            line=1,
            notready=True,
        )
        ctx = context({label: pending})
        ctx.tex_blocks = {
            label: "\\begin{lemma}Claim\\label{lem:unfinished}\\notready\\end{lemma}"
        }

        with patch("formalize_blueprint._ensure_phase1_semantic_plan") as planner:
            with self.assertRaises(RepairRequest) as raised:
                _run_phase1(ctx, [], {label}, "bottom-up")

        planner.assert_not_called()
        self.assertEqual(raised.exception.labels, [label])
        self.assertTrue(raised.exception.authorizes_blueprint_repair)

    def test_readiness_fixture_routes_authoritative_and_advisory_cases(self) -> None:
        fixture = json.loads(READINESS_FIXTURE.read_text(encoding="utf-8"))
        nodes = {
            case["label"]: Node(
                label=case["label"],
                kind=case["kind"],
                file=Path("content.tex"),
                line=1,
                notready=case.get("notready", False),
                open_claim=case.get("open_claim", False),
            )
            for case in fixture["source_cases"]
        }
        ctx = context(nodes)
        ctx.conjecture_policy = "record"
        ctx.tex_blocks = {
            case["label"]: case["tex"] for case in fixture["source_cases"]
        }

        request = _phase1_source_readiness_request(ctx, set(nodes))

        self.assertIsInstance(request, RepairRequest)
        self.assertEqual(set(request.labels), set(fixture["expected_repair_labels_record"]))
        self.assertNotIn(fixture["recorded_open_label"], request.labels)

        ctx.conjecture_policy = "attempt"
        request = _phase1_source_readiness_request(ctx, set(nodes))
        self.assertIsInstance(request, RepairRequest)
        self.assertEqual(set(request.labels), set(fixture["expected_repair_labels_attempt"]))

    def test_notready_theorem_repair_must_add_proof_before_marker_is_removed(self) -> None:
        label = "lem:pending"
        before = Node(
            label=label,
            kind="lemma",
            file=Path("content.tex"),
            line=1,
            notready=True,
        )
        after = Node(
            label=label,
            kind="lemma",
            file=Path("content.tex"),
            line=1,
            notready=False,
        )
        findings = _readiness_repair_postcondition_findings(
            before_nodes={label: before},
            after_nodes={label: after},
            before_blocks={label: "\\begin{lemma}Claim\\notready\\end{lemma}"},
            after_blocks={label: "\\begin{lemma}Claim\\end{lemma}"},
            labels=[label],
            conjecture_policy="record",
        )
        self.assertEqual(
            findings,
            [f"{label}: readiness repair did not add a blueprint proof"],
        )

        findings = _readiness_repair_postcondition_findings(
            before_nodes={label: before},
            after_nodes={label: after},
            before_blocks={label: "\\begin{lemma}Claim\\notready\\end{lemma}"},
            after_blocks={
                label: (
                    "\\begin{lemma}Claim\\end{lemma}"
                    "\\begin{proof}A complete argument.\\end{proof}"
                )
            },
            labels=[label],
            conjecture_policy="record",
        )
        self.assertEqual(findings, [])

    def test_planner_readiness_is_sanitized_and_defaults_to_ready(self) -> None:
        labels = ["def:flagged", "def:legacy"]
        ctx = context({label: node(label) for label in labels})
        response = json.dumps(
            {
                "contracts": [
                    {
                        "label": "def:flagged",
                        "representation": "concrete object",
                        "vocabulary": [],
                        "obligations": [],
                        "provider_requirements": [],
                        "readiness": "underspecified",
                        "gap": "the carrier type is not identified",
                    },
                    {
                        "label": "def:legacy",
                        "representation": "older response",
                        "vocabulary": [],
                        "obligations": [],
                        "provider_requirements": [],
                    },
                ]
            }
        )

        parsed, _findings = _parse_semantic_plan_entries(ctx, labels, response)

        self.assertEqual(parsed["def:flagged"]["readiness"], "underspecified")
        self.assertEqual(parsed["def:flagged"]["readiness_confirmation"], "pending")
        self.assertEqual(parsed["def:legacy"]["readiness"], "ready")
        self.assertEqual(parsed["def:legacy"]["readiness_confirmation"], "not_needed")

    def test_advisory_false_positive_is_confirmed_once_then_phase1_proceeds(self) -> None:
        label = "def:flagged"
        ctx = context({label: node(label)})
        ctx.base_timeout = 30
        ctx.base_effort = None
        ctx.semantic_plan_entries[label] = {
            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
            "statement_fp": ctx.stmt_fps[label],
            "readiness": "underspecified",
            "gap": "possibly missing a carrier",
            "readiness_confirmation": "pending",
        }
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "nodes": [
                        {"label": label, "readiness": "ready", "gap": ""}
                    ]
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response) as call:
            self.assertIsNone(_phase1_advisory_readiness_request(ctx, {label}))
            self.assertIsNone(_phase1_advisory_readiness_request(ctx, {label}))

        self.assertEqual(call.call_count, 1)
        self.assertEqual(
            ctx.semantic_plan_entries[label]["readiness_confirmation"],
            "confirmed_ready",
        )

    def test_only_independently_confirmed_advisory_authorizes_repair(self) -> None:
        label = "def:flagged"
        ctx = context({label: node(label)})
        ctx.base_timeout = 30
        ctx.base_effort = None
        ctx.semantic_plan_entries[label] = {
            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
            "statement_fp": ctx.stmt_fps[label],
            "readiness": "underspecified",
            "gap": "possibly missing a carrier",
            "readiness_confirmation": "pending",
        }
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "nodes": [
                        {
                            "label": label,
                            "readiness": "underspecified",
                            "gap": "the quantified carrier is absent",
                        }
                    ]
                }
            ),
        )

        with patch("formalize_blueprint._call_model", return_value=response):
            request = _phase1_advisory_readiness_request(ctx, {label})

        self.assertIsInstance(request, RepairRequest)
        self.assertTrue(request.authorizes_blueprint_repair)
        self.assertEqual(request.labels, [label])
        self.assertIn("quantified carrier", request.evidence_by_label[label])

    def test_parser_recovers_outer_plan_with_unescaped_tex_commands(self) -> None:
        label = "def:local-basis-unitary"
        ctx = context({label: node(label)})
        response = INVALID_TEX_ESCAPE_FIXTURE.read_text(encoding="utf-8")

        parsed, findings = _parse_semantic_plan_entries(ctx, [label], response)

        self.assertEqual(set(parsed), {label})
        self.assertIn(r"\dagger", parsed[label]["representation"])
        self.assertTrue(
            any(
                "malformed JSON string backslash" in finding
                for finding in findings["<response>"]
            )
        )

    def test_parser_never_substitutes_nested_object_for_malformed_outer_plan(self) -> None:
        label = "def:widget"
        ctx = context({label: node(label)})
        truncated = (
            '{"contracts":[{"label":"def:widget","representation":"broken '
            r'\dagger","vocabulary":[],"obligations":[],"provider_requirements":[]}'
        )

        parsed, findings = _parse_semantic_plan_entries(ctx, [label], truncated)

        self.assertEqual(parsed, {})
        self.assertIn("top-level contracts array", findings["<response>"][0])

    def test_parser_preserves_tex_command_that_looks_like_json_control_escape(self) -> None:
        label = "def:parameter"
        ctx = context({label: node(label)})
        response = (
            '{"contracts":[{"label":"def:parameter","representation":"the '
            r'\beta parameter","vocabulary":[],"obligations":[],'
            '"provider_requirements":[]}]}'
        )

        parsed, findings = _parse_semantic_plan_entries(ctx, [label], response)

        self.assertEqual(parsed[label]["representation"], r"the \beta parameter")
        self.assertIn("malformed JSON string backslash", findings["<response>"][0])

    def test_transient_planner_failure_uses_complete_blueprint_fallback(self) -> None:
        nodes = {
            "def:provider": node("def:provider"),
            "def:consumer": node("def:consumer", uses={"def:provider"}),
        }
        ctx = context(nodes)
        ctx.hard_timeout = 60
        ctx.base_effort = None
        ctx.runner_spec = "codex"
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

    def test_silent_planner_timeout_gets_one_fresh_recovery_call(self) -> None:
        label = "def:widget"
        ctx = context({label: node(label)})
        ctx.hard_timeout = 60
        ctx.base_effort = None
        ctx.runner_spec = "codex"
        response = json.dumps(
            {
                "contracts": [
                    {
                        "label": label,
                        "representation": "a concrete widget",
                        "vocabulary": [],
                        "obligations": [],
                        "provider_requirements": [],
                    }
                ]
            }
        )
        with patch(
            "formalize_blueprint._call_model",
            side_effect=[
                CallResult(status="timeout", duration_s=60),
                CallResult(status="ok", text=response, duration_s=4),
            ],
        ) as call_model:
            _ensure_phase1_semantic_plan(ctx, {label})

        self.assertEqual(call_model.call_count, 2)
        self.assertFalse(call_model.call_args_list[0].kwargs["force_fresh"])
        self.assertTrue(call_model.call_args_list[1].kwargs["force_fresh"])
        self.assertNotIn("fallback", ctx.semantic_plan_entries[label])
        retries = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_semantic_plan_hedge_started"
        ]
        self.assertEqual(len(retries), 1)

    def test_nonempty_partial_plan_is_merged_with_one_fresh_recovery(self) -> None:
        fixture = json.loads(PARTIAL_COVERAGE_FIXTURE.read_text(encoding="utf-8"))
        primary_label = fixture["primary_label"]
        requested_count = fixture["requested_count"]
        labels = [primary_label] + [
            f"def:historical-missing-{index:03d}"
            for index in range(1, requested_count)
        ]
        nodes = {label: node(label) for label in labels}
        nodes[primary_label] = node(
            primary_label,
            uses=set(fixture["primary_statement_uses"]),
        )
        ctx = context(nodes)
        ctx.hard_timeout = 60
        ctx.base_effort = None
        ctx.runner_spec = "codex"
        recovery = {
            "contracts": [
                {
                    "label": label,
                    "representation": f"Recovered interface for {label}.",
                    "vocabulary": [],
                    "obligations": [],
                    "provider_requirements": [],
                }
                for label in labels[1:]
            ]
        }

        with patch(
            "formalize_blueprint._call_model",
            side_effect=[
                CallResult(
                    status="ok",
                    text=json.dumps(fixture["primary_response"]),
                    duration_s=fixture["primary_duration_s"],
                ),
                CallResult(status="ok", text=json.dumps(recovery), duration_s=4),
            ],
        ) as call_model:
            _ensure_phase1_semantic_plan(ctx, set(labels))

        self.assertEqual(call_model.call_count, 2)
        self.assertFalse(call_model.call_args_list[0].kwargs["force_fresh"])
        self.assertTrue(call_model.call_args_list[1].kwargs["force_fresh"])
        self.assertEqual(set(ctx.semantic_plan_entries), set(labels))
        self.assertTrue(
            all("fallback" not in entry for entry in ctx.semantic_plan_entries.values())
        )
        result = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_semantic_plan_result"
        ][0]
        self.assertEqual(result["planned_count"], requested_count)
        self.assertEqual(result["fallback_count"], 0)

    def test_two_partial_plans_fall_back_only_for_uncovered_nodes(self) -> None:
        labels = ["def:first", "def:second", "def:third"]
        ctx = context({label: node(label) for label in labels})
        ctx.hard_timeout = 60
        ctx.base_effort = None
        ctx.runner_spec = "codex"

        def response(label: str) -> str:
            return json.dumps(
                {
                    "contracts": [
                        {
                            "label": label,
                            "representation": f"Interface for {label}.",
                            "vocabulary": [],
                            "obligations": [],
                            "provider_requirements": [],
                        }
                    ]
                }
            )

        with patch(
            "formalize_blueprint._call_model",
            side_effect=[
                CallResult(status="ok", text=response(labels[0]), duration_s=1),
                CallResult(status="ok", text=response(labels[1]), duration_s=1),
            ],
        ) as call_model:
            _ensure_phase1_semantic_plan(ctx, set(labels))

        self.assertEqual(call_model.call_count, 2)
        self.assertNotIn("fallback", ctx.semantic_plan_entries[labels[0]])
        self.assertNotIn("fallback", ctx.semantic_plan_entries[labels[1]])
        self.assertTrue(ctx.semantic_plan_entries[labels[2]]["fallback"])
        result = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_semantic_plan_result"
        ][0]
        self.assertEqual(result["planned_count"], 2)
        self.assertEqual(result["fallback_count"], 1)

    def test_slow_primary_is_not_killed_when_hedge_starts(self) -> None:
        label = "def:widget"
        ctx = context({label: node(label)})
        ctx.hard_timeout = 0.05
        ctx.base_effort = None
        ctx.runner_spec = "codex"
        ctx.escalation_runner_spec = "codex:planner-escalation"
        ctx.escalation_effort = "high"
        ctx.planner_tier = "escalation"
        response = json.dumps(
            {
                "contracts": [
                    {
                        "label": label,
                        "representation": "a concrete widget",
                        "vocabulary": [],
                        "obligations": [],
                        "provider_requirements": [],
                    }
                ]
            }
        )
        primary_started = threading.Event()
        hedge_started = threading.Event()
        primary_cancelled = threading.Event()

        def fake_call(*_args, **kwargs):
            self.assertTrue(kwargs["escalated"])
            self.assertEqual(kwargs["effort"], "high")
            control = kwargs["control"]
            if kwargs["force_fresh"]:
                hedge_started.set()
                return CallResult(status="ok", text=response, duration_s=0.01)
            primary_started.set()
            self.assertTrue(hedge_started.wait(1))
            while not control._cancelled:
                time.sleep(0.005)
            primary_cancelled.set()
            return CallResult(status="error", error="cancelled")

        with patch("formalize_blueprint._call_model", side_effect=fake_call) as call_model:
            _ensure_phase1_semantic_plan(ctx, {label})

        self.assertTrue(primary_started.is_set())
        self.assertTrue(hedge_started.is_set())
        self.assertTrue(primary_cancelled.wait(1))
        self.assertEqual(call_model.call_count, 2)
        self.assertNotIn("fallback", ctx.semantic_plan_entries[label])
        events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_semantic_plan_hedge_result"
        ]
        self.assertEqual(events[0]["winner"], "hedge")

    def test_primary_completion_before_threshold_does_not_start_hedge(self) -> None:
        label = "def:widget"
        ctx = context({label: node(label)})
        ctx.hard_timeout = 1
        ctx.base_effort = None
        ctx.runner_spec = "codex"
        response = json.dumps(
            {
                "contracts": [
                    {
                        "label": label,
                        "representation": "a concrete widget",
                        "vocabulary": [],
                        "obligations": [],
                        "provider_requirements": [],
                    }
                ]
            }
        )
        with patch(
            "formalize_blueprint._call_model",
            return_value=CallResult(status="ok", text=response, duration_s=0.01),
        ) as call_model:
            _ensure_phase1_semantic_plan(ctx, {label})

        self.assertEqual(call_model.call_count, 1)

    def test_planner_uses_selected_model_tier(self) -> None:
        label = "def:widget"
        response = json.dumps(
            {
                "contracts": [
                    {
                        "label": label,
                        "representation": "a concrete widget",
                        "vocabulary": [],
                        "obligations": [],
                        "provider_requirements": [],
                    }
                ]
            }
        )
        for tier, escalated, effort in (
            ("base", False, "medium"),
            ("escalation", True, "high"),
        ):
            with self.subTest(tier=tier):
                ctx = context({label: node(label)})
                ctx.hard_timeout = 60
                ctx.runner_spec = "codex:base-model"
                ctx.escalation_runner_spec = "codex:escalation-model"
                ctx.base_effort = "medium"
                ctx.escalation_effort = "high"
                ctx.planner_tier = tier
                with patch(
                    "formalize_blueprint._call_model",
                    return_value=CallResult(
                        status="ok", text=response, duration_s=0.01
                    ),
                ) as call_model:
                    _ensure_phase1_semantic_plan(ctx, {label})

                self.assertEqual(call_model.call_count, 1)
                self.assertEqual(
                    call_model.call_args.kwargs["escalated"], escalated
                )
                self.assertEqual(call_model.call_args.kwargs["effort"], effort)
                result = [
                    fields
                    for event, fields in ctx.telemetry.events
                    if event == "phase1_semantic_plan_result"
                ][0]
                self.assertEqual(result["planner_tier"], tier)
                self.assertEqual(
                    result["runner"],
                    "codex:escalation-model" if escalated else "codex:base-model",
                )

    def test_planner_defaults_to_escalation_tier(self) -> None:
        label = "def:widget"
        response = json.dumps(
            {
                "contracts": [
                    {
                        "label": label,
                        "representation": "a concrete widget",
                        "vocabulary": [],
                        "obligations": [],
                        "provider_requirements": [],
                    }
                ]
            }
        )
        ctx = context({label: node(label)})
        ctx.hard_timeout = 60
        ctx.runner_spec = "codex:base-model"
        ctx.escalation_runner_spec = "codex:escalation-model"
        ctx.base_effort = "medium"
        ctx.escalation_effort = "high"

        with patch(
            "formalize_blueprint._call_model",
            return_value=CallResult(status="ok", text=response, duration_s=0.01),
        ) as call_model:
            _ensure_phase1_semantic_plan(ctx, {label})

        self.assertTrue(call_model.call_args.kwargs["escalated"])
        self.assertEqual(call_model.call_args.kwargs["effort"], "high")
        result = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_semantic_plan_result"
        ][0]
        self.assertEqual(result["planner_tier"], "escalation")
        self.assertEqual(result["runner"], "codex:escalation-model")

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

        self.assertEqual(
            parsed["def:consumer"]["schema_version"],
            SEMANTIC_PLAN_SCHEMA_VERSION,
        )
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
