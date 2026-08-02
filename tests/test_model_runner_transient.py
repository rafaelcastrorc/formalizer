from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from model_runners.base import (  # noqa: E402
    ModelRunner,
    RunnerError,
    RunResult,
    TransientRunnerError,
    is_transient_error,
)
from formalize_blueprint import _call_model, _runner_failure_status  # noqa: E402


class FakeArtifact:
    def to_event(self, root):
        return {"path": "fixture.txt"}


class FakeTelemetry:
    def __init__(self):
        self.events: list[tuple[str, dict]] = []

    def store_text(self, kind, text, ext="txt"):
        return FakeArtifact()

    def record(self, event, **fields):
        self.events.append((event, fields))


class SequenceRunner(ModelRunner):
    backend_name = "sequence"

    def __init__(self, outcomes: list[RunResult | Exception]):
        super().__init__(timeout=10)
        self.outcomes = list(outcomes)
        self.calls = 0

    def _run_impl(self, prompt, system, cwd):
        outcome = self.outcomes[self.calls]
        self.calls += 1
        if isinstance(outcome, Exception):
            raise outcome
        return outcome


class ModelRunnerTransientTests(unittest.TestCase):
    def test_july31_websocket_failure_is_transient(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests/fixtures/phase1_orchestration_replay/transport_outage.json"
            ).read_text(encoding="utf-8")
        )["cases"][0]

        self.assertTrue(is_transient_error(RunnerError(fixture["error"])))
        self.assertEqual(
            _runner_failure_status(RunnerError(fixture["error"])),
            fixture["expected_classification"],
        )
        self.assertEqual(fixture["expected_repair_budget_delta"], 0)
        self.assertEqual(len(fixture["incorrectly_consumed_repair_trials"]), 7)

    def test_transport_classification_is_backend_neutral(self) -> None:
        errors = [
            "claude CLI exit 1: connection reset by peer",
            "network error: temporary DNS connection failure",
            "HTTP 503: service unavailable",
            "HTTP 429: rate limit exceeded",
        ]

        for error in errors:
            with self.subTest(error=error):
                exc = RunnerError(error)
                self.assertTrue(is_transient_error(exc))
                self.assertEqual(_runner_failure_status(exc), "transport_exhausted")

    def test_transient_failures_retry_inside_runner_and_recover(self) -> None:
        runner = SequenceRunner(
            [
                RunnerError("ERROR: Reconnecting... responses_websocket failed"),
                RunnerError("network error: connection reset"),
                RunResult(text="recovered"),
            ]
        )

        with patch("model_runners.base.time.sleep") as sleep:
            result = runner.run("prompt", retries=0)

        self.assertEqual(result.text, "recovered")
        self.assertEqual(runner.calls, 3)
        self.assertEqual([call.args[0] for call in sleep.call_args_list], [30, 60])

    def test_exhausted_transport_stays_distinct_from_model_output_failure(self) -> None:
        error = RunnerError("codex responses_websocket: Reconnecting... 4/5")
        runner = SequenceRunner([error, error, error, error])

        with patch("model_runners.base.time.sleep"), self.assertRaises(
            TransientRunnerError
        ) as raised:
            runner.run("prompt", retries=0)

        self.assertEqual(runner.calls, 4)
        self.assertIn("transport failed after 4 attempts", str(raised.exception))

    def test_non_transport_generation_error_is_not_reclassified(self) -> None:
        runner = SequenceRunner([RunnerError("model returned malformed JSON")])

        with patch("model_runners.base.time.sleep"), self.assertRaises(
            RunnerError
        ) as raised:
            runner.run("prompt", retries=0)

        self.assertNotIsInstance(raised.exception, TransientRunnerError)
        self.assertEqual(runner.calls, 1)

    def test_formalization_boundary_never_returns_transport_as_generation_error(self) -> None:
        error = RunnerError("codex responses_websocket: Reconnecting... 4/5")
        runner = SequenceRunner([error, error, error, error])
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            telemetry=telemetry,
            runner_spec="codex:test",
            escalation_runner_spec="codex:test",
        )

        with patch("model_runners.base.time.sleep"), patch(
            "formalize_blueprint._make_runner", return_value=runner
        ), self.assertRaises(TransientRunnerError):
            _call_model(
                ctx,
                "prompt",
                purpose="skeleton_declaration_patch",
                timeout=300,
                effort=None,
                labels=["lem:test"],
            )

        model_events = [fields for event, fields in telemetry.events if event == "model_call"]
        self.assertEqual(model_events[-1]["status"], "transport_exhausted")
        self.assertTrue(model_events[-1]["transport_error"])
        self.assertFalse(any(event == "phase1_generation_retry" for event, _ in telemetry.events))


if __name__ == "__main__":
    unittest.main()
