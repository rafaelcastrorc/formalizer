from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))
sys.path.insert(0, str(REPO_ROOT / "tests" / "replay"))

from replay_phase2_latency import (  # noqa: E402
    DEFAULT_FIXTURE,
    assert_improvement,
    replay_fixture,
)
from formalize_blueprint import PHASE2_COMPLETE_CORRECTION_TIMEOUT  # noqa: E402


class PhaseTwoLatencyReplayTests(unittest.TestCase):
    """Compare old and current orchestration with a deterministic clock."""

    def setUp(self) -> None:
        self.payload = json.loads(DEFAULT_FIXTURE.read_text(encoding="utf-8"))

    def test_retained_candidate_policy_reduces_historical_regeneration(self) -> None:
        report = replay_fixture(self.payload)
        configured_timeout = self.payload["deterministic_latency_benchmark"][
            "timeout_limits_s"
        ]["retained_candidate_correction"]

        assert_improvement(report)
        self.assertEqual(configured_timeout, PHASE2_COMPLETE_CORRECTION_TIMEOUT)
        self.assertEqual(report["legacy"]["full_generation_calls"], 7)
        self.assertEqual(report["retained"]["full_generation_calls"], 1)
        self.assertEqual(report["retained"]["correction_calls"], 1)
        self.assertGreater(report["improvement"]["simulated_speedup"], 2.5)
        self.assertEqual(
            report["improvement"]["per_correction_timeout_exposure_saved_s"],
            300.0,
        )

    def test_acceptance_requires_every_complete_node_gate(self) -> None:
        broken = json.loads(json.dumps(self.payload))
        accepted = broken["deterministic_latency_benchmark"][
            "retained_candidate_counterfactual"
        ][-1]
        accepted["gates"].remove("statement_alignment")

        with self.assertRaisesRegex(ValueError, "statement_alignment"):
            replay_fixture(broken)

    def test_replay_is_deterministic(self) -> None:
        first = replay_fixture(self.payload)
        second = replay_fixture(self.payload)
        self.assertEqual(first, second)


if __name__ == "__main__":
    unittest.main()
