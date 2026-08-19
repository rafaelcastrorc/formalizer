from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DIR = REPO_ROOT / "tests" / "fixtures" / "phase1_scheduler_replay"
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from replay_phase1_scheduler_latency import replay_fixture  # noqa: E402


class PhaseOneSchedulerLatencyReplayTests(unittest.TestCase):
    """Check the proposed scheduler against portable historical timings."""

    def _fixtures(self) -> list[dict]:
        return [
            json.loads(path.read_text(encoding="utf-8"))
            for path in sorted(FIXTURE_DIR.glob("*.json"))
        ]

    def test_replay_preserves_recorded_calls_and_durations(self) -> None:
        for fixture in self._fixtures():
            with self.subTest(run=fixture["source_run"]):
                result = replay_fixture(fixture, eligibility="eligible")
                expected = fixture["recorded_totals"]
                self.assertEqual(result.model_calls, expected["model_calls"])
                self.assertEqual(result.object_builds, expected["object_builds"])
                self.assertAlmostEqual(
                    result.model_seconds, expected["model_seconds"], places=2
                )
                self.assertAlmostEqual(
                    result.object_seconds, expected["object_seconds"], places=2
                )

    def test_branch_local_schedule_does_not_halve_either_run(self) -> None:
        for fixture in self._fixtures():
            with self.subTest(run=fixture["source_run"]):
                result = replay_fixture(fixture, eligibility="eligible")
                self.assertLess(result.simulated_speedup, 2.0)

    def test_even_optimistic_bound_cannot_halve_every_historical_run(self) -> None:
        results = [
            replay_fixture(
                fixture, eligibility="unbounded", drop_objects=True
            )
            for fixture in self._fixtures()
        ]
        self.assertTrue(
            any(result.simulated_speedup < 2.0 for result in results),
            "proposal unexpectedly met the 2x requirement on every fixture",
        )

    def test_replay_is_deterministic(self) -> None:
        fixture = self._fixtures()[0]
        first = replay_fixture(fixture, eligibility="eligible")
        second = replay_fixture(fixture, eligibility="eligible")
        self.assertEqual(first, second)


if __name__ == "__main__":
    unittest.main()
