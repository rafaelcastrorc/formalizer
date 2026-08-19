from __future__ import annotations

import hashlib
import json
import sys
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from replay_phase1_plans import (  # noqa: E402
    FIXTURE_RUNS_DIR,
    _replay_run,
)


class PhaseOneHistoricalReplayTests(unittest.TestCase):
    """Keep historical planner regressions reproducible without local telemetry."""

    def test_committed_plans_retain_initial_frontier_progress(self) -> None:
        run_files = sorted(FIXTURE_RUNS_DIR.glob("*.jsonl"))
        self.assertEqual(len(run_files), 10)
        for run_file in run_files:
            prefix = run_file.name[:15]
            with self.subTest(run=prefix):
                rows = _replay_run("simplex", prefix)
                selected = [row for row in rows if row["selected"]]
                self.assertEqual(len(selected), 1)
                self.assertEqual(
                    selected[0]["parsed_contracts"],
                    selected[0]["target_contracts"],
                )
                self.assertTrue(selected[0]["eligible_initial_frontier"])

    def test_committed_response_hashes_match_telemetry_metadata(self) -> None:
        for run_file in sorted(FIXTURE_RUNS_DIR.glob("*.jsonl")):
            for line in run_file.read_text(encoding="utf-8").splitlines():
                event = json.loads(line)
                response = event.get("response")
                if not response:
                    continue
                artifact = REPO_ROOT / response["path"]
                with self.subTest(run=run_file.name, artifact=artifact.name):
                    self.assertTrue(artifact.is_file())
                    self.assertEqual(
                        hashlib.sha256(artifact.read_bytes()).hexdigest(),
                        response["sha256"],
                    )


if __name__ == "__main__":
    unittest.main()
