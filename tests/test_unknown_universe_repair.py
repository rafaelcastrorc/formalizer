from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE = (
    REPO_ROOT
    / "tests"
    / "fixtures"
    / "phase1_orchestration_replay"
    / "unknown_universe_retry.json"
)
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from refine_blueprint_with_lean import _repair_unknown_universe_levels  # noqa: E402


class UnknownUniverseRepairTests(unittest.TestCase):
    def repair(self, source: str, diagnostics: str) -> tuple[tuple[str, ...], str]:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(source, encoding="utf-8")
            diagnostics = diagnostics.replace("{path}", str(path))
            repaired = _repair_unknown_universe_levels(path, diagnostics)
            return repaired, path.read_text(encoding="utf-8")

    def test_declares_exact_levels_reported_by_lean(self) -> None:
        repaired, source = self.repair(
            "import Mathlib\n\nset_option autoImplicit false\nstructure Box where\n  A : Type u\n  B : Type v\n",
            "{path}:5:12: error: unknown universe level `u`\n"
            "{path}:6:12: error: unknown universe level `v`\n"
            "{path}:7:12: error: unknown universe level `u`",
        )

        self.assertEqual(repaired, ("u", "v"))
        self.assertIn("import Mathlib\nuniverse u v\n", source)
        self.assertEqual(source.count("universe u v"), 1)

    def test_is_idempotent_and_ignores_other_files(self) -> None:
        repaired, source = self.repair(
            "import Mathlib\nuniverse u\n\nstructure Box where\n  A : Type u\n",
            "/tmp/Other.lean:4:12: error: unknown universe level `v`\n"
            "{path}:4:12: error: unknown universe level `u`",
        )

        self.assertEqual(repaired, ())
        self.assertEqual(source.count("universe u"), 1)
        self.assertNotIn("universe v", source)

    def test_unrelated_lean_error_does_not_modify_source(self) -> None:
        original = "set_option autoImplicit false\n#check MissingName\n"
        repaired, source = self.repair(
            original,
            "{path}:2:7: error: unknown identifier 'MissingName'",
        )

        self.assertEqual(repaired, ())
        self.assertEqual(source, original)

    def test_historical_uue_diagnostic_routes_to_zero_model_retry(self) -> None:
        case = json.loads(FIXTURE.read_text(encoding="utf-8"))
        repaired, source = self.repair(case["generated_source"], case["lean_output"])

        self.assertEqual(list(repaired), case["expected_declared_levels"])
        self.assertIn(case["expected_inserted_declaration"], source)
        self.assertEqual(case["expected_model_calls"], 0)
        self.assertEqual(case["expected_repair_trials_consumed"], 0)


if __name__ == "__main__":
    unittest.main()
