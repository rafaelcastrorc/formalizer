from __future__ import annotations

import io
import sys
import tempfile
import threading
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import formalize_blueprint  # noqa: E402


class FormalizationLoggingTests(unittest.TestCase):
    def test_active_stage_reports_concurrent_workers_without_stale_state(self) -> None:
        entered = [threading.Event(), threading.Event()]
        release = threading.Event()

        def run(stage: str, ready: threading.Event) -> None:
            with formalize_blueprint._stage(stage):
                ready.set()
                release.wait(timeout=2)

        threads = [
            threading.Thread(target=run, args=("model call A", entered[0])),
            threading.Thread(target=run, args=("model call B", entered[1])),
        ]
        for thread in threads:
            thread.start()
        try:
            self.assertTrue(all(event.wait(timeout=2) for event in entered))
            active = formalize_blueprint._active_stage()
            self.assertIn("model call A", active)
            self.assertIn("model call B", active)
        finally:
            release.set()
            for thread in threads:
                thread.join(timeout=2)

        self.assertEqual(formalize_blueprint._active_stage(), "idle")

    def test_unexpected_exception_is_written_to_persistent_log(self) -> None:
        scratch = REPO_ROOT / ".auto-blueprint"
        scratch.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(dir=scratch) as tmp:
            log_path = Path(tmp) / "run.log"
            stdout = io.StringIO()
            stderr = io.StringIO()

            with (
                patch.object(formalize_blueprint, "_run_log_path", return_value=log_path),
                patch.object(
                    formalize_blueprint,
                    "main",
                    side_effect=RuntimeError("transaction snapshot missing"),
                ),
                redirect_stdout(stdout),
                redirect_stderr(stderr),
            ):
                result = formalize_blueprint.logged_main(["simplex"])

            self.assertEqual(result, 1)
            persisted = log_path.read_text(encoding="utf-8")
            for output in (persisted, stderr.getvalue()):
                self.assertIn("Traceback (most recent call last)", output)
                self.assertIn("RuntimeError: transaction snapshot missing", output)


if __name__ == "__main__":
    unittest.main()
