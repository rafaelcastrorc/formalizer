"""Regression tests for optional Lean-library build readiness.

These tests cover the distinction that caused CSLib source declarations to be
offered to refinement even though no importable `.olean` files existed: a
matching checkout is installed, but it is not ready until a build/import stamp
for the active revision and toolchain exists.
"""
from __future__ import annotations

import argparse
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = REPO_ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from env_setup import lean_libs  # noqa: E402
import refine_blueprint_with_lean as legacy  # noqa: E402
import webui  # noqa: E402


class LeanLibraryReadinessTests(unittest.TestCase):
    def _fake_cslib(self, root: Path) -> tuple[Path, dict]:
        package = root / ".lake" / "packages" / "cslib"
        source = package / "Cslib" / "Init.lean"
        source.parent.mkdir(parents=True)
        source.write_text("def cslibSmoke : True := True.intro\n", encoding="utf-8")
        (package / "lakefile.toml").write_text(
            'name = "cslib"\n\n[[lean_lib]]\nname = "Cslib"\n',
            encoding="utf-8",
        )
        state = {"toolchain": "leanprover/lean4:v4.0.0", "checkouts": {"cslib": "abc123"}}
        return package, state

    def test_checkout_without_compiled_artifact_is_not_ready(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            _package, state = self._fake_cslib(root)
            with patch.object(lean_libs, "REPO_ROOT", root), patch.object(
                lean_libs, "BUILD_STATUS_DIR", root / ".auto-blueprint" / "library-build-status"
            ):
                status = lean_libs.library_build_status("cslib", state)
        self.assertFalse(status["ready"])
        self.assertIn("build or import verification", status["reason"])

    def test_matching_artifact_and_import_stamp_are_ready(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            package, state = self._fake_cslib(root)
            artifact = package / ".lake" / "build" / "lib" / "lean" / "Cslib" / "Init.olean"
            artifact.parent.mkdir(parents=True)
            artifact.write_bytes(b"olean")
            status_dir = root / ".auto-blueprint" / "library-build-status"
            status_dir.mkdir(parents=True)
            (status_dir / "cslib.json").write_text(
                json.dumps(
                    {
                        "revision": "abc123",
                        "toolchain": "leanprover/lean4:v4.0.0",
                        "module": "Cslib.Init",
                    }
                ),
                encoding="utf-8",
            )
            with patch.object(lean_libs, "REPO_ROOT", root), patch.object(
                lean_libs, "BUILD_STATUS_DIR", status_dir
            ):
                status = lean_libs.library_build_status("cslib", state)
        self.assertTrue(status["ready"])
        self.assertEqual(status["module"], "Cslib.Init")

    def test_apply_repairs_build_when_pins_are_already_current(self) -> None:
        args = argparse.Namespace(
            libs="mathlib,cslib", narrow=False, no_build=False, yes=True
        )
        resolution = lean_libs.Resolution(
            toolchain="leanprover/lean4:v4.0.0",
            pins={"mathlib": "math", "cslib": "cs"},
            feasible=True,
        )
        state = {
            "toolchain": resolution.toolchain,
            "checkouts": {"mathlib": "math", "cslib": "cs"},
        }
        with patch.object(lean_libs, "selected_libraries", return_value=["mathlib", "cslib"]), patch.object(
            lean_libs, "resolve", return_value=(resolution, {})
        ), patch.object(lean_libs, "current_state", return_value=state), patch.object(
            lean_libs, "library_build_status", side_effect=lambda name, _cur: {"ready": name == "mathlib"}
        ), patch.object(lean_libs, "save_cache"), patch.object(
            lean_libs, "apply", return_value=True
        ) as apply:
            code = lean_libs.cmd_apply(args)
        self.assertEqual(code, 0)
        apply.assert_called_once_with(resolution, run_build=True, adopt=False)

    def test_unready_optional_library_is_not_searched(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            for package, source_dir in (("mathlib", "Mathlib"), ("cslib", "Cslib")):
                source = root / ".lake" / "packages" / package / source_dir / "Init.lean"
                source.parent.mkdir(parents=True)
                source.write_text("\n", encoding="utf-8")
            with patch.object(legacy, "REPO_ROOT", root), patch.object(
                lean_libs,
                "selected_build_status",
                return_value={"mathlib": {"ready": True}, "cslib": {"ready": False}},
            ):
                roots = legacy._library_roots(["cslib", "mathlib"])
        self.assertEqual([name for name, _path in roots], ["Mathlib"])

    def test_web_status_requests_repair_for_matching_unbuilt_checkout(self) -> None:
        resolution = lean_libs.Resolution(
            toolchain="leanprover/lean4:v4.0.0",
            pins={"mathlib": "math", "cslib": "cs"},
            feasible=True,
        ).to_dict() | {"libs": ["mathlib", "cslib"]}
        state = {
            "toolchain": resolution["toolchain"],
            "checkouts": {"mathlib": "math", "cslib": "cs"},
        }
        readiness = {
            "mathlib": {"ready": True, "reason": "", "module": "Mathlib.Init"},
            "cslib": {
                "ready": False,
                "reason": "build or import verification is required",
                "module": "Cslib.Init",
            },
        }
        with patch.object(lean_libs, "selected_libraries", return_value=["mathlib", "cslib"]), patch.object(
            lean_libs, "load_cache", return_value=resolution
        ), patch.object(lean_libs, "current_state", return_value=state), patch.object(
            lean_libs, "selected_build_status", return_value=readiness
        ):
            payload = webui.library_update_brief(False)
        self.assertTrue(payload["needs_build"])
        self.assertTrue(payload["needs_update"])
        cslib = next(row for row in payload["rows"] if row["name"] == "cslib")
        self.assertFalse(cslib["needs_update"])
        self.assertFalse(cslib["build_ready"])


if __name__ == "__main__":
    unittest.main()
