"""Shared Lean/Lake readiness checks for CLI scripts and the local web UI.

The refinement loop should not discover a broken Lean environment by asking a
model to poke around in ``.lake``. This module performs the deterministic check
first: the repo must declare Lean, ``lake`` must be runnable, and a tiny Mathlib
import must compile through ``lake env lean``.
"""
from __future__ import annotations

import os
import shutil
import subprocess
import time
from dataclasses import asdict, dataclass
from pathlib import Path


@dataclass
class LeanPreflightResult:
    ok: bool
    message: str
    command: list[str]
    elapsed_s: float = 0.0
    stdout: str = ""
    stderr: str = ""

    def to_dict(self) -> dict:
        return asdict(self)


def path_with_elan_bin() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}{os.pathsep}{env.get('PATH', '')}"
    return env


def default_lean_command(repo_root: Path) -> list[str]:
    if not (repo_root / "lean-toolchain").is_file() or not (repo_root / "lakefile.lean").is_file():
        raise FileNotFoundError(
            "Lean is not declared for this repo. Expected lean-toolchain and lakefile.lean."
        )
    return ["lake", "env", "lean"]


def check_lean_environment(
    repo_root: Path,
    *,
    lean_command: list[str] | None = None,
    timeout: int = 90,
) -> LeanPreflightResult:
    command = lean_command or default_lean_command(repo_root)
    env = path_with_elan_bin()

    if not (repo_root / "lean-toolchain").is_file():
        return LeanPreflightResult(False, "lean-toolchain is missing", command)
    if not (repo_root / "lakefile.lean").is_file():
        return LeanPreflightResult(False, "lakefile.lean is missing", command)
    if shutil.which(command[0], path=env["PATH"]) is None:
        return LeanPreflightResult(
            False,
            f"`{command[0]}` is not on PATH. Run `uv run python scripts/setup_lean.py --install-elan`.",
            command,
        )

    scratch = repo_root / ".auto-blueprint" / "preflight"
    scratch.mkdir(parents=True, exist_ok=True)
    probe = scratch / "LeanPreflight.lean"
    probe.write_text("import Mathlib.Data.Nat.Basic\n\n#check Nat\n#check True\n", encoding="utf-8")

    started = time.time()
    try:
        proc = subprocess.run(
            command + [str(probe)],
            cwd=str(repo_root),
            env=env,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        elapsed = time.time() - started
        return LeanPreflightResult(
            False,
            f"Lean preflight timed out after {timeout}s",
            command + [str(probe)],
            elapsed_s=elapsed,
            stdout=exc.stdout or "",
            stderr=exc.stderr or "",
        )

    elapsed = time.time() - started
    if proc.returncode != 0:
        stderr = proc.stderr or ""
        stdout = proc.stdout or ""
        hint = "Lean preflight failed"
        combined = stderr + stdout
        if (
            "unknown package" in combined
            or "unknown module prefix" in combined
            or "No such file" in combined
            or "object file" in combined
            or ".olean" in combined
        ):
            hint += "; run `uv run python scripts/setup_lean.py --install-elan`"
        return LeanPreflightResult(
            False,
            hint,
            command + [str(probe)],
            elapsed_s=elapsed,
            stdout=stdout,
            stderr=stderr,
        )

    return LeanPreflightResult(
        True,
        "Lean/Lake/Mathlib preflight passed",
        command + [str(probe)],
        elapsed_s=elapsed,
        stdout=proc.stdout or "",
        stderr=proc.stderr or "",
    )
