#!/usr/bin/env python3
"""Install/check the Lean toolchain declared by this repository.

Python dependencies live in ``requirements.txt``. Lean is not a Python package,
so its equivalent project-level requirement is:

* ``lean-toolchain``: pins the Lean compiler/Lake version through elan;
* ``lakefile.lean``: declares Mathlib and any other Lean dependencies.

This script makes that explicit. In CI it should run after checkout. Locally,
run it once before using ``scripts/refine_blueprint_with_lean.py``. Without
``--install-elan`` it only verifies the toolchain and explains what is missing;
with ``--install-elan`` it bootstraps elan first, then downloads Mathlib cache.
"""
from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

from lean_preflight import check_lean_environment

REPO_ROOT = Path(__file__).resolve().parent.parent


def run(cmd: list[str], *, env: dict[str, str] | None = None) -> None:
    print(f"$ {' '.join(cmd)}", flush=True)
    subprocess.run(cmd, cwd=str(REPO_ROOT), env=env, check=True)


def _path_with_elan_bin() -> dict[str, str]:
    env = os.environ.copy()
    elan_bin = Path.home() / ".elan" / "bin"
    env["PATH"] = f"{elan_bin}{os.pathsep}{env.get('PATH', '')}"
    return env


def install_elan() -> None:
    curl = shutil.which("curl")
    if not curl:
        raise RuntimeError("curl is required to install elan automatically")
    run(
        [
            "sh",
            "-c",
            "curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y",
        ]
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--install-elan",
        action="store_true",
        help="Install elan automatically if it is missing.",
    )
    parser.add_argument(
        "--no-cache",
        action="store_true",
        help="Skip `lake exe cache get`; useful for very small local smoke checks.",
    )
    args = parser.parse_args(argv)

    if not (REPO_ROOT / "lean-toolchain").is_file():
        raise SystemExit("lean-toolchain is missing; Lean is not pinned for this repo")
    if not (REPO_ROOT / "lakefile.lean").is_file():
        raise SystemExit("lakefile.lean is missing; Mathlib dependencies are not declared")

    env = _path_with_elan_bin()
    if not shutil.which("elan", path=env["PATH"]):
        if not args.install_elan:
            raise SystemExit(
                "elan is not installed. Run:\n"
                "  uv run python scripts/setup_lean.py --install-elan"
            )
        install_elan()
        env = _path_with_elan_bin()

    if not shutil.which("lake", path=env["PATH"]):
        raise SystemExit("lake is still not on PATH after elan setup")

    run(["lake", "--version"], env=env)
    run(["lake", "update"], env=env)
    if not args.no_cache:
        run(["lake", "exe", "cache", "get"], env=env)

    result = check_lean_environment(REPO_ROOT)
    if not result.ok:
        print(result.stderr or result.stdout, file=sys.stderr)
        raise SystemExit(f"Lean setup finished, but preflight failed: {result.message}")

    print(f"Lean toolchain and Mathlib dependencies are ready ({result.elapsed_s:.1f}s preflight).")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (RuntimeError, subprocess.CalledProcessError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(1)
