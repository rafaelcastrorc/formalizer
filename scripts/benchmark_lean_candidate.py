#!/usr/bin/env python3
"""Measure where a generated Lean candidate spends compilation time.

This diagnostic does not modify generated modules or Lake artifacts. It copies
one single-declaration module into a temporary directory, derives imports-only
and statement-with-``sorry`` controls, and measures plain Lean checking versus
``.olean`` generation. The controls distinguish import cost, statement/type
elaboration, proof-body elaboration, and object-generation cost.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import signal
import subprocess
import tempfile
import time
from pathlib import Path

from formalize_blueprint import _compose_module, _normalize_terminal_sorry, _parse_module
from lean_preflight import default_lean_command
from refine_blueprint_with_lean import REPO_ROOT, _lean_env


def _run(command: list[str], *, timeout: int) -> dict[str, object]:
    started = time.monotonic()
    proc = subprocess.Popen(
        command,
        cwd=REPO_ROOT,
        env=_lean_env(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
        return {
            "status": "passed" if proc.returncode == 0 else "failed",
            "returncode": proc.returncode,
            "seconds": round(time.monotonic() - started, 3),
            "output": (stdout + stderr)[-2000:],
        }
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = proc.communicate()
        return {
            "status": "timeout",
            "returncode": None,
            "seconds": round(time.monotonic() - started, 3),
            "output": (stdout + stderr)[-2000:],
        }


def _variant_sources(source: Path, destination: Path) -> dict[str, Path]:
    parsed = _parse_module(source.read_text(encoding="utf-8"))
    if len(parsed.decls) != 1:
        raise ValueError(
            f"{source} must contain exactly one declaration; found {len(parsed.decls)}"
        )

    imports_only, _ = _compose_module(parsed.imports, parsed.preamble, [])
    sorry_decl = _normalize_terminal_sorry(parsed.decls[0].text)
    statement_only, _ = _compose_module(
        parsed.imports, parsed.preamble, [sorry_decl]
    )

    variants = {
        "imports_only": imports_only,
        "statement_sorry": statement_only,
        "real_proof": source.read_text(encoding="utf-8"),
    }
    paths: dict[str, Path] = {}
    for name, text in variants.items():
        path = destination / f"{name}.lean"
        path.write_text(text, encoding="utf-8")
        paths[name] = path
    return paths


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument(
        "--mode",
        choices=("plain", "olean", "both"),
        default="both",
    )
    parser.add_argument(
        "--variant",
        action="append",
        choices=("imports_only", "statement_sorry", "real_proof"),
        help="Measure only this variant (repeatable; default: all variants).",
    )
    args = parser.parse_args()
    source = args.source.resolve()
    lean = default_lean_command(REPO_ROOT)

    benchmark_root = REPO_ROOT / ".auto-blueprint" / "benchmarks"
    benchmark_root.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix="lean-candidate-", dir=benchmark_root
    ) as raw:
        directory = Path(raw)
        variants = _variant_sources(source, directory)
        results: dict[str, dict[str, object]] = {}
        selected = set(args.variant or variants)
        for name, path in variants.items():
            if name not in selected:
                continue
            results[name] = {}
            if args.mode in {"plain", "both"}:
                results[name]["plain"] = _run(
                    lean + [str(path)], timeout=args.timeout
                )
            if args.mode in {"olean", "both"}:
                output = directory / f"{name}.olean"
                results[name]["olean"] = _run(
                    lean + ["-o", str(output), str(path)], timeout=args.timeout
                )

    print(
        json.dumps(
            {
                "source": str(source),
                "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                "timeout_seconds": args.timeout,
                "results": results,
            },
            indent=2,
            sort_keys=True,
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
