#!/usr/bin/env python3
"""Refine a blueprint by using Lean as the critic.

This is the author/critic loop:

1. validate the current blueprint;
2. ask a model to generate a disposable Lean file from the blueprint only;
3. run Lean through this repo's Lake project;
4. if Lean fails, ask the model to fix the blueprint, not the Lean file;
5. repeat until Lean passes or ``--max-trials`` is exhausted.

Lean code is not the source of truth here. The generated files under
``.auto-blueprint/formalization/`` are test artifacts and are overwritten across
trials. A failed proof should cause better blueprint statements, hypotheses,
dependencies, or intermediate lemmas.
"""
from __future__ import annotations

import argparse
import re
import shlex
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from generate_blueprint import _extract_json, read_paper
from model_runners import RunnerError, get_runner
from validate_blueprint import Node, print_result, validate_blueprint

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
SKILL_PATH = REPO_ROOT / ".claude" / "skills" / "paper-to-blueprint" / "SKILL.md"
SCRATCH_DIR = REPO_ROOT / ".auto-blueprint" / "formalization"
PUBLISHED_LEAN_NAME = "formalization.lean"
FORBIDDEN_LEAN_PLACEHOLDERS = re.compile(r"\b(sorry|admit)\b|by\s*\?")


@dataclass
class LeanAttempt:
    ok: bool
    command: list[str]
    stdout: str = ""
    stderr: str = ""
    reason: str = ""

    @property
    def output(self) -> str:
        return "\n".join(part for part in (self.reason, self.stdout, self.stderr) if part).strip()


def _read_blueprint_source(name: str) -> str:
    src = REPO_ROOT / "blueprints" / name / "blueprint" / "src"
    content = src / "content.tex"
    if not content.is_file():
        raise FileNotFoundError(f"{content.relative_to(REPO_ROOT)} does not exist")
    parts = [f"% FILE: {content.relative_to(REPO_ROOT)}\n{content.read_text(encoding='utf-8')}"]
    common = src / "macros" / "common.tex"
    if common.is_file():
        parts.append(f"% FILE: {common.relative_to(REPO_ROOT)}\n{common.read_text(encoding='utf-8')}")
    return "\n\n".join(parts)


def _lean_name(label: str) -> str:
    name = re.sub(r"[^A-Za-z0-9_]+", "_", label).strip("_")
    if not name or name[0].isdigit():
        name = f"node_{name}"
    return name


def _node_summary(nodes: dict[str, Node]) -> str:
    lines: list[str] = []
    for label, node in sorted(nodes.items(), key=lambda item: (item[1].file, item[1].line, item[0])):
        uses = ", ".join(sorted(node.uses)) or "(none)"
        lean_decl = node.lean_decl or ""
        lines.append(
            f"- {label}: {node.kind}, Lean name `{_lean_name(label)}`, "
            f"uses [{uses}], settled decl `{lean_decl}`"
        )
    return "\n".join(lines)


def _extract_lean_code(text: str) -> str:
    fence = re.search(r"```(?:lean|lean4)?\s*([\s\S]*?)```", text)
    return (fence.group(1) if fence else text).strip()


def _default_lean_command() -> list[str]:
    if not (REPO_ROOT / "lean-toolchain").is_file() or not (REPO_ROOT / "lakefile.lean").is_file():
        raise FileNotFoundError(
            "Lean is not declared for this repo. Expected lean-toolchain and lakefile.lean."
        )
    if not any((Path.home() / ".elan" / "bin" / exe).is_file() for exe in ("lake", "lake.exe")):
        # lake may still be on PATH elsewhere, checked below; this message keeps
        # the common local setup failure direct.
        pass
    return ["lake", "env", "lean"]


def _run_lean(path: Path, lean_command: list[str]) -> LeanAttempt:
    code = path.read_text(encoding="utf-8")
    if FORBIDDEN_LEAN_PLACEHOLDERS.search(code):
        return LeanAttempt(
            ok=False,
            command=lean_command + [str(path)],
            reason="Lean attempt contains a forbidden placeholder (`sorry`, `admit`, or `by ?`).",
        )

    try:
        proc = subprocess.run(
            lean_command + [str(path)],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=600,
        )
    except FileNotFoundError as exc:
        raise FileNotFoundError(
            "Lake/Lean is not installed for this repo. Run:\n"
            "  uv run python scripts/setup_lean.py --install-elan"
        ) from exc

    return LeanAttempt(
        ok=proc.returncode == 0,
        command=lean_command + [str(path)],
        stdout=proc.stdout or "",
        stderr=proc.stderr or "",
    )


def _lean_prompt(name: str, blueprint_source: str, nodes: dict[str, Node]) -> str:
    return f"""TASK: BLUEPRINT-TO-LEAN-CHECK-ATTEMPT

Return exactly one Lean 4 file. Do not return markdown commentary.

Hard constraints:
- The blueprint below is the only mathematical source of truth.
- Do not strengthen, weaken, skip, or silently reinterpret blueprint statements.
- Do not use facts that are not Mathlib imports, explicit \\lean{{...}} settled
  declarations in the blueprint, or earlier blueprint nodes listed in \\uses{{...}}.
- Do not use `sorry`, `admit`, `by ?`, or comments that stand in for proof.
- Give each generated declaration the Lean name listed in the node summary.
- If the blueprint is missing a lemma/hypothesis/dependency, let Lean fail.
  Do not patch around missing blueprint content.

Start with:

import AutoBlueprint

Blueprint name: {name}

Node summary:
{_node_summary(nodes)}

Current blueprint source:
```tex
{blueprint_source}
```
"""


def _agent_refine_prompt(name: str, blueprint_source: str, lean_output: str, trial: int, paper_text: str) -> str:
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    return f"""TASK: REFINE-BLUEPRINT-FROM-LEAN-FAILURE

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.

You are the blueprint author. Fix the blueprint, not the Lean implementation.

Rules:
- Edit only `blueprints/{name}/blueprint/src/` and `blueprints/{name}/meta.yml`
  if metadata is genuinely wrong.
- Do not edit `.auto-blueprint/` Lean attempt files.
- Do not make the theorem weaker just to satisfy Lean.
- If Lean failed because the blueprint skipped an argument, add the missing
  lemma/proposition/definition as a blueprint node.
- If a proof needs an unstated dependency, add or correct `\\uses{{...}}`.
- If a statement is mathematically wrong compared with the paper, correct the
  statement in the blueprint.
- After editing, run `python scripts/validate_blueprint.py {name}`.

{paper_block}
Current blueprint source:
```tex
{blueprint_source}
```

Lean critic output:
```text
{lean_output[-12000:]}
```
"""


def _api_refine_prompt(name: str, blueprint_source: str, lean_output: str, trial: int, paper_text: str) -> str:
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    return f"""TASK: REFINE-BLUEPRINT-CONTENT-TEX

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.

Return exactly one JSON object:
{{
  "content_tex": "full replacement for blueprints/{name}/blueprint/src/content.tex",
  "notes": "short explanation of what changed"
}}

Rules:
- Fix the blueprint, not the Lean code.
- Do not make the theorem weaker just to satisfy Lean.
- Add missing intermediate blueprint nodes when the proof needs them.
- Correct `\\uses{{...}}` whenever dependencies were missing or wrong.
- Do not include `\\begin{{document}}` or `\\end{{document}}`.

{paper_block}
Current blueprint source:
```tex
{blueprint_source}
```

Lean critic output:
```text
{lean_output[-12000:]}
```
"""


def _write_api_refinement(name: str, text: str) -> None:
    payload = _extract_json(text)
    content_tex = str(payload.get("content_tex") or "").strip()
    if not content_tex:
        raise ValueError("refinement JSON did not include non-empty content_tex")
    if r"\begin{document}" in content_tex or r"\end{document}" in content_tex:
        raise ValueError("content_tex must not include a document environment")
    path = REPO_ROOT / "blueprints" / name / "blueprint" / "src" / "content.tex"
    path.write_text(content_tex.rstrip() + "\n", encoding="utf-8")
    notes = str(payload.get("notes") or "").strip()
    if notes:
        print(f"  refinement notes: {notes}")


def _write_report(name: str, lines: list[str]) -> Path:
    out_dir = SCRATCH_DIR / name
    out_dir.mkdir(parents=True, exist_ok=True)
    report = out_dir / "report.md"
    report.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return report


def _publish_passing_lean(name: str, lean_path: Path) -> Path:
    """Save the passing Lean attempt as a tracked blueprint artifact."""
    dest_dir = REPO_ROOT / "blueprints" / name / "blueprint" / "lean"
    dest_dir.mkdir(parents=True, exist_ok=True)
    dest = dest_dir / PUBLISHED_LEAN_NAME
    dest.write_text(lean_path.read_text(encoding="utf-8").rstrip() + "\n", encoding="utf-8")
    return dest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name", help="Existing blueprint name under blueprints/<name>/")
    parser.add_argument("--runner", default="codex", help="Runner spec, e.g. codex, openai:gpt-5")
    parser.add_argument("--max-trials", type=int, default=3, help="Stop after this many Lean attempts")
    parser.add_argument("--paper", help="Optional original paper path/URL/text for refinement context")
    parser.add_argument("--lean-command", help="Override checker command, e.g. 'lake env lean'")
    parser.add_argument(
        "--reasoning-effort",
        choices=("low", "medium", "high", "xhigh"),
        help="Codex reasoning effort for --runner codex/codex:<model>.",
    )
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args(argv)

    if args.max_trials < 1:
        raise SystemExit("--max-trials must be at least 1")

    runner_kwargs = {}
    if args.reasoning_effort:
        if not args.runner.startswith("codex"):
            raise SystemExit("--reasoning-effort is currently supported only for --runner codex")
        runner_kwargs["reasoning_effort"] = args.reasoning_effort

    paper_text = ""
    if args.paper:
        print(f"==> Reading paper context from {args.paper}", flush=True)
        paper_text, _source = read_paper(args.paper)

    lean_command = shlex.split(args.lean_command) if args.lean_command else _default_lean_command()
    runner = get_runner(
        args.runner,
        context_files=[SKILL_PATH],
        timeout=args.timeout,
        **runner_kwargs,
    )

    report_lines = [
        f"# Lean-Guided Blueprint Refinement: `{args.name}`",
        "",
        f"- runner: `{args.runner}`",
        f"- max trials: `{args.max_trials}`",
        f"- Lean command: `{' '.join(lean_command)}`",
        "",
    ]

    for trial in range(1, args.max_trials + 1):
        print(f"==> Trial {trial}/{args.max_trials}: validating blueprint", flush=True)
        validation = validate_blueprint(REPO_ROOT, args.name)
        print_result(validation)
        if not validation.ok:
            report_lines.append(f"## Trial {trial}: structural validation failed")
            report_lines.extend(f"- {error}" for error in validation.errors)
            report = _write_report(args.name, report_lines)
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return 1

        blueprint_source = _read_blueprint_source(args.name)

        print(f"==> Trial {trial}/{args.max_trials}: generating disposable Lean attempt", flush=True)
        lean_result = runner.run(
            _lean_prompt(args.name, blueprint_source, validation.nodes),
            cwd=REPO_ROOT,
            retries=0,
        )
        trial_dir = SCRATCH_DIR / args.name
        trial_dir.mkdir(parents=True, exist_ok=True)
        lean_path = trial_dir / f"trial_{trial:02d}.lean"
        lean_path.write_text(_extract_lean_code(lean_result.text).rstrip() + "\n", encoding="utf-8")

        print(f"==> Trial {trial}/{args.max_trials}: running Lean", flush=True)
        attempt = _run_lean(lean_path, lean_command)
        report_lines.append(f"## Trial {trial}")
        report_lines.append(f"- Lean file: `{lean_path.relative_to(REPO_ROOT)}`")

        if attempt.ok:
            published = _publish_passing_lean(args.name, lean_path)
            report_lines.append("- result: passed")
            report_lines.append(f"- published Lean: `{published.relative_to(REPO_ROOT)}`")
            report = _write_report(args.name, report_lines)
            print(f"Lean passed on trial {trial}.")
            print(f"Published Lean saved to {published.relative_to(REPO_ROOT)}")
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return 0

        critic_output = attempt.output
        report_lines.append("- result: failed")
        report_lines.append("")
        report_lines.append("```text")
        report_lines.append(critic_output[-4000:])
        report_lines.append("```")
        report_lines.append("")

        if trial == args.max_trials:
            break

        print(f"==> Trial {trial}/{args.max_trials}: repairing blueprint from Lean output", flush=True)
        if runner.mode == "agent":
            runner.run(
                _agent_refine_prompt(args.name, blueprint_source, critic_output, trial, paper_text),
                cwd=REPO_ROOT,
                retries=0,
            )
        else:
            refine_result = runner.run(
                _api_refine_prompt(args.name, blueprint_source, critic_output, trial, paper_text),
                cwd=REPO_ROOT,
                retries=1,
            )
            _write_api_refinement(args.name, refine_result.text)

    report_lines.append(f"Stopped after {args.max_trials} failed trial(s).")
    report = _write_report(args.name, report_lines)
    print(f"Lean did not pass after {args.max_trials} trial(s).")
    print(f"Report written to {report.relative_to(REPO_ROOT)}")
    return 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (FileNotFoundError, RunnerError, subprocess.TimeoutExpired) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
