#!/usr/bin/env python3
"""Paper -> blueprint generation entrypoint.

This is the command a user runs when they have a new research paper and want a
new ``blueprints/<name>/`` folder. It supports two production modes:

* agent mode (``--runner codex`` / ``--runner claude-code``): a local coding
  agent receives the paper plus repo instructions and may edit files/run scripts.
* API mode (``--runner openai:...`` / ``--runner anthropic:...``): the model
  returns JSON only; this script creates files, validates them, and builds them.

The rest of Auto-Blueprint still treats generated blueprints like any other
blueprint: ``validate_blueprint.py`` checks structure and ``build.py`` renders
the site.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
import urllib.request
from pathlib import Path

from model_runners import RunnerError, get_runner
from new_blueprint import BLUEPRINTS_DIR, REPO_ROOT, SKELETON_DIR, build_meta
from validate_blueprint import print_result, validate_blueprint

SKILL_PATH = REPO_ROOT / ".claude" / "skills" / "paper-to-blueprint" / "SKILL.md"
NAME_RE = re.compile(r"^[a-z0-9][a-z0-9._-]*$")


def _slug(value: str) -> str:
    slug = re.sub(r"[^a-z0-9._-]+", "-", value.lower()).strip("-._")
    slug = re.sub(r"-{2,}", "-", slug)
    if not slug or not slug[0].isalnum():
        slug = "generated-blueprint"
    return slug[:80]


def _extract_json(text: str) -> dict:
    fence = re.search(r"```(?:json)?\s*([\s\S]*?)```", text)
    candidates = [fence.group(1)] if fence else []
    brace = re.search(r"\{[\s\S]*\}", text)
    if brace:
        candidates.append(brace.group(0))
    for candidate in candidates:
        try:
            data = json.loads(candidate)
            if isinstance(data, dict):
                return data
        except json.JSONDecodeError:
            continue
    raise ValueError("model did not return a JSON object")


def _read_pdf_with_pdftotext(path: Path) -> str:
    exe = shutil.which("pdftotext")
    if not exe:
        return _read_pdf_with_pypdf(path)
    proc = subprocess.run(
        [exe, str(path), "-"],
        capture_output=True,
        text=True,
        timeout=180,
    )
    if proc.returncode != 0:
        raise RuntimeError((proc.stderr or proc.stdout or "pdftotext failed").strip())
    return proc.stdout


def _read_pdf_with_pypdf(path: Path) -> str:
    try:
        from pypdf import PdfReader
    except ImportError as exc:
        raise RuntimeError(
            f"{path} looks like a PDF, but neither `pdftotext` nor the Python "
            "`pypdf` package is available. Run `uv pip install -r requirements.txt`."
        ) from exc

    reader = PdfReader(str(path))
    pages: list[str] = []
    for i, page in enumerate(reader.pages, start=1):
        try:
            pages.append(page.extract_text() or "")
        except Exception as exc:  # noqa: BLE001 - keep extracting later pages
            pages.append(f"\n[page {i}: text extraction failed: {exc}]\n")
    text = "\n\n".join(pages).strip()
    if not text:
        raise RuntimeError(f"no text could be extracted from {path}")
    return text


def read_paper(source: str) -> tuple[str, str]:
    """Return ``(paper_text, source_label)`` from a file path, URL, or raw text."""
    if source.startswith(("http://", "https://")):
        with urllib.request.urlopen(source, timeout=60) as resp:
            data = resp.read()
        if source.lower().endswith(".pdf"):
            with tempfile.NamedTemporaryFile(suffix=".pdf", delete=False) as tmp:
                tmp.write(data)
                tmp_path = Path(tmp.name)
            try:
                return _read_pdf_with_pdftotext(tmp_path), source
            finally:
                tmp_path.unlink(missing_ok=True)
        return data.decode("utf-8", "replace"), source

    path = Path(source).expanduser()
    if path.is_file():
        if path.suffix.lower() == ".pdf":
            return _read_pdf_with_pdftotext(path), str(path)
        return path.read_text(encoding="utf-8"), str(path)

    return source, "pasted text"


def _api_prompt(paper_text: str, *, requested_name: str | None, source_label: str) -> str:
    name_part = f"Requested blueprint name: {requested_name}\n" if requested_name else ""
    return f"""TASK: PAPER-TO-BLUEPRINT-JSON

Convert the research paper below into a leanblueprint-style blueprint for this
Auto-Blueprint repository.

{name_part}Source: {source_label}

Return exactly one JSON object, with no markdown commentary. Required shape:

{{
  "name": "lowercase-url-safe-name",
  "title": "paper title",
  "authors": "paper authors",
  "description": "one-line thesis for the landing page",
  "home": "paper URL or empty string",
  "github": "repo URL or empty string",
  "build_pdf": false,
  "content_tex": "complete LaTeX body for blueprint/src/content.tex"
}}

Rules for content_tex:
- Do not include \\begin{{document}} or \\end{{document}}.
- Organize with \\chapter{{...}}.
- Include every important definition, lemma, proposition, theorem, corollary,
  construction, algorithm, and proof from the paper.
- Every theorem-like environment must have a unique \\label{{...}}.
- Every dependency must be represented with \\uses{{...}}.
- If a proof uses dependencies not needed in the statement, put \\uses{{...}}
  inside the proof environment too.
- Mark true library leaves with \\mathlibok and \\lean{{Fully.Qualified.Name}}
  only when confident. When unsure, treat the result as novel and include it
  fully.
- Use only theorem-like environments supported by the skeleton unless you also
  explain needed extensions in comments.

<paper>
{paper_text}
</paper>
"""


def _agent_prompt(paper_text: str, *, requested_name: str | None, source_label: str) -> str:
    name_part = f"Use this blueprint name unless it is invalid: {requested_name}\n" if requested_name else ""
    return f"""TASK: GENERATE-BLUEPRINT-IN-REPO

Generate a blueprint in this Auto-Blueprint repo from the paper below.

{name_part}Source: {source_label}

Follow the paper-to-blueprint context exactly. In particular:
1. Pick/validate a lowercase URL-safe blueprint name.
2. Run `python scripts/new_blueprint.py <name> --title ... --description ...`.
3. Overwrite `blueprints/<name>/blueprint/src/content.tex`.
4. Update title/author/home in web.tex and print.tex.
5. Run `python scripts/validate_blueprint.py <name>`.
6. Run `python scripts/build.py <name>`.
7. Fix validation/build issues before finishing.

At the end, report the blueprint name, node count, warnings/TODOs, and build
status. Do not commit changes.

<paper>
{paper_text}
</paper>
"""


def _replace_tex_command(text: str, command: str, value: str) -> str:
    escaped = value.replace("\\", r"\textbackslash{}").replace("{", r"\{").replace("}", r"\}")
    pattern = re.compile(rf"\\{command}\{{[^}}]*\}}")
    replacement = f"\\{command}{{{escaped}}}"
    if pattern.search(text):
        return pattern.sub(lambda _match: replacement, text, count=1)
    return text


def _set_home(text: str, home: str) -> str:
    if not home:
        return text
    if re.search(r"^\s*%?\s*\\home\{", text, re.MULTILINE):
        replacement = f"\\home{{{home}}}"
        return re.sub(
            r"^\s*%?\s*\\home\{[^}]*\}",
            lambda _match: replacement,
            text,
            count=1,
            flags=re.MULTILINE,
        )
    return text.replace(r"\author", rf"\home{{{home}}}" + "\n" + r"\author", 1)


def scaffold_from_payload(payload: dict, *, requested_name: str | None, force: bool) -> str:
    title = str(payload.get("title") or requested_name or "Generated Blueprint").strip()
    name = str(payload.get("name") or requested_name or _slug(title)).strip()
    name = _slug(name)
    if requested_name:
        name = requested_name
    if not NAME_RE.match(name):
        raise ValueError(f"invalid blueprint name {name!r}")

    content_tex = str(payload.get("content_tex") or "").strip()
    if not content_tex:
        raise ValueError("payload is missing non-empty content_tex")
    if r"\begin{document}" in content_tex or r"\end{document}" in content_tex:
        raise ValueError("content_tex must not contain document environment")

    dest = BLUEPRINTS_DIR / name
    if dest.exists():
        if not force:
            raise FileExistsError(f"{dest.relative_to(REPO_ROOT)} already exists; pass --force to replace it")
        shutil.rmtree(dest)

    BLUEPRINTS_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copytree(SKELETON_DIR, dest)

    description = str(payload.get("description") or "").strip()
    authors = str(payload.get("authors") or "").strip()
    home = str(payload.get("home") or "").strip()
    github = str(payload.get("github") or "").strip()
    build_pdf = bool(payload.get("build_pdf", False))

    (dest / "meta.yml").write_text(
        build_meta(
            name=name,
            title=title,
            description=description,
            build_pdf=build_pdf,
            home=home,
            github=github,
        ),
        encoding="utf-8",
    )
    src = dest / "blueprint" / "src"
    (src / "content.tex").write_text(content_tex.rstrip() + "\n", encoding="utf-8")
    for tex_name in ("web.tex", "print.tex"):
        tex_path = src / tex_name
        text = tex_path.read_text(encoding="utf-8")
        text = _replace_tex_command(text, "title", title)
        text = _replace_tex_command(text, "author", authors)
        if tex_name == "web.tex":
            text = _set_home(text, home)
        tex_path.write_text(text, encoding="utf-8")
    return name


def run_checked(cmd: list[str]) -> None:
    print(f"$ {' '.join(cmd)}")
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), text=True)
    if proc.returncode != 0:
        raise subprocess.CalledProcessError(proc.returncode, cmd)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("paper", help="PDF/text path, URL, or pasted paper text")
    parser.add_argument("--name", help="Blueprint folder/URL name")
    parser.add_argument("--runner", default="codex", help="Runner spec, e.g. codex, claude-code, openai:gpt-5")
    parser.add_argument(
        "--reasoning-effort",
        choices=("low", "medium", "high", "xhigh"),
        help="Codex reasoning effort for --runner codex/codex:<model>.",
    )
    parser.add_argument("--timeout", type=int, default=3600)
    parser.add_argument("--force", action="store_true", help="Replace an existing generated blueprint folder")
    parser.add_argument("--no-build", action="store_true", help="Validate only; do not run scripts/build.py")
    args = parser.parse_args(argv)

    print(f"==> Reading paper from {args.paper}", flush=True)
    paper_text, source_label = read_paper(args.paper)
    if len(paper_text.strip()) < 100:
        raise SystemExit("paper text is too short; pass a real paper path, URL, or extracted text")
    print(f"==> Extracted {len(paper_text):,} characters of paper text", flush=True)

    runner_kwargs = {}
    if args.reasoning_effort:
        if not args.runner.startswith("codex"):
            raise SystemExit("--reasoning-effort is currently supported only for --runner codex")
        runner_kwargs["reasoning_effort"] = args.reasoning_effort

    runner = get_runner(
        args.runner,
        context_files=[SKILL_PATH],
        timeout=args.timeout,
        **runner_kwargs,
    )
    if runner.mode == "agent":
        print(
            f"==> Starting {runner.backend_name} agent"
            f"{f' ({runner.model})' if runner.model else ''}; this can take several minutes",
            flush=True,
        )
        result = runner.run(
            _agent_prompt(paper_text, requested_name=args.name, source_label=source_label),
            cwd=REPO_ROOT,
            retries=0,
        )
        print(result.text)
        return 0

    print(f"==> Calling {runner.backend_name} API{f' ({runner.model})' if runner.model else ''}", flush=True)
    result = runner.run(
        _api_prompt(paper_text, requested_name=args.name, source_label=source_label),
        cwd=REPO_ROOT,
        retries=1,
    )
    payload = _extract_json(result.text)
    name = scaffold_from_payload(payload, requested_name=args.name, force=args.force)

    validation = validate_blueprint(REPO_ROOT, name)
    print_result(validation)
    if not validation.ok:
        raise SystemExit(1)

    if not args.no_build:
        run_checked([sys.executable, "scripts/build.py", name])
    print(f"Generated blueprint: blueprints/{name}/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
