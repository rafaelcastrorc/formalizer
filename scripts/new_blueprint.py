#!/usr/bin/env python3
"""Scaffold a new blueprint from ``templates/blueprint-skeleton/``.

Usage::

    python scripts/new_blueprint.py <name> --title "Title" --description "..."

It copies the skeleton to ``blueprints/<name>/`` and writes
``blueprints/<name>/meta.yml`` with the provided fields (and ``name: <name>``).
Nothing else is modified; edit ``blueprints/<name>/blueprint/src/content.tex``
to add your own content, then run ``python scripts/build.py``.
"""
from __future__ import annotations

import argparse
import re
import shutil
import sys
from pathlib import Path

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
SKELETON_DIR = REPO_ROOT / "templates" / "blueprint-skeleton"
BLUEPRINTS_DIR = REPO_ROOT / "blueprints"

# Names become URL subpaths and folder names: keep them lowercase-url-safe.
NAME_RE = re.compile(r"^[a-z0-9][a-z0-9._-]*$")
# meta.yml free-text fields are written as single-line double-quoted scalars;
# reject control characters (incl. newlines/tabs) that would corrupt them.
CONTROL_RE = re.compile(r"[\x00-\x1f\x7f]")


def build_meta(*, name: str, title: str, description: str,
               build_pdf: bool, home: str, github: str) -> str:
    """Build the meta.yml text and verify it round-trips to the intended values.

    Done by hand (not yaml.dump) to keep the explanatory comments and field
    order. Raises ValueError if any field would not survive a parse.
    """
    def q(value: str) -> str:
        return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'

    content = (
        "# Per-blueprint metadata. `name` MUST match the folder name; it is\n"
        "# used as the URL subpath (the blueprint is published at site/<name>/).\n"
        f"name: {name}\n"
        f"title: {q(title)}\n"
        f"description: {q(description)}\n"
        f"build_pdf: {'true' if build_pdf else 'false'}        "
        "# if true, also build + link a PDF (requires TeX in CI)\n"
        f"home: {q(home)}                # optional URL shown as a \"home\" link on the landing card\n"
        f"github: {q(github)}              # optional repo URL shown as a \"GitHub\" link on the landing card\n"
    )

    # Round-trip every user-supplied field through the YAML parser. Use an
    # explicit raise (not assert, which `python -O` strips).
    expected = {
        "name": name,
        "title": title,
        "description": description,
        "build_pdf": build_pdf,
        "home": home,
        "github": github,
    }
    parsed = yaml.safe_load(content)
    got = {k: parsed.get(k) for k in expected}
    if got != expected:
        raise ValueError(f"meta.yml would not round-trip: wrote {expected!r}, parsed {got!r}")
    return content


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("name", help="blueprint name (lowercase, url-safe; becomes the subpath)")
    parser.add_argument("--title", default=None, help="human title (default: the name)")
    parser.add_argument("--description", default="", help="one-line description")
    parser.add_argument("--build-pdf", action="store_true", help="set build_pdf: true")
    parser.add_argument("--home", default="", help="optional home URL")
    parser.add_argument("--github", default="", help="optional GitHub repo URL")
    args = parser.parse_args(argv)

    name = args.name
    if not NAME_RE.match(name):
        parser.error(
            f"invalid name {name!r}: use lowercase letters, digits, and . _ - "
            "(must start with a letter or digit)"
        )

    if not SKELETON_DIR.is_dir():
        parser.error(f"skeleton not found at {SKELETON_DIR}")

    title = args.title if args.title is not None else name
    for label, value in (("--title", title), ("--description", args.description),
                         ("--home", args.home), ("--github", args.github)):
        if CONTROL_RE.search(value):
            parser.error(f"{label} must not contain newlines or control characters")

    dest = BLUEPRINTS_DIR / name
    if dest.exists():
        parser.error(f"{dest.relative_to(REPO_ROOT)} already exists; refusing to overwrite")

    # Build & validate meta.yml content BEFORE touching the filesystem, so bad
    # input fails with zero changes (no orphaned dir that blocks a retry).
    try:
        meta_content = build_meta(
            name=name,
            title=title,
            description=args.description,
            build_pdf=args.build_pdf,
            home=args.home,
            github=args.github,
        )
    except (ValueError, yaml.YAMLError) as exc:
        parser.error(f"could not generate meta.yml: {exc}")

    BLUEPRINTS_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copytree(SKELETON_DIR, dest)
    (dest / "meta.yml").write_text(meta_content, encoding="utf-8")

    rel = dest.relative_to(REPO_ROOT)
    print(f"Created {rel}/")
    print(f"  Next: edit {rel}/blueprint/src/content.tex (and the \\title in web.tex/print.tex),")
    print(f"        then run:  python scripts/build.py")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
