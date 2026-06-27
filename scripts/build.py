#!/usr/bin/env python3
"""Build every blueprint plus the landing page into ``site/``.

This project hosts multiple leanblueprint/plasTeX *blueprints* without any Lean
toolchain. We deliberately do **not** invoke the ``leanblueprint`` CLI: its
module errors out at import time unless it finds a Git repository *and* a
``lakefile.lean``/``lakefile.toml`` (it is written for Lean projects). Instead
we run plasTeX exactly the way ``leanblueprint web`` does internally::

    plastex -c plastex.cfg web.tex          # run from inside blueprint/src/

That needs no Lean, no lake, no git remote -- only Python packages and graphviz.
See the README section "Why we call plasTeX directly" for the full rationale.

Usage::

    python scripts/build.py                 # build all blueprints (full rebuild)
    python scripts/build.py demo foo        # rebuild only these (keep the rest)
    python scripts/build.py --strict        # fail the run if any blueprint fails
    python scripts/build.py --print-needs-tex   # print true/false (CI TeX gate)

A full rebuild recreates ``site/`` from scratch. By default the run is
resilient: a blueprint that fails to build is reported (and annotated for CI)
but does not stop the others or block deployment; pass ``--strict`` to make any
failure fatal.
"""
from __future__ import annotations

import argparse
import configparser
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

import yaml
from jinja2 import Environment, FileSystemLoader, select_autoescape

# --------------------------------------------------------------------------- #
# Paths
# --------------------------------------------------------------------------- #
SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
BLUEPRINTS_DIR = REPO_ROOT / "blueprints"
SITE_DIR = REPO_ROOT / "site"
LANDING_TEMPLATE_DIR = SCRIPTS_DIR / "templates"
LANDING_TEMPLATE_NAME = "landing.html.j2"

# Run plasTeX with the *same* interpreter that runs this script -- that is where
# ``pip install -r requirements.txt`` placed plasTeX and its plugins. This avoids
# depending on ``plastex`` being on PATH (e.g. an unactivated virtualenv).
PLASTEX_BOOT = "import sys; from plasTeX.client import plastex; sys.exit(plastex())"

_TRUE_STRINGS = {"true", "yes", "on", "1"}
_FALSE_STRINGS = {"false", "no", "off", "0", "none", "null", ""}


# --------------------------------------------------------------------------- #
# Helpers
# --------------------------------------------------------------------------- #
def as_bool(value, *, where: str = "") -> bool:
    """Coerce a YAML scalar to bool the same way everywhere (build + CI gate).

    Accepts real booleans, ints, and the usual YAML truthy/falsy spellings.
    A quoted ``"false"`` must NOT become True (plain ``bool(str)`` would), and an
    unrecognized value is treated as False with a warning rather than silently
    truthy.
    """
    if isinstance(value, bool):
        return value
    if value is None:
        return False
    if isinstance(value, int):  # bool already handled above
        return value != 0
    s = str(value).strip().lower()
    if s in _TRUE_STRINGS:
        return True
    if s in _FALSE_STRINGS:
        return False
    print(f"  ! {where}unrecognized boolean {value!r}; treating as false")
    return False


def safe_url(value, *, where: str = "") -> str:
    """Allow only http(s)/mailto absolute URLs or relative paths in the landing
    page (drop e.g. ``javascript:`` schemes). Defense-in-depth for the future
    'untrusted paper -> blueprint' generator."""
    s = str(value or "").strip()
    if not s:
        return ""
    low = s.lower()
    if low.startswith(("http://", "https://", "mailto:")) or s.startswith(("/", "./", "../", "#")):
        return s
    print(f"  ! {where}ignoring unsafe URL {s!r} (only http(s)/mailto/relative allowed)")
    return ""


# --------------------------------------------------------------------------- #
# Model
# --------------------------------------------------------------------------- #
@dataclass
class Blueprint:
    """One blueprint discovered under ``blueprints/<name>/``."""

    name: str            # folder name == URL subpath
    dir: Path            # blueprints/<name>
    title: str
    description: str
    build_pdf: bool
    home: str
    github: str
    has_pdf: bool = field(default=False)  # set for the landing page from site/ state

    @property
    def src_dir(self) -> Path:
        return self.dir / "blueprint" / "src"

    @property
    def print_dir(self) -> Path:
        # latexmk is invoked with -output-directory=../print from src/.
        return self.dir / "blueprint" / "print"

    @property
    def web_dir(self) -> Path:
        """Where plasTeX writes the web build, read from this blueprint's
        plastex.cfg ``[files] directory`` (resolved relative to src/), so build.py
        and plasTeX share one source of truth. Falls back to ``../web/``."""
        directory = "../web/"
        cfg_path = self.src_dir / "plastex.cfg"
        if cfg_path.is_file():
            parser = configparser.ConfigParser(interpolation=None)
            try:
                parser.read(cfg_path, encoding="utf-8")
                directory = parser.get("files", "directory", fallback=directory).strip() or directory
            except configparser.Error:
                pass
        return (self.src_dir / directory).resolve()


# --------------------------------------------------------------------------- #
# Discovery
# --------------------------------------------------------------------------- #
def load_meta(meta_path: Path) -> dict:
    """Load meta.yml as a mapping. Raises on malformed YAML or a non-mapping;
    callers decide how to handle a bad file."""
    if not meta_path.exists():
        print(f"  ! {meta_path.relative_to(REPO_ROOT)} not found; using defaults")
        return {}
    with meta_path.open(encoding="utf-8") as fh:
        data = yaml.safe_load(fh) or {}
    if not isinstance(data, dict):
        raise ValueError(f"{meta_path} must contain a YAML mapping")
    return data


def discover_blueprints() -> list[Blueprint]:
    """Find every ``blueprints/<name>/`` that has ``blueprint/src/web.tex``.

    A blueprint with an unreadable meta.yml is skipped with a warning rather than
    aborting the whole run (mirrors the fail-soft build loop).
    """
    if not BLUEPRINTS_DIR.is_dir():
        return []

    blueprints: list[Blueprint] = []
    for child in sorted(BLUEPRINTS_DIR.iterdir()):
        if not child.is_dir():
            continue
        if not (child / "blueprint" / "src" / "web.tex").is_file():
            continue
        name = child.name
        try:
            meta = load_meta(child / "meta.yml")
        except (yaml.YAMLError, ValueError, OSError) as exc:
            print(f"  ! skipping {name!r}: bad meta.yml: {exc}", file=sys.stderr)
            continue

        meta_name = meta.get("name")
        if meta_name and meta_name != name:
            print(
                f"  ! meta.yml name {meta_name!r} != folder {name!r}; "
                f"using folder name as the URL subpath"
            )

        blueprints.append(
            Blueprint(
                name=name,
                dir=child,
                title=str(meta.get("title") or name),
                description=str(meta.get("description") or ""),
                build_pdf=as_bool(meta.get("build_pdf", False), where=f"{name}/meta.yml: "),
                home=safe_url(meta.get("home"), where=f"{name}/meta.yml: "),
                github=safe_url(meta.get("github"), where=f"{name}/meta.yml: "),
            )
        )
    return blueprints


# --------------------------------------------------------------------------- #
# Building
# --------------------------------------------------------------------------- #
def _run(cmd: list[str], cwd: Path) -> None:
    print(f"    $ {' '.join(cmd)}   (cwd={cwd.relative_to(REPO_ROOT)})")
    subprocess.run(cmd, cwd=str(cwd), check=True)


def build_pdf(bp: Blueprint) -> None:
    """Compile the PDF with latexmk -> xelatex (mirrors ``leanblueprint pdf``).

    Runs before the web build so that, if the blueprint has a bibliography,
    ``print.bbl`` can be reused as ``web.bbl`` (plasTeX does not call BibTeX).
    latexmk is incremental, so ``print/`` is intentionally not wiped.
    """
    bp.print_dir.mkdir(parents=True, exist_ok=True)
    _run(["latexmk", "-output-directory=../print", "print.tex"], cwd=bp.src_dir)

    bbl = bp.print_dir / "print.bbl"
    if bbl.exists():
        shutil.copy(bbl, bp.src_dir / "web.bbl")

    if not (bp.print_dir / "print.pdf").is_file():
        raise FileNotFoundError(
            f"build_pdf is true for {bp.name!r} but latexmk produced no "
            f"{bp.print_dir.relative_to(REPO_ROOT)}/print.pdf"
        )


def build_web(bp: Blueprint) -> None:
    """Render the web version with plasTeX (mirrors ``leanblueprint web``)."""
    web_dir = bp.web_dir
    # Start from a clean output dir so no stale files leak into the site.
    if web_dir.exists():
        shutil.rmtree(web_dir)
    web_dir.mkdir(parents=True, exist_ok=True)
    _run(
        [sys.executable, "-c", PLASTEX_BOOT, "-c", "plastex.cfg", "web.tex"],
        cwd=bp.src_dir,
    )

    index = web_dir / "index.html"
    if not index.is_file():
        raise FileNotFoundError(
            f"plasTeX did not produce {index} for {bp.name!r} "
            f"(check [files] directory in {bp.name}/blueprint/src/plastex.cfg)"
        )


def copy_to_site(bp: Blueprint) -> None:
    """Copy the rendered blueprint (and PDF, if any) into ``site/<name>/``."""
    dest = SITE_DIR / bp.name
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(bp.web_dir, dest)

    pdf = bp.print_dir / "print.pdf"
    if bp.build_pdf and pdf.is_file():
        shutil.copy(pdf, dest / "blueprint.pdf")


def build_blueprint(bp: Blueprint) -> None:
    print(f"==> {bp.name}")
    if bp.build_pdf:
        build_pdf(bp)
    build_web(bp)
    copy_to_site(bp)
    extra = " (+ blueprint.pdf)" if (SITE_DIR / bp.name / "blueprint.pdf").is_file() else ""
    print(f"  ok -> site/{bp.name}/{extra}")


# --------------------------------------------------------------------------- #
# Landing page
# --------------------------------------------------------------------------- #
def render_landing(blueprints: list[Blueprint]) -> None:
    env = Environment(
        loader=FileSystemLoader(str(LANDING_TEMPLATE_DIR)),
        autoescape=select_autoescape(["html", "xml", "html.j2"]),
        trim_blocks=True,
        lstrip_blocks=True,
    )
    template = env.get_template(LANDING_TEMPLATE_NAME)
    cards = []
    for bp in blueprints:
        has_pdf = (SITE_DIR / bp.name / "blueprint.pdf").is_file()
        cards.append(
            {
                "name": bp.name,
                "title": bp.title,
                "description": bp.description,
                "url": f"./{bp.name}/",
                "pdf_url": f"./{bp.name}/blueprint.pdf" if has_pdf else None,
                "home": bp.home,
                "github": bp.github,
            }
        )
    html = template.render(blueprints=cards)
    (SITE_DIR / "index.html").write_text(html, encoding="utf-8")
    print(f"==> landing page -> site/index.html ({len(cards)} blueprint(s))")


# --------------------------------------------------------------------------- #
# Entry point
# --------------------------------------------------------------------------- #
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "names",
        nargs="*",
        help="Only rebuild these blueprints; others already in site/ are kept "
        "(default: full rebuild of all).",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit non-zero if any blueprint fails (default: deploy the ones "
        "that succeeded).",
    )
    parser.add_argument(
        "--print-needs-tex",
        action="store_true",
        help="Print 'true' if any blueprint sets build_pdf, else 'false', then "
        "exit. Used by CI to decide whether to install TeX.",
    )
    args = parser.parse_args(argv)

    all_blueprints = discover_blueprints()

    if args.print_needs_tex:
        print("true" if any(bp.build_pdf for bp in all_blueprints) else "false")
        return 0

    only = set(args.names) if args.names else None
    if only:
        missing = sorted(only - {bp.name for bp in all_blueprints})
        for name in missing:
            print(f"  ! requested blueprint {name!r} not found; skipping")
    to_build = [bp for bp in all_blueprints if (only is None or bp.name in only)]

    if not all_blueprints:
        print("No blueprints found (need blueprints/<name>/blueprint/src/web.tex).")

    if only:
        # Incremental: keep previously-built blueprints, refresh just the named ones.
        print(f"Incremental build of {len(to_build)} blueprint(s); keeping the rest of site/.")
        SITE_DIR.mkdir(parents=True, exist_ok=True)
    else:
        # Full rebuild: recreate site/ from scratch (idempotent).
        if SITE_DIR.exists():
            shutil.rmtree(SITE_DIR)
        SITE_DIR.mkdir(parents=True)

    failures: list[str] = []
    built: list[Blueprint] = []
    for bp in to_build:
        try:
            build_blueprint(bp)
            built.append(bp)
        except Exception as exc:  # noqa: BLE001 - report and continue
            failures.append(bp.name)
            print(f"  FAILED: {bp.name}: {exc}", file=sys.stderr)
            # GitHub Actions annotation so failures are visible even when we
            # still deploy the healthy blueprints.
            print(f"::error title=Blueprint build failed::{bp.name}: {exc}")

    # Landing lists every blueprint that currently has output in site/ (so an
    # incremental build does not drop previously-published blueprints).
    listed = [bp for bp in all_blueprints if (SITE_DIR / bp.name / "index.html").is_file()]
    render_landing(listed)

    if failures:
        msg = f"\nFailed blueprints: {', '.join(failures)}"
        if args.strict:
            print(msg + " (--strict: failing the run)", file=sys.stderr)
            return 1
        if built:
            print(msg + f"\nBuilt {len(built)} of {len(to_build)}; deploying the rest.", file=sys.stderr)
            return 0
        print(msg + "\nNo blueprint built successfully.", file=sys.stderr)
        return 1

    print("\nDone.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
