#!/usr/bin/env python3
"""Build every blueprint plus the landing page into ``site/``.

This project hosts multiple leanblueprint/plasTeX *blueprints*. The website
build deliberately does **not** invoke Lean or the ``leanblueprint`` CLI; the
formalization loop is a separate layer. Instead we run plasTeX exactly the way
``leanblueprint web`` does internally::

    plastex -c plastex.cfg web.tex          # run from inside blueprint/src/

That needs no Lean, no Lake, and no git remote -- only Python packages and
graphviz. See the README section "Why we call plasTeX directly" for the full
rationale.

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
import html
import os
import re
import shutil
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

import yaml
from jinja2 import Environment, FileSystemLoader, select_autoescape
from validate_blueprint import Node, print_result, validate_blueprint

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
    def lean_dir(self) -> Path:
        # Passing formalizations are saved here by refine_blueprint_with_lean.py.
        return self.dir / "blueprint" / "lean"

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
    proc = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True)
    if proc.returncode != 0:
        # Surface the real error (plasTeX/latexmk output) so CI logs are
        # self-contained instead of just reporting "exit status 1".
        combined = (proc.stdout or "") + (proc.stderr or "")
        tail = "\n".join(combined.splitlines()[-40:])
        print("    ----- command output (last 40 lines) -----", file=sys.stderr)
        print(tail, file=sys.stderr)
        print("    ----- end command output -----", file=sys.stderr)
        raise subprocess.CalledProcessError(proc.returncode, cmd, proc.stdout, proc.stderr)


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


# Spliced into every rendered page so readers can get back to the landing page.
# plasTeX has no notion of the multi-blueprint landing page or our saved Lean
# artifact, so we inject those links after rendering. The marker keeps the pass
# idempotent across rebuilds.
HOME_LINK_MARKER = 'class="bp-home-link"'
LEAN_LINK_MARKER = 'class="bp-lean-link"'
HEADER_NAV_STYLE_MARKER = 'id="bp-header-nav-style"'
LOCAL_LEAN_LINK_MARKER = 'class="bp-local-lean-link"'
LOCAL_LEAN_STYLE_MARKER = 'id="bp-local-lean-style"'
PUBLISHED_LEAN_NAME = "formalization.lean"
LEAN_VIEWER_NAME = "index.html"

LEAN_KEYWORDS = (
    "abbrev",
    "axiom",
    "by",
    "class",
    "def",
    "deriving",
    "else",
    "end",
    "example",
    "have",
    "if",
    "import",
    "in",
    "inductive",
    "instance",
    "let",
    "lemma",
    "match",
    "namespace",
    "noncomputable",
    "open",
    "opaque",
    "private",
    "section",
    "simp",
    "structure",
    "theorem",
    "then",
    "where",
    "with",
)
LEAN_KEYWORD_RE = re.compile(r"\b(" + "|".join(re.escape(word) for word in LEAN_KEYWORDS) + r")\b")
LEAN_DECL_RE = re.compile(
    r"^\s*(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)\b"
)


def _href_from(html: Path, target: Path) -> str:
    return os.path.relpath(target, start=html.parent).replace(os.sep, "/")


def _lean_name(label: str) -> str:
    name = re.sub(r"[^A-Za-z0-9_]+", "_", label).strip("_")
    if not name or name[0].isdigit():
        name = f"node_{name}"
    return name


def _lean_declaration_lines(lean_file: Path) -> dict[str, int]:
    if not lean_file.is_file():
        return {}
    decls: dict[str, int] = {}
    for line_no, line in enumerate(lean_file.read_text(encoding="utf-8").splitlines(), start=1):
        match = LEAN_DECL_RE.match(line)
        if match:
            decls.setdefault(match.group(1), line_no)
    return decls


def _highlight_lean_line(line: str) -> str:
    """Small dependency-free Lean highlighter for the published static viewer."""
    escaped = html.escape(line, quote=False)
    code, sep, comment = escaped.partition("--")
    code = LEAN_KEYWORD_RE.sub(r'<span class="kw">\1</span>', code)
    if sep:
        return f'{code}<span class="comment">--{comment}</span>'
    return code or " "


def render_lean_viewer(dest: Path, bp: Blueprint) -> None:
    """Render ``lean/index.html`` beside the raw saved Lean file."""
    lean_file = dest / "lean" / PUBLISHED_LEAN_NAME
    if not lean_file.is_file():
        return

    viewer = lean_file.parent / LEAN_VIEWER_NAME
    lines = lean_file.read_text(encoding="utf-8").splitlines()
    rows = []
    for number, line in enumerate(lines, start=1):
        rows.append(
            f'<tr id="L{number}">'
            f'<td class="ln"><a href="#L{number}">{number}</a></td>'
            f'<td class="code"><code>{_highlight_lean_line(line)}</code></td>'
            f'</tr>'
        )

    title = html.escape(bp.title, quote=False)
    blueprint_href = _href_from(viewer, dest / "index.html")
    landing_href = _href_from(viewer, SITE_DIR / "index.html")
    raw_href = _href_from(viewer, lean_file)
    body = "\n".join(rows) or '<tr><td class="ln"></td><td class="code"><code> </code></td></tr>'
    viewer.write_text(
        f"""<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>Lean formalization - {title}</title>
  <style>
    :root {{
      --bg: #f7f8fa;
      --panel: #ffffff;
      --ink: #18202a;
      --muted: #667085;
      --accent: #2563eb;
      --border: #d9e0e8;
      --code-bg: #fbfcfe;
      --line: #8a96a6;
      --comment: #6a7f43;
      --keyword: #7c3aed;
    }}
    * {{ box-sizing: border-box; }}
    body {{
      margin: 0;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      color: var(--ink);
      background: var(--bg);
    }}
    .wrap {{ max-width: 76rem; margin: 0 auto; padding: 1.5rem 1rem 3rem; }}
    header {{
      display: flex;
      flex-wrap: wrap;
      gap: .75rem 1rem;
      align-items: center;
      justify-content: space-between;
      margin-bottom: 1rem;
    }}
    h1 {{ font-size: 1.35rem; line-height: 1.25; margin: 0; }}
    .subtitle {{ color: var(--muted); margin: .25rem 0 0; }}
    .links {{ display: flex; flex-wrap: wrap; gap: .5rem; }}
    a {{ color: var(--accent); }}
    .btn {{
      display: inline-block;
      text-decoration: none;
      font-size: .9rem;
      padding: .35rem .65rem;
      border: 1px solid var(--border);
      border-radius: .45rem;
      background: var(--panel);
    }}
    .codebox {{
      overflow: auto;
      border: 1px solid var(--border);
      border-radius: .5rem;
      background: var(--code-bg);
    }}
    table {{ width: 100%; border-collapse: collapse; font-size: .9rem; }}
    td {{ vertical-align: top; }}
    .ln {{
      width: 1%;
      min-width: 3.2rem;
      padding: 0 .75rem;
      text-align: right;
      color: var(--line);
      border-right: 1px solid var(--border);
      user-select: none;
    }}
    .ln a {{ color: inherit; text-decoration: none; }}
    .code {{ padding: 0 .9rem; }}
    code {{
      white-space: pre;
      font-family: ui-monospace, SFMono-Regular, Menlo, Monaco, Consolas, "Liberation Mono", monospace;
      line-height: 1.55;
      tab-size: 2;
    }}
    tr:target {{ background: #eaf2ff; }}
    .kw {{ color: var(--keyword); font-weight: 600; }}
    .comment {{ color: var(--comment); font-style: italic; }}
  </style>
</head>
<body>
  <div class="wrap">
    <header>
      <div>
        <h1>Lean formalization</h1>
        <p class="subtitle">{title}</p>
      </div>
      <nav class="links" aria-label="Lean formalization links">
        <a class="btn" href="{blueprint_href}">Blueprint</a>
        <a class="btn" href="{raw_href}">Raw .lean</a>
        <a class="btn" href="{landing_href}">All blueprints</a>
      </nav>
    </header>
    <main class="codebox">
      <table aria-label="Lean source">
        <tbody>
{body}
        </tbody>
      </table>
    </main>
  </div>
</body>
</html>
""",
        encoding="utf-8",
    )


def _inject_local_lean_style(text: str) -> str:
    if LOCAL_LEAN_STYLE_MARKER in text:
        return text
    style = """
<style id="bp-local-lean-style">
  .bp-local-lean-link {
    display: inline-block;
    margin-left: .35rem;
    padding: .05rem .35rem;
    border: 1px solid #b9d5ff;
    border-radius: .35rem;
    color: #1554b7;
    background: #eef6ff;
    font: 600 .72rem/1.35 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
    text-decoration: none;
    vertical-align: middle;
  }
  .bp-local-lean-link:hover { background: #dcecff; }
</style>"""
    if "</head>" in text:
        return text.replace("</head>", style + "\n</head>", 1)
    return style + "\n" + text


def _inject_header_nav_style(text: str) -> str:
    if HEADER_NAV_STYLE_MARKER in text:
        return text
    style = """
<style id="bp-header-nav-style">
  body > header {
    gap: .5rem;
    min-height: 2.5rem;
  }
  .bp-site-nav {
    display: flex;
    flex-wrap: wrap;
    gap: .45rem;
    align-items: center;
    margin-right: auto;
  }
  .bp-site-nav a {
    display: inline-flex;
    align-items: center;
    min-height: 1.65rem;
    padding: .18rem .55rem;
    border: 1px solid #d0d7de;
    border-radius: .45rem;
    background: #ffffff;
    color: #24292e;
    text-decoration: none;
    text-shadow: none;
    font: 600 .85rem/1.2 -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
    white-space: nowrap;
  }
  .bp-site-nav a:hover {
    background: #f6f8fa;
    border-color: #afb8c1;
  }
  .bp-site-nav .bp-lean-link {
    color: #1554b7;
    border-color: #b9d5ff;
    background: #eef6ff;
  }
  .bp-site-nav .bp-lean-link:hover {
    background: #dcecff;
  }
</style>"""
    if "</head>" in text:
        return text.replace("</head>", style + "\n</head>", 1)
    return style + "\n" + text


def inject_local_lean_links(dest: Path, nodes: dict[str, Node]) -> None:
    """Add per-node links from rendered statements to generated Lean lines."""
    lean_viewer = dest / "lean" / LEAN_VIEWER_NAME
    lean_file = dest / "lean" / PUBLISHED_LEAN_NAME
    decl_lines = _lean_declaration_lines(lean_file)
    if not lean_viewer.is_file() or not decl_lines:
        return

    node_links: dict[str, tuple[str, int]] = {}
    for label, node in nodes.items():
        if node.mathlibok:
            continue
        decl = _lean_name(label)
        line = decl_lines.get(decl)
        if line is not None:
            node_links[label] = (decl, line)
    if not node_links:
        return

    for html_path in dest.rglob("*.html"):
        if html_path == lean_viewer:
            continue
        text = html_path.read_text(encoding="utf-8")
        changed = False
        href = _href_from(html_path, lean_viewer)
        for label, (decl, line) in node_links.items():
            pattern = re.compile(
                r'(<div class="[^"]*_thmwrapper[^"]*" id="'
                + re.escape(label)
                + r'">[\s\S]*?<div class="thm_header_extras">\s*)'
            )
            decl_title = html.escape(decl, quote=True)
            badge = (
                f'\n    <a class="bp-local-lean-link" '
                f'href="{href}#L{line}" '
                f'title="Generated Lean declaration {decl_title}">Lean</a>\n'
            )
            text, count = pattern.subn(r"\1" + badge, text, count=1)
            changed = changed or bool(count)
        if changed:
            text = _inject_local_lean_style(text)
            html_path.write_text(text, encoding="utf-8")


def inject_header_links(dest: Path) -> None:
    """Add landing-page and saved-Lean links to each generated HTML header."""
    lean_viewer = dest / "lean" / LEAN_VIEWER_NAME
    for html in dest.rglob("*.html"):
        if html == lean_viewer:
            continue
        text = html.read_text(encoding="utf-8")
        if "<header>" not in text:
            continue
        links: list[str] = []
        if HOME_LINK_MARKER not in text:
            links.append(f'\n<a class="bp-home-link" href="{_href_from(html, SITE_DIR / "index.html")}">← All blueprints</a>')
        if lean_viewer.is_file() and LEAN_LINK_MARKER not in text:
            links.append(f'\n<a class="bp-lean-link" href="{_href_from(html, lean_viewer)}">Lean formalization</a>')
        if links:
            nav = '\n<nav class="bp-site-nav" aria-label="Blueprint site links">' + "".join(links) + "\n</nav>"
            text = _inject_header_nav_style(text)
            text = text.replace("<header>", "<header>" + nav, 1)
            html.write_text(text, encoding="utf-8")


def copy_to_site(bp: Blueprint, nodes: dict[str, Node]) -> None:
    """Copy the rendered blueprint plus saved artifacts into ``site/<name>/``."""
    dest = SITE_DIR / bp.name
    if dest.exists():
        shutil.rmtree(dest)
    shutil.copytree(bp.web_dir, dest)

    pdf = bp.print_dir / "print.pdf"
    if bp.build_pdf and pdf.is_file():
        shutil.copy(pdf, dest / "blueprint.pdf")

    if bp.lean_dir.is_dir():
        lean_files = sorted(bp.lean_dir.glob("*.lean"))
        if lean_files:
            lean_dest = dest / "lean"
            lean_dest.mkdir(parents=True, exist_ok=True)
            for lean_file in lean_files:
                shutil.copy(lean_file, lean_dest / lean_file.name)
            render_lean_viewer(dest, bp)
            inject_local_lean_links(dest, nodes)

    inject_header_links(dest)


def build_blueprint(bp: Blueprint) -> None:
    print(f"==> {bp.name}")
    validation = validate_blueprint(REPO_ROOT, bp.name)
    print_result(validation)
    if not validation.ok:
        raise ValueError(f"blueprint validation failed for {bp.name!r}")
    if bp.build_pdf:
        build_pdf(bp)
    build_web(bp)
    copy_to_site(bp, validation.nodes)
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
        has_lean = (SITE_DIR / bp.name / "lean" / LEAN_VIEWER_NAME).is_file()
        cards.append(
            {
                "name": bp.name,
                "title": bp.title,
                "description": bp.description,
                "url": f"./{bp.name}/",
                "pdf_url": f"./{bp.name}/blueprint.pdf" if has_pdf else None,
                "lean_url": f"./{bp.name}/lean/" if has_lean else None,
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
