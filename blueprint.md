# Spec: Multi-Blueprint Static Host (no Lean toolchain)

## Goal
Build a repo that compiles and hosts **multiple Lean-style "blueprints"** (the LaTeX → web + PDF documents with dependency graphs produced by `leanblueprint`/plasTeX), **without ever installing or compiling Lean**. One push → all blueprints rebuilt and deployed to a single static site, each at its own subpath, with a landing page linking to them.

## Background you must respect
- `leanblueprint` is a plasTeX plugin. Its document builds (`leanblueprint web`, `leanblueprint pdf`) need **no Lean**. Only `leanblueprint checkdecls` needs a compiled Lean project — we never run it.
- The blueprint's dependency graph is generated purely from LaTeX `\uses{}` macros. `\lean{}` / `\leanok` / `\mathlibok` are just annotations; with no Lean present they are not verified, which is intended.
- A blueprint build only needs the `blueprint/src/` file layout. It does **not** need a `lake`/Lean project, a lakefile, or elan.
- plasTeX renders web math via MathJax (client-side), so the **web** build likely needs no TeX install at all. TeX (texlive) is only needed for (a) the PDF and (b) bibliographies (plasTeX does not call BibTeX — for a web bibliography you must run `leanblueprint pdf` once before `leanblueprint web`).

## Non-goals (out of scope for this task)
- No Lean / elan / lake / Mathlib cache / doc-gen4 anywhere. Not in CI, not locally.
- No `checkdecls`.
- The "read a paper → generate a blueprint" generator is a **future** task. Design the layout so a generated blueprint is just one more `blueprints/<name>/` folder, but do not build the generator now.

## Tech stack (pin these)
- Python 3.11+
- `requirements.txt`:
  ```
  leanblueprint        # pulls in plastex, plastexdepgraph, pygraphviz
  pyyaml               # read per-blueprint meta.yml
  jinja2               # render the landing page
  ```
- System packages (CI + local): `graphviz`, `libgraphviz-dev`. Add a minimal TeX install **only if** PDF output or bibliographies are wanted (start without it and confirm web builds succeed).

## Repo layout to create
```
.
├── blueprints/
│   ├── demo/                      # a working example blueprint (see "Demo content" below)
│   │   ├── meta.yml
│   │   └── blueprint/
│   │       ├── plastex.cfg        # optional; config may instead live in web.tex preamble
│   │       └── src/
│   │           ├── web.tex
│   │           ├── print.tex
│   │           ├── content.tex
│   │           └── macros/
│   │               ├── common.tex
│   │               ├── web.tex
│   │               └── print.tex
│   └── (more blueprints, same shape)
├── templates/
│   └── blueprint-skeleton/        # clean copy of the blueprint/ + meta.yml above, used by new-blueprint script
├── scripts/
│   ├── build.py                   # build all blueprints + landing page into site/
│   └── new_blueprint.py           # scaffold a new blueprints/<name>/ from the skeleton
├── site/                          # GENERATED output (gitignored). build target.
├── .github/workflows/deploy.yml
├── requirements.txt
├── .gitignore                     # ignore site/, blueprints/*/blueprint/web/, blueprints/*/blueprint/print/
└── README.md
```

## Per-blueprint `meta.yml` schema
```yaml
name: demo                 # must match folder name; used as the URL subpath
title: "Demo Blueprint"    # shown on landing page
description: "A short one-line description."
build_pdf: false           # if true, also build + link the PDF (requires TeX in CI)
home: ""                   # optional URL for the blueprint's "home" button (\home)
github: ""                 # optional repo URL (\github)
```

## `scripts/build.py` behavior
For each directory `blueprints/<name>/` that contains `blueprint/src/web.tex`:
1. Load `blueprints/<name>/meta.yml`.
2. `cd blueprints/<name>/blueprint`.
3. If `meta.build_pdf` is true: run `leanblueprint pdf` (needs TeX). Always do PDF before web when a bibliography exists.
4. Run `leanblueprint web`.
   - **Primary:** `leanblueprint web` from inside the `blueprint/` dir.
   - **Fallback** (if it errors expecting a Lean/lake project, git remote, or similar): invoke plasTeX directly per the leanblueprint/plastexdepgraph docs, e.g. `plastex --plugins=leanblueprint src/web.tex` with the appropriate output-dir flag. Determine which of the two works in this environment and standardize the script on it; document the choice in README.
5. Copy the generated web output (default `blueprint/web/`) → `site/<name>/`.
6. If a PDF was built, glob for it under `blueprint/print/` and copy it to `site/<name>/blueprint.pdf`.
7. Return to repo root.

After all blueprints are built, render `site/index.html` from a Jinja2 template listing every blueprint as a card/link (`title`, `description`, link to `./<name>/`, and a PDF link when present). Keep the landing page a single self-contained HTML file (inline CSS, no build step, no external runtime deps).

The script must be idempotent and safe to run repeatedly: clear/recreate `site/` at the start.

## `scripts/new_blueprint.py` behavior
- Usage: `python scripts/new_blueprint.py <name> --title "..." --description "..."`
- Copy `templates/blueprint-skeleton/` → `blueprints/<name>/`, then write `blueprints/<name>/meta.yml` with the provided fields and `name: <name>`.
- Do not touch anything else. Print the path and a reminder to edit `content.tex`.

## CI: `.github/workflows/deploy.yml`
- Trigger: push to `main` (+ `workflow_dispatch`).
- Single Ubuntu job. **No Lean, no elan, no lake, no Mathlib cache.**
- Steps:
  1. `actions/checkout`
  2. `actions/setup-python` (3.11+), with pip caching keyed on `requirements.txt`.
  3. `sudo apt-get update && sudo apt-get install -y graphviz libgraphviz-dev` (add a minimal texlive set **only if** any `meta.build_pdf: true`).
  4. `pip install -r requirements.txt`
  5. `python scripts/build.py`
  6. Deploy `site/` to GitHub Pages using the official Pages flow: `actions/configure-pages`, `actions/upload-pages-artifact` (path `site`), `actions/deploy-pages`.
- Set `permissions: { pages: write, id-token: write, contents: read }` and a `concurrency` group so overlapping pushes don't clash.
- README must note: in repo Settings → Pages, set Source = "GitHub Actions".

## Demo content (seed `blueprints/demo/` and the skeleton)
`content.tex` must include at least two linked nodes so the dependency graph renders, e.g. a definition with a `\label`, and a theorem that `\uses{}` it and is marked `\leanok`. Keep `web.tex`/`print.tex`/`macros/*` as the standard leanblueprint layout (you can generate a throwaway one with `leanblueprint new` in a scratch dir to copy the canonical files, then delete all Lean/lake/CI artifacts it created — keep only `blueprint/`). Confirm the demo graph shows nodes and an edge.

## Acceptance criteria
1. `pip install -r requirements.txt` + `apt install graphviz libgraphviz-dev` is sufficient to build — **no Lean present on the machine.**
2. `python scripts/build.py` produces `site/index.html` plus `site/<name>/index.html` for every blueprint, each with a working interactive dependency graph.
3. Local preview works: `python scripts/build.py && (cd site && python -m http.server)` serves the landing page and every blueprint with correct relative links and assets.
4. `python scripts/new_blueprint.py foo --title "Foo"` then a rebuild publishes `site/foo/` with no other edits.
5. On push to `main`, CI builds and deploys to Pages, and the **web-only** build (no `build_pdf`) completes in roughly a minute or less (sanity check that nothing Lean-related is being installed).

## Gotchas to handle
- Relative paths only: do not hardcode absolute root paths in the landing page or assume the site root — everything is served under a subpath on GitHub Pages.
- Bibliography: if any blueprint has one, that blueprint needs `leanblueprint pdf` before `leanblueprint web`, and therefore TeX in CI.
- `blueprint/web/` and `blueprint/print/` are build artifacts — gitignore them; only `site/` is the deploy target (and that's gitignored too, produced fresh in CI).
