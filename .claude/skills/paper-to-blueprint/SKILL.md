---
name: paper-to-blueprint
description: >-
  Generate a leanblueprint-style blueprint for THIS repo from a math or CS
  paper. Reads the paper (PDF path, arXiv/URL, or pasted text), extracts EVERY
  definition, lemma, proposition, theorem, corollary, construction and proof,
  marks anything already in Mathlib or cslib as a settled dependency, and writes
  out everything else as full, granular blueprint nodes with a complete \uses
  dependency graph — as detailed as possible. Use whenever the user hands over a
  paper and wants a blueprint generated under blueprints/<name>/.
---

# Paper → Blueprint generator

Turn a research paper into a `blueprints/<name>/` folder of this repo: a
plasTeX/leanblueprint document whose dependency graph captures the paper's whole
logical skeleton. The guiding rule from the user:

> **Put in everything that is NOT already in Mathlib or cslib, and make it as
> detailed as possible.**

This skill only produces the blueprint *source* (LaTeX). It never installs or
runs Lean — consistent with this repo's design (see the top-level `README.md`
and `blueprint.md`).

## The core model — two kinds of node

Every mathematical item in the paper becomes a graph node of one of two kinds:

1. **Settled dependency** — the statement already exists in **Mathlib** or
   **cslib**. Emit it as a *leaf*: a short re-statement with `\mathlibok` and a
   `\lean{Fully.Qualified.Name}` link, and **no proof**. It renders dark green
   ("in a library") and anchors the edges that the paper's results depend on.
   Do not re-prove library facts.

2. **Novel content** — anything NOT in Mathlib/cslib (this is the paper's actual
   contribution, plus any folklore/standard results the libraries happen to lack).
   Emit it in **full**: precise statement, all hypotheses, `\label`, `\uses{...}`,
   and a **complete proof** in a `proof` environment with its own `\uses{...}`.
   Do **not** mark these `\leanok`/`\mathlibok` — they are the work to be
   formalized, so they should render blue/white in the graph.

When you are unsure whether something is in a library, **treat it as novel and
include it in full.** Over-inclusion is the correct failure mode here; the whole
point is to capture everything the paper actually needs.

Read `references/annotations.md` for the exact macro + colour semantics, and
`references/example-content.tex` for a model of well-structured output.

## Inputs

The user may give you any of:
- a **PDF path** → read it with the `Read` tool (`pages` for >10pp; read it ALL),
- an **arXiv abstract/PDF URL or other link** → fetch with `WebFetch` (prefer the
  HTML/`ar5iv` version for clean math; fall back to the PDF),
- **pasted LaTeX/text**.

If no paper is supplied, ask for one. If only a title is given, ask for the
file/URL — do not reconstruct a paper from memory.

## Workflow

### 1. Read the paper completely
Read the entire paper before writing anything — definitions in §2 are used by
proofs in §6. Note the title, authors, and a one-line thesis (for `meta.yml` and
the landing card). Capture the paper's URL if you have one (it becomes `\home`).

### 2. Build a complete inventory
List **every** numbered or named item, in dependency order where possible:
definitions, notation/assumptions that carry logical weight, lemmas,
propositions, theorems, corollaries, named constructions/algorithms, and **each
proof**. Give every item a stable label (see Conventions). Miss nothing — a
"clearly" or "it is easy to see" still gets a node.

For a **large paper** (say >15 items or many sections), fan out: spawn one
`Explore`/`general-purpose` subagent per section to return that section's items
as structured data (label, kind, statement, hypotheses, dependencies, proof
sketch, and a guess at Mathlib/cslib membership), then merge. Keep extraction
faithful — subagents transcribe and structure, they do not invent mathematics.

### 3. Classify each item against Mathlib / cslib
For each item decide **settled** vs **novel** (see references for how to phrase
each). To check library membership, in rough order of trust:
- your own knowledge of Mathlib/cslib contents;
- **Loogle** (`https://loogle.lean-lang.org/`) / **Moogle** for Mathlib by
  statement shape or name (via `WebFetch`/`WebSearch`);
- search the **cslib** repository for CS results (process calculi, λ-calculus,
  type systems, semantics, automata, etc.) — `WebSearch` for
  `cslib lean <concept>` and read the repo;
- a general `WebSearch` to confirm a result is genuinely standard.

Record, for settled items, the exact Lean declaration name to put in `\lean{}`
when you are confident; if you know it's in a library but not the exact name,
still mark `\mathlibok` and add a `% TODO: confirm decl name` comment rather than
guessing a name that may not exist.

### 4. Build the dependency DAG
For each node, list what its **statement** uses and what its **proof** uses
(these can differ — put statement deps on the environment, proof deps inside the
`proof`). Every edge must point at a real `\label`. Prefer a fine-grained graph:
if a proof has independently meaningful steps, split them into their own lemmas
so the structure (and the eventual formalization) is granular.

### 5. Scaffold the blueprint
Pick a short url-safe `name` (kebab-case, e.g. an author/keyword). Then, from the
repo root, using the project's Python (see **Environment** below):

```
<py> scripts/new_blueprint.py <name> \
  --title "<Paper title>" \
  --description "<one-line thesis>"
```

(Add `--home <paper-url>` / `--github <repo>` if you have them; add `--build-pdf`
only if the user wants a PDF — it requires TeX.)

### 6. Write the content
- Overwrite `blueprints/<name>/blueprint/src/content.tex` with the full extracted
  material, organised into `\chapter{}`s mirroring the paper. Follow
  `references/example-content.tex`.
- Set `\title{}`/`\author{}` in both `web.tex` and `print.tex`. If you have the
  paper URL, uncomment/add `\home{<url>}` in `web.tex`.
- If the paper needs theorem-like environments beyond the five provided
  (`theorem, proposition, lemma, corollary, definition`), add e.g.
  `\newtheorem{construction}[theorem]{Construction}` to
  `blueprints/<name>/blueprint/src/macros/common.tex` so they appear as graph
  nodes. Use `$...$`/`\[...\]` for math (matches the repo).

### 7. Build and verify
Incremental build (keeps other blueprints):

```
<py> scripts/build.py <name>
```

Then verify, and treat warnings as defects to fix:
- exit status `ok -> site/<name>/`;
- `site/<name>/dep_graph_document.html` contains the expected node labels and a
  plausible edge count (grep for your `def:`/`lem:`/`thm:` labels and `->`);
- **no undefined `\uses`/`\ref` targets** in the plasTeX log (a typo'd label
  silently drops an edge) — every label referenced must be defined;
- spot-check a content page renders the math.

Optionally `cd site && <py> -m http.server` to preview at `localhost:8000`.

### 8. Report
Tell the user: the `name`/URL subpath, counts (total nodes, # marked
Mathlib/cslib vs # novel, # edges), anything marked `\notready` or left with a
`% TODO` (e.g. proofs the paper omitted and you could not reconstruct), and any
Lean decl names you could not confirm. Offer to refine, add a PDF, or push.

## "As detailed as possible" checklist
- One node per logical unit — don't bundle several results into one theorem.
- Full hypotheses, exact quantifiers, and definitions of all notation used.
- Write out **every** proof, including steps the paper calls trivial. If a proof
  is genuinely omitted and you cannot honestly reconstruct it, create the node,
  mark it `\notready`, and leave a `% TODO` describing the gap — never invent a
  proof and never silently drop the result.
- Split multi-step proofs into sub-lemmas so the graph is granular.
- **Formalizability granularity (hard rule):** every node must be individually
  formalizable as ONE Lean declaration with 1-1 structural correspondence to
  its statement. Never emit "witness package" / "interface" mega-nodes that
  bundle a recursive construction, several correctness equations, and a
  runtime/transfer claim into one lemma — downstream Lean verification treats
  the blueprint as the source of truth, so a node that needs unstated helper
  statements to formalize is a malformed node. Break such content into
  separate definition/lemma nodes up front (the construction, each correctness
  equation, each transfer claim) and wire them with `\uses`. Rule of thumb:
  if a statement needs more than ~4 named fields or equations, decompose it.
- Wire **every** dependency with `\uses` (statement-level and proof-level).
- Keep the paper's numbering/names in node titles so a reader can cross-reference.

## Environment
Use the project's Python that has `requirements.txt` installed. Detect it:
prefer `./.venv/bin/python` if present; else use a `python3` for which
`python3 -c "import plasTeX, yaml, jinja2"` succeeds. If none works, tell the
user to run `python -m venv .venv && .venv/bin/pip install -r requirements.txt`
(plus system `graphviz`/`libgraphviz-dev`, **and a LaTeX install** — plasTeX
needs `kpsewhich` + the class/package files to resolve `\documentclass` and
`\usepackage`, even though math is rendered client-side by MathJax; on
Debian/Ubuntu: `texlive-latex-base texlive-latex-recommended
texlive-fonts-recommended texlive-latex-extra`) and stop. Never install or
invoke Lean, elan, lake, or Mathlib.

## Conventions
- Labels by kind: `def:`, `lem:`, `prop:`, `thm:`, `cor:`, `constr:`, `alg:`,
  `assumption:`, plus a short slug (`thm:main`, `lem:subst-lemma`). Stable and
  unique within the blueprint.
- One `\chapter` per major paper section; keep statements in `content.tex` only
  (no `\begin{document}` — `web.tex`/`print.tex` supply that).
- `name` (folder/URL) is lowercase `[a-z0-9._-]`, starting alphanumeric.
