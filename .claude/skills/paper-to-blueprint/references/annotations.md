# leanblueprint annotation & colour cheatsheet

These are the macros the `blueprint` plasTeX plugin (loaded via `plugins=` in
`plastex.cfg`) actually understands, with the exact graph semantics. Verified
against the installed `leanblueprint/Packages/blueprint.py` and
`plastexdepgraph/Packages/depgraph.py`.

## Macros you put on theorem-like environments and proofs

| Macro | Goes on | Meaning |
|---|---|---|
| `\label{kind:slug}` | every node | the node's id; targets of `\uses`/`\ref` |
| `\uses{a, b, ...}` | statement **and/or** `proof` | draws a dependency edge from this node to each label. Put statement deps on the environment; proof deps inside `\begin{proof}` |
| `\proves{label}` | inside a `proof` | marks that this proof proves `label` (use when a proof is detached from its statement) |
| `\leanok` | statement or proof | "formalized in Lean". On a statement = stated; in its proof = proved |
| `\mathlibok` | statement | already in Mathlib (implies `\leanok`). Renders **dark green** |
| `\notready` | statement | not ready to formalize. Renders **orange** |
| `\lean{Fully.Qualified.Name}` | statement | links the node to a Lean declaration in the mathlib docs (no Lean needed to build) |
| `\discussion{N}` | statement | links to GitHub issue `N` (needs `\github{}` in `web.tex`) |

## Node colours (what the reader sees)

The colour encodes formalization state, computed from the macros above plus
whether all a node's dependencies are themselves done:

- **dark green** — `\mathlibok`: in a library (our "settled dependency" leaf).
- **green** — `\leanok`: stated/proved in Lean.
- **blue** — *can be stated*: all its `\uses` deps are done, but it isn't marked
  yet. This is what a fresh **novel** node turns once its prerequisites are
  settled — exactly what you want the paper's results to look like.
- **orange** — `\notready`.
- **white / uncoloured** — stated but some dependency is still missing.

## How this maps to the two-kind model

- **Settled dependency (in Mathlib/cslib):**
  ```latex
  \begin{definition}[Topological space]
    \label{def:topspace}
    \lean{TopologicalSpace}
    \mathlibok
    A topological space is ...                 % brief restatement, NO proof
  \end{definition}
  ```
  If you know it's in a library but not the exact decl name, keep `\mathlibok`
  and add `% TODO: confirm Lean decl name` rather than guessing a fake name.

- **Novel content (the paper's contribution / library gaps):**
  ```latex
  \begin{theorem}[Main result]
    \label{thm:main}
    \uses{def:topspace, lem:key}                % statement-level deps
    Statement, with full hypotheses ...         % NO \leanok / \mathlibok
  \end{theorem}
  \begin{proof}
    \uses{lem:key, lem:helper}                  % proof-level deps (may differ)
    Full proof, every step ...
  \end{proof}
  ```

- **Genuine gap (paper omits a proof and you cannot honestly reconstruct it):**
  ```latex
  \begin{lemma}[...]
    \label{lem:omitted}
    \uses{...}
    \notready                                   % renders orange = flagged
    Statement ...
  \end{lemma}
  % TODO: paper states this without proof ("omitted"); reconstruct or cite.
  ```

## Available theorem environments

Provided in `macros/common.tex`: `theorem`, `proposition`, `lemma`,
`corollary`, `definition` (all share the `theorem` counter), plus `proof`.
Need more (e.g. `construction`, `algorithm`, `assumption`, `example`)? Add
`\newtheorem{construction}[theorem]{Construction}` to that blueprint's
`macros/common.tex` and it becomes a graph node automatically.
