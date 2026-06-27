# Blueprint Evaluation Report

Each of the seven blueprints was reviewed by an independent adversarial agent
that read the full source paper and graded the generated `content.tex` against
it. Reviewers actively hunted for hallucinated math, dropped results,
misclassified library leaves, and broken dependency edges. They were read-only;
nothing was modified.

## Scores

| Blueprint | Score | Grade | Faith. | Compl. | Proof | Classif. | Graph | Honesty |
|---|--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| magic-communication | 88 | A−/B+ | 5 | 5 | 4 | 4 | 4 | 4 |
| gv-concatenated | 88 | A− | 5 | 5 | 4 | 5 | 5 | 4 |
| expander-codes | 86 | B+ | 4 | 5 | 3 | 4 | 5 | 5 |
| gradient-coding | 86 | B+ | 5 | 4 | 5 | 3 | 3 | 4 |
| batch-codes | 85 | B+ | 4 | 5 | 4 | 3 | 5 | 4 |
| subquadratic-transformers | 82 | B | 4 | 5 | 3 | 3 | 4 | 5 |
| repeat-channels | 72 | C+ | 4 | 5 | 4 | 2 | 5 | 2 |
| **Average** | **84** | **B** | 4.4 | 4.9 | 3.9 | 3.4 | 4.4 | 4.0 |

(Dimensions each scored /5: Faithfulness, Completeness, Proof detail &
correctness, Mathlib/cslib classification, Dependency-graph integrity,
Annotation honesty.)

## Headline finding

**No blueprint contained hallucinated/fabricated mathematics at the level of
main results.** Statements, hypotheses, constants, and the core proofs were
transcribed faithfully (Faithfulness and Completeness average 4.4 and 4.9).
The systematic weak spot is **Mathlib/cslib classification** (avg 3.4): the
"is this actually in the library, and what is the exact declaration name?"
judgment is unreliable — unsurprising since no Lean is installed and the
agents guessed decl names. The second theme is a handful of **true-but-misproved
or garbled derivation steps** that do not change any final result.

## Cross-cutting issues (ranked by impact)

### 1. Over-eager `\mathlibok` with wrong / nonexistent declarations
- **repeat-channels (most severe):** Shannon `def:entropy`, `def:cond-entropy`,
  `def:mutual-info`, `lem:entropy-chain-rule`, and Birkhoff's pointwise ergodic
  theorem `thm:birkhoff` are marked `\mathlibok` but are **not in Mathlib**
  (verified via Loogle). They are load-bearing for the capacity arguments, so a
  formalizer would be badly misled. Also `def:edit-distance` cites a nonexistent
  `Nat.levenshtein` and conflates indel distance with substitution-allowing
  Levenshtein.
- **subquadratic-transformers:** `lem:kron-inner` cites `Matrix.dotProduct_kronecker`,
  which does **not exist**; `def:kron` points at the *matrix* Kronecker map for a
  flattened *vector* product.
- **batch-codes:** `lem:dual-dim` cites the inner-product-space lemma
  `Subspace.finrank_add_finrank_orthogonal` (wrong namespace; inapplicable over
  a finite field — the bilinear-form version is needed).
- **gradient-coding:** `lem:chernoff` (multiplicative Chernoff) and `lem:stirling`
  are derived inequalities, not single Mathlib decls; should be novel/`\notready`.
- **gv-concatenated:** `lem:tv-distance` links `Measure.totalVariation` (returns a
  measure), not the scalar ½·L¹ distance the node states.
- **Base-2 vs natural-log `Real.binEntropy`** (gv-concatenated, expander-codes,
  magic-communication): all three link Mathlib's natural-log `binEntropy` for a
  base-2 quantity. In **magic-communication** this is not merely a constant
  factor — used as-is it would make `lem:index-rac` and `lem:multiplex-bound`
  **false**.

*Note: every one of these carries a `% TODO: confirm` flag, so they are honestly
marked as uncertain — but the dark-green "in a library" status is misleading.*

### 2. True-but-misproved or garbled steps (final results unaffected)
- **gv-concatenated** `lem:entropy-binom-lower`: the bound is true (via Stirling)
  but the written step `1/(n+1) ≥ 1/√(2n)` is false — the proof as written is invalid.
- **subquadratic-transformers** `lem:additive-msd-maxip-equiv` (Lemma B.5): the
  padding construction is mis-transcribed (wrong zero/one blocks), breaking the
  claimed inner-product preservation; the conclusion is still true.
- **expander-codes:** three garbled lines — an inverted threshold fraction in
  `lem:distance-eigenvalue`, a leftover wrong intermediate in `thm:explicit`, and
  a self-contradictory `δ = 3/4+ε … so δ > 3/4+ε` in `thm:parallel-correct`.
  All final bounds are correct.
- **batch-codes** `lem:e-good`: statement omits the "indices distinct" hypothesis
  that its own proof uses (false as stated; satisfied at the only call site).
- **repeat-channels** `thm:main`: a parenthetical calls a deletion+insertion
  "edit distance 3" (it is 2; the paper's correct count is two deletions + one
  insertion = 3). Total `kδ` unaffected.

### 3. Dependency-graph defects (mostly isolated to one blueprint)
- **gradient-coding (significant):** `thm:random-main`'s proof `\uses` omits
  `lem:nonbipartite-one`, which is the *only* link from the entire "Characterization
  of α*" chapter to the main theorem — leaving that chapter effectively dangling.
  `thm:sparsification` similarly omits `lem:claim-frontier`, and there is one
  spurious edge. (The earlier cycle fix was confirmed correct.)
- **subquadratic-transformers:** `def:bow` is an orphan (defined, never used).
- **magic-communication:** `thm:q-to-psm`'s proof omits `def:magic-gate` from its
  `\uses` though it invokes the TX=PXT relation; `lem:model-comparison` is an orphan.
- **gv-concatenated:** `lem:trace-inner-product` is an orphan.
- All blueprints: **zero dangling `\uses` targets and zero cycles** — every
  reference resolves and the DAGs are acyclic (graph dimension avg 4.4).

### 4. Annotation honesty — mostly good, a few sketch-as-proof lapses
- `\notready` is genuinely reserved for externally-cited / paper-sketched results
  almost everywhere (subquadratic-transformers and expander-codes: 5/5).
- Lapses: **gv-concatenated** `prop:rlc-smooth` and **magic-communication**
  `prop:relational-sim` / `prop:tdepth-lb` present sketch-level arguments as
  complete (the magic ones are in-paper remarks that should be short full nodes,
  not `\notready`). **repeat-channels** scores low here only because the
  misclassified leaves assert library membership they lack.

## Per-blueprint top fixes

- **repeat-channels (72):** reclassify the 5 info-theory leaves as novel/`\notready`
  (not in Mathlib); fix `def:edit-distance` decl + indel semantics; fix the
  `thm:main` "edit distance 3" parenthetical.
- **subquadratic-transformers (82):** fix the Lemma B.5 padding construction; make
  `lem:kron-inner` a novel node (drop the fabricated decl); wire or drop `def:bow`.
- **batch-codes (85):** fix `lem:dual-dim` Lean reference (bilinear-form version);
  add the distinctness hypothesis to `lem:e-good`.
- **gradient-coding (86):** add the two missing proof edges (`lem:nonbipartite-one`
  → `thm:random-main`, `lem:claim-frontier` → `thm:sparsification`); reclassify
  `lem:chernoff`/`lem:stirling`.
- **expander-codes (86):** fix the three garbled derivation lines; add a `\lean{}`
  name to `lem:azuma` (or drop `\mathlibok` pending confirmation).
- **gv-concatenated (88):** fix the `lem:entropy-binom-lower` proof step; re-link
  `lem:tv-distance`; mark `prop:rlc-smooth` `\notready`.
- **magic-communication (88):** address the base-2 entropy problem (it makes two
  dependent bounds false as linked); convert the two in-paper `\notready` remarks
  to short full nodes; add the missing `def:magic-gate` proof edge.

## Bottom line

The blueprints are **faithful and complete reconstructions** of the papers'
logical skeletons, with clean, acyclic dependency graphs and honest gap-flagging.
They are suitable as formalization roadmaps today, with one caveat: **treat every
`\mathlibok` leaf as unverified** until its declaration name is checked against
current Mathlib — that is where essentially all of the real errors concentrate.
A second pass fixing the ~5 misproved-but-true steps and the
repeat-channels/gradient-coding issues would lift the set to a solid A−.
