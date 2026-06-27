# Blueprint Generation Report

Auto-generated record of the paper → blueprint runs (via the
`paper-to-blueprint` skill). Each blueprint was produced by one extraction
subagent that read the full paper, classified every item against Mathlib/cslib,
and wrote a maximally detailed `content.tex`. All seven build cleanly with no
undefined `\uses`/`\ref` targets.

## Token usage (per extraction agent)

| # | Blueprint | Paper (pages) | Tokens | Tool calls | Wall time |
|---|---|---|--:|--:|--:|
| 1 | gv-concatenated | When Do Low-Rate Concatenated Codes Approach the GV Bound? (41) | 164,295 | 48 | ~17.9 min |
| 2 | gradient-coding | Approximate Gradient Coding with Optimal Decoding (30) | 116,725 | 32 | ~10.4 min |
| 3 | magic-communication | Magic and Communication Complexity (24) | 110,885 | 36 | ~11.7 min |
| 4 | subquadratic-transformers | Fundamental Limitations on Subquadratic Alternatives to Transformers (23) | 96,270 | 19 | ~7.8 min |
| 5 | repeat-channels | Efficient Near-Optimal Codes for General Repeat Channels (14) | 85,355 | 23 | ~7.7 min |
| 6 | expander-codes | Expander Codes (Sipser–Spielman, 1996) (13) | 78,764 | 18 | ~7.2 min |
| 7 | batch-codes | Improved Batch Code Lower Bounds (8) | 68,023 | 18 | ~6.0 min |
| | **Total** | **7 papers (~153 pages)** | **720,317** | **194** | — |

Notes:
- These are the per-agent extraction costs only; main-loop orchestration tokens
  are not broken out by the harness.
- Agents ran in two parallel batches (3 then 4), so wall-clock per batch ≈ the
  slowest agent in that batch, not the sum of the column.
- Cost tracks page count and proof density closely.

## Blueprint contents

| Blueprint | Nodes | Mathlib/cslib leaves | Novel (full proof) | Edges | `\notready` |
|---|--:|--:|--:|--:|--:|
| gv-concatenated | 57 | 10 | 41 | ~93 | 6 |
| gradient-coding | 60 | 6 | 54 | ~105 | 8 |
| magic-communication | 58 | 1 | 57 | ~90 | 11 |
| subquadratic-transformers | 55 | 5 | 50 | ~92 | 3 |
| repeat-channels | 34 | 13 | 21 | ~49 | 5 |
| expander-codes | 44 | 5 | 39 | ~76 | 6 |
| batch-codes | 22 | 6 | 16 | ~34 | 0 |
| **Total** | **330** | **46** | **278** | **~539** | **39** |

(Per-agent classification; `\notready` nodes overlap the novel/leaf columns.)

## `\notready` nodes (honest gaps — external citations or paper-only sketches)

- **gv-concatenated (6):** `thm:gv-bound` (classical GV bound), `lem:self-dual-basis`,
  `lem:poisson-splitting`, `lem:poisson-chernoff`, `lem:h2-inv-upper`, `lem:h2-inv-lower`.
- **gradient-coding (8):** incl. `lem:trace-psd` (Kleinman–Athans), `lem:cocoercivity`
  (Needell et al.), `lem:expander-mixing` (HLW), `lem:linear-time-decode`,
  `prop:random-lower-remark`, `prop:lower-robust`.
- **magic-communication (11):** `thm:speelman-nlqc`, `lem:gh-instantaneous`,
  `lem:gh-xor`, `lem:equality-dpar`, `lem:equality-rpar`, `lem:index-rac`,
  `lem:forr-r-lb`, `lem:abcd-r-lb`, `constr:forr-protocol`, `prop:relational-sim`,
  `prop:tdepth-lb`.
- **subquadratic-transformers (3):** `thm:seth-implies-ovc` (Williams 2005),
  `thm:additive-maxip-karthik` (Karthik–Manurangsi 2020), `thm:additive-bmaxip-to-ov` (Chen 2020).
- **repeat-channels (5):** `thm:gen-shannon` (Dobrushin), `thm:outer-code` (HS17/HRS19),
  `thm:dobrushin-main`, `lem:tdc-rate`, `lem:buffer-balance` (last three: paper gives only sketches).
- **expander-codes (6):** `thm:lps-margulis`, `prop:lps-construct`, `lem:alon-chung`,
  `lem:kahale`, `lem:gilbert-varshamov`, `thm:alon-general` (paper gives only a sketch).
- **batch-codes:** none — every result fully reconstructed.

## Known caveats / things to verify

- **Unconfirmed `\lean{}` decl names:** many Mathlib leaves carry
  `% TODO: confirm Lean decl name` — the concept is standard but the exact
  declaration name was not verified against current Mathlib.
- **`Real.binEntropy`** (used in gv-concatenated, expander-codes,
  magic-communication): Mathlib's version uses natural log; these papers use
  base-2 (constant-factor difference) — note when formalizing.
- **repeat-channels information-theory leaves** (`def:entropy`, `def:cond-entropy`,
  `def:mutual-info`, `lem:entropy-chain-rule`, `thm:birkhoff`) are marked
  `\mathlibok`, but general measure-theoretic mutual information may not be in
  Mathlib yet — re-check before trusting the dark-green status.
- **gradient-coding** had one dependency cycle (`thm:random-main` ↔
  `lem:moment-bound`); resolved by dropping the redundant statement-level
  back-edge (graph must be acyclic).

## Process notes

- Extraction used the `.claude/skills/paper-to-blueprint` skill.
- Theorem environments: only the five built-in graph types (definition, lemma,
  proposition, theorem, corollary) were used; paper-specific kinds
  ("Claim/Construction/Observation") were mapped onto these with the original
  label preserved in the node title, to avoid the fragile `thms=` package option.
