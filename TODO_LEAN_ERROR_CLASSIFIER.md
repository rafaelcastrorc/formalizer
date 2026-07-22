# TODO: Lean Error Classifier

The current Lean-guided refinement loop uses a heuristic to decide whether a
Lean failure is a bad Lean-generation attempt or evidence that the blueprint is
missing/wrong.

That is not good enough long-term.

## Problem

Some Lean errors are clearly Lean-encoding issues:

- syntax errors;
- bad imports;
- missing explicit type annotations;
- implicit argument inference failures;
- invalid projection / field notation;
- generated names that do not match local definitions.

These should usually trigger another Lean-generation attempt from the same
blueprint.

Other failures mean the blueprint itself is underspecified:

- a proof needs a lemma not present in the blueprint;
- a theorem statement is too weak/strong/wrong;
- a dependency is missing from `\uses{...}`;
- a definition in the blueprint is ambiguous or mathematically incomplete.

These should trigger blueprint repair.

The hard case is that Lean may report both categories with similar messages.
For example, `unknown identifier Foo` might mean:

- the Lean generator forgot to define/import `Foo`; or
- the blueprint forgot to introduce `Foo` as a needed node.

## Desired Classifier

Add an explicit classifier step between Lean failure and the next action:

```text
blueprint + generated Lean + Lean errors
        ↓
classifier
        ↓
one of:
  lean_generation_issue
  blueprint_issue
  ambiguous
```

## Behavior

If `lean_generation_issue`:

```text
retry Lean generation from the same blueprint
do not edit blueprint
```

If `blueprint_issue`:

```text
repair blueprint
then regenerate Lean from the repaired blueprint
```

If `ambiguous`:

```text
stop and write a report
do not mutate the blueprint automatically
```

## Classifier Output

The classifier should return structured JSON:

```json
{
  "classification": "lean_generation_issue | blueprint_issue | ambiguous",
  "confidence": "low | medium | high",
  "reason": "short explanation",
  "evidence": [
    "specific Lean error line or blueprint node",
    "specific missing definition/dependency if applicable"
  ],
  "recommended_action": "retry_lean | repair_blueprint | stop"
}
```

## Guardrails

- Never repair the blueprint from a low-confidence classification.
- Never weaken a theorem just to make Lean compile.
- Never accept a generated Lean file that uses `sorry`, `admit`, `by ?`,
  `axiom`, `constant`, or `opaque`.
- Treat classifier output as advisory; the deterministic audit still decides
  whether Lean is publishable.

## Future Integration Point

In `scripts/refine_blueprint_with_lean.py`, replace the current heuristic
`_is_lean_generation_issue(...)` decision with:

```text
classify_lean_failure(blueprint_source, lean_code, lean_output)
```

Then branch based on the structured classification.

## Related TODO: Difficulty-Aware Scheduling

The refinement loop now has a deterministic scheduler heuristic that classifies
ready blueprint nodes as `easy`, `medium`, or `hard` before forming a
dependency-closed chunk. This is intentionally simple and should be improved.

There is also a pre-refinement decomposition pass. Before the first Lean chunk,
it logs structurally suspicious unresolved nodes, asks the model whether those
nodes should be split into helper blueprint nodes, validates any resulting
blueprint edit, and records the before/after outcome. This is intentionally
bounded and still keeps the blueprint as the source of truth: if decomposition
happens, it happens in `content.tex` before Lean generation.

Current scoring signals:

- node kind:
  - theorem/corollary adds high weight;
  - lemma/proposition adds medium weight;
  - definition adds no weight by itself;
- number of explicit `\uses{...}` dependencies;
- source-block length;
- proof length;
- displayed-math and equation-like token counts;
- finite sum/product counts;
- reindexing, induction, continuity, construction, matrix, and asymptotic
  language;
- hard-keyword hits such as `reduction`, `hardness`, `runtime`, `transfer`,
  `approximation`, `tensor`, `SETH`, and `OVC`.

Current behavior:

- before chunking, a bounded prepass may ask the model to decompose the most
  suspicious unresolved nodes;
- `hard` nodes are isolated as singleton chunks;
- a small number of `medium` nodes may be batched;
- `easy` nodes may batch up to the internal chunk limit.

Telemetry now records data for these classifier families:

- pre-decomposition: candidate features/reasons, whether the prepass changed
  the blueprint, which labels changed, and node counts before/after;
- scheduling/runtime: chosen chunk, difficulty summary, timeout used, prompt
  size, model duration, timeout/error status, and final chunk outcome;
- Lean-vs-blueprint failure: generated Lean, Lean/audit output, rejected labels,
  retry/repair/decomposition routing, and downstream invalidation;
- library ranking: local candidate declaration snippets, target labels, model
  duration, Lean success/failure, and audit result.

`scripts/build_classifier_dataset.py` flattens this into JSONL tables including
`pre_decomposition_examples.jsonl`, `decision_examples.jsonl`,
`model_call_examples.jsonl`, `node_feature_examples.jsonl`, and
`repair_examples.jsonl`.

Open questions/improvements:

- Use historical run data: if a node repeatedly causes long model calls,
  statement-audit failures, or blueprint repairs, mark it hard in future runs.
- Separate "hard because mathematically deep" from "hard because the blueprint
  is underspecified"; the latter should trigger proof-text/statement repair,
  not just singleton scheduling.
- Track actual elapsed times per node/chunk and feed that back into scheduling.
- Include audit-failure categories such as tautological correctness,
  erased runtime transfer, abstract problem tags, or missing reconstruction as
  hard-node signals.
- Consider exposing the scheduler's classification in the Web UI so users can
  see why a node was isolated.
- Eventually replace the heuristic with a classifier that returns structured
  JSON, but keep deterministic fallbacks so scheduling does not require an
  extra model call.

The key invariant is that scheduling must not change the blueprint's meaning.
It only decides how much of the existing blueprint graph to send to the model at
once.
