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
