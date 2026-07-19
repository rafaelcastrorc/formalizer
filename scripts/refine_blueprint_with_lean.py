#!/usr/bin/env python3
"""Refine a blueprint by using Lean as the critic.

This is the author/critic loop:

1. validate the current blueprint;
2. ask a model to generate a disposable Lean file from the blueprint only;
3. run Lean through this repo's Lake project;
4. if Lean fails, ask the model to fix the blueprint, not the Lean file;
5. repeat until Lean passes or ``--max-trials`` is exhausted.

Lean code is not the source of truth here. The generated files under
``.auto-blueprint/formalization/`` are test artifacts and are overwritten across
trials. A failed proof should cause better blueprint statements, hypotheses,
dependencies, or intermediate lemmas.
"""
from __future__ import annotations

import argparse
<<<<<<< Updated upstream
=======
import contextlib
import hashlib
import json
import os
>>>>>>> Stashed changes
import re
import shlex
import subprocess
import sys
import time
from dataclasses import dataclass
from pathlib import Path

from generate_blueprint import _extract_json, read_paper
from model_runners import RunnerError, get_runner
from validate_blueprint import Node, print_result, validate_blueprint

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
SKILL_PATH = REPO_ROOT / ".claude" / "skills" / "paper-to-blueprint" / "SKILL.md"
SCRATCH_DIR = REPO_ROOT / ".auto-blueprint" / "formalization"
PUBLISHED_LEAN_NAME = "formalization.lean"
FORBIDDEN_LEAN_PLACEHOLDERS = re.compile(r"\b(sorry|admit)\b|by\s*\?")


@dataclass
class LeanAttempt:
    ok: bool
    command: list[str]
    stdout: str = ""
    stderr: str = ""
    reason: str = ""

    @property
    def output(self) -> str:
        return "\n".join(part for part in (self.reason, self.stdout, self.stderr) if part).strip()


def _read_blueprint_source(name: str) -> str:
    src = REPO_ROOT / "blueprints" / name / "blueprint" / "src"
    content = src / "content.tex"
    if not content.is_file():
        raise FileNotFoundError(f"{content.relative_to(REPO_ROOT)} does not exist")
    parts = [f"% FILE: {content.relative_to(REPO_ROOT)}\n{content.read_text(encoding='utf-8')}"]
    common = src / "macros" / "common.tex"
    if common.is_file():
        parts.append(f"% FILE: {common.relative_to(REPO_ROOT)}\n{common.read_text(encoding='utf-8')}")
    return "\n\n".join(parts)


def _lean_name(label: str) -> str:
    name = re.sub(r"[^A-Za-z0-9_]+", "_", label).strip("_")
    if not name or name[0].isdigit():
        name = f"node_{name}"
    return name


def _node_summary(nodes: dict[str, Node]) -> str:
    lines: list[str] = []
    for label, node in sorted(nodes.items(), key=lambda item: (item[1].file, item[1].line, item[0])):
        uses = ", ".join(sorted(node.uses)) or "(none)"
        lean_decl = node.lean_decl or ""
        lines.append(
            f"- {label}: {node.kind}, Lean name `{_lean_name(label)}`, "
            f"uses [{uses}], settled decl `{lean_decl}`"
        )
    return "\n".join(lines)


<<<<<<< Updated upstream
=======
def _node_order(nodes: dict[str, Node]) -> list[str]:
    return [
        label
        for label, _node in sorted(
            nodes.items(),
            key=lambda item: (str(item[1].file), item[1].line, item[0]),
        )
    ]


HARD_NODE_KEYWORDS = (
    "approximation",
    "bichromatic",
    "correctness",
    "hardness",
    "lower bound",
    "ovc",
    "reconstruction",
    "reduction",
    "runtime",
    "seth",
    "tensor",
    "transfer",
)


def _node_difficulty(label: str, node: Node, block: str) -> str:
    """Classify a blueprint node for scheduling, not for mathematical meaning."""
    text = f"{label}\n{node.kind}\n{block}".lower()
    score = 0
    if node.kind in {"theorem", "corollary"}:
        score += 5
    elif node.kind in {"lemma", "proposition"}:
        score += 2
    score += min(len(node.uses), 6) // 2
    if len(block) > 3500:
        score += 3
    elif len(block) > 1800:
        score += 1
    score += sum(1 for keyword in HARD_NODE_KEYWORDS if keyword in text)

    if score >= 6:
        return "hard"
    if score >= 3:
        return "medium"
    return "easy"


def _next_chunk(nodes: dict[str, Node], accepted: set[str], *, chunk_size: int) -> list[str]:
    """Pick a dependency-closed chunk, batching easy nodes and isolating hard ones."""
    available = set(accepted) | {label for label, node in nodes.items() if node.mathlibok}
    remaining = [label for label in _node_order(nodes) if label not in available]
    blocks = _node_tex_blocks(nodes)
    difficulties = {
        label: _node_difficulty(label, node, blocks.get(label, ""))
        for label, node in nodes.items()
    }
    chunk: list[str] = []
    progressed = True
    while progressed and len(chunk) < chunk_size:
        progressed = False
        for label in remaining:
            if label in chunk:
                continue
            node = nodes[label]
            if not node.uses <= (available | set(chunk)):
                continue

            difficulty = difficulties[label]
            if difficulty == "hard":
                # If a hard node is the first ready obligation, isolate it.
                # If easy/medium nodes are already in this chunk, leave the
                # hard node for the next pass instead of mixing obligations.
                if not chunk:
                    chunk.append(label)
                return chunk

            medium_count = sum(1 for item in chunk if difficulties[item] == "medium")
            if difficulty == "medium" and medium_count >= MEDIUM_NODES_PER_CHUNK:
                return chunk

            chunk.append(label)
            progressed = True
            if len(chunk) >= chunk_size:
                break
    return chunk


def _chunk_summary(nodes: dict[str, Node], labels: list[str]) -> str:
    return _node_summary({label: nodes[label] for label in labels})


def _chunk_difficulty_summary(nodes: dict[str, Node], labels: list[str]) -> str:
    blocks = _node_tex_blocks({label: nodes[label] for label in labels})
    return ", ".join(
        f"{label}={_node_difficulty(label, nodes[label], blocks.get(label, ''))}"
        for label in labels
    )


def _node_fingerprints(nodes: dict[str, Node]) -> dict[str, str]:
    blocks = _node_tex_blocks(nodes)
    return {
        label: hashlib.sha256(blocks.get(label, "").encode("utf-8")).hexdigest()
        for label in nodes
    }


def _dependency_descendants(nodes: dict[str, Node], changed: set[str]) -> set[str]:
    """Return labels whose transitive dependencies include any changed label."""
    affected = set(changed)
    progressed = True
    while progressed:
        progressed = False
        for label, node in nodes.items():
            if label in affected:
                continue
            if node.uses & affected:
                affected.add(label)
                progressed = True
    return affected


def _dependency_descendants_within(nodes: dict[str, Node], changed: set[str], universe: set[str]) -> set[str]:
    """Return changed labels plus their blueprint descendants inside ``universe``."""
    return _dependency_descendants(nodes, changed) & universe


def _dependency_closure(nodes: dict[str, Node], labels: list[str]) -> set[str]:
    """Return all transitive blueprint dependencies of the supplied labels."""
    seen: set[str] = set()
    stack = list(labels)
    while stack:
        label = stack.pop()
        node = nodes.get(label)
        if node is None:
            continue
        for dep in node.uses:
            if dep not in nodes or dep in seen:
                continue
            seen.add(dep)
            stack.append(dep)
    return seen


def _nonmathlib_uses_missing_from_decl(
    label: str,
    node: Node,
    decl: LeanDecl,
    nodes: dict[str, Node],
    decls: dict[str, LeanDecl],
) -> list[str]:
    """Find explicit blueprint dependencies not visible in this Lean declaration.

    ``\\uses`` is the blueprint's public dependency contract. For generated
    declarations corresponding to blueprint nodes, the Lean statement/body
    should mention each non-Mathlib dependency's generated declaration name,
    either directly or through a same-module helper structure/result type used
    by that declaration. This catches ignored dependencies without rejecting
    patterns like ``def def_msd : MSDData := ...`` where ``MSDData`` carries the
    dependency field type.
    """
    visible_text = _decl_text_with_local_helpers(decl, decls)
    missing: list[str] = []
    for dep in sorted(node.uses):
        dep_node = nodes.get(dep)
        if dep_node is None or dep_node.mathlibok:
            continue
        dep_name = _lean_name(dep)
        if not re.search(rf"\b{re.escape(dep_name)}\b", visible_text):
            missing.append(dep)
    return missing


def _decl_text_with_local_helpers(decl: LeanDecl, decls: dict[str, LeanDecl], *, max_depth: int = 2) -> str:
    """Return declaration text plus nearby helper declarations it references.

    This is a conservative local approximation of the Lean dependency graph.
    It is only used for deterministic statement-audit coverage; Lean itself
    remains the authority for compilation.
    """
    seen = {decl.name}
    parts = [decl.text]
    frontier = [decl]
    for _depth in range(max_depth):
        next_frontier: list[LeanDecl] = []
        haystack = "\n".join(item.text for item in frontier)
        for name, candidate in decls.items():
            if name in seen:
                continue
            if re.search(rf"\b{re.escape(name)}\b", haystack):
                seen.add(name)
                parts.append(candidate.text)
                next_frontier.append(candidate)
        if not next_frontier:
            break
        frontier = next_frontier
    return "\n\n".join(parts)


def _accepted_state(chunks: list[AcceptedChunk]) -> tuple[set[str], list[str], list[str]]:
    labels: set[str] = set()
    imports: list[str] = []
    signatures: list[str] = []
    for chunk in chunks:
        labels.update(chunk.labels)
        module_import = f"import {chunk.module}"
        for item in [module_import]:
            if item not in imports:
                imports.append(item)
        signatures.append(chunk.signatures)
    return labels, imports, signatures


def _standalone_accepted_code(chunks: list[AcceptedChunk]) -> str:
    imports: list[str] = []
    bodies: list[str] = []
    for chunk in chunks:
        for item in chunk.imports:
            if item not in imports:
                imports.append(item)
        bodies.append(chunk.body)
    return _compose_lean_file(imports, bodies)


def _node_tex_blocks(nodes: dict[str, Node]) -> dict[str, str]:
    """Extract the rendered-source contract for each blueprint node."""
    by_file: dict[Path, str] = {}
    blocks: dict[str, str] = {}
    for label, node in nodes.items():
        if node.file not in by_file:
            by_file[node.file] = node.file.read_text(encoding="utf-8")
        text = by_file[node.file]
        label_pos = text.find(rf"\label{{{label}}}")
        if label_pos == -1:
            blocks[label] = ""
            continue
        begin = text.rfind(r"\begin{", 0, label_pos)
        env_end = text.find(r"\end{", label_pos)
        if begin == -1 or env_end == -1:
            blocks[label] = text[label_pos : label_pos + 1200]
            continue
        env_close = text.find("}", env_end)
        if env_close == -1:
            blocks[label] = text[begin : env_end + 80]
            continue
        block_end = env_close + 1
        proof = re.match(r"\s*\\begin\{proof\}[\s\S]*?\\end\{proof\}", text[block_end:])
        if proof:
            block_end += proof.end()
        blocks[label] = text[begin:block_end].strip()
    return blocks


def _lean_module_for(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def _library_roots() -> list[tuple[str, Path]]:
    """Return local Lean library roots; CS Lib is included when installed."""
    roots: list[tuple[str, Path]] = []
    mathlib = REPO_ROOT / ".lake" / "packages" / "mathlib" / "Mathlib"
    if mathlib.is_dir():
        roots.append(("Mathlib", mathlib))
    packages = REPO_ROOT / ".lake" / "packages"
    if packages.is_dir():
        for child in sorted(packages.iterdir()):
            low = child.name.lower().replace("-", "").replace("_", "")
            if "cslib" not in low:
                continue
            for candidate in (child / "CSLib", child / "Cslib", child / "CsLib", child):
                if candidate.is_dir():
                    roots.append(("CSLib", candidate))
                    break
    return roots


def _search_terms_from_blueprint(nodes: dict[str, Node], blueprint_blocks: dict[str, str]) -> list[str]:
    """Build lexical search terms for local Mathlib/CS Lib lookup."""
    stopwords = {
        "about",
        "after",
        "also",
        "apply",
        "argument",
        "because",
        "before",
        "begin",
        "between",
        "blueprint",
        "claim",
        "commute",
        "concrete",
        "condition",
        "definition",
        "different",
        "displayed",
        "double",
        "equivalently",
        "exists",
        "factor",
        "fin",
        "finite",
        "fintype",
        "formal",
        "function",
        "given",
        "have",
        "hypothesis",
        "label",
        "later",
        "lemma",
        "mathsf",
        "number",
        "only",
        "paper",
        "proof",
        "proposition",
        "real",
        "result",
        "reverse",
        "should",
        "statement",
        "sum",
        "there",
        "theorem",
        "these",
        "this",
        "threshold",
        "type",
        "uses",
        "used",
        "vector",
        "where",
        "which",
        "with",
    }
    aliases = {
        "inner product": ["inner", "innerProduct", "dotProduct"],
        "tensor": ["TensorProduct", "kron"],
        "kronecker": ["TensorProduct", "tmul"],
        "hamming": ["hamming", "Hamming"],
        "edit distance": ["levenshtein", "editDistance"],
        "levenshtein": ["levenshtein"],
        "entropy": ["entropy", "binEntropy"],
        "orthogonal": ["orthogonal", "Orthogonal"],
        "continuous": ["Continuous", "continuous"],
        "finite sum": ["Finset.sum"],
        "softmax": ["softmax", "Real.exp"],
        "simple graph": ["SimpleGraph"],
        "variance": ["variance"],
        "probability": ["ProbabilityTheory", "MeasureTheory"],
    }
    terms: list[str] = []
    seen: set[str] = set()

    def add(term: str) -> None:
        term = term.strip()
        if len(term) < 3 or term.lower() in seen:
            return
        seen.add(term.lower())
        terms.append(term)

    for label, node in nodes.items():
        add(_lean_name(label))
        if node.lean_decl:
            add(node.lean_decl)
        text = blueprint_blocks.get(label, "")
        low = text.lower()
        for phrase, phrase_terms in aliases.items():
            if phrase in low:
                for term in phrase_terms:
                    add(term)
    return terms


def _parse_declaration_from_line(line: str) -> str | None:
    match = LEAN_DECL_START_RE.match(line)
    if match:
        return match.group(2)
    return None


def _lean_decl_snippet(path: Path, line_no: int, *, max_lines: int = 8, max_chars: int = 900) -> str:
    """Return the declaration header near file:line so the model need not open it."""
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError:
        return ""
    start = max(0, line_no - 1)
    out: list[str] = []
    for line in lines[start : start + max_lines]:
        stripped = line.rstrip()
        if stripped.lstrip().startswith("--"):
            continue
        out.append(stripped)
        joined = "\n".join(out).strip()
        if ":=" in stripped or " where" in stripped or len(joined) >= max_chars:
            break
    return "\n".join(out).strip()[:max_chars]


def _candidate_from_decl_line(
    roots: list[tuple[str, Path]],
    path: Path,
    line_no: int,
    line: str,
    terms: list[str],
) -> LibraryCandidate | None:
    decl = _parse_declaration_from_line(line.strip())
    if decl is None:
        return None

    resolved = path.resolve()
    lib_name = "Lean"
    module = path.stem
    for name, root in [(name, root.resolve()) for name, root in roots]:
        if resolved == root or root in resolved.parents:
            lib_name = name
            module = _lean_module_for(root, resolved)
            break

    matched = next(
        (
            term
            for term in terms
            if term.lower() in line.lower()
            or term.lower() in decl.lower()
            or term.lower() in module.lower()
        ),
        terms[0],
    )
    return LibraryCandidate(
        lib_name,
        module,
        decl,
        resolved,
        line_no,
        matched,
        _lean_decl_snippet(resolved, line_no),
    )


def _python_library_candidates(
    roots: list[tuple[str, Path]],
    terms: list[str],
    *,
    max_candidates: int,
) -> list[LibraryCandidate]:
    if not roots or not terms:
        return []
    lowered = [term.lower() for term in terms[:80]]
    candidates: list[LibraryCandidate] = []
    seen: set[tuple[str, str]] = set()
    for _name, root in roots:
        for path in root.rglob("*.lean"):
            try:
                with path.open(encoding="utf-8") as fh:
                    for line_no, line in enumerate(fh, start=1):
                        low = line.lower()
                        if not any(term in low for term in lowered):
                            continue
                        candidate = _candidate_from_decl_line(roots, path, line_no, line, terms)
                        if candidate is None:
                            continue
                        key = (candidate.module, candidate.declaration)
                        if key in seen:
                            continue
                        seen.add(key)
                        candidates.append(candidate)
                        if len(candidates) >= max_candidates:
                            return candidates
            except OSError:
                continue
    return candidates


def _rg_library_candidates(
    roots: list[tuple[str, Path]],
    terms: list[str],
    *,
    max_candidates: int,
) -> list[LibraryCandidate]:
    rg = shutil.which("rg")
    if not rg or not roots or not terms:
        return _python_library_candidates(roots, terms, max_candidates=max_candidates)
    pattern = "|".join(re.escape(term) for term in terms[:80])
    cmd = [
        rg,
        "--no-heading",
        "--line-number",
        "--glob",
        "*.lean",
        pattern,
        *[str(root) for _name, root in roots],
    ]
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), capture_output=True, text=True)
    if proc.returncode not in {0, 1}:
        return _python_library_candidates(roots, terms, max_candidates=max_candidates)

    candidates: list[LibraryCandidate] = []
    seen: set[tuple[str, str]] = set()
    for raw in proc.stdout.splitlines():
        parts = raw.split(":", 2)
        if len(parts) != 3:
            continue
        path = Path(parts[0])
        try:
            line_no = int(parts[1])
        except ValueError:
            continue
        line = parts[2].strip()
        candidate = _candidate_from_decl_line(roots, path, line_no, line, terms)
        if candidate is None:
            continue

        key = (candidate.module, candidate.declaration)
        if key in seen:
            continue
        seen.add(key)
        candidates.append(candidate)
        if len(candidates) >= max_candidates:
            break
    return candidates or _python_library_candidates(roots, terms, max_candidates=max_candidates)


def _library_search_terms_prompt(name: str, blueprint_source: str, existing_terms: list[str]) -> str:
    return f"""TASK: PROPOSE-LEAN-LIBRARY-SEARCH-TERMS

The deterministic local Mathlib/CS Lib search found too few useful candidates.
Propose better Lean library search terms for the blueprint below.

Return exactly one JSON object:
{{
  "terms": ["short Lean/library search term", "..."]
}}

Rules:
- Return terms only; do not generate Lean.
- Prefer likely declaration names, module words, and common theorem names.
- Include synonyms when paper terminology may differ from Lean terminology.
- Keep the list under 40 terms.

Blueprint name: {name}

Existing terms already tried:
{", ".join(existing_terms[:80])}

Blueprint source:
```tex
{blueprint_source[:20000]}
```
"""


def _search_local_lean_libraries(
    name: str,
    nodes: dict[str, Node],
    blueprint_source: str,
    *,
    term_runner=None,
) -> tuple[str, list[LibraryCandidate]]:
    """Search local Mathlib/CS Lib once for the current blueprint version."""
    roots = _library_roots()
    root_names = ", ".join(name for name, _root in roots) or "(none)"
    print(f"==> Searching local Lean libraries for candidate declarations ({root_names})", flush=True)
    blueprint_blocks = _node_tex_blocks(nodes)
    terms = _search_terms_from_blueprint(nodes, blueprint_blocks)
    candidates = _rg_library_candidates(roots, terms, max_candidates=MAX_LIBRARY_CANDIDATES)

    if len(candidates) < MIN_LIBRARY_CANDIDATES_BEFORE_MODEL_TERMS and term_runner is not None:
        print("  deterministic search was sparse; asking model for extra search terms", flush=True)
        result = term_runner.run(_library_search_terms_prompt(name, blueprint_source, terms), cwd=REPO_ROOT, retries=0)
        try:
            payload = _extract_json(result.text)
            extra_terms = [str(term) for term in payload.get("terms", []) if str(term).strip()]
        except ValueError:
            extra_terms = []
        if extra_terms:
            terms.extend(extra_terms)
            candidates = _rg_library_candidates(roots, terms, max_candidates=MAX_LIBRARY_CANDIDATES)

    lines = []
    lines.append(
        "- Candidate modules below were found by deterministic local search; "
        "treat module paths as already verified."
    )
    if not any(lib == "CSLib" for lib, _root in roots):
        lines.append("- CS Lib: not installed locally under `.lake/packages/`; search used available local libraries only.")
    for cand in candidates:
        rel = cand.file
        try:
            rel = cand.file.relative_to(REPO_ROOT)
        except ValueError:
            pass
        lines.append(
            f"- {cand.library}: `{cand.declaration}` in `{cand.module}` "
            f"({rel}:{cand.line}, matched `{cand.matched}`)"
        )
        if cand.snippet:
            lines.append("  ```lean")
            lines.extend(f"  {line}" for line in cand.snippet.splitlines())
            lines.append("  ```")

    print(f"  found {len(candidates)} candidate declaration(s)", flush=True)
    summary = "\n".join(lines) if lines else "- No local Lean library candidates found."
    return summary, candidates


def _lean_declarations(code: str) -> dict[str, LeanDecl]:
    lines = code.splitlines()
    starts: list[tuple[int, re.Match[str]]] = []
    for idx, line in enumerate(lines):
        match = LEAN_DECL_START_RE.match(line)
        if match:
            starts.append((idx, match))

    decls: dict[str, LeanDecl] = {}
    for pos, (start_idx, match) in enumerate(starts):
        end_idx = starts[pos + 1][0] if pos + 1 < len(starts) else len(lines)
        name = match.group(2)
        decls[name] = LeanDecl(
            kind=match.group(1),
            name=name,
            line=start_idx + 1,
            text="\n".join(lines[start_idx:end_idx]).strip(),
        )
    return decls


def _module_safe_name(name: str) -> str:
    parts = re.split(r"[^A-Za-z0-9]+", name)
    safe = "".join(part[:1].upper() + part[1:] for part in parts if part)
    return safe or "Blueprint"


def _generated_module_dir(name: str) -> Path:
    return REPO_ROOT / "AutoBlueprint" / "Generated" / _module_safe_name(name)


def _chunk_module(name: str, chunk_number: int) -> tuple[str, Path]:
    base = _module_safe_name(name)
    module = f"AutoBlueprint.Generated.{base}.Chunk{chunk_number:02d}"
    path = REPO_ROOT / "AutoBlueprint" / "Generated" / base / f"Chunk{chunk_number:02d}.lean"
    return module, path


def _chunk_manifest_path(name: str) -> Path:
    return _generated_module_dir(name) / "manifest.json"


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _write_chunk_manifest(name: str, accepted_chunks: list[AcceptedChunk]) -> None:
    """Record accepted chunks so --continue can skip re-verifying unchanged ones.

    Each entry stores enough to prove nothing relevant changed: the chunk file
    hash (the Lean code) and the per-label blueprint fingerprints (the TeX the
    audit judged it against). If both still match at resume time, the previous
    Lean check and alignment audit verdicts still hold.
    """
    entries = []
    for chunk in accepted_chunks:
        try:
            sha = _file_sha256(chunk.path)
        except OSError:
            continue
        entries.append(
            {
                "file": chunk.path.name,
                "sha256": sha,
                "labels": list(chunk.labels),
                "fingerprints": dict(chunk.fingerprints),
            }
        )
    path = _chunk_manifest_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"chunks": entries}, indent=2) + "\n", encoding="utf-8")


def _read_chunk_manifest(name: str) -> dict[str, dict]:
    try:
        data = json.loads(_chunk_manifest_path(name).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    entries = data.get("chunks") if isinstance(data, dict) else None
    if not isinstance(entries, list):
        return {}
    return {entry["file"]: entry for entry in entries if isinstance(entry, dict) and "file" in entry}


def _olean_roots() -> list[Path]:
    """Directories holding compiled .olean trees for local packages."""
    roots = [REPO_ROOT / ".lake" / "build" / "lib" / "lean"]
    packages = REPO_ROOT / ".lake" / "packages"
    if packages.is_dir():
        roots.extend(sorted(packages.glob("*/.lake/build/lib/lean")))
    return [root for root in roots if root.is_dir()]


def _missing_olean_imports(import_lines: list[str]) -> list[str]:
    """Return import lines whose module has no compiled .olean locally.

    Only flags modules whose top-level namespace is owned by a local package
    root (e.g. Mathlib, Batteries); core namespaces like Init/Lean/Std live in
    the toolchain and are never flagged. Generated AutoBlueprint modules are
    compiled by this script itself and are skipped too.
    """
    roots = _olean_roots()
    missing: list[str] = []
    for line in import_lines:
        module = line.strip()
        if not module.startswith("import "):
            continue
        module = module[len("import "):].strip()
        if not module or module.startswith("AutoBlueprint"):
            continue
        top = module.split(".", 1)[0]
        rel = Path(*module.split("."))
        owned = False
        found = False
        for root in roots:
            if (root / top).is_dir() or (root / f"{top}.olean").is_file():
                owned = True
                if (root / rel.parent / f"{rel.name}.olean").is_file():
                    found = True
                    break
        if owned and not found:
            missing.append(line.strip())
    return missing


def _decl_signatures(code: str) -> str:
    signatures: list[str] = []
    for decl in _lean_declarations(code).values():
        lines = decl.text.splitlines()
        head_lines: list[str] = []
        for line in lines:
            head_lines.append(line)
            if ":=" in line or line.strip().endswith("where"):
                break
            if len(head_lines) >= 8:
                break
        head = "\n".join(head_lines)
        head = head.split(":=", 1)[0].rstrip()
        signatures.append(head)
    return "\n\n".join(signatures)


def _deterministic_statement_audit(
    code: str,
    nodes: dict[str, Node],
    all_nodes: dict[str, Node] | None = None,
) -> list[str]:
    """Catch obvious coverage and weakening failures before using model judgment."""
    issues: list[str] = []
    decls = _lean_declarations(code)
    all_nodes = all_nodes or nodes
    required = {label: node for label, node in nodes.items() if not node.mathlibok}

    missing = [f"{label} -> `{_lean_name(label)}`" for label in sorted(required) if _lean_name(label) not in decls]
    if missing:
        shown = ", ".join(missing[:20])
        more = "" if len(missing) <= 20 else f", ... ({len(missing)} total)"
        issues.append(f"missing generated declarations for blueprint nodes: {shown}{more}")

    prop_true = [
        f"{decl.kind} {decl.name}"
        for decl in decls.values()
        if decl.kind in {"def", "abbrev"} and re.search(r":\s*Prop\s*:=\s*True\b", decl.text)
    ]
    if prop_true:
        shown = ", ".join(prop_true[:20])
        more = "" if len(prop_true) <= 20 else f", ... ({len(prop_true)} total)"
        issues.append(f"defines propositions as `True`: {shown}{more}")

    placeholder_decls = [
        decl.name
        for decl in decls.values()
        if PLACEHOLDER_NAME_RE.search(decl.name) or PLACEHOLDER_NAME_RE.search(decl.text[:300])
    ]
    if placeholder_decls:
        shown = ", ".join(placeholder_decls[:20])
        more = "" if len(placeholder_decls) <= 20 else f", ... ({len(placeholder_decls)} total)"
        issues.append(f"contains placeholder/gap declarations instead of aligned statements: {shown}{more}")

    for label, node in required.items():
        decl = decls.get(_lean_name(label))
        if decl is None:
            continue
        if node.kind == "definition" and decl.kind in {"theorem", "lemma"}:
            issues.append(
                f"{label} is a blueprint definition but generated `{decl.kind} {decl.name}`; "
                "definitions should normally be Lean `def`/`structure`/`inductive` declarations"
            )
        if node.kind in {"lemma", "proposition", "theorem", "corollary"} and decl.kind in {
            "structure",
            "inductive",
            "class",
        }:
            issues.append(f"{label} is theorem-like but generated `{decl.kind} {decl.name}`")
        missing_deps = _nonmathlib_uses_missing_from_decl(label, node, decl, all_nodes, decls)
        if missing_deps:
            shown = ", ".join(f"{dep} -> `{_lean_name(dep)}`" for dep in missing_deps[:12])
            more = "" if len(missing_deps) <= 12 else f", ... ({len(missing_deps)} total)"
            issues.append(
                f"{label} does not mention required blueprint dependency/dependencies: {shown}{more}"
            )
    return issues


def _deterministic_audit_kind(issues: list[str]) -> str:
    """Classify deterministic audit failures without another model call."""
    text = "\n".join(issues).lower()
    blueprint_markers = (
        "blueprint definition but generated",
        "defines propositions as `true`",
        "placeholder/gap declarations",
        "theorem-like but generated",
    )
    if any(marker in text for marker in blueprint_markers):
        return "blueprint"
    return "lean-generation"


>>>>>>> Stashed changes
def _extract_lean_code(text: str) -> str:
    fence = re.search(r"```(?:lean|lean4)?\s*([\s\S]*?)```", text)
    return (fence.group(1) if fence else text).strip()


def _default_lean_command() -> list[str]:
    if not (REPO_ROOT / "lean-toolchain").is_file() or not (REPO_ROOT / "lakefile.lean").is_file():
        raise FileNotFoundError(
            "Lean is not declared for this repo. Expected lean-toolchain and lakefile.lean."
        )
    if not any((Path.home() / ".elan" / "bin" / exe).is_file() for exe in ("lake", "lake.exe")):
        # lake may still be on PATH elsewhere, checked below; this message keeps
        # the common local setup failure direct.
        pass
    return ["lake", "env", "lean"]


def _run_lean(path: Path, lean_command: list[str]) -> LeanAttempt:
    code = path.read_text(encoding="utf-8")
    if FORBIDDEN_LEAN_PLACEHOLDERS.search(code):
        return LeanAttempt(
            ok=False,
            command=lean_command + [str(path)],
            reason="Lean attempt contains a forbidden placeholder (`sorry`, `admit`, or `by ?`).",
        )

    try:
        proc = subprocess.Popen(
            lean_command + [str(path)],
            cwd=str(REPO_ROOT),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except FileNotFoundError as exc:
        raise FileNotFoundError(
            "Lake/Lean is not installed for this repo. Run:\n"
            "  uv run python scripts/setup_lean.py --install-elan"
        ) from exc

    start = time.time()
    while True:
        try:
            stdout, stderr = proc.communicate(timeout=30)
            break
        except subprocess.TimeoutExpired:
            elapsed = int(time.time() - start)
            if elapsed >= 600:
                proc.kill()
                stdout, stderr = proc.communicate()
                return LeanAttempt(
                    ok=False,
                    command=lean_command + [str(path)],
                    stdout=stdout or "",
                    stderr=stderr or "",
                    reason="Lean check timed out after 600s.",
                )
            print(f"  lean still checking... {elapsed}s elapsed", flush=True)

    return LeanAttempt(
        ok=proc.returncode == 0,
        command=lean_command + [str(path)],
        stdout=stdout or "",
        stderr=stderr or "",
    )


def _lean_prompt(name: str, blueprint_source: str, nodes: dict[str, Node]) -> str:
    return f"""TASK: BLUEPRINT-TO-LEAN-CHECK-ATTEMPT

Return exactly one Lean 4 file. Do not return markdown commentary.

Hard constraints:
- The blueprint below is the only mathematical source of truth.
- Do not strengthen, weaken, skip, or silently reinterpret blueprint statements.
- Do not use facts that are not Mathlib imports, explicit \\lean{{...}} settled
  declarations in the blueprint, or earlier blueprint nodes listed in \\uses{{...}}.
- Do not use `sorry`, `admit`, `by ?`, or comments that stand in for proof.
- Give each generated declaration the Lean name listed in the node summary.
- If the blueprint is missing a lemma/hypothesis/dependency, let Lean fail.
  Do not patch around missing blueprint content.
- Do not compile or run `lake`/`lean` yourself; you have read-only access. A
  separate checker compiles your reply, and its errors come back to you on the
  next trial. Write the complete file in one pass and return it.

Imports:
- Import only the specific Mathlib modules your file needs, e.g.
  `import Mathlib.Analysis.InnerProductSpace.Basic`.
- Confirm each module path exists by checking the Mathlib source under
  `.lake/packages/mathlib/Mathlib/` before using it.
- Do not use the blanket `import Mathlib` or `import AutoBlueprint`; they load
  every Mathlib module and make each compile check several times slower.

Blueprint name: {name}

Node summary:
{_node_summary(nodes)}

Current blueprint source:
```tex
{blueprint_source}
```
"""


<<<<<<< Updated upstream
def _agent_refine_prompt(name: str, blueprint_source: str, lean_output: str, trial: int, paper_text: str) -> str:
=======
def _chunk_lean_prompt(
    name: str,
    blueprint_source: str,
    nodes: dict[str, Node],
    target_labels: list[str],
    accepted_labels: set[str],
    accepted_signatures: str,
    accepted_imports: list[str],
    *,
    library_context: str = "",
    previous_lean_error: str = "",
    previous_chunk_code: str = "",
    audit_history: str = "",
    unavailable_imports: list[str] | None = None,
) -> str:
    retry_block = ""
    if previous_lean_error:
        previous_code_block = ""
        if previous_chunk_code:
            code = previous_chunk_code
            if len(code) > 45000:
                code = code[:45000] + "\n-- ... (truncated)"
            previous_code_block = f"""
Your previous attempt is below. START FROM IT: keep every declaration that is
not implicated in the errors exactly as written, and change only what is needed
to fix the reported errors. Do not re-derive or restyle unaffected code. Return
the full corrected file.

```lean
{code}
```
"""
        retry_block = f"""

Previous generated Lean attempt for this same chunk failed. Do not change the
mathematical content. Fix only the Lean encoding, imports, explicit arguments,
and proofs for this chunk.

Previous Lean/audit output:
```text
{previous_lean_error[-12000:]}
```
{previous_code_block}"""
    audit_history_block = ""
    if audit_history:
        audit_history_block = f"""

Earlier statement-alignment audit rejections for nodes in this chunk (possibly
from previous attempts or previous chunk numbers). The auditor WILL reject the
same patterns again. Your new Lean must address these complaints directly. In
particular, never satisfy a correctness field with a tautology (`rfl` against a
definition you introduced for that purpose), an identity implication
(`P -> P`), or by assuming the conclusion as an input field of an
oracle-answer/witness structure.

```text
{audit_history[-8000:]}
```
"""
    unavailable_block = ""
    if unavailable_imports:
        unavailable_block = (
            "\nUnavailable imports (no compiled .olean in this local build; NEVER import"
            "\nthese, and avoid tactics/lemmas that require them):\n"
            + "\n".join(f"- {item}" for item in sorted(unavailable_imports))
            + "\n"
        )
    target_set = set(target_labels)
    dependency_labels = [
        label
        for label in _node_order(nodes)
        if label in (_dependency_closure(nodes, target_labels) - target_set)
    ]
    target_blocks = _node_tex_blocks({label: nodes[label] for label in target_labels})
    dependency_blocks = _node_tex_blocks({label: nodes[label] for label in dependency_labels})
    target_text = "\n\n".join(
        f"## {label}\n```tex\n{target_blocks.get(label, '')[:5000]}\n```"
        for label in target_labels
    )
    dependency_text = "\n\n".join(
        f"## {label}\n```tex\n{dependency_blocks.get(label, '')[:2500]}\n```"
        for label in dependency_labels
        if label not in accepted_labels and not nodes[label].mathlibok
    )
    if not dependency_text:
        dependency_text = "- All transitive dependencies are already accepted, Mathlib-backed, or in the target chunk."
    accepted_list = ", ".join(sorted(accepted_labels)) or "(none yet)"
    return f"""TASK: BLUEPRINT-CHUNK-TO-LEAN-CHECK-ATTEMPT

Return exactly one Lean 4 code block/file. Do not return markdown commentary.

You see the whole node graph for global context, but your proof obligation is
only the current dependency-closed chunk. The TeX source blocks below are the
local contract for this generation call.

Hard constraints:
- The blueprint below is the only mathematical source of truth.
- Generate Lean declarations for every target node in the current chunk.
- Do not redefine accepted declarations from earlier chunks.
- If a target node has `\\uses{{label}}`, the generated public declaration for
  that target node must visibly use the generated Lean declaration for `label`
  (for example `lem_inner_scaled`), either directly or through a same-module
  helper/result structure. Do not duplicate a dependency inline or silently
  ignore it.
- If one blueprint node explicitly introduces several named definitions,
  predicates, fields, or regimes, define those names separately. Do not hide
  them inside one bundled theorem/tuple/structure unless the blueprint itself
  says that bundle is the mathematical object.
- You may introduce helper declarations only when they are concrete Lean
  definitions/lemmas needed for target nodes, and they must not be fake paper
  assumptions.
- Do not call invented helpers such as `foo_from_blueprint`,
  `foo_from_paper`, `Karthik_Manurangsi_2020_reduction`, or similar names that
  merely assert a paper result.
- Do not use `sorry`, `admit`, `by ?`, `axiom`, `constant`, or `opaque`.
- Do not emit declarations like `theorem name : True := by trivial`.
- Include only imports you actually need. Do not use blanket `import Mathlib`
  or `import AutoBlueprint`.
- Keep `set_option autoImplicit false`.
- If this chunk depends on accepted nodes, use the imported accepted
  declarations exactly as written. Do not redefine them.
- If the blueprint is missing a lemma/hypothesis/dependency, let the checker
  fail rather than patching around missing content.

The script will compile:

    imports of accepted chunk modules + your new chunk code

So your output should contain imports plus new declarations for this chunk. It
must not repeat accepted declarations.
{unavailable_block}{retry_block}{audit_history_block}

Blueprint name: {name}

Accepted blueprint nodes:
{accepted_list}

Accepted Lean module imports:
```lean
{chr(10).join(accepted_imports) if accepted_imports else "-- none yet"}
```

Current target chunk:
{_chunk_summary(nodes, target_labels)}

Whole blueprint node graph:
{_node_summary(nodes)}

Accepted Lean signatures:
```lean
{accepted_signatures[-12000:] if accepted_signatures else "-- none yet"}
```

Local Lean library candidates:
{library_context or "- No local library candidates were found."}

Lean API idioms:
{LEAN_IDIOM_CHEATSHEET}

Target blueprint source:
{target_text}

Relevant dependency source:
{dependency_text}
"""


def _agent_refine_prompt(
    name: str,
    blueprint_source: str,
    lean_output: str,
    trial: int,
    paper_text: str,
    *,
    escalation_note: str = "",
) -> str:
>>>>>>> Stashed changes
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    escalation_block = f"\nIMPORTANT: {escalation_note}\n" if escalation_note else ""
    return f"""TASK: REFINE-BLUEPRINT-FROM-LEAN-FAILURE

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.

You are the blueprint author. Fix the blueprint, not the Lean implementation.
{escalation_block}

Rules:
- Edit only `blueprints/{name}/blueprint/src/` and `blueprints/{name}/meta.yml`
  if metadata is genuinely wrong.
- Do not edit `.auto-blueprint/` Lean attempt files.
- Do not make the theorem weaker just to satisfy Lean.
- If Lean failed because the blueprint skipped an argument, add the missing
  lemma/proposition/definition as a blueprint node.
- If a proof needs an unstated dependency, add or correct `\\uses{{...}}`.
- If a statement is mathematically wrong compared with the paper, correct the
  statement in the blueprint.
- After editing, run `python scripts/validate_blueprint.py {name}`.

{paper_block}
Current blueprint source:
```tex
{blueprint_source}
```

Lean critic output:
```text
{lean_output[-12000:]}
```
"""


def _api_refine_prompt(
    name: str,
    blueprint_source: str,
    lean_output: str,
    trial: int,
    paper_text: str,
    *,
    escalation_note: str = "",
) -> str:
    paper_block = f"\nOriginal paper context:\n<paper>\n{paper_text}\n</paper>\n" if paper_text else ""
    escalation_block = f"\nIMPORTANT: {escalation_note}\n" if escalation_note else ""
    return f"""TASK: REFINE-BLUEPRINT-CONTENT-TEX

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.
{escalation_block}

Return exactly one JSON object:
{{
  "content_tex": "full replacement for blueprints/{name}/blueprint/src/content.tex",
  "notes": "short explanation of what changed"
}}

Rules:
- Fix the blueprint, not the Lean code.
- Do not make the theorem weaker just to satisfy Lean.
- Add missing intermediate blueprint nodes when the proof needs them.
- Correct `\\uses{{...}}` whenever dependencies were missing or wrong.
- Do not include `\\begin{{document}}` or `\\end{{document}}`.

{paper_block}
Current blueprint source:
```tex
{blueprint_source}
```

Lean critic output:
```text
{lean_output[-12000:]}
```
"""


def _write_api_refinement(name: str, text: str) -> None:
    payload = _extract_json(text)
    content_tex = str(payload.get("content_tex") or "").strip()
    if not content_tex:
        raise ValueError("refinement JSON did not include non-empty content_tex")
    if r"\begin{document}" in content_tex or r"\end{document}" in content_tex:
        raise ValueError("content_tex must not include a document environment")
    path = REPO_ROOT / "blueprints" / name / "blueprint" / "src" / "content.tex"
    path.write_text(content_tex.rstrip() + "\n", encoding="utf-8")
    notes = str(payload.get("notes") or "").strip()
    if notes:
        print(f"  refinement notes: {notes}")


def _write_report(name: str, lines: list[str]) -> Path:
    out_dir = SCRATCH_DIR / name
    out_dir.mkdir(parents=True, exist_ok=True)
    report = out_dir / "report.md"
    report.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")
    return report


def _publish_passing_lean(name: str, lean_path: Path) -> Path:
    """Save the passing Lean attempt as a tracked blueprint artifact."""
    dest_dir = REPO_ROOT / "blueprints" / name / "blueprint" / "lean"
    dest_dir.mkdir(parents=True, exist_ok=True)
    dest = dest_dir / PUBLISHED_LEAN_NAME
    dest.write_text(lean_path.read_text(encoding="utf-8").rstrip() + "\n", encoding="utf-8")
    return dest


<<<<<<< Updated upstream
=======
def _publish_lean_text(name: str, code: str) -> Path:
    """Save the assembled passing Lean entrypoint as a tracked blueprint artifact."""
    dest_dir = REPO_ROOT / "blueprints" / name / "blueprint" / "lean"
    dest_dir.mkdir(parents=True, exist_ok=True)
    dest = dest_dir / PUBLISHED_LEAN_NAME
    dest.write_text(code.rstrip() + "\n", encoding="utf-8")
    return dest


def _rebuild_site_for(name: str) -> Path:
    """Rebuild one blueprint so the published site links the Lean viewer."""
    cmd = [sys.executable, "scripts/build.py", name]
    print(f"==> Rebuilding site for {name}", flush=True)
    proc = subprocess.run(cmd, cwd=str(REPO_ROOT), text=True)
    if proc.returncode != 0:
        raise subprocess.CalledProcessError(proc.returncode, cmd)
    return REPO_ROOT / "site" / name / "lean" / "index.html"


def _load_existing_accepted_chunks(
    *,
    name: str,
    validation_nodes: dict[str, Node],
    lean_command: list[str],
    audit_runner,
    paper_text: str,
) -> tuple[list[AcceptedChunk], int]:
    """Resume from generated chunk modules that still pass Lean and audit.

    Continuing is intentionally not a blind trust operation: each existing
    module is checked against the current blueprint before it is accepted as
    context. The first stale/failing module and every later generated module are
    removed, because later modules may import or rely on the failing one.
    """
    generated_dir = _generated_module_dir(name)
    chunk_paths = sorted(generated_dir.glob("Chunk*.lean"))
    accepted: list[AcceptedChunk] = []
    next_number = 1
    if not chunk_paths:
        return accepted, next_number

    print("==> Continuing from existing generated Lean chunks", flush=True)
    manifest = _read_chunk_manifest(name)
    current_fingerprints_all = _node_fingerprints(validation_nodes)
    for index, path in enumerate(chunk_paths):
        match = re.fullmatch(r"Chunk(\d+)\.lean", path.name)
        if not match:
            continue
        chunk_number = int(match.group(1))
        module_name, _module_path = _chunk_module(name, chunk_number)
        code = path.read_text(encoding="utf-8")

        # Fast path: the manifest proves this exact code already passed Lean and
        # the alignment audit against blueprint nodes whose TeX is unchanged, so
        # re-running either would recompute a known verdict. Accept directly.
        entry = manifest.get(path.name)
        if (
            entry is not None
            and entry.get("labels")
            and path.with_suffix(".olean").is_file()
            and entry.get("sha256") == _file_sha256(path)
            and all(
                label in validation_nodes
                and current_fingerprints_all.get(label) == fingerprint
                for label, fingerprint in (entry.get("fingerprints") or {}).items()
            )
            and set(entry.get("fingerprints") or {}) == set(entry["labels"])
        ):
            imports, body = _split_lean_imports_and_body(code)
            imports = [item for item in imports if not item.startswith("import AutoBlueprint.Generated.")]
            accepted.append(
                AcceptedChunk(
                    labels=list(entry["labels"]),
                    imports=imports,
                    body=body,
                    fingerprints=dict(entry["fingerprints"]),
                    module=module_name,
                    path=path,
                    signatures=_decl_signatures(code),
                )
            )
            next_number = chunk_number + 1
            print(
                f"  {path.relative_to(REPO_ROOT)} unchanged since acceptance (manifest); "
                "skipping re-check",
                flush=True,
            )
            continue

        decls = _lean_declarations(code)
        labels = [
            label
            for label in _node_order(validation_nodes)
            if not validation_nodes[label].mathlibok and _lean_name(label) in decls
        ]
        if not labels:
            print(f"  {path.relative_to(REPO_ROOT)} has no current blueprint declarations; discarding", flush=True)
            failed_index = index
            next_number = chunk_number
            break

        print(
            f"  checking {path.relative_to(REPO_ROOT)} "
            f"({', '.join(labels)})",
            flush=True,
        )
        lean_attempt = _run_lean(path, lean_command)
        audit_failure = None
        if lean_attempt.ok:
            audit_failure = _run_statement_alignment_audit(
                audit_runner,
                name,
                {label: validation_nodes[label] for label in labels},
                path,
                paper_text,
                all_nodes=validation_nodes,
            )
        object_attempt = _compile_module_olean(path, lean_command) if lean_attempt.ok and audit_failure is None else None
        if not lean_attempt.ok or audit_failure is not None or object_attempt is None or not object_attempt.ok:
            print(f"  {path.relative_to(REPO_ROOT)} is stale or no longer passes; discarding from here", flush=True)
            failed_index = index
            next_number = chunk_number
            break

        imports, body = _split_lean_imports_and_body(code)
        imports = [item for item in imports if not item.startswith("import AutoBlueprint.Generated.")]
        current_fingerprints = _node_fingerprints(validation_nodes)
        accepted.append(
            AcceptedChunk(
                labels=labels,
                imports=imports,
                body=body,
                fingerprints={label: current_fingerprints[label] for label in labels},
                module=module_name,
                path=path,
                signatures=_decl_signatures(code),
            )
        )
        next_number = chunk_number + 1
    else:
        failed_index = len(chunk_paths)

    for stale in chunk_paths[failed_index:]:
        for artifact in (stale, stale.with_suffix(".olean")):
            try:
                artifact.unlink()
            except FileNotFoundError:
                pass
    _write_chunk_manifest(name, accepted)
    if accepted:
        accepted_labels, _imports, _signatures = _accepted_state(accepted)
        partial = _standalone_accepted_code(accepted)
        partial_path = SCRATCH_DIR / name / "partial_formalization.lean"
        partial_path.write_text(partial.rstrip() + "\n", encoding="utf-8")
        print(f"  resumed with {len(accepted_labels)} accepted blueprint node(s)", flush=True)
    return accepted, next_number


>>>>>>> Stashed changes
def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name", help="Existing blueprint name under blueprints/<name>/")
    parser.add_argument("--runner", default="codex", help="Runner spec, e.g. codex, openai:gpt-5")
    parser.add_argument("--max-trials", type=int, default=3, help="Stop after this many Lean attempts")
    parser.add_argument("--paper", help="Optional original paper path/URL/text for refinement context")
    parser.add_argument("--lean-command", help="Override checker command, e.g. 'lake env lean'")
    parser.add_argument(
        "--reasoning-effort",
        choices=("low", "medium", "high", "xhigh"),
        help="Codex reasoning effort for --runner codex/codex:<model>.",
    )
    parser.add_argument("--timeout", type=int, default=3600)
    args = parser.parse_args(argv)

    if args.max_trials < 1:
        raise SystemExit("--max-trials must be at least 1")

    runner_kwargs = {}
    if args.reasoning_effort:
        if not args.runner.startswith("codex"):
            raise SystemExit("--reasoning-effort is currently supported only for --runner codex")
        runner_kwargs["reasoning_effort"] = args.reasoning_effort

    paper_text = ""
    if args.paper:
        print(f"==> Reading paper context from {args.paper}", flush=True)
        paper_text, _source = read_paper(args.paper)

    lean_command = shlex.split(args.lean_command) if args.lean_command else _default_lean_command()
    runner = get_runner(
        args.runner,
        context_files=[SKILL_PATH],
        timeout=args.timeout,
        **runner_kwargs,
    )

    # Lean generation is read-only: the model writes one Lean file as its reply
    # and this script runs the single compile check. Without shell access the
    # agent cannot burn its session repeatedly self-checking against a full
    # Mathlib import. The repair step keeps the unrestricted runner.
    gen_runner = get_runner(
        args.runner,
        context_files=[SKILL_PATH],
        timeout=args.timeout,
        readonly=True,
        **runner_kwargs,
    )

    report_lines = [
        f"# Lean-Guided Blueprint Refinement: `{args.name}`",
        "",
        f"- runner: `{args.runner}`",
        f"- max trials: `{args.max_trials}`",
        f"- Lean command: `{' '.join(lean_command)}`",
        "",
    ]

<<<<<<< Updated upstream
    for trial in range(1, args.max_trials + 1):
        print(f"==> Trial {trial}/{args.max_trials}: validating blueprint", flush=True)
=======
    removed_stale = _clear_stale_attempt_artifacts(args.name)
    if removed_stale:
        print(f"==> removed {removed_stale} stale Lean attempt artifact(s)", flush=True)

    generated_dir = _generated_module_dir(args.name)
    if generated_dir.exists() and not args.continue_run:
        shutil.rmtree(generated_dir)

    accepted_chunks: list[AcceptedChunk] = []
    if args.continue_run:
        resume_validation = validate_blueprint(REPO_ROOT, args.name)
        if not resume_validation.ok:
            print_result(resume_validation)
            report_lines.append("## Resume validation failed")
            report_lines.extend(f"- {error}" for error in resume_validation.errors)
            report = _write_report(args.name, report_lines)
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return 1
        accepted_chunks, chunk_number = _load_existing_accepted_chunks(
            name=args.name,
            validation_nodes=resume_validation.nodes,
            lean_command=lean_command,
            audit_runner=gen_runner,
            paper_text=paper_text,
        )
    else:
        chunk_number = 1
    accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
    repair_trials = 0
    # Audit rejections per blueprint label. Survives chunk renumbering so a
    # regeneration of the same node after a (possibly no-op) blueprint repair
    # still sees what the auditor rejected last time.
    rejection_history: dict[str, list[str]] = {}
    # Import lines discovered to have no compiled .olean locally; fed back into
    # every later generation prompt so the model stops importing them.
    unavailable_imports: set[str] = set()

    while True:
        print(
            f"==> Chunk {chunk_number}: validating blueprint "
            f"(blueprint repairs used {repair_trials}/{args.max_trials})",
            flush=True,
        )
>>>>>>> Stashed changes
        validation = validate_blueprint(REPO_ROOT, args.name)
        print_result(validation)
        if not validation.ok:
            report_lines.append(f"## Trial {trial}: structural validation failed")
            report_lines.extend(f"- {error}" for error in validation.errors)
            report = _write_report(args.name, report_lines)
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return 1

        blueprint_source = _read_blueprint_source(args.name)

        print(
            f"==> Trial {trial}/{args.max_trials}: generating disposable Lean attempt "
            "(read-only model call; Lean check runs locally afterwards)",
            flush=True,
        )
        lean_result = gen_runner.run(
            _lean_prompt(args.name, blueprint_source, validation.nodes),
            cwd=REPO_ROOT,
            retries=0,
        )
        trial_dir = SCRATCH_DIR / args.name
        trial_dir.mkdir(parents=True, exist_ok=True)
        lean_path = trial_dir / f"trial_{trial:02d}.lean"
        lean_code = _extract_lean_code(lean_result.text).rstrip() + "\n"
        lean_path.write_text(lean_code, encoding="utf-8")
        print(
            f"  wrote {lean_path.relative_to(REPO_ROOT)} "
            f"({len(lean_code.splitlines())} lines, model took {lean_result.duration_s:.0f}s)",
            flush=True,
        )
        if re.search(r"^import (Mathlib|AutoBlueprint)\s*$", lean_code, re.MULTILINE):
            print(
                "  note: attempt uses a blanket Mathlib import; the compile check will be slower",
                flush=True,
            )

        print(f"==> Trial {trial}/{args.max_trials}: running Lean", flush=True)
        attempt = _run_lean(lean_path, lean_command)
        report_lines.append(f"## Trial {trial}")
        report_lines.append(f"- Lean file: `{lean_path.relative_to(REPO_ROOT)}`")

        if attempt.ok:
            published = _publish_passing_lean(args.name, lean_path)
            report_lines.append("- result: passed")
            report_lines.append(f"- published Lean: `{published.relative_to(REPO_ROOT)}`")
            report = _write_report(args.name, report_lines)
            print(f"Lean passed on trial {trial}.")
            print(f"Published Lean saved to {published.relative_to(REPO_ROOT)}")
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return 0

<<<<<<< Updated upstream
        critic_output = attempt.output
        print(f"  lean failed on trial {trial}; last lines of output:", flush=True)
        for line in critic_output.strip().splitlines()[-8:]:
            print(f"    {line}", flush=True)
        report_lines.append("- result: failed")
        report_lines.append("")
        report_lines.append("```text")
        report_lines.append(critic_output[-4000:])
        report_lines.append("```")
        report_lines.append("")

        if trial == args.max_trials:
            break

        print(f"==> Trial {trial}/{args.max_trials}: repairing blueprint from Lean output", flush=True)
        if runner.mode == "agent":
            repair = runner.run(
                _agent_refine_prompt(args.name, blueprint_source, critic_output, trial, paper_text),
                cwd=REPO_ROOT,
                retries=0,
            )
            print(f"  blueprint repair finished ({repair.duration_s:.0f}s)", flush=True)
        else:
            refine_result = runner.run(
                _api_refine_prompt(args.name, blueprint_source, critic_output, trial, paper_text),
                cwd=REPO_ROOT,
                retries=1,
            )
            _write_api_refinement(args.name, refine_result.text)
=======
        print(
            "==> Next dependency-closed chunk: "
            + ", ".join(target_labels)
            + f" ({len(accepted_labels)} accepted, "
            + f"{len(validation.nodes) - len(accepted_labels)} remaining including this chunk)",
            flush=True,
        )
        difficulty_summary = _chunk_difficulty_summary(validation.nodes, target_labels)
        print(f"  scheduler difficulty: {difficulty_summary}", flush=True)
        library_context, library_candidates = _search_local_lean_libraries(
            args.name,
            validation.nodes,
            blueprint_source,
            term_runner=gen_runner,
        )
        report_lines.append(f"- local library candidates: `{len(library_candidates)}`")
        report_lines.append(f"## Chunk {chunk_number}")
        report_lines.append(f"- target nodes: `{', '.join(target_labels)}`")
        report_lines.append(f"- scheduler difficulty: `{difficulty_summary}`")
        critic_output = ""
        last_attempt_kind = "lean-generation"
        last_chunk_code = ""
        for lean_try in range(1, LEAN_GENERATION_RETRIES + 1):
            print(
                f"==> Chunk {chunk_number}, Lean attempt "
                f"{lean_try}/{LEAN_GENERATION_RETRIES}: generating disposable Lean "
                "(read-only model call; Lean check runs locally afterwards)",
                flush=True,
            )
            history_snippets: list[str] = []
            for label in target_labels:
                for snippet in rejection_history.get(label, [])[-2:]:
                    if snippet not in history_snippets:
                        history_snippets.append(snippet)
            try:
                lean_result = gen_runner.run(
                    _chunk_lean_prompt(
                        args.name,
                        blueprint_source,
                        validation.nodes,
                        target_labels,
                        accepted_labels,
                        "\n\n".join(accepted_signatures),
                        accepted_imports,
                        library_context=library_context,
                        previous_lean_error=critic_output if last_attempt_kind == "lean-generation" else "",
                        previous_chunk_code=last_chunk_code if last_attempt_kind == "lean-generation" else "",
                        audit_history="\n\n".join(history_snippets),
                        unavailable_imports=sorted(unavailable_imports),
                    ),
                    cwd=REPO_ROOT,
                    retries=0,
                )
            except RunnerError as exc:
                report_lines.append(f"- Lean attempt {lean_try}: model call failed before Lean was generated")
                report_lines.append("")
                report_lines.append("```text")
                report_lines.append(str(exc)[-4000:])
                report_lines.append("```")
                report_lines.append("")
                report_lines.append(
                    "Stopped because the read-only Lean-generation model call failed before "
                    "producing a chunk; the blueprint was not changed."
                )
                report = _write_report(args.name, report_lines)
                print(f"Lean generation model call failed: {exc}", flush=True)
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                return 1
            trial_dir = SCRATCH_DIR / args.name
            trial_dir.mkdir(parents=True, exist_ok=True)
            module_name, module_path = _chunk_module(args.name, chunk_number)
            module_path.parent.mkdir(parents=True, exist_ok=True)
            lean_path = module_path
            chunk_code = _extract_lean_code(lean_result.text).rstrip() + "\n"
            chunk_import_lines, _chunk_body = _split_lean_imports_and_body(chunk_code)
            missing_imports = _missing_olean_imports(chunk_import_lines)
            removed_imports_note = ""
            if missing_imports:
                # Deterministic pre-check: these imports would fail Lean with
                # "object file ... does not exist" after a full (expensive)
                # generation. Strip them, let Lean judge the rest, and remember
                # them so later prompts forbid them up front.
                unavailable_imports.update(missing_imports)
                print(
                    "  removed import(s) with no compiled .olean in the local build: "
                    + ", ".join(item[len("import "):] for item in missing_imports),
                    flush=True,
                )
                report_lines.append(
                    f"  - removed unavailable import(s): `{', '.join(missing_imports)}`"
                )
                missing_set = set(missing_imports)
                chunk_code = "\n".join(
                    line for line in chunk_code.splitlines() if line.strip() not in missing_set
                ).rstrip() + "\n"
                removed_imports_note = (
                    "\n\nNote: the following imports were removed before compiling because "
                    "their modules have no compiled .olean in the local Mathlib build. Do "
                    "not import them; avoid tactics/lemmas that need them: "
                    + ", ".join(missing_imports)
                )
            lean_code, new_imports, new_body = _compose_module_file(accepted_imports, chunk_code)
            last_chunk_code = chunk_code
            lean_path.write_text(lean_code, encoding="utf-8")
            scratch_attempt = trial_dir / f"chunk_{chunk_number:02d}_attempt_{lean_try:02d}.lean"
            scratch_attempt.write_text(lean_code, encoding="utf-8")
            print(
                f"  wrote {lean_path.relative_to(REPO_ROOT)} "
                f"({len(lean_code.splitlines())} lines, model took {lean_result.duration_s:.0f}s)",
                flush=True,
            )
            if re.search(r"^import (Mathlib|AutoBlueprint)\s*$", lean_code, re.MULTILINE):
                print(
                    "  note: attempt uses a blanket Mathlib import; the compile check will be slower",
                    flush=True,
                )

            print(f"==> Chunk {chunk_number}: running Lean", flush=True)
            attempt = _run_lean(lean_path, lean_command)
            report_lines.append(f"- Lean attempt {lean_try}: `{scratch_attempt.relative_to(REPO_ROOT)}`")

            if attempt.ok:
                print(f"==> Chunk {chunk_number}: auditing statement alignment", flush=True)
                audit_failure = _run_statement_alignment_audit(
                    gen_runner,
                    args.name,
                    {label: validation.nodes[label] for label in target_labels},
                    lean_path,
                    paper_text,
                    all_nodes=validation.nodes,
                )
                if audit_failure is not None:
                    attempt = audit_failure
                    critic_output = attempt.output
                    last_attempt_kind = attempt.kind
                    rejected_for_history = (
                        set(attempt.rejected_labels or []) & set(target_labels)
                    ) or set(target_labels)
                    for label in rejected_for_history:
                        rejection_history.setdefault(label, []).append(critic_output[-2500:])
                    print(
                        f"  statement alignment audit failed ({attempt.kind}); last lines:",
                        flush=True,
                    )
                    for line in critic_output.strip().splitlines()[-8:]:
                        print(f"    {line}", flush=True)
                    report_lines.append(f"  - result: failed statement alignment audit ({attempt.kind})")
                    report_lines.append("")
                    report_lines.append("```text")
                    report_lines.append(critic_output[-4000:])
                    report_lines.append("```")
                    report_lines.append("")
                    if attempt.kind == "blueprint" and attempt.rejected_labels:
                        rejected_in_chunk = set(attempt.rejected_labels) & set(target_labels)
                        affected_in_chunk = _dependency_descendants_within(
                            validation.nodes,
                            rejected_in_chunk,
                            set(target_labels),
                        )
                        keep_labels = [label for label in target_labels if label not in affected_in_chunk]
                        if keep_labels:
                            pruned = _prune_chunk_to_labels(
                                module_imports=accepted_imports,
                                original_chunk_code=chunk_code,
                                target_labels=target_labels,
                                keep_labels=keep_labels,
                            )
                            if pruned is not None:
                                lean_path.write_text(pruned.lean_code, encoding="utf-8")
                                pruned_attempt_path = (
                                    trial_dir / f"chunk_{chunk_number:02d}_accepted_subset.lean"
                                )
                                pruned_attempt_path.write_text(pruned.lean_code, encoding="utf-8")
                                print(
                                    "  trying to keep independent passing subset: "
                                    + ", ".join(keep_labels),
                                    flush=True,
                                )
                                subset_lean = _run_lean(lean_path, lean_command)
                                subset_audit = None
                                if subset_lean.ok:
                                    subset_audit = _run_statement_alignment_audit(
                                        gen_runner,
                                        args.name,
                                        {label: validation.nodes[label] for label in keep_labels},
                                        lean_path,
                                        paper_text,
                                        all_nodes=validation.nodes,
                                    )
                                if subset_lean.ok and subset_audit is None:
                                    object_attempt = _compile_module_olean(module_path, lean_command)
                                    if object_attempt.ok:
                                        accepted_chunks.append(
                                            AcceptedChunk(
                                                labels=list(keep_labels),
                                                imports=list(pruned.imports),
                                                body=pruned.body,
                                                fingerprints={
                                                    label: current_fingerprints[label]
                                                    for label in keep_labels
                                                },
                                                module=module_name,
                                                path=module_path,
                                                signatures=pruned.signatures,
                                            )
                                        )
                                        _write_chunk_manifest(args.name, accepted_chunks)
                                        accepted_labels, accepted_imports, accepted_signatures = (
                                            _accepted_state(accepted_chunks)
                                        )
                                        partial = _standalone_accepted_code(accepted_chunks)
                                        partial_path = trial_dir / "partial_formalization.lean"
                                        partial_path.write_text(partial.rstrip() + "\n", encoding="utf-8")
                                        print(
                                            "  kept independent subset; rejected/downstream nodes "
                                            "will be repaired/regenerated",
                                            flush=True,
                                        )
                                        report_lines.append(
                                            "  - kept independent passing subset: "
                                            f"`{', '.join(keep_labels)}`"
                                        )
                                        report_lines.append(
                                            f"  - pruned subset Lean: `{pruned_attempt_path.relative_to(REPO_ROOT)}`"
                                        )
                                    else:
                                        print(
                                            "  independent subset did not compile as an importable module; "
                                            "discarding it",
                                            flush=True,
                                        )
                                else:
                                    print(
                                        "  independent subset did not pass Lean/audit after pruning; "
                                        "discarding it",
                                        flush=True,
                                    )
                    if attempt.kind != "lean-generation":
                        break
                    continue

                object_attempt = _compile_module_olean(module_path, lean_command)
                if not object_attempt.ok:
                    critic_output = object_attempt.output
                    last_attempt_kind = "lean-generation"
                    print("  accepted chunk failed .olean compilation; last lines:", flush=True)
                    for line in critic_output.strip().splitlines()[-8:]:
                        print(f"    {line}", flush=True)
                    report_lines.append("  - result: failed generated module .olean compilation")
                    report_lines.append("")
                    report_lines.append("```text")
                    report_lines.append(critic_output[-4000:])
                    report_lines.append("```")
                    report_lines.append("")
                    continue

                signatures = _decl_signatures(lean_code)
                accepted_chunks.append(
                    AcceptedChunk(
                        labels=list(target_labels),
                        imports=list(new_imports),
                        body=new_body,
                        fingerprints={label: current_fingerprints[label] for label in target_labels},
                        module=module_name,
                        path=module_path,
                        signatures=signatures,
                    )
                )
                _write_chunk_manifest(args.name, accepted_chunks)
                accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
                partial = _standalone_accepted_code(accepted_chunks)
                partial_path = trial_dir / "partial_formalization.lean"
                partial_path.write_text(partial.rstrip() + "\n", encoding="utf-8")
                report_lines.append("- result: chunk passed")
                report_lines.append("- statement alignment audit: passed")
                report_lines.append(f"- accepted through nodes: `{len(accepted_labels)}`")
                report_lines.append(f"- partial Lean: `{partial_path.relative_to(REPO_ROOT)}`")
                print(
                    f"Chunk {chunk_number} passed; accepted {len(accepted_labels)} "
                    f"of {len(validation.nodes)} blueprint nodes.",
                    flush=True,
                )
                chunk_number += 1
                break

            critic_output = attempt.output + removed_imports_note
            last_attempt_kind = attempt.kind
            print(
                f"  lean failed on chunk {chunk_number}, attempt {lean_try} "
                f"({attempt.kind}); last lines of output:",
                flush=True,
            )
            for line in critic_output.strip().splitlines()[-8:]:
                print(f"    {line}", flush=True)
            report_lines.append(f"  - result: failed ({attempt.kind})")
            report_lines.append("")
            report_lines.append("```text")
            report_lines.append(critic_output[-4000:])
            report_lines.append("```")
            report_lines.append("")

            if attempt.kind != "lean-generation":
                break

        if set(target_labels) <= accepted_labels:
            continue

        if last_attempt_kind == "lean-generation":
            report_lines.append(
                "Stopped because Lean generation failed repeatedly for the same chunk; "
                "the blueprint was not changed."
            )
            report = _write_report(args.name, report_lines)
            print(
                "Lean generation failed repeatedly; not safe to repair the blueprint from "
                "syntax/elaboration/audit errors.",
                flush=True,
            )
            print(f"Report written to {report.relative_to(REPO_ROOT)}")
            return 1

        if repair_trials >= args.max_trials:
            break

        escalation_note = ""
        while True:
            repair_trials += 1
            print(
                f"==> Blueprint repair {repair_trials}/{args.max_trials} "
                f"from chunk {chunk_number} Lean/audit output",
                flush=True,
            )
            if runner.mode == "agent":
                repair = runner.run(
                    _agent_refine_prompt(
                        args.name,
                        blueprint_source,
                        critic_output,
                        repair_trials,
                        paper_text,
                        escalation_note=escalation_note,
                    ),
                    cwd=REPO_ROOT,
                    retries=0,
                )
                print(f"  blueprint repair finished ({repair.duration_s:.0f}s)", flush=True)
            else:
                refine_result = runner.run(
                    _api_refine_prompt(
                        args.name,
                        blueprint_source,
                        critic_output,
                        repair_trials,
                        paper_text,
                        escalation_note=escalation_note,
                    ),
                    cwd=REPO_ROOT,
                    retries=1,
                )
                try:
                    _write_api_refinement(args.name, refine_result.text)
                except ValueError as exc:
                    report_lines.append("## API blueprint repair returned invalid JSON/content")
                    report_lines.append("")
                    report_lines.append("```text")
                    report_lines.append(str(exc))
                    report_lines.append("")
                    report_lines.append(refine_result.text[-4000:])
                    report_lines.append("```")
                    report = _write_report(args.name, report_lines)
                    print(f"API blueprint repair failed: {exc}", flush=True)
                    print(f"Report written to {report.relative_to(REPO_ROOT)}")
                    return 1

            repaired_validation = validate_blueprint(REPO_ROOT, args.name)
            if not repaired_validation.ok:
                print_result(repaired_validation)
                report_lines.append("## Blueprint repair produced invalid structure")
                report_lines.extend(f"- {error}" for error in repaired_validation.errors)
                report = _write_report(args.name, report_lines)
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                return 1

            repaired_fingerprints = _node_fingerprints(repaired_validation.nodes)
            changed = {
                label
                for label, before in current_fingerprints.items()
                if repaired_fingerprints.get(label) != before
            }
            changed |= {label for label in repaired_fingerprints if label not in current_fingerprints}
            if changed or escalation_note or repair_trials >= args.max_trials:
                break
            # The repair call ran but left every node's TeX untouched — the
            # audit will reject the exact same content again. Escalate once
            # with an explicit instruction instead of regenerating blind.
            print(
                "  blueprint repair did not change parsed node text; escalating once "
                "with explicit instructions",
                flush=True,
            )
            report_lines.append("- blueprint repair was a no-op; escalated with explicit instructions")
            escalation_note = (
                "Your previous repair attempt changed NOTHING in the parsed node text — "
                "the validator found zero modified nodes, so the audit will reject the "
                "same content again. You MUST materially edit the TeX of the rejected "
                "node(s) this time: add the missing concrete semantics, hypotheses, "
                "parameters, or split the node into smaller nodes. If you believe the "
                "blueprint is already correct and the Lean generation is at fault, "
                "still make the node text more explicit about the required statement "
                "shape so the generator cannot satisfy it with a tautology."
            )
        invalidated = _dependency_descendants(repaired_validation.nodes, changed) if changed else set()
        before_count = len(accepted_chunks)
        kept_chunks: list[AcceptedChunk] = []
        dropped_chunks: list[AcceptedChunk] = []
        for chunk in accepted_chunks:
            if set(chunk.labels) & invalidated:
                dropped_chunks.append(chunk)
            else:
                kept_chunks.append(chunk)
        for chunk in dropped_chunks:
            for artifact in (chunk.path, chunk.path.with_suffix(".olean")):
                try:
                    artifact.unlink()
                except FileNotFoundError:
                    pass
        accepted_chunks = kept_chunks
        _write_chunk_manifest(args.name, accepted_chunks)
        accepted_labels, accepted_imports, accepted_signatures = _accepted_state(accepted_chunks)
        dropped = before_count - len(accepted_chunks)
        if changed:
            print(
                f"  blueprint changed {len(changed)} node(s); invalidated "
                f"{len(invalidated)} downstream node(s); kept {len(accepted_chunks)} accepted chunk(s)",
                flush=True,
            )
            report_lines.append(
                f"- blueprint repair changed `{len(changed)}` node(s), invalidated "
                f"`{len(invalidated)}` downstream node(s), dropped `{dropped}` accepted chunk(s)"
            )
        else:
            print("  blueprint repair did not change parsed node text; keeping accepted chunks", flush=True)
            report_lines.append("- blueprint repair did not change parsed node text; kept accepted chunks")
        chunk_number += 1
>>>>>>> Stashed changes

    report_lines.append(f"Stopped after {args.max_trials} failed trial(s).")
    report = _write_report(args.name, report_lines)
    print(f"Lean did not pass after {args.max_trials} trial(s).")
    print(f"Report written to {report.relative_to(REPO_ROOT)}")
    return 1


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (FileNotFoundError, RunnerError, subprocess.TimeoutExpired) as exc:
        print(f"error: {exc}", file=sys.stderr)
        raise SystemExit(2)
