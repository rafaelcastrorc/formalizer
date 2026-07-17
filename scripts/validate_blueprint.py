#!/usr/bin/env python3
"""Validate generated blueprint sources before rendering them.

This is intentionally deterministic: model-generated content must pass these
checks before plasTeX/build output is accepted. The validator is not a proof
checker; it checks the structural contract that Auto-Blueprint relies on:

* a blueprint lives under ``blueprints/<name>/blueprint/src``;
* theorem-like environments have labels;
* labels are unique;
* every ``\\uses{...}`` target exists;
* the dependency graph is acyclic;
* ``\\input``/``\\include`` may split content across local ``.tex`` files, but
  generated LaTeX must not read files outside this blueprint's ``src/`` folder.
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

import yaml

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO_ROOT = SCRIPTS_DIR.parent
BLUEPRINTS_DIR = REPO_ROOT / "blueprints"

BUILTIN_ENVS = ("definition", "lemma", "proposition", "theorem", "corollary")

_BEGIN_RE = re.compile(r"\\begin\{([a-zA-Z*]+)\}")
_INPUT_RE = re.compile(r"\\(?:input|include)\{([^}]*)\}")
_LABEL_RE = re.compile(r"\\label\{([^}]*)\}")
_LEAN_RE = re.compile(r"\\lean\{([^}]*)\}")
_MATHLIBOK_RE = re.compile(r"\\mathlibok\b")
_NEWTHEOREM_RE = re.compile(r"\\newtheorem\*?\{([a-zA-Z]+)\}")
_PROOF_RE = re.compile(r"\s*\\begin\{proof\}([\s\S]*?)\\end\{proof\}")
_USES_RE = re.compile(r"\\uses\{([^}]*)\}")


@dataclass
class Node:
    label: str
    kind: str
    file: Path
    line: int
    uses: set[str] = field(default_factory=set)
    mathlibok: bool = False
    lean_decl: str | None = None


@dataclass
class ValidationResult:
    name: str
    nodes: dict[str, Node] = field(default_factory=dict)
    errors: list[str] = field(default_factory=list)
    warnings: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not self.errors


def _rel(path: Path) -> str:
    try:
        return str(path.relative_to(REPO_ROOT))
    except ValueError:
        return str(path)


def _line_at(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def _strip_comments(tex: str) -> str:
    """Blank LaTeX comments without changing character offsets."""
    out: list[str] = []
    for line in tex.split("\n"):
        prev = ""
        for i, ch in enumerate(line):
            if ch == "%" and prev != "\\":
                line = line[:i] + " " * (len(line) - i)
                break
            prev = ch
        out.append(line)
    return "\n".join(out)


def _uses(body: str) -> set[str]:
    return {
        item.strip()
        for group in _USES_RE.findall(body)
        for item in group.split(",")
        if item.strip()
    }


def _theorem_envs(src_dir: Path) -> set[str]:
    envs = set(BUILTIN_ENVS)
    common = src_dir / "macros" / "common.tex"
    if common.is_file():
        envs |= set(_NEWTHEOREM_RE.findall(common.read_text(encoding="utf-8")))
    envs.discard("proof")
    return envs


def _resolve_tex_path(src_dir: Path, raw: str) -> Path | None:
    rel = raw.strip()
    if not rel:
        return None
    candidate = (src_dir / rel)
    if candidate.suffix != ".tex":
        candidate = candidate.with_suffix(".tex")
    try:
        resolved = candidate.resolve()
        src_root = src_dir.resolve()
    except OSError:
        return None
    if resolved != src_root and src_root not in resolved.parents:
        return None
    return resolved


def _input_files(src_dir: Path, result: ValidationResult) -> list[Path]:
    """Return content.tex plus safe nested inputs in inclusion order."""
    seen: list[Path] = []

    def visit(path: Path) -> None:
        if path in seen:
            return
        if not path.is_file():
            result.errors.append(f"{_rel(path)}: included file does not exist")
            return
        seen.append(path)
        text = _strip_comments(path.read_text(encoding="utf-8"))
        for match in _INPUT_RE.finditer(text):
            raw = match.group(1)
            target = _resolve_tex_path(src_dir, raw)
            if target is None:
                result.errors.append(
                    f"{_rel(path)}:{_line_at(text, match.start())}: unsafe include path {raw!r}"
                )
                continue
            visit(target)

    visit(src_dir / "content.tex")
    return seen


def _parse_file(path: Path, envs: set[str], result: ValidationResult) -> None:
    raw = path.read_text(encoding="utf-8")
    text = _strip_comments(raw)
    pos = 0

    while True:
        begin = _BEGIN_RE.search(text, pos)
        if begin is None:
            break

        env = begin.group(1).rstrip("*")
        end_marker = f"\\end{{{begin.group(1)}}}"
        end = text.find(end_marker, begin.end())
        line = _line_at(text, begin.start())
        if end == -1:
            result.errors.append(f"{_rel(path)}:{line}: missing {end_marker}")
            pos = begin.end()
            continue

        block_end = end + len(end_marker)
        body = text[begin.end():end]

        if env == "proof" or env not in envs:
            # Keep scanning inside non-node environments. Some generated or
            # hand-written TeX nests theorem-like nodes inside wrappers or even
            # proof blocks; plasTeX can render those, so the validator should
            # still see their labels and dependencies.
            pos = begin.end()
            continue

        label_matches = list(_LABEL_RE.finditer(body))
        if not label_matches:
            result.errors.append(f"{_rel(path)}:{line}: {env} environment has no \\label")
            pos = block_end
            continue
        if len(label_matches) > 1:
            result.warnings.append(
                f"{_rel(path)}:{line}: {env} environment has multiple labels; using the first"
            )

        label = label_matches[0].group(1).strip()
        if not label:
            result.errors.append(f"{_rel(path)}:{line}: empty label")
            pos = block_end
            continue

        proof_uses: set[str] = set()
        proof_match = _PROOF_RE.match(text, block_end)
        if proof_match:
            proof_uses = _uses(proof_match.group(1))

        lean = _LEAN_RE.search(body)
        node = Node(
            label=label,
            kind=env,
            file=path,
            line=line,
            uses=_uses(body) | proof_uses,
            mathlibok=bool(_MATHLIBOK_RE.search(body)),
            lean_decl=lean.group(1).strip() if lean else None,
        )

        if label in result.nodes:
            prev = result.nodes[label]
            result.errors.append(
                f"{_rel(path)}:{line}: duplicate label {label!r}; first seen at "
                f"{_rel(prev.file)}:{prev.line}"
            )
        else:
            result.nodes[label] = node

        pos = block_end


def _check_cycles(result: ValidationResult) -> None:
    indeg = {label: 0 for label in result.nodes}
    dependents = {label: [] for label in result.nodes}
    for label, node in result.nodes.items():
        for dep in node.uses:
            if dep in result.nodes:
                indeg[label] += 1
                dependents[dep].append(label)

    ready = [label for label, degree in indeg.items() if degree == 0]
    seen: list[str] = []
    while ready:
        label = ready.pop(0)
        seen.append(label)
        for dependent in dependents[label]:
            indeg[dependent] -= 1
            if indeg[dependent] == 0:
                ready.append(dependent)

    if len(seen) != len(result.nodes):
        cyclic = sorted(set(result.nodes) - set(seen))
        result.errors.append(f"dependency cycle involving: {', '.join(cyclic[:20])}")


def validate_blueprint(repo_root: Path, name: str) -> ValidationResult:
    src_dir = repo_root / "blueprints" / name / "blueprint" / "src"
    result = ValidationResult(name=name)

    if not src_dir.is_dir():
        result.errors.append(f"blueprints/{name}/blueprint/src does not exist")
        return result
    if not (src_dir / "content.tex").is_file():
        result.errors.append(f"blueprints/{name}/blueprint/src/content.tex does not exist")
        return result
    if not (src_dir / "web.tex").is_file():
        result.errors.append(f"blueprints/{name}/blueprint/src/web.tex does not exist")
        return result

    meta_path = repo_root / "blueprints" / name / "meta.yml"
    if meta_path.is_file():
        try:
            meta = yaml.safe_load(meta_path.read_text(encoding="utf-8")) or {}
            if not isinstance(meta, dict):
                result.errors.append(f"{_rel(meta_path)}: must contain a YAML mapping")
            elif meta.get("name") and meta["name"] != name:
                result.errors.append(
                    f"{_rel(meta_path)}: name {meta['name']!r} does not match folder {name!r}"
                )
        except yaml.YAMLError as exc:
            result.errors.append(f"{_rel(meta_path)}: invalid YAML: {exc}")
    else:
        result.warnings.append(f"blueprints/{name}/meta.yml missing; build will use defaults")

    envs = _theorem_envs(src_dir)
    for path in _input_files(src_dir, result):
        _parse_file(path, envs, result)

    if not result.nodes:
        result.errors.append(f"blueprints/{name}: no theorem-like nodes found")

    for label, node in sorted(result.nodes.items()):
        missing = sorted(dep for dep in node.uses if dep not in result.nodes)
        if missing:
            result.errors.append(
                f"{_rel(node.file)}:{node.line}: {label!r} uses missing label(s): "
                f"{', '.join(missing)}"
            )
        if node.mathlibok and not node.lean_decl:
            result.warnings.append(
                f"{_rel(node.file)}:{node.line}: {label!r} has \\mathlibok but no \\lean{{...}}"
            )

    _check_cycles(result)
    return result


def print_result(result: ValidationResult) -> None:
    status = "ok" if result.ok else "FAILED"
    print(f"==> validate {result.name}: {status} ({len(result.nodes)} node(s))")
    for warning in result.warnings:
        print(f"  warning: {warning}")
    for error in result.errors:
        print(f"  error: {error}", file=sys.stderr)


def discover_names(repo_root: Path) -> list[str]:
    root = repo_root / "blueprints"
    if not root.is_dir():
        return []
    return sorted(
        child.name
        for child in root.iterdir()
        if child.is_dir() and (child / "blueprint" / "src" / "web.tex").is_file()
    )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate blueprint source structure.")
    parser.add_argument("names", nargs="*", help="Blueprint names to validate (default: all)")
    args = parser.parse_args(argv)

    names = args.names or discover_names(REPO_ROOT)
    if not names:
        print("No blueprints found.")
        return 0

    failed = False
    for name in names:
        result = validate_blueprint(REPO_ROOT, name)
        print_result(result)
        failed = failed or not result.ok
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
