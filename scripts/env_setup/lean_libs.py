#!/usr/bin/env python3
"""Resolve and apply a mutually-compatible set of Lean libraries.

A Lake project has exactly ONE toolchain, and every Lean library pins a
specific toolchain plus a Mathlib revision. So "add a library" is really
"adopt a dependency set that every library agrees on". Libraries move through
toolchains over time, which means a common point usually exists *somewhere in
their history* even when their current heads disagree.

`resolve` finds it: for each library it reads the history of `lean-toolchain`,
intersects the toolchain values across all libraries, and picks the newest one
they all support -- reporting how far back each library has to sit. Nothing is
hardcoded; re-running as libraries publish new versions moves the answer
forward on its own.

`apply` writes that answer into `lean-toolchain` and the managed block of
`lakefile.lean`, runs a scoped `lake update`, fetches the Mathlib cache, and
builds -- restoring every file it touched if any step fails.

    lean_libs.py resolve [--libs mathlib,cslib] [--json]
    lean_libs.py apply   [--libs mathlib,cslib] [--yes]
    lean_libs.py status
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
REPO_ROOT = SCRIPTS_DIR.parent
MIRROR_DIR = REPO_ROOT / ".auto-blueprint" / "lib-mirrors"
CACHE_PATH = REPO_ROOT / ".auto-blueprint" / "lib-compat.json"
BUILD_STATUS_DIR = REPO_ROOT / ".auto-blueprint" / "library-build-status"
LAKEFILE = REPO_ROOT / "lakefile.lean"
TOOLCHAIN_FILE = REPO_ROOT / "lean-toolchain"
MANIFEST = REPO_ROOT / "lake-manifest.json"

MANAGED_BEGIN = "-- BEGIN MANAGED REQUIRES"
MANAGED_END = "-- END MANAGED REQUIRES"
CACHE_TTL_S = 24 * 3600

# Known libraries. Only `mathlib` is required; the rest are optional and are
# resolved against it. Adding an entry here (or via `--add`) is all the
# registry this needs -- what is *installed* is read from lake-manifest.json.
KNOWN_LIBS: dict[str, str] = {
    "mathlib": "https://github.com/leanprover-community/mathlib4.git",
    "cslib": "https://github.com/leanprover/cslib.git",
    "physlib": "https://github.com/leanprover-community/physlib.git",
}


# ---------------------------------------------------------------------------
# Lean toolchain versions


_TOOLCHAIN_RE = re.compile(
    r"leanprover/lean4:v?(?P<maj>\d+)\.(?P<min>\d+)\.(?P<pat>\d+)(?:-rc(?P<rc>\d+))?"
)


def toolchain_key(toolchain: str) -> tuple | None:
    """Sortable key for a toolchain string, or None if unparseable.

    A release sorts AFTER its own release candidates: v4.33.0-rc1 < v4.33.0.
    """
    m = _TOOLCHAIN_RE.search(toolchain or "")
    if not m:
        return None
    rc = m.group("rc")
    return (
        int(m.group("maj")),
        int(m.group("min")),
        int(m.group("pat")),
        1 if rc is None else 0,  # release beats rc
        int(rc) if rc else 0,
    )


# ---------------------------------------------------------------------------
# Git mirrors


def _git(*args: str, cwd: Path | None = None, timeout: int = 180) -> str:
    proc = subprocess.run(
        ["git", *args],
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    if proc.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {proc.stderr.strip()[:300]}")
    return proc.stdout


def sync_mirror(name: str, url: str, *, quiet: bool = False) -> Path:
    """Blobless bare mirror: full history metadata, blobs fetched on demand."""
    MIRROR_DIR.mkdir(parents=True, exist_ok=True)
    path = MIRROR_DIR / f"{name}.git"
    if path.is_dir():
        if not quiet:
            print(f"  fetching {name}...", flush=True)
        _git("fetch", "--filter=blob:none", "--force", "origin", "+refs/heads/*:refs/heads/*", cwd=path)
    else:
        if not quiet:
            print(f"  cloning {name} (blobless)...", flush=True)
        _git("clone", "--filter=blob:none", "--bare", url, str(path), timeout=600)
    return path


@dataclass
class LibState:
    name: str
    url: str
    # toolchain -> newest (commit_sha, unix_time) of this library supporting it
    toolchains: dict[str, tuple[str, int]] = field(default_factory=dict)
    head: str = ""
    head_toolchain: str = ""
    error: str = ""


def read_lib_state(name: str, url: str, *, quiet: bool = False) -> LibState:
    """Timeline of every toolchain this library has ever declared."""
    state = LibState(name=name, url=url)
    try:
        mirror = sync_mirror(name, url, quiet=quiet)
    except Exception as exc:  # unreachable repo, bad URL, network down
        state.error = str(exc)[:200]
        return state
    try:
        head_branch = _git("symbolic-ref", "--short", "HEAD", cwd=mirror).strip()
    except RuntimeError:
        head_branch = "main"
    try:
        log = _git(
            "log", head_branch, "--format=%H %ct", "--", "lean-toolchain", cwd=mirror
        )
    except RuntimeError as exc:
        state.error = str(exc)[:200]
        return state
    for line in log.splitlines():
        parts = line.split()
        if len(parts) != 2:
            continue
        sha, ts = parts[0], int(parts[1])
        try:
            value = _git("show", f"{sha}:lean-toolchain", cwd=mirror).strip()
        except RuntimeError:
            continue
        if toolchain_key(value) is None:
            continue
        # `git log` is newest-first, so the first sighting is the newest commit
        # at which this library declared that toolchain.
        state.toolchains.setdefault(value, (sha, ts))
        if not state.head:
            state.head, state.head_toolchain = sha, value
    return state


# ---------------------------------------------------------------------------
# Resolution


@dataclass
class Resolution:
    toolchain: str = ""
    pins: dict[str, str] = field(default_factory=dict)      # lib -> sha
    staleness_days: dict[str, int] = field(default_factory=dict)
    feasible: bool = False
    reason: str = ""
    groups: dict[str, list[str]] = field(default_factory=dict)  # toolchain -> libs (infeasible case)

    def to_dict(self) -> dict:
        return {
            "resolved_at": int(time.time()),
            "toolchain": self.toolchain,
            "pins": self.pins,
            "staleness_days": self.staleness_days,
            "feasible": self.feasible,
            "reason": self.reason,
            "groups": self.groups,
        }


def resolve(libs: list[str], *, quiet: bool = False) -> tuple[Resolution, dict[str, LibState]]:
    states: dict[str, LibState] = {}
    for name in libs:
        url = KNOWN_LIBS.get(name)
        if not url:
            states[name] = LibState(name=name, url="", error="unknown library (not in KNOWN_LIBS)")
            continue
        states[name] = read_lib_state(name, url, quiet=quiet)

    usable = {n: s for n, s in states.items() if not s.error and s.toolchains}
    broken = [f"{n} ({s.error})" for n, s in states.items() if s.error]
    if broken:
        return Resolution(feasible=False, reason="unreachable: " + "; ".join(broken)), states
    if not usable:
        return Resolution(feasible=False, reason="no library history available"), states

    common = set.intersection(*(set(s.toolchains) for s in usable.values()))
    if not common:
        # No shared toolchain: report how they group, so the caller can decide
        # to install a subset rather than guess.
        groups: dict[str, list[str]] = {}
        for n, s in usable.items():
            groups.setdefault(s.head_toolchain, []).append(n)
        return (
            Resolution(
                feasible=False,
                reason="no toolchain is supported by every selected library",
                groups=groups,
            ),
            states,
        )

    best = max(common, key=lambda t: toolchain_key(t) or ())
    now = int(time.time())
    res = Resolution(toolchain=best, feasible=True)
    for n, s in usable.items():
        sha, ts = s.toolchains[best]
        res.pins[n] = sha
        res.staleness_days[n] = max(0, (now - ts) // 86400)
    return res, states


# ---------------------------------------------------------------------------
# Apply


def _installed_mathlib_rev() -> str:
    try:
        m = json.loads(MANIFEST.read_text(encoding="utf-8"))
    except Exception:
        return ""
    for p in m.get("packages", []):
        if p.get("name") == "mathlib":
            return p.get("rev", "")
    return ""


def current_state() -> dict:
    return {
        "toolchain": TOOLCHAIN_FILE.read_text(encoding="utf-8").strip()
        if TOOLCHAIN_FILE.is_file() else "",
        "mathlib_rev": _installed_mathlib_rev(),
        "installed": sorted(
            p.name for p in (REPO_ROOT / ".lake" / "packages").iterdir()
        ) if (REPO_ROOT / ".lake" / "packages").is_dir() else [],
        "checkouts": _package_checkouts(),
    }


def _package_checkouts() -> dict[str, str]:
    """Revision each package is ACTUALLY checked out at, keyed by lowercase name.

    The manifest records what lake intends; a killed or partial `lake update`
    can leave the working tree somewhere else entirely. Comparing against the
    manifest alone would report a desynced tree as up to date.
    """
    out: dict[str, str] = {}
    packages = REPO_ROOT / ".lake" / "packages"
    if not packages.is_dir():
        return out
    for child in sorted(packages.iterdir()):
        if not child.is_dir():
            continue
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=str(child),
            capture_output=True, text=True,
        )
        if proc.returncode == 0:
            out[child.name.lower()] = proc.stdout.strip()
    return out


def _lean_lib_target(pkg_dir: Path, name: str) -> str | None:
    """The `lean_lib` in this package that corresponds to library `name`.

    A package's DEFAULT targets can be several libraries (physlib ships
    Physlib, PhyslibAlpha and QuantumInfo), so `lake build @physlib` compiles
    far more than was selected. Return just the matching library's target, or
    None if it cannot be identified - callers then fall back to the package.
    """
    key = name.lower().replace("-", "").replace("_", "")
    names: list[str] = []
    toml = pkg_dir / "lakefile.toml"
    lean = pkg_dir / "lakefile.lean"
    try:
        if toml.is_file():
            text = toml.read_text(encoding="utf-8")
            # Only names under a [[lean_lib]] header, not [[lean_exe]] etc.
            for block in re.split(r"^\s*\[\[", text, flags=re.M)[1:]:
                if not block.startswith("lean_lib"):
                    continue
                m = re.search(r'^\s*name\s*=\s*"([^"]+)"', block, re.M)
                if m:
                    names.append(m.group(1))
        elif lean.is_file():
            names = re.findall(
                r"^\s*lean_lib\s+«?([A-Za-z0-9_.\-]+)»?", lean.read_text(encoding="utf-8"), re.M
            )
    except Exception:  # noqa: BLE001 - a parse failure just means "fall back"
        return None
    for lib in names:
        if lib.lower().replace("-", "").replace("_", "") == key:
            return lib
    return None


def _normalized_name(name: str) -> str:
    return name.lower().replace("-", "").replace("_", "")


def _package_dir(name: str) -> Path | None:
    """Return the installed package directory matching a registry name."""
    packages = REPO_ROOT / ".lake" / "packages"
    if not packages.is_dir():
        return None
    key = _normalized_name(name)
    for child in packages.iterdir():
        if child.is_dir() and _normalized_name(child.name) == key:
            return child
    return None


def _build_stamp_path(name: str) -> Path:
    return BUILD_STATUS_DIR / f"{_normalized_name(name)}.json"


def _probe_module(pkg_dir: Path, lib: str) -> tuple[str, Path] | None:
    """Pick a stable source module whose import proves the built library loads."""
    source_root = pkg_dir / lib
    if not source_root.is_dir():
        source_root = next(
            (
                child for child in pkg_dir.iterdir()
                if child.is_dir() and _normalized_name(child.name) == _normalized_name(lib)
            ),
            None,
        )
    if source_root is None or not source_root.is_dir():
        return None
    sources = sorted(source_root.rglob("*.lean"), key=lambda path: (len(path.parts), str(path)))
    if not sources:
        return None
    root_init = source_root / "Init.lean"
    source = root_init if root_init.is_file() else sources[0]
    module = ".".join(source.relative_to(pkg_dir).with_suffix("").parts)
    return module, source


def library_build_status(name: str, cur: dict | None = None) -> dict:
    """Whether an installed library is compiled for the active pinned state.

    A checkout is not usable merely because its source revision matches the
    manifest. Optional libraries are ready only after their selected lean_lib
    target built and an import probe passed for this exact revision/toolchain.
    Mathlib readiness is covered by the ordinary preflight and its cached root
    artifact, so it does not require a local stamp.
    """
    cur = cur or current_state()
    pkg_dir = _package_dir(name)
    revision = cur.get("checkouts", {}).get(_normalized_name(name), "")
    if pkg_dir is None or not revision:
        return {"ready": False, "reason": "source not installed", "module": ""}

    lib = _lean_lib_target(pkg_dir, name)
    if not lib:
        return {
            "ready": False,
            "reason": "could not identify the package lean_lib target",
            "module": "",
        }
    probe = _probe_module(pkg_dir, lib)
    if probe is None:
        return {"ready": False, "reason": "library has no importable Lean module", "module": ""}
    module, source = probe
    artifact = pkg_dir / ".lake" / "build" / "lib" / "lean" / source.relative_to(pkg_dir)
    artifact = artifact.with_suffix(".olean")

    if name == "mathlib":
        return {
            "ready": artifact.is_file(),
            "reason": "" if artifact.is_file() else "compiled Mathlib artifact is missing",
            "module": module,
        }

    try:
        stamp = json.loads(_build_stamp_path(name).read_text(encoding="utf-8"))
    except Exception:
        stamp = {}
    expected = {
        "revision": revision,
        "toolchain": cur.get("toolchain", ""),
        "module": module,
    }
    ready = artifact.is_file() and all(stamp.get(key) == value for key, value in expected.items())
    return {
        "ready": ready,
        "reason": "" if ready else "build or import verification is required",
        "module": module,
    }


def selected_build_status(cur: dict | None = None) -> dict[str, dict]:
    cur = cur or current_state()
    return {name: library_build_status(name, cur) for name in selected_libraries()}


def _pins_satisfied(pins: dict[str, str], cur: dict) -> bool:
    """True only if EVERY pinned library is present and checked out at its pin.

    Checking just Mathlib's revision would call the project up to date while a
    newly selected library was never installed, making `apply` a silent no-op
    for exactly the case it exists to handle.
    """
    checkouts = cur.get("checkouts", {})
    for name, sha in pins.items():
        have = checkouts.get(name.lower())
        if have is None or have != sha:
            return False
    return True


def render_requires(pins: dict[str, str]) -> str:
    lines = [
        MANAGED_BEGIN + " -- generated by `scripts/env_setup/lean_libs.py apply`; do not edit by hand.",
        "-- Revisions are RESOLVED, not authored: `lean_libs.py resolve` reads each",
        "-- library's lean-toolchain history and picks the newest toolchain they all",
        "-- support, then pins every library (and Mathlib) to a matching revision.",
        "-- Never restore a floating ref such as `@ \"master\"` here: any lake invocation",
        "-- would silently check out a newer Mathlib and invalidate the compiled tree,",
        "-- and a Mathlib whose toolchain differs from `lean-toolchain` fails every",
        "-- import with `incompatible header`.",
    ]
    for name in sorted(pins, key=lambda n: (n != "mathlib", n)):
        lines.append(f'require {name} from git')
        lines.append(f'  "{KNOWN_LIBS[name]}" @ "{pins[name]}"')
    lines.append(MANAGED_END)
    return "\n".join(lines)


def write_managed_block(pins: dict[str, str]) -> None:
    text = LAKEFILE.read_text(encoding="utf-8")
    block = render_requires(pins)
    if MANAGED_BEGIN in text and MANAGED_END in text:
        head = text.split(MANAGED_BEGIN)[0]
        tail = text.split(MANAGED_END, 1)[1]
        text = head + block + tail
    else:  # first adoption: append before the default target if we can
        text = text.rstrip() + "\n\n" + block + "\n"
    LAKEFILE.write_text(text, encoding="utf-8")


def apply(res: Resolution, *, run_build: bool = True, adopt: bool = True) -> bool:
    """Adopt a resolution, restoring every touched file if anything fails."""
    if not res.feasible:
        print(f"refusing to apply an infeasible resolution: {res.reason}")
        return False
    snapshot = {
        p: p.read_text(encoding="utf-8")
        for p in (LAKEFILE, TOOLCHAIN_FILE, MANIFEST)
        if p.is_file()
    }

    def restore(why: str) -> bool:
        if adopt:
            for p, text in snapshot.items():
                p.write_text(text, encoding="utf-8")
            suffix = "\nrestored lakefile.lean, lean-toolchain, lake-manifest.json"
        else:
            suffix = ""
        print(f"\nFAILED: {why}{suffix}")
        return False

    if adopt:
        print(f"==> toolchain -> {res.toolchain}")
        TOOLCHAIN_FILE.write_text(res.toolchain + "\n", encoding="utf-8")
        for name, sha in res.pins.items():
            print(f"==> {name} -> {sha[:12]} ({res.staleness_days.get(name, 0)}d behind head)")
        write_managed_block(res.pins)

        before = json.loads(snapshot[MANIFEST]) if MANIFEST in snapshot else {"packages": []}
        before_revs = {p["name"]: p.get("rev") for p in before.get("packages", [])}

        print("==> lake update (scoped)")
        proc = subprocess.run(
            ["lake", "update", *res.pins.keys()],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=1800,
        )
        if proc.returncode != 0:
            return restore(f"lake update: {proc.stderr.strip()[-400:]}")

        # Hard gate: nothing we did not ask for may have moved.
        after = json.loads(MANIFEST.read_text(encoding="utf-8"))
        for p in after.get("packages", []):
            name, rev = p.get("name"), p.get("rev")
            if name in res.pins:
                continue
            if name in before_revs and before_revs[name] != rev:
                return restore(
                    f"lake update moved an unrequested package: {name} "
                    f"{str(before_revs[name])[:10]} -> {str(rev)[:10]}"
                )
    else:
        print("==> library pins are current; repairing compiled artifacts only")
        after = json.loads(MANIFEST.read_text(encoding="utf-8"))

    if not run_build:
        print("==> skipping build (--no-build)")
        return True

    # Mathlib comes prebuilt; everything else must be compiled from source.
    if adopt:
        print("==> lake exe cache get (mathlib oleans)")
        subprocess.run(["lake", "exe", "cache", "get"], cwd=str(REPO_ROOT), timeout=3600)

    # Build ONLY the selected libraries, never a blanket `lake build` of every
    # installed package. Each is built once here, on purpose, so that the first
    # blueprint node importing it is not paying for a from-source compile
    # inside a Lean-check timeout.
    # Use the package name Lake itself recorded, not our lowercase key: a
    # library's lakefile may camel-case it (physlib -> PhysLib), and building a
    # target that does not exist would roll back a good install.
    manifest_names = {
        str(p.get("name", "")).lower().replace("-", "").replace("_", ""): p.get("name")
        for p in after.get("packages", [])
    }
    for name in res.pins:
        if name == "mathlib":
            continue
        if library_build_status(name)["ready"]:
            print(f"==> {name} build already verified")
            continue
        _build_stamp_path(name).unlink(missing_ok=True)
        pkg = manifest_names.get(name.lower().replace("-", "").replace("_", "")) or name
        # Build ONLY the selected library, not every default target of its
        # package: physlib's defaults also include QuantumInfo, which roughly
        # doubles the work for a library nobody asked for.
        lib = _lean_lib_target(REPO_ROOT / ".lake" / "packages" / pkg, name)
        target = f"@{pkg}/{lib}" if lib else f"@{pkg}"
        if not lib:
            print(f"    (could not identify a lean_lib for {name}; building all its targets)")
        print(f"==> lake build {target}")
        proc = subprocess.run(
            ["lake", "build", target], cwd=str(REPO_ROOT), timeout=7200
        )
        if proc.returncode != 0:
            return restore(f"lake build {target} failed")
        probe = _probe_module(REPO_ROOT / ".lake" / "packages" / pkg, lib or name)
        if probe is None:
            return restore(f"could not find an import probe for {name}")
        module, _source = probe
        probe_path = REPO_ROOT / ".auto-blueprint" / "preflight" / f"Library{name.title()}.lean"
        probe_path.parent.mkdir(parents=True, exist_ok=True)
        probe_path.write_text(f"import {module}\n", encoding="utf-8")
        print(f"==> verify import {module}")
        proc = subprocess.run(
            ["lake", "env", "lean", str(probe_path)],
            cwd=str(REPO_ROOT), capture_output=True, text=True, timeout=300,
        )
        if proc.returncode != 0:
            detail = (proc.stdout + proc.stderr).strip()[-400:]
            return restore(f"import {module} failed: {detail}")
        BUILD_STATUS_DIR.mkdir(parents=True, exist_ok=True)
        _build_stamp_path(name).write_text(
            json.dumps(
                {
                    "revision": res.pins[name],
                    "toolchain": res.toolchain,
                    "module": module,
                    "verified_at": int(time.time()),
                },
                indent=2,
            ) + "\n",
            encoding="utf-8",
        )

    if adopt:
        print("==> lake build (this package)")
        proc = subprocess.run(["lake", "build"], cwd=str(REPO_ROOT), timeout=7200)
        if proc.returncode != 0:
            return restore("lake build failed")
    print("\nOK: " + ("applied and built." if adopt else "library builds repaired."))
    return True


# ---------------------------------------------------------------------------
# CLI


SELECTION_PATH = REPO_ROOT / ".auto-blueprint" / "lean-libs.json"


def selected_libraries() -> list[str]:
    """Libraries this project wants to stay mutually compatible.

    This is deliberately project-level and NOT derived from what happens to be
    installed or from what blueprints currently cite: a library you intend to
    adopt has to be in the resolution before it is installed, or the resolver
    would keep proposing a toolchain that the library you want cannot use.
    """
    try:
        data = json.loads(SELECTION_PATH.read_text(encoding="utf-8"))
        sel = [s for s in data.get("selected", []) if s in KNOWN_LIBS]
        if sel:
            return sel
    except Exception:
        pass
    installed = {
        p.lower().replace("-", "").replace("_", "") for p in current_state()["installed"]
    }
    return [n for n in KNOWN_LIBS if n in installed] or ["mathlib"]


def set_selected_libraries(libs: list[str]) -> list[str]:
    keep: list[str] = []
    for l in libs:  # order-preserving dedupe: a repeat would emit a duplicate require
        if l in KNOWN_LIBS and l not in keep:
            keep.append(l)
    if "mathlib" not in keep:
        keep.insert(0, "mathlib")  # everything is resolved against Mathlib
    SELECTION_PATH.parent.mkdir(parents=True, exist_ok=True)
    SELECTION_PATH.write_text(json.dumps({"selected": keep}, indent=2), encoding="utf-8")
    return keep


def load_cache() -> dict | None:
    try:
        return json.loads(CACHE_PATH.read_text(encoding="utf-8"))
    except Exception:
        return None


def save_cache(payload: dict) -> None:
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    CACHE_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def cmd_resolve(args) -> int:
    libs = [s.strip() for s in args.libs.split(",") if s.strip()] or selected_libraries()
    cached = load_cache()
    if (
        not args.refresh
        and cached
        and cached.get("libs") == libs
        and time.time() - cached.get("resolved_at", 0) < CACHE_TTL_S
    ):
        payload = cached
        if not args.json:
            age = int((time.time() - cached["resolved_at"]) // 60)
            print(f"(cached {age} min ago; --refresh to re-check)")
    else:
        res, _states = resolve(libs, quiet=args.json)
        payload = res.to_dict() | {"libs": libs, "current": current_state()}
        save_cache(payload)

    if args.json:
        print(json.dumps(payload, indent=2))
        return 0 if payload.get("feasible") else 1

    cur = payload.get("current", {})
    print(f"\ninstalled : {cur.get('toolchain','?')} | mathlib {str(cur.get('mathlib_rev',''))[:12]}")
    if not payload.get("feasible"):
        print(f"resolved  : INFEASIBLE - {payload.get('reason')}")
        for tc, names in (payload.get("groups") or {}).items():
            print(f"            {tc}: {', '.join(names)}")
        return 1
    print(f"resolved  : {payload['toolchain']}")
    for name, sha in payload["pins"].items():
        d = payload["staleness_days"].get(name, 0)
        print(f"            {name:10} {sha[:12]}  ({d}d behind head)")
    if payload["toolchain"] != cur.get("toolchain") or payload["pins"].get("mathlib") != cur.get("mathlib_rev"):
        print("\naction    : differs from installed - run `lean_libs.py apply` to adopt")
    else:
        print("\naction    : up to date")
    return 0


def cmd_apply(args) -> int:
    libs = [s.strip() for s in args.libs.split(",") if s.strip()] or selected_libraries()
    # Applying a subset of the selected set resolves against fewer constraints,
    # so it can pick a NEWER toolchain that the omitted libraries do not
    # support - silently undoing the compatibility the selection encodes, and
    # invalidating every compiled olean. Make that require an explicit opt-in.
    dropped = [l for l in selected_libraries() if l not in libs]
    if dropped and not args.narrow:
        print(
            f"refusing to apply without {', '.join(dropped)}: these are in the "
            f"selected set, and resolving without them can pick a toolchain "
            f"they do not support.\n"
            f"  use `select` to change the set, or --narrow to override."
        )
        return 1
    res, _ = resolve(libs)
    if not res.feasible:
        print(f"INFEASIBLE: {res.reason}")
        for tc, names in res.groups.items():
            print(f"  {tc}: {', '.join(names)}")
        return 1
    cur = current_state()
    pins_current = res.toolchain == cur["toolchain"] and _pins_satisfied(res.pins, cur)
    builds_current = all(
        library_build_status(name, cur)["ready"] for name in libs
    )
    if pins_current and (args.no_build or builds_current):
        print("already up to date; nothing to do")
        return 0
    if not args.yes:
        print(f"would adopt {res.toolchain} with " +
              ", ".join(f"{n}@{s[:8]}" for n, s in res.pins.items()))
        print("re-run with --yes to apply")
        return 0
    ok = apply(res, run_build=not args.no_build, adopt=not pins_current)
    if ok:
        save_cache(res.to_dict() | {"libs": libs, "current": current_state()})
    return 0 if ok else 1


def cmd_select(args) -> int:
    keep = set_selected_libraries([s.strip() for s in args.libs.split(",") if s.strip()])
    print("selected:", ", ".join(keep))
    print("run `lean_libs.py resolve` to see the newest toolchain they all support")
    return 0


def cmd_status(args) -> int:
    cur = current_state()
    print(f"toolchain   : {cur['toolchain']}")
    print(f"mathlib rev : {cur['mathlib_rev']}")
    print(f"installed   : {', '.join(cur['installed']) or '(none)'}")
    cached = load_cache()
    if cached:
        age = int((time.time() - cached.get("resolved_at", 0)) // 60)
        print(f"last resolve: {age} min ago -> {cached.get('toolchain') or cached.get('reason')}")
    else:
        print("last resolve: never")
    print(f"known libs  : {', '.join(sorted(KNOWN_LIBS))}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("resolve", help="find the newest toolchain all libraries support")
    p.add_argument("--libs", default="", help="comma-separated names (default: the selected set)")
    p.add_argument("--json", action="store_true")
    p.add_argument("--refresh", action="store_true", help="ignore the cached result")
    p.set_defaults(func=cmd_resolve)

    p = sub.add_parser("apply", help="adopt the resolved set (snapshots and restores on failure)")
    p.add_argument("--libs", default="", help="comma-separated names (default: the selected set)")
    p.add_argument("--yes", action="store_true", help="actually write and build")
    p.add_argument("--no-build", action="store_true", help="update pins without building")
    p.add_argument("--narrow", action="store_true",
                   help="allow applying fewer libraries than the selected set")
    p.set_defaults(func=cmd_apply)

    p = sub.add_parser("status", help="show installed vs last resolved")
    p.set_defaults(func=cmd_status)

    p = sub.add_parser("select", help="set the libraries to keep mutually compatible")
    p.add_argument("libs", help="comma-separated library names")
    p.set_defaults(func=cmd_select)

    args = parser.parse_args(argv)
    if not shutil.which("git"):
        print("git not found on PATH", file=sys.stderr)
        return 2
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
