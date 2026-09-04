"""Local web UI for the Auto-Blueprint pipeline.

Wraps the existing CLI scripts (generate_blueprint.py, refine_blueprint_with_lean.py,
validate_blueprint.py, build.py) behind a small browser dashboard with live logs.
Stdlib-only server; no new dependencies.

Run:

    uv run python scripts/webui.py            # http://127.0.0.1:8321
    uv run python scripts/webui.py --port 9000 --no-open
"""

from __future__ import annotations

import argparse
import base64
import atexit
import contextlib
import errno
import hashlib
import json
import mimetypes
import os
import re
import signal
import subprocess
import sys
import threading
import time
import urllib.parse
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from model_runners.api import choose_model, list_anthropic_model_ids, list_openai_model_ids
from model_runners.cli import choose_codex_base_model, choose_codex_escalation_model, list_codex_model_ids

from lean_preflight import check_lean_environment, default_lean_command

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = REPO_ROOT / "scripts"
BLUEPRINTS_DIR = REPO_ROOT / "blueprints"
SITE_DIR = REPO_ROOT / "site"
STATE_DIR = REPO_ROOT / ".auto-blueprint"
WEBUI_STATE = STATE_DIR / "webui.json"
LAST_REFINE_SETTINGS = STATE_DIR / "last-refine-settings.json"
UPLOAD_DIR = STATE_DIR / "webui-uploads"

RUNNER_BACKENDS = ["claude-code", "codex", "anthropic", "openai", "mock"]
REASONING_EFFORTS = ["", "low", "medium", "high", "xhigh"]
MODEL_SUGGESTIONS = {
    "anthropic": [],
    "claude-code": ["haiku", "sonnet", "opus"],
    "codex": [],
    "mock": [],
    "openai": [],
}

NAME_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")
# Library names reach a subprocess argument, so keep them to a safe charset.
LIB_NAME_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")

MODEL_SUGGESTION_CACHE: dict[str, object] = {"at": 0.0, "data": {}}
MODEL_SUGGESTION_TTL_S = 30

REFINE_SETTING_KEYS = {
    "name",
    "fast",
    "workers",
    "section_size",
    "max_trials",
    "conjecture_policy",
    "planner_tier",
    "runner_backend",
    "runner_model",
    "escalation_runner_backend",
    "escalation_runner_model",
    "reasoning_effort",
    "escalation_reasoning_effort",
    "timeout",
    "hard_timeout",
    "lean_command",
    "paper",
    "resume_mode",
}


def _read_last_refine_settings() -> dict:
    """Load the reusable Refine settings saved by the last accepted UI run."""
    try:
        payload = json.loads(LAST_REFINE_SETTINGS.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if not isinstance(payload, dict):
        return {}
    return {key: payload[key] for key in REFINE_SETTING_KEYS if key in payload}


def _write_last_refine_settings(payload: dict) -> None:
    """Atomically persist every visible setting from an accepted Refine run."""
    settings = {
        key: payload[key]
        for key in REFINE_SETTING_KEYS
        if key in payload and isinstance(payload[key], (str, int, float, bool))
    }
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    pending = LAST_REFINE_SETTINGS.with_suffix(".json.pending")
    pending.write_text(
        json.dumps(settings, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    os.replace(pending, LAST_REFINE_SETTINGS)


def _store_uploaded_file(filename: str, encoded_data: str) -> Path:
    """Store a browser upload at a stable content-addressed path.

    Last-used Refine settings may point at an uploaded paper after the Web UI
    restarts, so uploads cannot live in a process-scoped temporary directory.
    """
    raw_name = Path(filename or "paper.pdf").name
    safe = re.sub(r"[^A-Za-z0-9._-]", "_", raw_name) or "paper.pdf"
    data = base64.b64decode(encoded_data, validate=True)
    digest = hashlib.sha256(data).hexdigest()[:16]
    UPLOAD_DIR.mkdir(parents=True, exist_ok=True)
    dest = UPLOAD_DIR / f"{digest}-{safe}"
    if not dest.is_file():
        pending = UPLOAD_DIR / f".{dest.name}.pending"
        pending.write_bytes(data)
        os.replace(pending, dest)
    return dest


def _nonempty_suggestions(data: dict) -> bool:
    return any(bool(models) for models in data.values())


def model_suggestions() -> dict:
    now = time.time()
    cached = MODEL_SUGGESTION_CACHE.get("data")
    if (
        isinstance(cached, dict)
        and _nonempty_suggestions(cached)
        and now - float(MODEL_SUGGESTION_CACHE.get("at") or 0) < MODEL_SUGGESTION_TTL_S
    ):
        return {backend: list(models) for backend, models in cached.items()}

    suggestions = {backend: list(models) for backend, models in MODEL_SUGGESTIONS.items()}
    with contextlib.suppress(Exception):
        suggestions["openai"] = list_openai_model_ids(timeout=4)
    with contextlib.suppress(Exception):
        suggestions["anthropic"] = list_anthropic_model_ids(timeout=4)
    with contextlib.suppress(Exception):
        suggestions["codex"] = list_codex_model_ids(timeout=4)
    if _nonempty_suggestions(suggestions):
        MODEL_SUGGESTION_CACHE["at"] = now
        MODEL_SUGGESTION_CACHE["data"] = suggestions
    elif isinstance(cached, dict) and _nonempty_suggestions(cached):
        # A transient CLI/API lookup failure should not blank an already useful
        # dropdown. Try again on the next /api/state request.
        return {backend: list(models) for backend, models in cached.items()}
    return suggestions


def fast_runner_defaults(suggestions: dict | None = None) -> dict:
    """Resolved Web UI preset for the fast pipeline's two-tier model policy."""
    suggestions = suggestions or model_suggestions()
    if os.environ.get("OPENAI_API_KEY"):
        openai_models = suggestions.get("openai", [])
        return {
            "base": {
                "backend": "openai",
                "model": choose_model(openai_models, prefer=("mini", "nano")),
                "effort": "",
            },
            "escalation": {
                "backend": "openai",
                "model": choose_model(openai_models, prefer=("gpt", "o"), avoid=("mini", "nano")),
                "effort": "",
            },
            "source": "OPENAI_API_KEY",
        }
    if os.environ.get("ANTHROPIC_API_KEY"):
        anthropic_models = suggestions.get("anthropic", [])
        return {
            "base": {
                "backend": "anthropic",
                "model": choose_model(anthropic_models, prefer=("haiku",)),
                "effort": "",
            },
            "escalation": {
                "backend": "anthropic",
                "model": choose_model(anthropic_models, prefer=("sonnet", "opus"), avoid=("haiku",)),
                "effort": "",
            },
            "source": "ANTHROPIC_API_KEY",
        }
    return {
        "base": {
            "backend": "codex",
            "model": choose_codex_base_model(suggestions.get("codex", [])),
            "effort": "medium",
        },
        "escalation": {
            "backend": "codex",
            "model": choose_codex_escalation_model(suggestions.get("codex", [])),
            "effort": "high",
        },
        "source": "local Codex fallback",
    }


# ---------------------------------------------------------------------------
# Job management: one subprocess at a time, log buffered for polling.
# ---------------------------------------------------------------------------

class Job:
    def __init__(self, action: str, cmd: list[str]):
        self.action = action
        self.cmd = cmd
        self.started = time.time()
        self.status = "running"
        self.returncode: int | None = None
        self.lock = threading.Lock()
        log_dir = STATE_DIR / "webui-logs"
        log_dir.mkdir(parents=True, exist_ok=True)
        stamp = time.strftime("%Y%m%d-%H%M%S")
        self.log_path = log_dir / f"{stamp}-{action}.log"
        self._stdout_file = self.log_path.open("w", encoding="utf-8")
        self._stdout_file.write("$ " + " ".join(cmd) + "\n")
        self._stdout_file.flush()
        self.proc = subprocess.Popen(
            cmd,
            cwd=str(REPO_ROOT),
            stdout=self._stdout_file,
            stderr=subprocess.STDOUT,
            text=True,
            start_new_session=True,
        )
        threading.Thread(target=self._wait, daemon=True).start()
        _update_webui_job_state(self.proc.pid, self.proc.pid, action, self.log_path)

    def _log_control_event(self, message: str) -> None:
        with contextlib.suppress(Exception):
            self._stdout_file.write(f"==> webui control: {message}\n")
            self._stdout_file.flush()

    def _wait(self) -> None:
        rc = self.proc.wait()
        self._stdout_file.write(f"==> exit code {rc}\n")
        self._stdout_file.close()
        _clear_webui_job_state(self.proc.pid)
        with self.lock:
            self.returncode = rc
            if self.status != "stopped":
                self.status = "done" if rc == 0 else "failed"

    def stop(self) -> None:
        with self.lock:
            self.status = "stopped"
        try:
            self._log_control_event(
                f"sending SIGTERM to job process group {self.proc.pid} "
                f"(action={self.action}, pid={self.proc.pid})"
            )
            os.killpg(self.proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            return
        try:
            self.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            try:
                self._log_control_event(
                    f"job process group {self.proc.pid} ignored SIGTERM for 10s; sending SIGKILL"
                )
                os.killpg(self.proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.proc.wait()
        finally:
            _clear_webui_job_state(self.proc.pid)

    def snapshot(self, offset: int) -> dict:
        with self.lock:
            lines = _read_log_lines(self.log_path)
            # Cap one response; the client advances `offset` by `total` and
            # picks the rest up on the next poll a second later.
            chunk = _log_chunk(lines, offset)
            return {
                "action": self.action,
                "status": self.status,
                "returncode": self.returncode,
                "elapsed": int(time.time() - self.started),
                "total": offset + len(chunk),
                "lines": chunk,
                "log_path": str(self.log_path.relative_to(REPO_ROOT)),
            }

    def status_only(self) -> dict:
        """Job status without any log content, for the /api/state poll."""
        with self.lock:
            return {
                "action": self.action,
                "status": self.status,
                "returncode": self.returncode,
                "elapsed": int(time.time() - self.started),
                "log_path": str(self.log_path.relative_to(REPO_ROOT)),
            }


CURRENT_JOB: Job | None = None
JOB_LOCK = threading.Lock()


# ---------------------------------------------------------------------------
# Single-instance handling.
# ---------------------------------------------------------------------------

def _read_webui_state() -> dict:
    try:
        data = json.loads(WEBUI_STATE.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return data if isinstance(data, dict) else {}


def _write_webui_state(port: int) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    previous = _read_webui_state()
    state = {
        "pid": os.getpid(),
        "port": port,
        "url": f"http://127.0.0.1:{port}",
        "started": int(time.time()),
    }
    try:
        previous_job_pid = int(previous.get("job_pid") or 0)
    except (TypeError, ValueError):
        previous_job_pid = 0
    if _pid_is_running(previous_job_pid):
        for key in ("job_pid", "job_pgid", "job_action", "job_started", "job_log"):
            if key in previous:
                state[key] = previous[key]
    WEBUI_STATE.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")


def _merge_webui_state(updates: dict) -> None:
    STATE_DIR.mkdir(parents=True, exist_ok=True)
    state = _read_webui_state()
    state.update(updates)
    WEBUI_STATE.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")


def _update_webui_job_state(job_pid: int, job_pgid: int, action: str, log_path: Path | None = None) -> None:
    state = _read_webui_state()
    if state.get("pid") != os.getpid():
        return
    updates = {
        "job_pid": job_pid,
        "job_pgid": job_pgid,
        "job_action": action,
        "job_started": int(time.time()),
    }
    if log_path is not None:
        updates["job_log"] = str(log_path)
    _merge_webui_state(updates)


def _append_job_control_log(log_path: str | Path | None, message: str) -> None:
    if not log_path:
        return
    try:
        path = Path(log_path)
        if not path.is_absolute():
            path = REPO_ROOT / path
        with path.open("a", encoding="utf-8") as fh:
            fh.write(f"==> webui control: {message}\n")
    except OSError:
        pass


def _clear_webui_job_state(job_pid: int | None = None) -> None:
    state = _read_webui_state()
    if state.get("pid") != os.getpid():
        return
    if job_pid is not None and state.get("job_pid") != job_pid:
        return
    for key in ("job_pid", "job_pgid", "job_action", "job_started", "job_log"):
        state.pop(key, None)
    WEBUI_STATE.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")


def _clear_webui_state() -> None:
    state = _read_webui_state()
    if state.get("pid") != os.getpid():
        return
    try:
        job_pid = int(state.get("job_pid") or 0)
    except (TypeError, ValueError):
        job_pid = 0
    if _pid_is_running(job_pid):
        for key in ("pid", "port", "url", "started"):
            state.pop(key, None)
        WEBUI_STATE.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")
        return
    try:
        WEBUI_STATE.unlink()
    except FileNotFoundError:
        pass


def _kill_process_group(pgid: int, label: str, *, timeout: float = 10.0) -> bool:
    print(f"==> stopping {label} process group {pgid}")
    state = _read_webui_state()
    _append_job_control_log(
        state.get("job_log"),
        f"sending SIGTERM to process group {pgid} via _kill_process_group ({label})",
    )
    try:
        os.killpg(pgid, signal.SIGTERM)
    except ProcessLookupError:
        return True
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            os.killpg(pgid, 0)
        except ProcessLookupError:
            return True
        time.sleep(0.1)
    print(f"==> {label} process group {pgid} did not exit; killing")
    _append_job_control_log(
        state.get("job_log"),
        f"process group {pgid} ignored SIGTERM for {timeout:.1f}s; sending SIGKILL ({label})",
    )
    try:
        os.killpg(pgid, signal.SIGKILL)
    except ProcessLookupError:
        return True
    return False


def _pid_is_running(pid: int | None) -> bool:
    if not pid:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def _latest_run_log() -> Path | None:
    try:
        logs = list((STATE_DIR / "formalization").glob("*/run-*.log"))
    except OSError:
        return None
    if not logs:
        return None
    return max(logs, key=lambda path: path.stat().st_mtime)


# Cache of parsed log lines keyed by path, invalidated on (size, mtime). The
# UI polls once a second and every poll used to re-read and re-split the whole
# file; on a fast-growing log that is O(filesize) per request per client, and
# ThreadingHTTPServer runs those concurrently.
_LOG_CACHE: dict[str, tuple[int, float, list[str]]] = {}
_LOG_CACHE_LOCK = threading.Lock()
# Ceiling on one log response. A runaway run can emit thousands of lines in
# seconds (measured: 1732 lines / 149KB in 22s), and sending that in one body
# is what turns a disconnected browser into a BrokenPipeError. Bytes are the
# binding constraint, not lines - agent output lines are long and highly
# variable - so cap both. The client polls every second and advances `offset`,
# so a backlog drains over a few polls instead of one huge write.
MAX_LOG_LINES_PER_RESPONSE = 400
MAX_LOG_BYTES_PER_RESPONSE = 64 * 1024


def _log_chunk(lines: list[str], offset: int) -> list[str]:
    """Bounded slice of `lines` starting at `offset`, by count and by bytes."""
    chunk: list[str] = []
    used = 0
    for line in lines[offset : offset + MAX_LOG_LINES_PER_RESPONSE]:
        used += len(line) + 1
        if chunk and used > MAX_LOG_BYTES_PER_RESPONSE:
            break
        chunk.append(line)
    return chunk


def _read_log_lines(path: Path | None) -> list[str]:
    if path is None:
        return []
    key = str(path)
    try:
        st = path.stat()
    except OSError:
        return []
    with _LOG_CACHE_LOCK:
        cached = _LOG_CACHE.get(key)
        if cached and cached[0] == st.st_size and cached[1] == st.st_mtime:
            return cached[2]
    try:
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return []
    with _LOG_CACHE_LOCK:
        _LOG_CACHE[key] = (st.st_size, st.st_mtime, lines)
        if len(_LOG_CACHE) > 8:
            for stale in list(_LOG_CACHE)[:-8]:
                _LOG_CACHE.pop(stale, None)
    return lines


def _status_only(snapshot: dict | None) -> dict | None:
    """Strip log content from a snapshot dict (adopted-job path)."""
    if not snapshot:
        return None
    return {k: v for k, v in snapshot.items() if k not in ("lines", "total")}


def _adopted_job_snapshot(offset: int) -> dict | None:
    """Expose a still-running job after a Web UI restart/crash lost CURRENT_JOB."""
    state = _read_webui_state()
    try:
        job_pid = int(state.get("job_pid") or 0)
    except (TypeError, ValueError):
        job_pid = 0
    if not _pid_is_running(job_pid) or not _recorded_job_matches(job_pid):
        if state.get("pid") == os.getpid() and job_pid:
            _clear_webui_job_state(job_pid)
        return None

    log_path = Path(state["job_log"]) if state.get("job_log") else _latest_run_log()
    lines = _read_log_lines(log_path)
    try:
        started = int(state.get("job_started") or time.time())
    except (TypeError, ValueError):
        started = int(time.time())
    chunk = _log_chunk(lines, offset)
    payload = {
        "action": state.get("job_action", "run"),
        "status": "running",
        "returncode": None,
        "elapsed": max(0, int(time.time() - started)),
        "total": offset + len(chunk),
        "lines": chunk,
        "adopted": True,
    }
    if log_path is not None:
        payload["log_path"] = str(log_path.relative_to(REPO_ROOT))
    return payload


def _stop_recorded_job() -> bool:
    state = _read_webui_state()
    try:
        job_pid = int(state.get("job_pid") or 0)
        job_pgid = int(state.get("job_pgid") or job_pid)
    except (TypeError, ValueError):
        return False
    if not _pid_is_running(job_pid) or not _recorded_job_matches(job_pid):
        return False
    try:
        _append_job_control_log(
            state.get("job_log"),
            f"sending SIGTERM to recorded job process group {job_pgid} "
            f"(job_pid={job_pid}, requested through /api/stop without live Job object)",
        )
        os.killpg(job_pgid, signal.SIGTERM)
    except ProcessLookupError:
        return False
    return True


def _pid_command(pid: int) -> str:
    proc = subprocess.run(
        ["ps", "-p", str(pid), "-o", "command="],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return ""
    return proc.stdout.strip()


def _recorded_job_matches(pid: int) -> bool:
    command = _pid_command(pid)
    if not command:
        return False
    markers = (
        "scripts/refine_blueprint_with_lean.py",
        "scripts/formalize_blueprint.py",
        "scripts/generate_blueprint.py",
        "scripts/env_setup/setup_lean.py",
        "scripts/validate_blueprint.py",
        "scripts/build.py",
    )
    return any(marker in command for marker in markers) and (
        "Auto-Blueprint" in command or str(REPO_ROOT) in command
    )


def _looks_like_previous_webui(pid: int) -> bool:
    command = _pid_command(pid)
    return "webui.py" in command


def _terminate_webui_pid(pid: int, label: str) -> bool:
    print(f"==> stopping previous Auto-Blueprint UI at {label} (pid {pid})")
    try:
        os.kill(pid, signal.SIGTERM)
    except ProcessLookupError:
        return True
    deadline = time.time() + 5
    while time.time() < deadline:
        if not _pid_is_running(pid):
            return True
        time.sleep(0.1)
    print(f"==> previous UI pid {pid} did not exit; killing")
    try:
        os.kill(pid, signal.SIGKILL)
    except ProcessLookupError:
        return True
    deadline = time.time() + 2
    while time.time() < deadline:
        if not _pid_is_running(pid):
            return True
        time.sleep(0.1)
    return not _pid_is_running(pid)


def _pids_listening_on_port(port: int) -> list[int]:
    proc = subprocess.run(
        ["lsof", "-nP", f"-iTCP:{port}", "-sTCP:LISTEN", "-t"],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return []
    pids: list[int] = []
    for line in proc.stdout.splitlines():
        try:
            pids.append(int(line.strip()))
        except ValueError:
            continue
    return pids


def _stop_webui_on_port(port: int) -> bool:
    stopped = False
    for pid in _pids_listening_on_port(port):
        if pid == os.getpid() or not _looks_like_previous_webui(pid):
            continue
        stopped = _terminate_webui_pid(pid, f"http://127.0.0.1:{port}") or stopped
    return stopped


def _stale_pipeline_process_groups() -> dict[int, str]:
    proc = subprocess.run(
        ["ps", "-axo", "pid,pgid,command"],
        capture_output=True,
        text=True,
    )
    if proc.returncode != 0:
        return {}
    groups: dict[int, str] = {}
    state = _read_webui_state()
    try:
        recorded_job_pgid = int(state.get("job_pgid") or 0)
    except (TypeError, ValueError):
        recorded_job_pgid = 0
    markers = (
        "scripts/refine_blueprint_with_lean.py",
        "scripts/formalize_blueprint.py",
        "scripts/generate_blueprint.py",
    )
    for line in proc.stdout.splitlines()[1:]:
        parts = line.strip().split(None, 2)
        if len(parts) != 3:
            continue
        pid_s, pgid_s, command = parts
        if not any(marker in command for marker in markers):
            continue
        if "Auto-Blueprint" not in command and str(REPO_ROOT) not in command:
            continue
        try:
            pid = int(pid_s)
            pgid = int(pgid_s)
        except ValueError:
            continue
        if pid == os.getpid() or pgid == os.getpgrp():
            continue
        if recorded_job_pgid and pgid == recorded_job_pgid:
            continue
        groups[pgid] = command[:120]
    return groups


def _stop_stale_pipeline_jobs() -> None:
    for pgid, command in _stale_pipeline_process_groups().items():
        _kill_process_group(pgid, f"stale Auto-Blueprint job ({command})")


def _stop_previous_webui() -> None:
    state = _read_webui_state()
    try:
        job_pid = int(state.get("job_pid") or 0)
    except (TypeError, ValueError):
        job_pid = 0
    has_live_job = _pid_is_running(job_pid)
    try:
        pid = int(state.get("pid") or 0)
    except (TypeError, ValueError):
        pid = 0
    if pid <= 0 or pid == os.getpid():
        return
    if not _pid_is_running(pid):
        if not has_live_job:
            try:
                WEBUI_STATE.unlink()
            except FileNotFoundError:
                pass
        return
    if not _looks_like_previous_webui(pid):
        print(f"==> ignoring stale Web UI state for unrelated pid {pid}")
        return

    old_url = state.get("url") or f"http://127.0.0.1:{state.get('port', '?')}"
    if _terminate_webui_pid(pid, str(old_url)):
        if not has_live_job:
            try:
                WEBUI_STATE.unlink()
            except FileNotFoundError:
                pass
        return
    print("==> trying next free port")


def _stop_current_job() -> None:
    with JOB_LOCK:
        job = CURRENT_JOB
    if job is not None and job.status == "running":
        job.stop()


def start_job(action: str, cmd: list[str]) -> tuple[bool, str]:
    global CURRENT_JOB
    with JOB_LOCK:
        if CURRENT_JOB is not None and CURRENT_JOB.status == "running":
            return False, f"a `{CURRENT_JOB.action}` job is still running; stop it first"
        if _adopted_job_snapshot(0) is not None:
            return False, "a previous Auto-Blueprint job is still running; stop it first"
        CURRENT_JOB = Job(action, cmd)
        return True, ""


# ---------------------------------------------------------------------------
# Command construction from form parameters.
# ---------------------------------------------------------------------------

def runner_spec_from(p: dict, backend_key: str, model_key: str, default_backend: str = "claude-code") -> str:
    backend = p.get(backend_key, default_backend)
    if backend not in RUNNER_BACKENDS:
        raise ValueError(f"unknown runner backend: {backend}")
    model = (p.get(model_key) or "").strip()
    return f"{backend}:{model}" if model else backend


def runner_spec(p: dict) -> str:
    return runner_spec_from(p, "runner_backend", "runner_model")


def effort_arg(p: dict, effort_key: str, backend_key: str, flag: str) -> list[str]:
    effort = (p.get(effort_key) or "").strip()
    if not effort:
        return []
    if p.get(backend_key) != "codex":
        raise ValueError(f"{flag} is only supported for the codex runner")
    if effort not in REASONING_EFFORTS:
        raise ValueError(f"unknown reasoning effort: {effort}")
    return [flag, effort]


def common_runner_args(p: dict) -> list[str]:
    args = ["--runner", runner_spec(p)]
    args += effort_arg(p, "reasoning_effort", "runner_backend", "--reasoning-effort")
    timeout = str(p.get("timeout") or "").strip()
    if timeout:
        if not timeout.isdigit() or int(timeout) < 1:
            raise ValueError("timeout must be a positive number of seconds")
        args += ["--timeout", timeout]
    return args


def positive_int_field(p: dict, key: str, label: str) -> str:
    value = str(p.get(key) or "").strip()
    if value:
        if not value.isdigit() or int(value) < 1:
            raise ValueError(f"{label} must be a positive number of seconds")
    return value


def build_command(action: str, p: dict) -> list[str]:
    py = sys.executable
    if action == "setup_lean":
        cmd = [py, str(SCRIPTS / "env_setup" / "setup_lean.py"), "--install-elan"]
        if p.get("no_cache"):
            cmd.append("--no-cache")
        return cmd

    if action == "generate":
        paper = (p.get("paper") or "").strip()
        if not paper:
            raise ValueError("paper path/URL is required")
        cmd = [py, str(SCRIPTS / "generate_blueprint.py"), paper]
        name = (p.get("name") or "").strip()
        if name:
            if not NAME_RE.match(name):
                raise ValueError("name must be lowercase and url-safe (a-z, 0-9, dashes)")
            cmd += ["--name", name]
        cmd += common_runner_args(p)
        if p.get("force"):
            cmd.append("--force")
        if p.get("no_build"):
            cmd.append("--no-build")
        return cmd

    if action == "refine":
        name = (p.get("name") or "").strip()
        if not name:
            raise ValueError("pick a blueprint to refine")
        fast = bool(p.get("fast", True))
        script = "formalize_blueprint.py" if fast else "refine_blueprint_with_lean.py"
        cmd = [py, str(SCRIPTS / script), name]
        cmd += common_runner_args(p)
        if fast:
            workers = str(p.get("workers") or "").strip()
            if workers:
                if not workers.isdigit() or int(workers) < 1:
                    raise ValueError("workers must be a positive number")
                cmd += ["--workers", workers]
            section_size = str(p.get("section_size") or "").strip()
            if section_size:
                if not section_size.isdigit() or int(section_size) < 1:
                    raise ValueError("section size must be a positive number")
                cmd += ["--section-size", section_size]
            conjecture_policy = str(
                p.get("conjecture_policy") or "record"
            ).strip()
            if conjecture_policy not in {"record", "attempt"}:
                raise ValueError("conjecture policy must be record or attempt")
            cmd += ["--conjecture-policy", conjecture_policy]
            planner_tier = str(p.get("planner_tier") or "escalation").strip()
            if planner_tier not in {"base", "escalation"}:
                raise ValueError("planner model must be base or escalation")
            cmd += ["--planner-tier", planner_tier]
            escalation_runner = runner_spec_from(
                p,
                "escalation_runner_backend",
                "escalation_runner_model",
                default_backend=(p.get("runner_backend") or "claude-code"),
            )
            if escalation_runner != runner_spec(p):
                cmd += ["--escalation-runner", escalation_runner]
            cmd += effort_arg(
                p,
                "escalation_reasoning_effort",
                "escalation_runner_backend",
                "--escalation-effort",
            )
        hard_timeout = positive_int_field(p, "hard_timeout", "hard-node timeout")
        if hard_timeout:
            base_timeout = int(str(p.get("timeout") or "300").strip() or "300")
            if int(hard_timeout) < base_timeout:
                raise ValueError("hard-node timeout must be at least the base timeout")
            cmd += ["--hard-timeout", hard_timeout]
        trials = str(p.get("max_trials") or "3").strip()
        if not trials.isdigit() or int(trials) < 1:
            raise ValueError("max trials must be a positive number")
        cmd += ["--max-trials", trials]
        paper = (p.get("paper") or "").strip()
        if paper:
            cmd += ["--paper", paper]
        lean_command = (p.get("lean_command") or "").strip()
        if lean_command:
            cmd += ["--lean-command", lean_command]
        # Always send the starting point explicitly. `--continue` is the fast
        # pipeline's default, so omitting the choice would make Fresh appear to
        # work in the UI while the CLI silently resumed mutable state.
        if "resume_mode" in p:
            resume_mode = str(p.get("resume_mode") or "latest").strip()
        elif "continue_run" in p:
            # Backward compatibility for older clients and saved tests.
            resume_mode = "latest" if p.get("continue_run") else "fresh"
        else:
            resume_mode = "latest"
        if resume_mode not in {"latest", "phase1", "fresh"}:
            raise ValueError("starting point must be latest, phase1, or fresh")
        if resume_mode == "phase1" and not fast:
            raise ValueError(
                "the saved Phase 1 checkpoint is available only in the fast pipeline"
            )
        cmd.append(
            {
                "latest": "--continue",
                "phase1": "--continue-phase1",
                "fresh": "--fresh",
            }[resume_mode]
        )
        return cmd

    if action == "validate":
        cmd = [py, str(SCRIPTS / "validate_blueprint.py")]
        cmd += [n for n in p.get("names", []) if NAME_RE.match(n)]
        return cmd

    if action == "build":
        cmd = [py, str(SCRIPTS / "build.py")]
        cmd += [n for n in p.get("names", []) if NAME_RE.match(n)]
        if p.get("strict"):
            cmd.append("--strict")
        return cmd

    if action == "libraries":
        # Adopting a resolved set rewrites lean-toolchain, the managed block
        # of lakefile.lean, and the manifest; lean_libs.py snapshots all three
        # and restores them if any step fails. It runs through the normal job
        # runner so it can never overlap a formalization run.
        libs = [n for n in (p.get("libs") or []) if LIB_NAME_RE.match(n)]
        cmd = [py, str(SCRIPTS / "env_setup" / "lean_libs.py"), "apply", "--yes"]
        # No explicit list => apply the saved selection (the CLI default). Only
        # pass --libs when the caller really named a set, so the CLI's guard
        # against applying a narrower-than-selected set stays meaningful.
        if libs:
            cmd += ["--libs", ",".join(libs)]
        if p.get("no_build"):
            cmd.append("--no-build")
        return cmd

    raise ValueError(f"unknown action: {action}")


def libraries_payload(refresh: bool = False) -> dict:
    """Installed Lean libraries plus the newest mutually-compatible set.

    Resolution is a pure read of each library's `lean-toolchain` history, so
    it is safe to run on a UI poll; it is cached for a day because the answer
    only moves when a library publishes a new toolchain.
    """
    try:
        from env_setup import lean_libs
    except Exception as exc:  # noqa: BLE001
        return {"ok": False, "message": f"resolver unavailable: {exc}"}
    try:
        current = lean_libs.current_state()
        build_status = lean_libs.selected_build_status(current)
        known = sorted(lean_libs.KNOWN_LIBS)
        # Project-level: a library you intend to adopt must be in the
        # resolution BEFORE it is installed, or the resolver keeps proposing a
        # toolchain that library cannot use.
        selected = lean_libs.selected_libraries()
        cached = lean_libs.load_cache()
        fresh = (
            cached
            and not refresh
            and cached.get("libs") == selected
            and time.time() - cached.get("resolved_at", 0) < lean_libs.CACHE_TTL_S
        )
        if fresh:
            resolution = cached
        else:
            res, _states = lean_libs.resolve(selected, quiet=True)
            resolution = res.to_dict() | {"libs": selected, "current": current}
            lean_libs.save_cache(resolution)
        age_s = int(time.time() - resolution.get("resolved_at", 0))
        return {
            "ok": True,
            "current": current,
            "known": known,
            "selected": selected,
            "build_status": build_status,
            "resolution": resolution,
            "checked_age_s": age_s,
            # Every pinned library must be present at its pin - checking only
            # Mathlib's rev would report "up to date" while a newly selected
            # library was never installed.
            "up_to_date": bool(
                resolution.get("feasible")
                and resolution.get("toolchain") == current.get("toolchain")
                and lean_libs._pins_satisfied(resolution.get("pins") or {}, current)
                and all(
                    status.get("ready")
                    for status in build_status.values()
                )
            ),
        }
    except Exception as exc:  # noqa: BLE001
        return {"ok": False, "message": str(exc)}


def _meta_libraries(meta_path: Path) -> list[str]:
    try:
        import yaml

        data = yaml.safe_load(meta_path.read_text(encoding="utf-8")) or {}
    except Exception:  # noqa: BLE001
        return []
    libs = data.get("libraries")
    if isinstance(libs, str):
        libs = [part.strip() for part in libs.split(",")]
    return [str(x).strip() for x in libs if str(x).strip()] if isinstance(libs, list) else []


_META_LIBS_HEADER = [
    "# Lean libraries searched for candidate declarations, highest priority",
    "# first. Managed by the web UI's Lean libraries tab.",
]


def _set_meta_libraries(meta_path: Path, libs: list[str]) -> None:
    """Rewrite a blueprint's `libraries:` order in place.

    Edited as text rather than via a yaml round-trip: meta.yml is
    comment-documented for humans and safe_load/dump would strip every comment.
    """
    lines = meta_path.read_text(encoding="utf-8").splitlines()
    out: list[str] = []
    i = 0
    while i < len(lines):
        # Strip the previously written header too, or every save appends
        # another copy of it.
        if lines[i] in _META_LIBS_HEADER:
            i += 1
            continue
        if re.match(r"^libraries\s*:", lines[i]):
            i += 1
            while i < len(lines) and re.match(r"^\s*-\s", lines[i]):
                i += 1  # drop an existing block-style list
            continue
        out.append(lines[i])
        i += 1
    while out and not out[-1].strip():
        out.pop()
    if libs:
        out.extend(_META_LIBS_HEADER)
        out.append("libraries: [" + ", ".join(libs) + "]")
    meta_path.write_text("\n".join(out) + "\n", encoding="utf-8")


def blueprint_libraries_payload(name: str, order: list[str] | None = None) -> dict:
    """Per-blueprint search priority (meta.yml `libraries:`).

    Distinct from the project-level selected set: selection decides what is
    INSTALLED and kept mutually compatible, this decides what Generate/Refine
    SEARCH, and in what order, for one paper.
    """
    try:
        from env_setup import lean_libs

        meta_path = BLUEPRINTS_DIR / name / "meta.yml"
        if not meta_path.is_file():
            return {"ok": False, "message": f"no meta.yml for {name}"}
        installed = lean_libs.selected_libraries()
        if order is not None:
            keep: list[str] = []
            for lib in order:  # ignore unknown/uninstalled, preserve given order
                if lib in installed and lib not in keep:
                    keep.append(lib)
            _set_meta_libraries(meta_path, keep)
        current = _meta_libraries(meta_path)
        return {
            "ok": True,
            "name": name,
            "available": installed,
            "order": current,
            # No declared order => the selected set, in selection order.
            "effective": current or installed,
        }
    except Exception as exc:  # noqa: BLE001
        return {"ok": False, "message": str(exc)}


def library_update_brief(refresh: bool = False) -> dict:
    """What is installed vs. what the resolver says should be, per library.

    Reads the cached resolution by default so the Lean status box stays fast:
    resolving hits the network (mirror fetches). `refresh` forces a re-resolve.
    """
    try:
        from env_setup import lean_libs

        selected = lean_libs.selected_libraries()
        cached = None if refresh else lean_libs.load_cache()
        if cached and cached.get("libs") != selected:
            cached = None  # resolved for a different set; not comparable
        if cached and time.time() - cached.get("resolved_at", 0) >= lean_libs.CACHE_TTL_S:
            cached = None  # past the daily TTL: re-check upstream unprompted
        if cached is None:
            res, _states = lean_libs.resolve(selected, quiet=True)
            cached = res.to_dict() | {"libs": selected}
            lean_libs.save_cache(cached)
        cur = lean_libs.current_state()
        build_status = lean_libs.selected_build_status(cur)
        checkouts = cur.get("checkouts", {})
        pins = cached.get("pins") or {}
        stale = cached.get("staleness_days") or {}
        rows = []
        for name in selected:
            want = pins.get(name)
            have = checkouts.get(name.lower())
            rows.append({
                "name": name,
                "installed": have,
                "resolved": want,
                # Not installed at all, or installed at a different revision.
                "needs_update": bool(want) and have != want,
                "behind_days": stale.get(name),
                "build_ready": bool(build_status.get(name, {}).get("ready")),
                "build_reason": build_status.get(name, {}).get("reason", ""),
                "probe_module": build_status.get(name, {}).get("module", ""),
            })
        tc_now, tc_want = cur.get("toolchain"), cached.get("toolchain")
        return {
            "ok": True,
            "feasible": bool(cached.get("feasible")),
            "reason": cached.get("reason") or "",
            "toolchain": tc_want,
            "toolchain_installed": tc_now,
            "toolchain_changes": bool(tc_want) and tc_now != tc_want,
            "rows": rows,
            "needs_build": any(not r["build_ready"] for r in rows),
            "needs_update": any(r["needs_update"] for r in rows)
                            or any(not r["build_ready"] for r in rows)
                            or (bool(tc_want) and tc_now != tc_want),
            "checked_age_s": int(time.time() - cached.get("resolved_at", 0)),
        }
    except Exception as exc:  # noqa: BLE001
        return {"ok": False, "message": str(exc)}


def lean_status_payload(refresh_libs: bool = False) -> dict:
    """Return a JSON-ready Lean setup status for the browser UI."""
    try:
        result = check_lean_environment(REPO_ROOT, lean_command=default_lean_command(REPO_ROOT))
        payload = result.to_dict()
        # Setup can be "ready" while libraries are behind: report both here so
        # one panel answers "can Lean run?" and "is anything out of date?".
        payload["libraries"] = library_update_brief(refresh=refresh_libs)
        return payload
    except Exception as exc:  # noqa: BLE001 - status endpoint should explain all setup failures
        return {
            "ok": False,
            "message": str(exc),
            "command": ["lake", "env", "lean"],
            "elapsed_s": 0.0,
            "stdout": "",
            "stderr": "",
        }


# ---------------------------------------------------------------------------
# Blueprint discovery for the dashboard.
# ---------------------------------------------------------------------------

def list_blueprints() -> list[dict]:
    try:
        import yaml
    except ImportError:
        yaml = None
    out = []
    if not BLUEPRINTS_DIR.is_dir():
        return out
    for d in sorted(BLUEPRINTS_DIR.iterdir()):
        if not d.is_dir():
            continue
        title = d.name
        meta_file = d / "meta.yml"
        if yaml and meta_file.is_file():
            try:
                meta = yaml.safe_load(meta_file.read_text()) or {}
                title = meta.get("title") or d.name
            except Exception:
                pass
        out.append({
            "name": d.name,
            "title": title,
            "built": (SITE_DIR / d.name / "index.html").is_file(),
            "phase1_checkpoint": (
                STATE_DIR
                / "formalization"
                / d.name
                / "phase1-checkpoint"
                / "manifest.json"
            ).is_file(),
        })
    return out


# ---------------------------------------------------------------------------
# HTTP handler.
# ---------------------------------------------------------------------------

class Handler(BaseHTTPRequestHandler):
    def log_message(self, fmt, *args):  # quiet the default access log
        pass

    # -- helpers ------------------------------------------------------------

    def send_json(self, obj: dict, code: int = 200) -> None:
        body = json.dumps(obj).encode()
        try:
            self.send_response(code)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        except (BrokenPipeError, ConnectionResetError):
            # The browser navigated away, reloaded, or fell behind mid-write.
            # Small responses never surface this (they fit the socket buffer),
            # so it only appears when a response is large - exactly when a run
            # is misbehaving and the log is growing fast. Nothing to recover.
            self.close_connection = True

    def read_json(self) -> dict:
        length = int(self.headers.get("Content-Length", 0))
        if length <= 0:
            return {}
        return json.loads(self.rfile.read(length))

    def send_file(self, path: Path) -> None:
        ctype = mimetypes.guess_type(str(path))[0] or "application/octet-stream"
        data = path.read_bytes()
        try:
            self.send_response(200)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data)))
            self.end_headers()
            self.wfile.write(data)
        except (BrokenPipeError, ConnectionResetError):
            self.close_connection = True

    # -- routes -------------------------------------------------------------

    def do_GET(self) -> None:
        path, _, query = self.path.partition("?")
        if path == "/":
            body = PAGE.encode()
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
        elif path == "/api/state":
            suggestions = model_suggestions()
            # Status only: the log is tailed incrementally through /api/log,
            # so never ship log lines here. This endpoint used to send
            # snapshot(0) - the ENTIRE log - on every poll, which is invisible
            # for a normal 5-10KB run log but became a ~150KB write per poll
            # when a misbehaving run wrote 1732 lines in 22 seconds.
            try:
                adopted = None if CURRENT_JOB else _adopted_job_snapshot(0)
            except Exception:
                adopted = None
            job_status = CURRENT_JOB.status_only() if CURRENT_JOB else _status_only(adopted)
            self.send_json({
                "blueprints": list_blueprints(),
                "backends": RUNNER_BACKENDS,
                "efforts": [e for e in REASONING_EFFORTS if e],
                "model_suggestions": suggestions,
                "runner_defaults": fast_runner_defaults(suggestions),
                "last_refine_settings": _read_last_refine_settings(),
                "job": job_status,
            })
        elif path == "/api/lean/status":
            params = {k: v[0] for k, v in urllib.parse.parse_qs(query).items()}
            self.send_json(lean_status_payload(refresh_libs=params.get("refresh") == "1"))
        elif path == "/api/libraries":
            # urlencoded: the browser sends commas as %2C, and a raw split would
            # hand LIB_NAME_RE one undecodable blob and quietly select nothing.
            params = {k: v[0] for k, v in urllib.parse.parse_qs(query).items()}
            if params.get("select"):
                try:
                    from env_setup import lean_libs

                    names = [
                        n for n in params["select"].split(",") if LIB_NAME_RE.match(n)
                    ]
                    lean_libs.set_selected_libraries(names)
                except Exception:  # noqa: BLE001
                    pass
            self.send_json(
                libraries_payload(
                    refresh=params.get("refresh") == "1" or bool(params.get("select"))
                )
            )
        elif path == "/api/blueprint-libraries":
            params = {k: v[0] for k, v in urllib.parse.parse_qs(query).items()}
            name = params.get("name", "")
            if not LIB_NAME_RE.match(name):
                self.send_json({"ok": False, "message": "bad blueprint name"})
            else:
                order = None
                if "order" in params:
                    order = [
                        n for n in params["order"].split(",") if LIB_NAME_RE.match(n)
                    ]
                self.send_json(blueprint_libraries_payload(name, order))
        elif path == "/api/log":
            params = dict(kv.split("=", 1) for kv in query.split("&") if "=" in kv)
            offset = int(params.get("offset", 0))
            if CURRENT_JOB is None:
                adopted = _adopted_job_snapshot(offset)
                self.send_json(adopted if adopted else {"status": "idle", "lines": [], "total": 0})
            else:
                self.send_json(CURRENT_JOB.snapshot(offset))
        elif path.startswith("/site/"):
            rel = path[len("/site/"):] or "index.html"
            target = (SITE_DIR / rel).resolve()
            if target.is_dir():
                target = target / "index.html"
            if not str(target).startswith(str(SITE_DIR.resolve())) or not target.is_file():
                self.send_json({"error": "not found"}, 404)
            else:
                self.send_file(target)
        else:
            self.send_json({"error": "not found"}, 404)

    def do_POST(self) -> None:
        try:
            if self.path == "/api/run":
                p = self.read_json()
                cmd = build_command(p.get("action", ""), p)
                ok, err = start_job(p.get("action", ""), cmd)
                if ok:
                    if p.get("action") == "refine":
                        with contextlib.suppress(OSError):
                            _write_last_refine_settings(p)
                    self.send_json({"ok": True})
                else:
                    self.send_json({"error": err}, 409)
            elif self.path == "/api/stop":
                if CURRENT_JOB and CURRENT_JOB.status == "running":
                    CURRENT_JOB.stop()
                else:
                    _stop_recorded_job()
                self.send_json({"ok": True})
            elif self.path == "/api/upload":
                p = self.read_json()
                dest = _store_uploaded_file(
                    str(p.get("filename") or "paper.pdf"),
                    str(p.get("data") or ""),
                )
                self.send_json({"ok": True, "path": str(dest)})
            else:
                self.send_json({"error": "not found"}, 404)
        except (ValueError, KeyError, json.JSONDecodeError) as exc:
            self.send_json({"error": str(exc)}, 400)


# ---------------------------------------------------------------------------
# Frontend (single page, inline CSS/JS).
# ---------------------------------------------------------------------------

PAGE = r"""<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Auto-Blueprint</title>
<style>
  :root {
    --bg: #f6f7f9; --panel: #ffffff; --border: #dcdfe4; --text: #1a1f27;
    --muted: #5c6572; --accent: #2563eb; --accent-text: #ffffff;
    --ok: #15803d; --bad: #b91c1c; --log-bg: #11151c; --log-text: #d3dae4;
  }
  @media (prefers-color-scheme: dark) {
    :root {
      --bg: #11151c; --panel: #1a2028; --border: #2c3542; --text: #e5eaf1;
      --muted: #8b95a3; --accent: #3b82f6; --log-bg: #0b0e13; --log-text: #c9d2dd;
    }
  }
  * { box-sizing: border-box; }
  body { margin: 0; font: 14px/1.5 -apple-system, "SF Pro Text", "Segoe UI", sans-serif;
         background: var(--bg); color: var(--text); }
  header { padding: 14px 22px; border-bottom: 1px solid var(--border);
           display: flex; align-items: baseline; gap: 12px; }
  header h1 { font-size: 17px; margin: 0; }
  header span { color: var(--muted); font-size: 12.5px; }
  main { display: grid; grid-template-columns: 400px 1fr; gap: 18px;
         padding: 18px 22px; max-width: 1400px; }
  @media (max-width: 900px) { main { grid-template-columns: 1fr; } }
  .panel { background: var(--panel); border: 1px solid var(--border);
           border-radius: 10px; padding: 16px; }
  .tabs { display: flex; gap: 6px; margin-bottom: 14px; flex-wrap: wrap; }
  .tabs button { border: 1px solid var(--border); background: transparent; color: var(--text);
                 padding: 5px 12px; border-radius: 999px; cursor: pointer; font-size: 13px; }
  .tabs button.active { background: var(--accent); border-color: var(--accent);
                        color: var(--accent-text); }
  label { display: block; margin: 10px 0 3px; font-size: 12.5px; color: var(--muted); }
  input[type=text], input[type=number], select {
    width: 100%; padding: 7px 9px; border: 1px solid var(--border); border-radius: 7px;
    background: var(--bg); color: var(--text); font-size: 13.5px; }
  .row { display: flex; gap: 10px; } .row > div { flex: 1; }
  .check { display: flex; align-items: center; gap: 7px; margin-top: 10px;
           font-size: 13px; color: var(--text); }
  .check label { margin: 0; color: var(--text); }
  .actions { margin-top: 16px; display: flex; gap: 8px; align-items: center; }
  .run { background: var(--accent); color: var(--accent-text); border: none;
         padding: 8px 20px; border-radius: 7px; font-size: 14px; cursor: pointer; }
  .run:disabled { opacity: .5; cursor: default; }
  .secondary { background: transparent; color: var(--text); border: 1px solid var(--border);
               padding: 6px 10px; border-radius: 7px; cursor: pointer; font-size: 13px; }
  .secondary:disabled { opacity: .45; cursor: default; }
  .stop { background: transparent; color: var(--bad); border: 1px solid var(--bad);
          padding: 7px 14px; border-radius: 7px; cursor: pointer; display: none; }
  .hint { font-size: 12px; color: var(--muted); margin-top: 4px; }
  table.libs { border-collapse: collapse; margin: .5rem 0; font-size: 13px; }
  table.libs th, table.libs td { text-align: left; padding: 3px 14px 3px 0; }
  table.libs th { color: var(--muted); font-weight: 500; }
  .error { color: var(--bad); font-size: 13px; margin-top: 10px; min-height: 18px; }
  .leanbox { border: 1px solid var(--border); border-radius: 7px; padding: 9px;
             margin-top: 10px; font-size: 12.5px; color: var(--muted); background: var(--bg); }
  .leanbox.ok { border-color: var(--ok); color: var(--ok); }
  .leanbox.bad { border-color: var(--bad); color: var(--bad); }
  .leanbox button { margin-top: 7px; border: 1px solid var(--border); border-radius: 6px;
                    background: transparent; color: var(--text); padding: 5px 9px; cursor: pointer; }
  .leanbox code { color: var(--text); }
  /* NOTE: this page is a Python raw string, so a CSS escape like '\25B8' would
     need care; use the literal glyph instead. */
  .leanbox summary { cursor: pointer; list-style: none; user-select: none; }
  .leanbox summary::-webkit-details-marker { display: none; }
  .leanbox summary::before { content: '▸'; display: inline-block; width: 1em;
                             transition: transform .12s; }
  .leanbox details[open] > summary::before { transform: rotate(90deg); }
  .leanbox .badge { border: 1px solid currentColor; border-radius: 999px;
                    padding: 0 6px; margin-left: 6px; font-size: 11px; }
  .status { font-size: 13px; margin-left: auto; }
  .status.running { color: var(--accent); } .status.done { color: var(--ok); }
  .status.failed, .status.stopped { color: var(--bad); }
  .stages { border: 1px solid var(--border); border-radius: 8px; margin-bottom: 12px;
            overflow-y: auto; background: var(--bg); max-height: 168px; }
  .stage { display: grid; grid-template-columns: minmax(0, 1fr) auto auto; gap: 12px;
           align-items: center; min-height: 34px; padding: 5px 10px; border-bottom: 1px solid var(--border);
           font-size: 12.5px; }
  .stage:last-child { border-bottom: none; }
  .stage .name { overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
  .stage .time { color: var(--muted); font-variant-numeric: tabular-nums; }
  .stage .pill { border: 1px solid var(--border); border-radius: 999px; padding: 1px 8px;
                 color: var(--muted); font-size: 11.5px; }
  .stage.running .pill { color: var(--accent); border-color: var(--accent); }
  .stage.done .pill { color: var(--ok); border-color: var(--ok); }
  .progress { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 8px;
              margin-bottom: 12px; }
  @media (max-width: 900px) { .progress { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
  .metric { border: 1px solid var(--border); border-radius: 8px; padding: 8px 10px;
            background: var(--bg); min-width: 0; }
  .metric .label { color: var(--muted); font-size: 11.5px; white-space: nowrap;
                   overflow: hidden; text-overflow: ellipsis; }
  .metric .value { margin-top: 2px; font-size: 18px; line-height: 1.15;
                   font-weight: 650; font-variant-numeric: tabular-nums; }
  .metric .sub { color: var(--muted); font-size: 11.5px; min-height: 16px;
                 white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
  .metric .completion-breakdown { display: flex; flex-wrap: wrap; gap: 3px 16px;
                                  margin-top: 5px; color: var(--muted);
                                  font-size: 11.5px; line-height: 1.35; }
  .metric .completion-breakdown span { white-space: nowrap; }
  .metric .completion-breakdown strong { color: var(--text); font-weight: 650;
                                         font-variant-numeric: tabular-nums; }
  #log { background: var(--log-bg); color: var(--log-text); border-radius: 10px;
         padding: 14px; height: 430px; overflow: auto; white-space: pre-wrap;
         word-break: break-word; font: 12px/1.55 ui-monospace, "SF Mono", Menlo, monospace; }
  h2 { font-size: 14px; margin: 0 0 10px; }
  ul.bps { list-style: none; margin: 0; padding: 0; }
  ul.bps li { display: flex; align-items: center; gap: 8px; padding: 7px 2px;
              border-bottom: 1px solid var(--border); font-size: 13.5px; }
  ul.bps li:last-child { border-bottom: none; }
  ul.bps .name { color: var(--muted); font-size: 12px; }
  ul.bps a { color: var(--accent); text-decoration: none; margin-left: auto; font-size: 12.5px; }
  .dot { width: 8px; height: 8px; border-radius: 50%; background: var(--muted); flex: none; }
  .dot.built { background: var(--ok); }
  .drop { border: 1.5px dashed var(--border); border-radius: 7px; padding: 8px;
          text-align: center; color: var(--muted); font-size: 12.5px; margin-top: 6px;
          cursor: pointer; }
  .drop.over { border-color: var(--accent); color: var(--accent); }
</style>
</head>
<body>
<header><h1>Auto-Blueprint</h1><span>papers &rarr; lean blueprints, without the command line</span></header>
<main>
  <div>
    <div class="panel">
      <div class="tabs" id="tabs"></div>
      <div id="form"></div>
      <div class="actions">
        <button class="run" id="runBtn" onclick="run()">Run</button>
        <button class="stop" id="stopBtn" onclick="stopJob()">Stop</button>
        <span class="status" id="status"></span>
      </div>
      <div class="error" id="error"></div>
    </div>
    <div class="panel" style="margin-top:18px">
      <h2>Blueprints</h2>
      <ul class="bps" id="bps"></ul>
    </div>
  </div>
  <div class="panel">
    <h2 style="display:flex"><span>Log</span>
      <span style="margin-left:auto;font-weight:normal;color:var(--muted);font-size:12px" id="cmdline"></span></h2>
    <div id="progress" class="progress"></div>
    <div id="stages" class="stages"><div class="stage"><span class="name">No running job</span><span class="time">0s</span><span class="pill">idle</span></div></div>
    <div id="log"></div>
  </div>
</main>
<script>
const TABS = [
  {id:'generate',  label:'Generate'},
  {id:'refine',    label:'Refine with Lean'},
  {id:'validate',  label:'Validate'},
  {id:'build',     label:'Build site'},
  {id:'libraries', label:'Lean libraries'},
];
let state = {blueprints: [], backends: [], efforts: [], model_suggestions: {}, runner_defaults: {}, last_refine_settings: {}};
let active = 'generate';
let offset = 0;
let jobWasRunning = false;
let stageRows = [];
let modelStateSignature = '';
let currentStage = null;
let fallbackStageSecond = 0;
let progress = {};

function el(id){ return document.getElementById(id); }
function esc(s){ const d=document.createElement('div'); d.textContent=s; return d.innerHTML; }

function fmtDuration(sec){
  sec = Math.max(0, Math.floor(sec || 0));
  const h = Math.floor(sec / 3600), m = Math.floor((sec % 3600) / 60), s = sec % 60;
  if (h) return `${h}h ${String(m).padStart(2,'0')}m`;
  if (m) return `${m}m ${String(s).padStart(2,'0')}s`;
  return `${s}s`;
}

function logSecond(line, jobElapsed){
  const m = line.match(/^\[\+(\d+)s\]\s*/);
  if (m) return Number(m[1]);
  fallbackStageSecond = Math.max(fallbackStageSecond + 1, jobElapsed || 0);
  return fallbackStageSecond;
}

function stripLogPrefix(line){
  return line
    .replace(/^\[\+\d+s\]\s*/, '')
    .replace(/^\[[^\]]+\]\s*/, '');
}

function resetProgress(){
  progress = {};
  renderProgress();
}

function metric(label, value, sub=''){
  return `<div class="metric">
    <div class="label">${esc(label)}</div>
    <div class="value">${esc(value)}</div>
    <div class="sub">${esc(sub)}</div>
  </div>`;
}

function completionMetric(value, verified, open, fallbackSub=''){
  if (verified == null || open == null) return metric('Overall nodes completed', value, fallbackSub);
  return `<div class="metric">
    <div class="label">Overall nodes completed</div>
    <div class="value">${esc(value)}</div>
    <div class="completion-breakdown">
      <span><strong>${esc(verified)}</strong> verified nodes</span>
      <span><strong>${esc(open)}</strong> open conjectures</span>
    </div>
  </div>`;
}

function renderProgress(){
  const box = el('progress');
  if (!box) return;
  if (!(progress && progress.visible)) {
    box.style.display = 'none';
    box.innerHTML = '';
    return;
  }
  box.style.display = 'grid';
  const total = Number.isFinite(progress.totalNodes) ? progress.totalNodes : null;
  const proven = Number.isFinite(progress.acceptedNodes) ? progress.acceptedNodes : null;
  const remaining = Number.isFinite(progress.remainingNodes)
    ? progress.remainingNodes
    : (total != null && proven != null ? Math.max(total - proven, 0) : null);
  const trialsUsed = Number.isFinite(progress.repairTrialsUsed) ? progress.repairTrialsUsed : null;
  const trialsMax = Number.isFinite(progress.repairTrialsMax) ? progress.repairTrialsMax : null;
  const trialsLeft = trialsUsed != null && trialsMax != null ? Math.max(trialsMax - trialsUsed, 0) : null;
  const provenSub = total != null && proven != null ? `${Math.round((proven / Math.max(total, 1)) * 100)}%` : '';
  const verifiedCount = Number.isFinite(progress.verifiedNodes) ? progress.verifiedNodes : null;
  const recordedCount = Number.isFinite(progress.recordedConjectures) ? progress.recordedConjectures : null;
  const phase1Frozen = Number.isFinite(progress.phase1Frozen) ? progress.phase1Frozen : null;
  const phase1Required = Number.isFinite(progress.phase1Required) ? progress.phase1Required : null;
  if (active === 'refine' && !progress.legacyPipeline) {
    const pct = (n, d) => `${Math.round((n / Math.max(d, 1)) * 100)}%`;
    box.innerHTML = [
      metric('Phase 1 contracts frozen', phase1Frozen == null || phase1Required == null ? '—' :
        `${phase1Frozen}/${phase1Required}`,
        phase1Frozen == null || phase1Required == null ? '' : pct(phase1Frozen, phase1Required)),
      completionMetric(
        proven == null || total == null ? '—' : `${proven}/${total}`,
        verifiedCount,
        recordedCount,
        provenSub),
      metric('Repair/retry trials left', trialsLeft == null ? '—' : String(trialsLeft),
        trialsUsed == null || trialsMax == null ? '' : `${trialsUsed}/${trialsMax} used`),
    ].join('');
  } else {
    // Legacy per-chunk logs do not expose stage-specific counters.
    box.innerHTML = [
      metric('Blueprint nodes', total == null ? '—' : String(total), progress.currentChunk ? `chunk ${progress.currentChunk}` : ''),
      metric('Proven so far', proven == null ? '—' : String(proven), provenSub),
      metric('Nodes remaining', remaining == null ? '—' : String(remaining), total == null ? '' : `of ${total}`),
      metric('Repair/retry trials left', trialsLeft == null ? '—' : String(trialsLeft),
        trialsUsed == null || trialsMax == null ? '' : `${trialsUsed}/${trialsMax} used`),
    ].join('');
  }
}

function ingestProgressLines(lines){
  let changed = false;
  for (const raw of lines || []){
    const line = stripLogPrefix(raw);
    let m;
    if (line.includes('refine_blueprint_with_lean.py') || line.includes('formalize_blueprint.py')) {
      progress.visible = true;
      changed = true;
    }
    if ((m = line.match(/validate [^:]+: ok \((\d+) node\(s\)\)/))){
      progress.totalNodes = Number(m[1]);
      changed = true;
    }
    if ((m = line.match(/==> Progress: (\d+)\/(\d+) blueprint nodes verified; repairs (\d+)\/(\d+)/))){
      progress.acceptedNodes = Number(m[1]);
      progress.totalNodes = Number(m[2]);
      progress.remainingNodes = Math.max(progress.totalNodes - progress.acceptedNodes, 0);
      progress.repairTrialsUsed = Number(m[3]);
      progress.repairTrialsMax = Number(m[4]);
      changed = true;
    }
    if ((m = line.match(/==> Progress: Phase 1 contracts (\d+)\/(\d+) frozen; Phase 2 Lean implementations (\d+)\/(\d+) complete; overall (\d+)\/(\d+) complete \((\d+) verified, (\d+) open conjectures recorded\); (?:repairs|repair\/retries) (\d+)\/(\d+)/))){
      progress.legacyPipeline = false;
      progress.phase1Frozen = Number(m[1]);
      progress.phase1Required = Number(m[2]);
      progress.phase2Implemented = Number(m[3]);
      progress.phase2Required = Number(m[4]);
      progress.acceptedNodes = Number(m[5]);
      progress.totalNodes = Number(m[6]);
      progress.verifiedNodes = Number(m[7]);
      progress.recordedConjectures = Number(m[8]);
      progress.remainingNodes = Math.max(progress.totalNodes - progress.acceptedNodes, 0);
      progress.repairTrialsUsed = Number(m[9]);
      progress.repairTrialsMax = Number(m[10]);
      changed = true;
    }
    if ((m = line.match(/==> Progress: Phase 1 contracts (\d+)\/(\d+) frozen; Phase 2 Lean implementations (\d+)\/(\d+) complete; overall (\d+)\/(\d+) verified; (?:repairs|repair\/retries) (\d+)\/(\d+)/))){
      progress.legacyPipeline = false;
      progress.phase1Frozen = Number(m[1]);
      progress.phase1Required = Number(m[2]);
      progress.phase2Implemented = Number(m[3]);
      progress.phase2Required = Number(m[4]);
      progress.acceptedNodes = Number(m[5]);
      progress.totalNodes = Number(m[6]);
      progress.verifiedNodes = Number(m[5]);
      progress.recordedConjectures = 0;
      progress.remainingNodes = Math.max(progress.totalNodes - progress.acceptedNodes, 0);
      progress.repairTrialsUsed = Number(m[7]);
      progress.repairTrialsMax = Number(m[8]);
      changed = true;
    }
    if ((m = line.match(/(?:blueprint repairs|repair\/retry trials) used (\d+)\/(\d+)/))){
      progress.repairTrialsUsed = Number(m[1]);
      progress.repairTrialsMax = Number(m[2]);
      changed = true;
    }
    if ((m = line.match(/resumed with (\d+) accepted blueprint node\(s\)/))){
      progress.acceptedNodes = Number(m[1]);
      changed = true;
    }
    if ((m = line.match(/\((\d+) accepted,\s+(\d+) remaining including this chunk\)/))){
      progress.acceptedNodes = Number(m[1]);
      progress.remainingNodes = Number(m[2]);
      progress.totalNodes = progress.acceptedNodes + progress.remainingNodes;
      changed = true;
    }
    if ((m = line.match(/Chunk (\d+) passed; accepted (\d+) of (\d+) blueprint nodes/))){
      progress.legacyPipeline = true;
      progress.currentChunk = Number(m[1]);
      progress.acceptedNodes = Number(m[2]);
      progress.totalNodes = Number(m[3]);
      progress.remainingNodes = Math.max(progress.totalNodes - progress.acceptedNodes, 0);
      changed = true;
    } else if ((m = line.match(/==> Chunk (\d+):/))){
      progress.legacyPipeline = true;
      progress.currentChunk = Number(m[1]);
      changed = true;
    }
    if (line.includes('All chunks passed')){
      if (Number.isFinite(progress.totalNodes)) {
        progress.acceptedNodes = progress.totalNodes;
        progress.remainingNodes = 0;
      }
      changed = true;
    }
  }
  if (changed) renderProgress();
}

function stageFromLine(line){
  line = stripLogPrefix(line);
  let m;
  if (line.includes('Reading paper context') || line.includes('Reading paper from')) return 'Read paper';
  if (line.includes('Checking Lean/Lake/Mathlib setup')) return 'Lean preflight';
  if (line.includes('removed') && line.includes('stale Lean attempt')) return 'Cleanup stale attempts';
  if ((m = line.match(/==> validate [^:]+: ok/))) return 'Validate blueprint';

  // Fast statements-first pipeline.
  if ((m = line.match(/==> Initial declaration pass: creating boilerplate for (\d+) node\(s\) \((\d+) declarations already available\)/))) {
    return `Initial pass · boilerplate (${m[2]}/${Number(m[1]) + Number(m[2])} available)`;
  }
  if ((m = line.match(/==> Initial declaration pass: stating (\d+) node\(s\) in one call/))) {
    return `Initial pass · generate declarations (${m[1]} nodes)`;
  }
  if ((m = line.match(/==> Initial declaration pass: generating one complete provisional Lean environment for (\d+) node\(s\)/))) {
    return `Initial pass · complete environment (${m[1]} nodes)`;
  }
  if ((m = line.match(/==> Initial declaration pass: creating one complete boilerplate file for (\d+) node\(s\)/))) {
    return `Initial pass · boilerplate file (${m[1]} nodes)`;
  }
  if ((m = line.match(/==> Initial declaration pass attempt (\d+)\/2/))) {
    return `Initial pass · whole-environment attempt ${m[1]}/2`;
  }
  if (line.includes('Initial Lean skeleton complete')) {
    return 'Initial pass · boilerplate complete';
  }
  if ((m = line.match(/==> Phase 2 whole-node repair: completing (\d+) new\/changed blueprint node/))) {
    return `Phase 2 · complete repaired nodes (${m[1]})`;
  }
  if ((m = line.match(/==> Phase 2 whole-node repair: completing (\d+) dependency-ready node/))) {
    return `Phase 2 · complete repaired frontier (${m[1]} nodes)`;
  }
  if ((m = line.match(/==> Phase 2 complete-node candidate (\d+): (\d+) node/))) {
    return `Phase 2 · validate complete candidate (${m[2]})`;
  }
  if ((m = line.match(/==> Phase 2 repaired node (\d+): (\d+) node/))) {
    return `Phase 2 · validate complete candidate (${m[2]})`;
  }
  if (line.includes('Phase 2 whole-node repair integration gate')) {
    return 'Phase 2 · integrate complete repaired nodes';
  }
  if (line.includes('Phase 2 whole-node repair complete')) {
    return 'Phase 2 · repaired nodes complete';
  }
  if (line.includes('Phase 2 whole-node repair')) {
    return 'Phase 2 · repair complete nodes';
  }
  if ((m = line.match(/==> Phase 1: added (\d+) provisional name\(s\) introduced by blueprint repair/))) {
    return `Phase 1 · add repaired helper names (${m[1]})`;
  }
  if ((m = line.match(/==> Phase 1: freezing (\d+) new\/changed statement contract/))) {
    return `Phase 1 · freeze initial skeleton (${m[1]} contracts)`;
  }
  if ((m = line.match(/==> Phase 1: refining bottom-up ready frontier (\d+) \((\d+) node/))) {
    return `Phase 1 · dependency frontier ${m[1]} (${m[2]} nodes)`;
  }
  if ((m = line.match(/==> Phase 1: refining statements (top-down|bottom-up) for (\d+) node\(s\) \((\d+) already frozen\)/))) {
    return `Phase 1 · ${m[1]} statements (${m[3]}/${Number(m[2]) + Number(m[3])} frozen)`;
  }
  if ((m = line.match(/==> Phase 1: refining top-down statement layer (\d+) \((\d+) node\(s\)\)/))) {
    return `Phase 1 · statement frontier ${m[1]} (${m[2]} nodes)`;
  }
  if ((m = line.match(/==> Phase 1: refining bottom-up statement layer (\d+) \((\d+) node\(s\)\)/))) {
    return `Phase 1 · dependency frontier ${m[1]} (${m[2]} nodes)`;
  }
  if ((m = line.match(/==> Phase 1: generating exact statements for (\d+) provisional declaration\(s\)/))) {
    return `Phase 1 · generate exact statements (${m[1]} nodes)`;
  }
  if ((m = line.match(/==> Skeleton section (\d+): (\d+) node\(s\)/))) {
    return `Phase 1 · skeleton section ${m[1]} (${m[2]} nodes)`;
  }
  if ((m = line.match(/==> Initial declaration section (\d+): (\d+) node\(s\)/))) {
    return `Initial pass · section ${m[1]} (${m[2]} nodes)`;
  }
  if ((m = line.match(/==> Initial declaration retry (\d+)\/(\d+):/))) {
    return `Initial pass · retry ${m[1]}/${m[2]}`;
  }
  if ((m = line.match(/==> Phase 1 design plan: generating two independent full-context candidates concurrently \((\d+) nodes\)/))) {
    return `Phase 1 · compare two contract plans (${m[1]} nodes)`;
  }
  if ((m = line.match(/==> Phase 1 semantic plan: coordinating (\d+) node\(s\) in one compact full-context call/))) {
    return `Phase 1 · compact semantic plan (${m[1]} nodes)`;
  }
  if ((m = line.match(/==> Model call: ([a-z_]+) \((\d+) node\(s\), timeout (\d+)s/))) {
    const purpose = {
      initial_declaration_generation: 'initial declaration generation',
      skeleton_generation: 'skeleton generation',
      skeleton_design_pass: 'skeleton design',
      phase1_design_plan: 'Phase 1 statement plan',
      phase1_design_plan_candidate_a: 'Phase 1 contract-plan candidate A',
      phase1_design_plan_candidate_b: 'Phase 1 contract-plan candidate B',
      phase1_design_plan_audit: 'Phase 1 contract-plan audit',
      phase1_design_plan_correction: 'Phase 1 contract-plan correction',
      phase1_semantic_plan: 'Phase 1 compact semantic plan',
      phase1_statement_generation: 'Phase 1 statement generation',
      skeleton_declaration_patch: 'skeleton patch',
      statement_audit: 'statement audit',
      proof_batch: 'proof batch',
      proof_singleton: 'singleton proof',
      phase2_whole_node_repair: 'complete repaired node',
      phase2_complete_node_correction: 'correct retained complete node',
      blueprint_repair: 'blueprint repair',
      section_normalization: 'section normalization',
    }[m[1]] || m[1].replace(/_/g, ' ');
    return `Model · ${purpose} (${m[2]} nodes, ${m[3]}s budget)`;
  }
  if ((m = line.match(/==> Phase 1 contract-plan audit: checking (\d+) proposed interface/))) {
    return `Phase 1 · validate contract plan (${m[1]} nodes)`;
  }
  if ((m = line.match(/==> Phase 1 contract-plan correction \((base|escalation)\):/))) {
    return `Phase 1 · correct contract plan (${m[1]})`;
  }
  if ((m = line.match(/==> Phase 1 layer (\d+): compiling (\d+) validated-contract candidate group/))) {
    return `Phase 1 · compile validated contracts (layer ${m[1]}, ${m[2]} groups)`;
  }
  if (line.includes('compiled unchanged under the complete Mathlib environment')) {
    return 'Phase 1 · resolve Lean environment';
  }
  if ((m = line.match(/==> Phase 1 layer (\d+): checking (\d+) integrated declaration/))) {
    return `Phase 1 · final contract audit (layer ${m[1]}, ${m[2]} nodes)`;
  }
  if (line.includes('deterministic audit isolated')) return 'Phase 1 · deterministic audit patch';
  if (line.includes('deterministic audit failed')) return 'Phase 1 · deterministic audit';
  if (line.includes('lean rejected skeleton section')) return 'Phase 1 · Lean skeleton check';
  if (line.includes('alignment audit rejected statements')) return 'Phase 1 · statement alignment audit';
  if ((m = line.match(/section (\d+) frozen/))) return `Phase 1 · section ${m[1]} frozen`;
  if ((m = line.match(/section (\d+) provisioned/))) return `Initial pass · section ${m[1]} provisioned`;
  if (line.includes('Phase 1 froze')) return 'Phase 1 · statement contracts frozen';
  if (line.includes('Phase 1 integration recheck') || line.includes('Phase 1 integration gate')) return 'Phase 1 · integration recheck';
  if ((m = line.match(/==> Phase 2: implementing deferred bodies for top-down ready frontier (\d+) \((\d+) node\(s\)\) with (\d+) worker\(s\)/))) {
    return `Phase 2 · root-first ready frontier ${m[1]} (${m[2]} nodes, ${m[3]} workers)`;
  }
  if ((m = line.match(/==> Phase 2: implementing deferred bodies for top-down frontier (\d+) \((\d+) node\(s\)\) with (\d+) worker\(s\)/))) {
    return `Phase 2 · root-first frontier ${m[1]} (${m[2]} nodes, ${m[3]} workers)`;
  }
  if ((m = line.match(/==> Phase 2: implementing deferred bodies for bottom-up frontier (\d+) \((\d+) node\(s\)\) with (\d+) worker\(s\)/))) {
    return `Phase 2 · dependency-first frontier ${m[1]} (${m[2]} nodes, ${m[3]} workers)`;
  }
  if ((m = line.match(/==> Phase 2: filling proofs for top-down frontier (\d+) \((\d+) node\(s\)\) with (\d+) worker\(s\)/))) {
    return `Phase 2 · root-first frontier ${m[1]} (${m[2]} nodes, ${m[3]} workers)`;
  }
  if ((m = line.match(/==> Phase 2: filling proofs for bottom-up frontier (\d+) \((\d+) node\(s\)\) with (\d+) worker\(s\)/))) {
    return `Phase 2 · dependency-first frontier ${m[1]} (${m[2]} nodes, ${m[3]} workers)`;
  }
  if ((m = line.match(/==> Phase 2: filling proofs for (\d+) section\(s\) with (\d+) worker\(s\)/))) {
    return `Phase 2 · fill proofs (${m[1]} sections, ${m[2]} workers)`;
  }
  if (line.includes('tactic ladder closed') || line.includes('tactic ladder crashed')) return 'Phase 2 · tactic ladder';
  if (line.includes('batch timed out; reducing batch size')) return 'Phase 2 · resize proof batch';
  if (line.includes('accepted ') && line.includes(' implementation(s)')) return 'Phase 2 · implementation accepted';
  if (line.includes('accepted ') && line.includes(' proof(s)')) return 'Phase 2 · proof accepted';
  if (line.includes('Final from-scratch Lean check')) return 'Final Lean check';

  // Legacy per-chunk pipeline.
  if ((m = line.match(/==> Chunk (\d+): validating blueprint/))) return `Chunk ${m[1]} · validate blueprint`;
  if (line.includes('Searching local Lean libraries')) return 'Search local Lean libraries';
  if ((m = line.match(/==> Chunk (\d+), Lean attempt (\d+)\/\d+: generating/))) {
    return `Chunk ${m[1]} · generate Lean attempt ${m[2]}`;
  }
  if ((m = line.match(/==> Chunk (\d+): running Lean/))) return `Chunk ${m[1]} · Lean check`;
  if ((m = line.match(/==> Chunk (\d+): auditing statement alignment/))) return `Chunk ${m[1]} · statement audit`;
  if ((m = line.match(/==> Blueprint repair (\d+)\/(\d+)/))) return `Blueprint repair ${m[1]}/${m[2]}`;
  if (line.includes('All chunks accepted; running final')) return 'Final Lean check';
  if (line.includes('Site rebuilt') || line.includes('Build site')) return 'Rebuild site';
  if (line.includes('Report written') || line.startsWith('==> exit code')) return 'Finish';
  return null;
}

function resetStages(){
  stageRows = [];
  currentStage = null;
  fallbackStageSecond = 0;
  resetProgress();
  renderStages({status:'idle', elapsed:0});
}

function ingestStageLines(lines, job){
  for (const line of lines || []){
    const name = stageFromLine(line);
    if (!name) continue;
    const t = logSecond(line, job && job.elapsed);
    if (currentStage && currentStage.name === name) continue;
    if (currentStage && currentStage.end == null) currentStage.end = t;
    currentStage = {name, start:t, end:null};
    stageRows.push(currentStage);
  }
  renderStages(job || {status:'idle', elapsed:0});
}

function renderStages(job){
  const box = el('stages');
  if (!box) return;
  if (!stageRows.length){
    box.innerHTML = '<div class="stage"><span class="name">No stage data yet</span><span class="time">0s</span><span class="pill">idle</span></div>';
    return;
  }
  const now = job && job.status === 'running' ? (job.elapsed || fallbackStageSecond) : fallbackStageSecond;
  box.innerHTML = stageRows.map((row)=>{
    const running = row.end == null && job && job.status === 'running';
    const end = row.end == null ? now : row.end;
    const state = running ? 'running' : 'done';
    const pill = running ? 'running' : 'done';
    return `<div class="stage ${state}">
      <span class="name">${esc(row.name)}</span>
      <span class="time">${fmtDuration(end - row.start)}</span>
      <span class="pill">${pill}</span>
    </div>`;
  }).join('');
  box.scrollTop = box.scrollHeight;
}

renderProgress();

function modelList(id, backend){
  const names = (state.model_suggestions && state.model_suggestions[backend]) || [];
  return `<datalist id="${id}">${names.map(m=>`<option value="${esc(m)}"></option>`).join('')}</datalist>`;
}

function runnerBlock(prefix, title, defaultBackend='claude-code', defaultEffort='', defaultModel=''){
  const backendId = `${prefix}_backend`;
  const modelId = `${prefix}_model`;
  const effortId = `${prefix}_effort`;
  const listId = `${prefix}_models`;
  const opts = state.backends.map(b=>`<option ${b===defaultBackend?'selected':''}>${b}</option>`).join('');
  const effs = ['<option value="">(default)</option>']
    .concat(state.efforts.map(e=>`<option ${e===defaultEffort?'selected':''}>${e}</option>`)).join('');
  return `
    <div class="row">
      <div><label>${title} runner</label>
        <select id="${backendId}" onchange="runnerChanged('${prefix}')">${opts}</select></div>
      <div><label>${title} model (optional)</label>
        <input type="text" id="${modelId}" list="${listId}" value="${esc(defaultModel)}" placeholder="blank = runner default">
        ${modelList(listId, defaultBackend)}</div>
    </div>
    <div class="row">
      <div><label>${title} reasoning effort (codex only)</label>
        <select id="${effortId}" disabled>${effs}</select></div>
      <div><label>${title} model policy</label>
        <div class="hint">${title === 'Base' ? 'Normal batched calls use this.' : 'Singleton retries and blueprint repair use this.'}</div></div>
    </div>`;
}

function runnerDefault(tier, key, fallback){
  const d = (state.runner_defaults && state.runner_defaults[tier]) || {};
  return d[key] || fallback;
}

function runnerFields(baseTimeout='3600', includeHard=false, opts={}){
  const backend = opts.defaultBackend || 'claude-code';
  const effort = opts.defaultEffort || '';
  const model = opts.defaultModel || '';
  const hard = includeHard ? `
    <div class="row">
      <div><label>Hard-node timeout / planner hedge (seconds)</label>
        <input type="number" id="f_hard_timeout" value="600" min="1"></div>
      <div><label>Timeout behavior</label>
        <div class="hint">Hard chunks use this limit. A slow compact planner starts a parallel fresh call at this threshold without killing the original.</div></div>
    </div>` : '';
  return `
    ${runnerBlock('f', 'Base', backend, effort, model)}
    <div class="row">
      <div><label>Base model-call timeout (seconds)</label>
        <input type="number" id="f_timeout" value="${baseTimeout}" min="1"></div>
      <div></div>
    </div>${hard}`;
}

function escalationRunnerFields(){
  return `
    ${runnerBlock(
      'f_escalation',
      'Escalation',
      runnerDefault('escalation', 'backend', 'codex'),
      runnerDefault('escalation', 'effort', 'high'),
      runnerDefault('escalation', 'model', 'gpt-5.5')
    )}`;
}

function paperField(required){
  return `
    <label>Paper — local path or URL${required?'':' (optional context)'}</label>
    <input type="text" id="f_paper" placeholder="/path/to/paper.pdf or https://arxiv.org/...">
    <div class="drop" id="drop">drop a PDF here or click to upload</div>`;
}

function bpSelect(){
  const opts = state.blueprints.map(b=>`<option value="${b.name}">${b.name}</option>`).join('');
  return opts || '<option value="">(no blueprints yet)</option>';
}

function bpChecks(){
  if (!state.blueprints.length) return '<div class="hint">No blueprints found.</div>';
  return state.blueprints.map(b=>
    `<div class="check"><input type="checkbox" class="bpcheck" value="${b.name}" id="c_${b.name}">
     <label for="c_${b.name}">${b.name}</label></div>`).join('');
}

const FORMS = {
  generate: () => `
    ${paperField(true)}
    <label>Blueprint name (optional — the model picks one if empty)</label>
    <input type="text" id="f_name" placeholder="my-paper">
    ${runnerFields('3600')}
    <div class="check"><input type="checkbox" id="f_force"><label for="f_force">Force (replace existing folder)</label></div>
    <div class="check"><input type="checkbox" id="f_nobuild"><label for="f_nobuild">Validate only, skip site build</label></div>`,
  refine: () => `
    <label>Blueprint</label>
    <select id="f_name">${bpSelect()}</select>
    <div class="check"><input type="checkbox" id="f_fast" checked><label for="f_fast">Fast statements-first pipeline (recommended; uncheck for the legacy per-chunk loop)</label></div>
    <div class="hint">Model preset: ${esc((state.runner_defaults && state.runner_defaults.source) || 'local Codex fallback')}.</div>
    <div style="margin-top:8px">
      <button type="button" class="secondary" id="lastSettingsBtn" onclick="applyLastRefineSettings()"
        ${Object.keys(state.last_refine_settings || {}).length ? '' : 'disabled'}>Use last-used settings</button>
      <span class="hint" id="lastSettingsStatus">Restores every setting from the last accepted Refine run.</span>
    </div>
    <label>Parallel workers</label>
    <input type="number" id="f_workers" value="3" min="1">
    <div class="hint">Phase 1 freezes statements bottom up; Phase 2 implements them top down.</div>
    <label>Skeleton section size (fast pipeline only; statements per Phase-1 call — shrinks automatically on timeouts)</label>
    <input type="number" id="f_section_size" value="12" min="1">
    <label>Max repair/retry trials</label>
    <input type="number" id="f_trials" value="100" min="1">
    <label>Conjectures</label>
    <select id="f_conjecture_policy">
      <option value="record" selected>Record as open propositions (recommended)</option>
      <option value="attempt">Attempt model-generated proofs</option>
    </select>
    <div class="hint">Attempt mode first adds a proof to the blueprint, then asks Lean to formalize that blueprint proof. Record mode publishes explicit open claims as open propositions. Other <code>\\notready</code> nodes are repaired in the unpublished blueprint before Phase 1.</div>
    <div class="leanbox" id="leanStatus">
      <details><summary>Lean setup not checked.</summary>
        <button type="button" onclick="checkLean()">Check Lean setup</button>
      </details>
    </div>
    <label>Starting point</label>
    <select id="f_resume_mode">
      <option value="latest" selected>Continue latest unpublished refinement</option>
      <option value="phase1">Restart Phase 2 from saved Phase 1 snapshot</option>
      <option value="fresh">Start fresh from published blueprint</option>
    </select>
    <div class="hint" id="resumeHint">Reuses the current blueprint draft, frozen statements, and accepted proofs.</div>
    ${paperField(false)}
    ${runnerFields('300', true, {
      defaultBackend: runnerDefault('base', 'backend', 'codex'),
      defaultEffort: runnerDefault('base', 'effort', 'medium'),
      defaultModel: runnerDefault('base', 'model', 'gpt-5.5')
    })}
    <div id="fastEscalationFields">
      ${escalationRunnerFields()}
      <label>Compact planner model</label>
      <select id="f_planner_tier">
        <option value="base">Base model</option>
        <option value="escalation" selected>Escalation model</option>
      </select>
      <div class="hint">Chooses the model for the compact Phase 1 semantic plan only. Its primary and hedge calls use the same selection.</div>
    </div>
    <label>Lean command override (optional)</label>
    <input type="text" id="f_leancmd" placeholder="lake env lean">`,
  validate: () => `
    <div class="hint">Select blueprints to validate (none = all).</div>
    ${bpChecks()}`,
  build: () => `
    <div class="hint">Select blueprints to rebuild (none = full rebuild).</div>
    ${bpChecks()}
    <div class="check"><input type="checkbox" id="f_strict"><label for="f_strict">Strict (fail if any blueprint fails)</label></div>`,
  libraries: () => `
    <div class="hint">A Lean project has one toolchain, and every library pins one.
      The resolver reads each library's <code>lean-toolchain</code> history and picks the
      newest version they all support &mdash; nothing is hardcoded, so this moves forward
      on its own as libraries publish new versions.</div>
    <div id="libs_body">checking&hellip;</div>
    <hr style="margin:1rem 0;border:0;border-top:1px solid var(--line,#333)">
    <div class="hint"><b>Search priority</b> &mdash; which libraries Generate and Refine
      search for existing declarations, and in what order. Set per blueprint, because
      different papers want different libraries first. Highest priority at the top;
      unchecked libraries are not searched at all.</div>
    <label class="lbl" for="f_libbp">Blueprint</label>
    <select id="f_libbp" onchange="loadBlueprintLibs()">${bpSelect()}</select>
    <div id="bplibs_body">&nbsp;</div>`,
};

function renderTabs(){
  el('tabs').innerHTML = TABS.map(t=>
    `<button class="${t.id===active?'active':''}" onclick="setTab('${t.id}')">${t.label}</button>`).join('');
}
function setTab(id){ active = id; renderTabs(); renderForm(); renderProgress(); }

async function loadLibraries(refresh){
  const body = el('libs_body');
  if (!body) return;
  body.innerHTML = refresh ? 'checking upstream&hellip;' : 'checking&hellip;';
  let d;
  try {
    d = await (await fetch('/api/libraries' + (refresh ? '?refresh=1' : ''))).json();
  } catch (e) { body.textContent = 'resolver unreachable'; return; }
  if (!d.ok){ body.textContent = d.message || 'resolver failed'; return; }
  const cur = d.current || {}, r = d.resolution || {};
  const age = d.checked_age_s < 90 ? 'just now'
            : d.checked_age_s < 5400 ? Math.round(d.checked_age_s/60) + ' min ago'
            : Math.round(d.checked_age_s/3600) + ' h ago';
  let html = '<table class="libs"><tr><th>library</th><th>pinned</th><th>behind head</th></tr>';
  if (r.feasible){
    for (const [name, sha] of Object.entries(r.pins || {})){
      const d0 = (r.staleness_days || {})[name];
      const build = (d.build_status || {})[name] || {};
      html += `<tr><td>${esc(name)}</td><td><code>${esc(sha.slice(0,12))}</code></td>`
           +  `<td>${d0 === 0 ? 'head' : d0 + 'd'}</td>`
           +  `<td>${build.ready ? '<span class="dot built"></span> ready' : '<b>build required</b>'}</td></tr>`;
    }
  }
  html += '</table>';
  const label = r.feasible
    ? `resolved toolchain <code>${esc((r.toolchain||'').split(':').pop())}</code>`
    : `<b>no common toolchain</b> &mdash; ${esc(r.reason || '')}`;
  const groups = !r.feasible && r.groups
    ? '<div class="hint">' + Object.entries(r.groups).map(([tc, ns]) =>
        `${esc(tc.split(':').pop())}: ${ns.map(esc).join(', ')}`).join('<br>') + '</div>'
    : '';
  const needsBuild = Object.values(d.build_status || {}).some(s => !s.ready);
  const status = d.up_to_date
    ? '<span class="dot built"></span> up to date'
    : (r.feasible && needsBuild ? '<b>build required</b> &mdash; prepare selected libraries'
       : (r.feasible ? '<b>differs from installed</b> &mdash; applying rebuilds Lean state' : ''));
  const picker = (d.known || []).map(n => {
    const on = (d.selected || []).includes(n);
    const lock = n === 'mathlib' ? ' disabled' : '';
    return `<label style="margin-right:1rem"><input type="checkbox" class="libpick" value="${esc(n)}"`
         + `${on ? ' checked' : ''}${lock} onchange="selectLibraries()"> ${esc(n)}</label>`;
  }).join('');
  body.innerHTML = `
    <div class="hint">Keep compatible:</div><div style="margin:.3rem 0">${picker}</div>`;
  html = html.replace('<th>behind head</th>', '<th>behind head</th><th>compile status</th>');
  body.innerHTML += `
    <div>installed: <code>${esc((cur.toolchain||'?').split(':').pop())}</code>
         &middot; mathlib <code>${esc(String(cur.mathlib_rev||'').slice(0,12))}</code></div>
    <div style="margin:.35rem 0">${label} &middot; checked ${age} ${status}</div>
    ${groups}${html}
    <button type="button" onclick="loadLibraries(true)">Check now</button>
    ${(!d.up_to_date && r.feasible)
        ? ` <button type="button" onclick="applyLibraries(${JSON.stringify(d.selected).replace(/"/g,'&quot;')})">${needsBuild ? 'Build / repair libraries' : 'Apply &amp; rebuild'}</button>`
        : ''}`;
}

// Per-blueprint search priority (meta.yml `libraries:`). Kept separate from the
// selected set above: selection decides what is installed, this decides what
// Generate/Refine search, and in what order, for one paper.
let bplibs = {name:'', order:[], available:[]};

async function loadBlueprintLibs(){
  const body = el('bplibs_body'), sel = el('f_libbp');
  if (!body || !sel || !sel.value) { if (body) body.innerHTML = ''; return; }
  body.innerHTML = 'loading&hellip;';
  let d;
  try {
    d = await (await fetch('/api/blueprint-libraries?name=' + encodeURIComponent(sel.value))).json();
  } catch (e) { body.textContent = 'unreachable'; return; }
  if (!d.ok){ body.textContent = d.message || 'failed'; return; }
  bplibs = {name: d.name, order: d.order || [], available: d.available || []};
  renderBlueprintLibs(d);
}

function renderBlueprintLibs(d){
  const body = el('bplibs_body');
  if (!body) return;
  // Ranked libraries first in their chosen order, then the unranked ones.
  const rest = bplibs.available.filter(n => !bplibs.order.includes(n));
  const rows = bplibs.order.map((n,i) => {
    const up   = i === 0 ? ' disabled' : '';
    const down = i === bplibs.order.length - 1 ? ' disabled' : '';
    return `<tr><td><input type="checkbox" checked onchange="toggleLib('${esc(n)}')"></td>`
         + `<td>${i+1}</td><td>${esc(n)}</td>`
         + `<td><button type="button" onclick="moveLib(${i},-1)"${up}>&uarr;</button>`
         + `<button type="button" onclick="moveLib(${i},1)"${down}>&darr;</button></td></tr>`;
  }).join('');
  const restRows = rest.map(n =>
    `<tr><td><input type="checkbox" onchange="toggleLib('${esc(n)}')"></td>`
    + `<td>&mdash;</td><td>${esc(n)}</td><td></td></tr>`).join('');
  const note = bplibs.order.length
    ? `searched: <code>${bplibs.order.map(esc).join(' &gt; ')}</code>`
    : `no override &mdash; searched in selection order: `
      + `<code>${(bplibs.available || []).map(esc).join(' &gt; ')}</code>`;
  body.innerHTML = `<table class="libs">`
    + `<tr><th>use</th><th>rank</th><th>library</th><th>order</th></tr>`
    + rows + restRows + `</table><div class="hint" style="margin-top:.4rem">${note}</div>`;
}

function moveLib(i, delta){
  const j = i + delta, o = bplibs.order;
  if (j < 0 || j >= o.length) return;
  [o[i], o[j]] = [o[j], o[i]];
  renderBlueprintLibs();
  saveBlueprintLibs();
}

function toggleLib(name){
  const i = bplibs.order.indexOf(name);
  if (i >= 0) bplibs.order.splice(i, 1); else bplibs.order.push(name);
  renderBlueprintLibs();
  saveBlueprintLibs();
}

async function saveBlueprintLibs(){
  try {
    await fetch('/api/blueprint-libraries?name=' + encodeURIComponent(bplibs.name)
                + '&order=' + encodeURIComponent(bplibs.order.join(',')));
  } catch (e) {}
}

async function selectLibraries(){
  const picked = [...document.querySelectorAll('.libpick')]
    .filter(c => c.checked || c.disabled).map(c => c.value);
  const body = el('libs_body');
  if (body) body.innerHTML = 'resolving&hellip;';
  try {
    await fetch('/api/libraries?select=' + encodeURIComponent(picked.join(',')));
  } catch (e) {}
  loadLibraries(false);
}

async function applyLibraries(libs){
  if (!confirm('Prepare the selected Lean libraries?\n\nIf pins differ, this rewrites '
             + 'lean-toolchain and the managed block of lakefile.lean. It then builds '
             + 'missing library artifacts and verifies an actual import. Frozen Lean '
             + 'statements need re-verifying only if the toolchain changes.\n\n'
             + 'lean_libs.py restores every file it touched if any step fails.')) return;
  const r = await fetch('/api/run', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({action:'libraries', libs})});
  const j = await r.json();
  if (j.error){ el('error').textContent = j.error; return; }
  el('log').textContent = ''; offset = 0; resetStages();
}

function selectedBlueprint(){
  const name = el('f_name') ? el('f_name').value : '';
  return (state.blueprints || []).find(b => b.name === name) || null;
}

function updateResumeOptions(){
  const resume = el('f_resume_mode');
  if (!resume) return;
  const phase1 = [...resume.options].find(o => o.value === 'phase1');
  const bp = selectedBlueprint();
  const fast = !el('f_fast') || el('f_fast').checked;
  const available = !!(fast && bp && bp.phase1_checkpoint);
  if (phase1) {
    phase1.disabled = !available;
    phase1.textContent = available
      ? 'Restart Phase 2 from saved Phase 1 snapshot'
      : 'Restart Phase 2 from saved Phase 1 snapshot (not available)';
  }
  if (resume.value === 'phase1' && !available) resume.value = 'latest';
  const hint = el('resumeHint');
  if (!hint) return;
  if (resume.value === 'phase1') {
    hint.textContent = 'Restores an immutable copy captured when Phase 1 completed and discards later unpublished Phase 2 changes.';
  } else if (resume.value === 'fresh') {
    hint.textContent = 'Discards all unpublished refinement state and starts from the published blueprint.';
  } else {
    hint.textContent = 'Reuses the current blueprint draft, frozen statements, and accepted proofs.';
  }
}

function applyLastRefineSettings(){
  const saved = state.last_refine_settings || {};
  if (!Object.keys(saved).length) return;
  const ids = {
    name:'f_name', paper:'f_paper', resume_mode:'f_resume_mode',
    workers:'f_workers', section_size:'f_section_size', max_trials:'f_trials',
    conjecture_policy:'f_conjecture_policy', planner_tier:'f_planner_tier',
    runner_backend:'f_backend', runner_model:'f_model',
    escalation_runner_backend:'f_escalation_backend',
    escalation_runner_model:'f_escalation_model', reasoning_effort:'f_effort',
    escalation_reasoning_effort:'f_escalation_effort', timeout:'f_timeout',
    hard_timeout:'f_hard_timeout', lean_command:'f_leancmd'
  };
  if (Object.prototype.hasOwnProperty.call(saved, 'fast') && el('f_fast')) {
    el('f_fast').checked = !!saved.fast;
  }
  for (const [key, id] of Object.entries(ids)) {
    if (Object.prototype.hasOwnProperty.call(saved, key) && el(id)) {
      el(id).value = String(saved[key] == null ? '' : saved[key]);
    }
  }
  ['f', 'f_escalation'].forEach(updateModelList);
  if (Object.prototype.hasOwnProperty.call(saved, 'paper') && el('drop')) {
    const paper = String(saved.paper || '');
    el('drop').textContent = paper ? 'using saved paper: ' + paper.split('/').pop() : 'drop a PDF here or click to upload';
  }
  effortToggle();
  toggleFastFields();
  updateResumeOptions();
  const status = el('lastSettingsStatus');
  if (status) status.textContent = 'Last-used settings applied.';
}

function renderForm(){
  el('form').innerHTML = FORMS[active]();
  el('error').textContent = '';
  // The libraries tab drives its own actions; params() has no case for it and
  // would otherwise fall through to `build`, so a click on Run would silently
  // rebuild the site.
  const runBtn = el('runBtn');
  if (runBtn) runBtn.style.display = (active === 'libraries') ? 'none' : '';
  if (active === 'libraries') loadLibraries(false);
  effortToggle();
  const fast = el('f_fast');
  if (fast) fast.onchange = () => { toggleFastFields(); updateResumeOptions(); };
  const blueprint = el('f_name');
  if (active === 'refine' && blueprint) blueprint.onchange = updateResumeOptions;
  const resume = el('f_resume_mode');
  if (resume) resume.onchange = updateResumeOptions;
  toggleFastFields();
  updateResumeOptions();
  const drop = el('drop');
  if (drop){
    const input = document.createElement('input');
    input.type = 'file'; input.accept = '.pdf,.tex,.txt'; input.style.display = 'none';
    drop.appendChild(input);
    drop.onclick = () => input.click();
    input.onchange = () => input.files[0] && upload(input.files[0]);
    drop.ondragover = e => { e.preventDefault(); drop.classList.add('over'); };
    drop.ondragleave = () => drop.classList.remove('over');
    drop.ondrop = e => { e.preventDefault(); drop.classList.remove('over');
                         e.dataTransfer.files[0] && upload(e.dataTransfer.files[0]); };
  }
    if (active === 'refine') setTimeout(checkLean, 0);
}

function updateModelList(prefix){
  const backend = el(`${prefix}_backend`);
  const list = el(`${prefix}_models`);
  if (!backend || !list) return;
  const names = (state.model_suggestions && state.model_suggestions[backend.value]) || [];
  list.innerHTML = names.map(m=>`<option value="${esc(m)}"></option>`).join('');
}

function refreshVisibleModelLists(){
  ['f', 'f_escalation'].forEach(updateModelList);
  const defaults = state.runner_defaults || {};
  [['f', 'base'], ['f_escalation', 'escalation']].forEach(([prefix, tier])=>{
    const model = el(`${prefix}_model`);
    const d = defaults[tier] || {};
    if (model && !model.value && d.model) model.value = d.model;
  });
}

function runnerChanged(prefix){
  updateModelList(prefix);
  effortToggle();
}

function effortToggle(){
  [['f_backend','f_effort'], ['f_escalation_backend','f_escalation_effort']].forEach(([bid,eid])=>{
    const b = el(bid), eff = el(eid);
    if (b && eff) eff.disabled = b.value !== 'codex';
  });
}

function toggleFastFields(){
  const fast = el('f_fast');
  const box = el('fastEscalationFields');
  if (box && fast) box.style.display = fast.checked ? '' : 'none';
}

async function upload(file){
  const drop = el('drop');
  drop.textContent = 'uploading ' + file.name + '…';
  const buf = await file.arrayBuffer();
  const b64 = btoa(new Uint8Array(buf).reduce((s,x)=>s+String.fromCharCode(x), ''));
  const r = await fetch('/api/upload', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({filename: file.name, data: b64})});
  const j = await r.json();
  if (j.path){ el('f_paper').value = j.path; drop.textContent = 'uploaded: ' + file.name; }
  else { drop.textContent = 'upload failed: ' + (j.error || 'unknown'); }
}

function params(){
  const v = id => { const n = el(id); return n ? n.value : ''; };
  const c = id => { const n = el(id); return !!(n && n.checked); };
  const common = {
    runner_backend: v('f_backend'), runner_model: v('f_model'),
    escalation_runner_backend: v('f_escalation_backend'),
    escalation_runner_model: v('f_escalation_model'),
    reasoning_effort: el('f_effort') && !el('f_effort').disabled ? v('f_effort') : '',
    escalation_reasoning_effort: el('f_escalation_effort') && !el('f_escalation_effort').disabled ? v('f_escalation_effort') : '',
    timeout: v('f_timeout'),
    hard_timeout: v('f_hard_timeout'),
  };
  if (active === 'generate')
    return {action:'generate', paper:v('f_paper'), name:v('f_name'),
            force:c('f_force'), no_build:c('f_nobuild'), ...common};
  if (active === 'refine')
    return {action:'refine', name:v('f_name'), max_trials:v('f_trials'),
            paper:v('f_paper'), lean_command:v('f_leancmd'),
            resume_mode:v('f_resume_mode') || 'latest', fast:c('f_fast'), workers:v('f_workers'),
            section_size:v('f_section_size'),
            conjecture_policy:v('f_conjecture_policy'),
            planner_tier:v('f_planner_tier') || 'escalation',
            ...common};
  const names = [...document.querySelectorAll('.bpcheck:checked')].map(n=>n.value);
  if (active === 'validate') return {action:'validate', names};
  return {action:'build', names, strict:c('f_strict')};
}

async function run(){
  el('error').textContent = '';
  resetProgress();
  const payload = params();
  if (active === 'refine' && payload.resume_mode === 'fresh') {
    // --fresh discards both unpublished TeX and generated Lean state.
    // Either may represent hours of work; never discard them silently.
    const ok = confirm(
      'Start FRESH?\\n\\nThis discards the unpublished blueprint draft, all ' +
      'frozen Lean statements, and accepted proofs for "' +
      (payload.name || '?') + '". The published blueprint is unchanged.\\n\\n' +
      'Choose "Continue latest unpublished refinement" to resume instead.');
    if (!ok) return;
  }
  if (active === 'refine' && payload.resume_mode === 'phase1') {
    const ok = confirm(
      'Restart from the saved PHASE 1 snapshot?\n\nThis discards all later ' +
      'unpublished Phase 2 changes and accepted proofs for "' +
      (payload.name || '?') + '". The saved snapshot and published blueprint ' +
      'remain unchanged.');
    if (!ok) return;
  }
  if (active === 'refine') {
    progress.visible = true;
    const maxTrials = Number(payload.max_trials);
    if (Number.isFinite(maxTrials)) {
      progress.repairTrialsUsed = 0;
      progress.repairTrialsMax = maxTrials;
    }
    renderProgress();
  }
  const r = await fetch('/api/run', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify(payload)});
  const j = await r.json();
  if (j.error){ el('error').textContent = j.error; return; }
  el('log').textContent = '';
  offset = 0;
  resetStages();
}

async function stopJob(){ await fetch('/api/stop', {method:'POST'}); }

async function runLeanSetup(){
  el('error').textContent = '';
  const r = await fetch('/api/run', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify({action:'setup_lean'})});
  const j = await r.json();
  if (j.error){ el('error').textContent = j.error; return; }
  el('log').textContent = '';
  offset = 0;
  resetStages();
}

// Library freshness, rendered inside the same Lean status box: one panel
// answers both "can Lean run?" and "is anything out of date?".
function libUpdateHtml(L){
  if (!L || !L.ok) return '';
  if (!L.feasible){
    return `<div style="margin-top:7px"><b>No common toolchain</b> &mdash; ${esc(L.reason || '')}`
         + `<br><button type="button" onclick="checkLean(true)">Re-check upstream</button></div>`;
  }
  const age = L.checked_age_s < 90 ? 'just now'
            : L.checked_age_s < 5400 ? Math.round(L.checked_age_s/60) + ' min ago'
            : Math.round(L.checked_age_s/3600) + ' h ago';
  let rows = '';
  for (const r of (L.rows || [])){
    const have = r.installed ? r.installed.slice(0,10) : '(not installed)';
    const want = r.resolved ? r.resolved.slice(0,10) : '?';
    const behind = (r.behind_days === 0) ? 'head'
                 : (r.behind_days == null ? '' : r.behind_days + 'd behind head');
    const build = r.build_ready ? '<span class="dot built"></span> ready'
                : `<b>build required</b>${r.build_reason ? ' &mdash; ' + esc(r.build_reason) : ''}`;
    rows += `<tr><td>${esc(r.name)}</td>`
         +  `<td><code>${esc(have)}</code></td>`
         +  `<td>${r.needs_update ? '&rarr; <code>' + esc(want) + '</code>' : 'current'}</td>`
         +  `<td>${build}</td><td class="hint">${esc(behind)}</td></tr>`;
  }
  const tc = L.toolchain_changes
    ? `<div><b>toolchain</b> <code>${esc((L.toolchain_installed||'').split(':').pop())}</code>`
      + ` &rarr; <code>${esc((L.toolchain||'').split(':').pop())}</code>`
      + ` &mdash; changing it rebuilds the Lean state</div>`
    : `<div class="hint">toolchain <code>${esc((L.toolchain||'').split(':').pop())}</code></div>`;
  const action = L.needs_update
    ? ` <button type="button" onclick="applyLibraries()">${L.needs_build ? 'Build / repair libraries' : 'Update libraries'}</button>`
    : '';
  return `<div style="margin-top:9px">`
       + (L.needs_build ? `<b>Library build required</b>`
          : (L.needs_update ? `<b>Updates available</b>` : `Libraries up to date`))
       + ` <span class="hint">&middot; checked ${age}</span>`
       + `<table class="libs" style="margin-top:5px">`
       + `<tr><th>library</th><th>installed</th><th>resolved</th><th>compile status</th><th></th></tr>${rows}</table>`
       + tc
       + `<button type="button" onclick="checkLean(true)">Check for updates</button>${action}</div>`;
}

// Whether the Lean box is expanded. Held in JS because checkLean() replaces the
// box's innerHTML, which would otherwise snap it shut on every refresh.
let leanOpen = false;

function leanDetails(summaryHtml, bodyHtml){
  return `<details ${leanOpen ? 'open' : ''} ontoggle="leanOpen = this.open">`
       + `<summary>${summaryHtml}</summary>${bodyHtml}</details>`;
}

async function checkLean(refreshLibs){
  const box = el('leanStatus');
  if (!box) return;
  box.className = 'leanbox';
  box.innerHTML = refreshLibs
    ? 'Checking upstream for library updates…'
    : 'Checking Lean/Lake/Mathlib setup…';
  try {
    const r = await fetch('/api/lean/status' + (refreshLibs ? '?refresh=1' : ''));
    const j = await r.json();
    const cmd = (j.command || []).join(' ');
    const detail = (j.stderr || j.stdout || '').trim().split('\n').slice(-5).join('\n');
    box.className = 'leanbox ' + (j.ok ? 'ok' : 'bad');
    const L = j.libraries;
    // Keep the headline outside the fold: collapsed still has to answer
    // "is Lean ready" and "is anything out of date".
    const badge = (L && L.ok && L.feasible && L.needs_build)
      ? `<span class="badge">library build required</span>`
      : (L && L.ok && L.feasible && L.needs_update)
      ? `<span class="badge">updates available</span>`
      : (L && L.ok && !L.feasible ? `<span class="badge">no common toolchain</span>` : '');
    // Something needing attention opens the box; a clean check leaves it as-is.
    if (!j.ok || (L && L.ok && (L.needs_update || !L.feasible))) leanOpen = true;
    box.innerHTML = leanDetails(
      `${esc(j.message || (j.ok ? 'Lean setup ready' : 'Lean setup failed'))}` +
        (j.elapsed_s ? ` · ${Number(j.elapsed_s).toFixed(1)}s` : '') + badge,
      (cmd ? `<code>${esc(cmd)}</code>` : '') +
        (detail ? `<pre style="white-space:pre-wrap;margin:7px 0 0">${esc(detail)}</pre>` : '') +
        `<br><button type="button" onclick="checkLean()">Check again</button>` +
        (j.ok ? '' : ` <button type="button" onclick="runLeanSetup()">Run Lean setup</button>`) +
        libUpdateHtml(L));
  } catch (e) {
    box.className = 'leanbox bad';
    leanOpen = true;
    box.innerHTML = leanDetails(
      `Could not check Lean setup: ${esc(String(e))}`,
      `<button type="button" onclick="checkLean()">Check again</button>` +
      ` <button type="button" onclick="runLeanSetup()">Run Lean setup</button>`);
  }
}

async function poll(){
  try {
    const r = await fetch('/api/log?offset=' + offset);
    const j = await r.json();
    if (j.lines && j.lines.length){
      const log = el('log');
      const atBottom = log.scrollTop + log.clientHeight >= log.scrollHeight - 30;
      log.textContent += j.lines.join('\n') + '\n';
      offset = j.total;
      ingestStageLines(j.lines, j);
      ingestProgressLines(j.lines);
      if (atBottom) log.scrollTop = log.scrollHeight;
    }
    const running = j.status === 'running';
    el('runBtn').disabled = running;
    el('stopBtn').style.display = running ? 'inline-block' : 'none';
    const st = el('status');
    const mins = Math.floor((j.elapsed||0)/60), secs = (j.elapsed||0)%60;
    st.textContent = j.status === 'idle' ? '' :
      (running ? `running · ${mins}m ${String(secs).padStart(2,'0')}s` : j.status);
    st.className = 'status ' + (j.status || '');
    renderStages(j);
    if (jobWasRunning && !running) refreshState();
    jobWasRunning = running;
  } catch (e) { /* server briefly unavailable; keep polling */ }
  setTimeout(poll, 1000);
}

async function refreshState(){
  const r = await fetch('/api/state');
  const s = await r.json();
  const firstLoad = !state.backends.length;
  const nextModelSignature = JSON.stringify({
    suggestions: s.model_suggestions || {},
    defaults: s.runner_defaults || {},
  });
  state = s;
  el('bps').innerHTML = s.blueprints.map(b=>`
    <li><span class="dot ${b.built?'built':''}"></span>
        <span>${esc(b.title)}</span> <span class="name">${b.name}</span>
        ${b.built?`<a href="/site/${b.name}/" target="_blank">view</a>`:''}</li>`).join('')
    || '<li class="hint">No blueprints yet — generate one.</li>';
  if (firstLoad){ renderTabs(); renderForm(); }
  else if (nextModelSignature !== modelStateSignature) refreshVisibleModelLists();
  if (!firstLoad && active === 'refine') {
    const last = el('lastSettingsBtn');
    if (last) last.disabled = !Object.keys(state.last_refine_settings || {}).length;
    updateResumeOptions();
  }
  modelStateSignature = nextModelSignature;
}

refreshState().then(poll);
</script>
</body>
</html>
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--port", type=int, default=8321)
    parser.add_argument(
        "--keep-existing",
        action="store_true",
        help="Do not stop a previously started Auto-Blueprint Web UI instance.",
    )
    parser.add_argument(
        "--strict-port",
        action="store_true",
        help="Fail instead of trying the next port if --port is already in use.",
    )
    parser.add_argument("--no-open", action="store_true", help="Do not open the browser")
    args = parser.parse_args()

    if not args.keep_existing:
        _stop_previous_webui()
        for candidate in range(args.port, args.port + 20):
            _stop_webui_on_port(candidate)

    server = None
    port = args.port
    for candidate in range(args.port, args.port + 20):
        try:
            server = ThreadingHTTPServer(("127.0.0.1", candidate), Handler)
            port = candidate
            break
        except OSError as exc:
            if exc.errno != errno.EADDRINUSE or args.strict_port:
                raise
            print(f"==> port {candidate} is already in use; trying {candidate + 1}")
    if server is None:
        raise SystemExit(f"no free port found in {args.port}..{args.port + 19}")

    url = f"http://127.0.0.1:{port}"
    _write_webui_state(port)
    atexit.register(_clear_webui_state)

    def handle_exit_signal(_signum, _frame) -> None:
        raise KeyboardInterrupt

    old_sigterm = signal.getsignal(signal.SIGTERM)
    signal.signal(signal.SIGTERM, handle_exit_signal)

    print(f"==> Auto-Blueprint UI running at {url}  (Ctrl-C to quit)")
    if not args.no_open:
        webbrowser.open(url)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n==> shutting down")
    finally:
        signal.signal(signal.SIGTERM, old_sigterm)
        server.server_close()
        _clear_webui_state()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
