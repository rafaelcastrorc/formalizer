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
import errno
import json
import mimetypes
import os
import re
import signal
import subprocess
import sys
import tempfile
import threading
import time
import webbrowser
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

from lean_preflight import check_lean_environment, default_lean_command

REPO_ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = REPO_ROOT / "scripts"
BLUEPRINTS_DIR = REPO_ROOT / "blueprints"
SITE_DIR = REPO_ROOT / "site"
STATE_DIR = REPO_ROOT / ".auto-blueprint"
WEBUI_STATE = STATE_DIR / "webui.json"
UPLOAD_DIR = Path(tempfile.mkdtemp(prefix="auto-blueprint-webui-"))

RUNNER_BACKENDS = ["claude-code", "codex", "anthropic", "openai", "mock"]
REASONING_EFFORTS = ["", "low", "medium", "high", "xhigh"]

NAME_RE = re.compile(r"^[a-z0-9][a-z0-9-]*$")


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
            os.killpg(self.proc.pid, signal.SIGTERM)
        except ProcessLookupError:
            return
        try:
            self.proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(self.proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            self.proc.wait()
        finally:
            _clear_webui_job_state(self.proc.pid)

    def snapshot(self, offset: int) -> dict:
        with self.lock:
            lines = _read_log_lines(self.log_path)
            return {
                "action": self.action,
                "status": self.status,
                "returncode": self.returncode,
                "elapsed": int(time.time() - self.started),
                "total": len(lines),
                "lines": lines[offset:],
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


def _read_log_lines(path: Path | None) -> list[str]:
    if path is None:
        return []
    try:
        return path.read_text(encoding="utf-8", errors="replace").splitlines()
    except OSError:
        return []


def _adopted_job_snapshot(offset: int) -> dict | None:
    """Expose a still-running job after a Web UI restart/crash lost CURRENT_JOB."""
    state = _read_webui_state()
    try:
        job_pid = int(state.get("job_pid") or 0)
    except (TypeError, ValueError):
        job_pid = 0
    if not _pid_is_running(job_pid):
        if state.get("pid") == os.getpid() and job_pid:
            _clear_webui_job_state(job_pid)
        return None

    log_path = Path(state["job_log"]) if state.get("job_log") else _latest_run_log()
    lines = _read_log_lines(log_path)
    try:
        started = int(state.get("job_started") or time.time())
    except (TypeError, ValueError):
        started = int(time.time())
    payload = {
        "action": state.get("job_action", "run"),
        "status": "running",
        "returncode": None,
        "elapsed": max(0, int(time.time() - started)),
        "total": len(lines),
        "lines": lines[offset:],
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
    if not _pid_is_running(job_pid):
        return False
    try:
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


def _looks_like_previous_webui(pid: int) -> bool:
    command = _pid_command(pid)
    return "webui.py" in command


def _terminate_webui_pid(pid: int, label: str) -> bool:
    print(f"==> stopping previous Auto-Blueprint UI at {label} (pid {pid})")
    os.kill(pid, signal.SIGTERM)
    deadline = time.time() + 5
    while time.time() < deadline:
        if not _pid_is_running(pid):
            return True
        time.sleep(0.1)
    print(f"==> previous UI pid {pid} did not exit yet")
    return False


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

def runner_spec(p: dict) -> str:
    backend = p.get("runner_backend", "claude-code")
    if backend not in RUNNER_BACKENDS:
        raise ValueError(f"unknown runner backend: {backend}")
    model = (p.get("runner_model") or "").strip()
    return f"{backend}:{model}" if model else backend


def common_runner_args(p: dict) -> list[str]:
    args = ["--runner", runner_spec(p)]
    effort = (p.get("reasoning_effort") or "").strip()
    if effort:
        if p.get("runner_backend") != "codex":
            raise ValueError("reasoning effort is only supported for the codex runner")
        if effort not in REASONING_EFFORTS:
            raise ValueError(f"unknown reasoning effort: {effort}")
        args += ["--reasoning-effort", effort]
    timeout = str(p.get("timeout") or "").strip()
    if timeout:
        if not timeout.isdigit():
            raise ValueError("timeout must be a number of seconds")
        args += ["--timeout", timeout]
    return args


def build_command(action: str, p: dict) -> list[str]:
    py = sys.executable
    if action == "setup_lean":
        cmd = [py, str(SCRIPTS / "setup_lean.py"), "--install-elan"]
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
        cmd = [py, str(SCRIPTS / "refine_blueprint_with_lean.py"), name]
        cmd += common_runner_args(p)
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

    raise ValueError(f"unknown action: {action}")


def lean_status_payload() -> dict:
    """Return a JSON-ready Lean setup status for the browser UI."""
    try:
        result = check_lean_environment(REPO_ROOT, lean_command=default_lean_command(REPO_ROOT))
        return result.to_dict()
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
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def read_json(self) -> dict:
        length = int(self.headers.get("Content-Length", 0))
        if length <= 0:
            return {}
        return json.loads(self.rfile.read(length))

    def send_file(self, path: Path) -> None:
        ctype = mimetypes.guess_type(str(path))[0] or "application/octet-stream"
        data = path.read_bytes()
        self.send_response(200)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

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
            adopted = None if CURRENT_JOB else _adopted_job_snapshot(0)
            self.send_json({
                "blueprints": list_blueprints(),
                "backends": RUNNER_BACKENDS,
                "efforts": [e for e in REASONING_EFFORTS if e],
                "job": CURRENT_JOB.snapshot(0) if CURRENT_JOB else adopted,
            })
        elif path == "/api/lean/status":
            self.send_json(lean_status_payload())
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
                raw_name = Path(p.get("filename", "paper.pdf")).name
                safe = re.sub(r"[^A-Za-z0-9._-]", "_", raw_name) or "paper.pdf"
                dest = UPLOAD_DIR / safe
                dest.write_bytes(base64.b64decode(p.get("data", "")))
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
  .stop { background: transparent; color: var(--bad); border: 1px solid var(--bad);
          padding: 7px 14px; border-radius: 7px; cursor: pointer; display: none; }
  .hint { font-size: 12px; color: var(--muted); margin-top: 4px; }
  .error { color: var(--bad); font-size: 13px; margin-top: 10px; min-height: 18px; }
  .leanbox { border: 1px solid var(--border); border-radius: 7px; padding: 9px;
             margin-top: 10px; font-size: 12.5px; color: var(--muted); background: var(--bg); }
  .leanbox.ok { border-color: var(--ok); color: var(--ok); }
  .leanbox.bad { border-color: var(--bad); color: var(--bad); }
  .leanbox button { margin-top: 7px; border: 1px solid var(--border); border-radius: 6px;
                    background: transparent; color: var(--text); padding: 5px 9px; cursor: pointer; }
  .leanbox code { color: var(--text); }
  .status { font-size: 13px; margin-left: auto; }
  .status.running { color: var(--accent); } .status.done { color: var(--ok); }
  .status.failed, .status.stopped { color: var(--bad); }
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
    <div id="log"></div>
  </div>
</main>
<script>
const TABS = [
  {id:'generate', label:'Generate'},
  {id:'refine',   label:'Refine with Lean'},
  {id:'validate', label:'Validate'},
  {id:'build',    label:'Build site'},
];
let state = {blueprints: [], backends: [], efforts: []};
let active = 'generate';
let offset = 0;
let jobWasRunning = false;

function el(id){ return document.getElementById(id); }
function esc(s){ const d=document.createElement('div'); d.textContent=s; return d.innerHTML; }

function runnerFields(){
  const opts = state.backends.map(b=>`<option ${b==='claude-code'?'selected':''}>${b}</option>`).join('');
  const effs = ['<option value="">(default)</option>']
    .concat(state.efforts.map(e=>`<option>${e}</option>`)).join('');
  return `
    <div class="row">
      <div><label>Runner</label>
        <select id="f_backend" onchange="effortToggle()">${opts}</select></div>
      <div><label>Model (optional)</label>
        <input type="text" id="f_model" placeholder="e.g. claude-fable-5"></div>
    </div>
    <div class="row">
      <div><label>Reasoning effort (codex only)</label>
        <select id="f_effort" disabled>${effs}</select></div>
      <div><label>Timeout (seconds)</label>
        <input type="number" id="f_timeout" value="3600"></div>
    </div>`;
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
    ${runnerFields()}
    <div class="check"><input type="checkbox" id="f_force"><label for="f_force">Force (replace existing folder)</label></div>
    <div class="check"><input type="checkbox" id="f_nobuild"><label for="f_nobuild">Validate only, skip site build</label></div>`,
  refine: () => `
    <label>Blueprint</label>
    <select id="f_name">${bpSelect()}</select>
    <label>Max blueprint-repair trials</label>
    <input type="number" id="f_trials" value="3" min="1">
    <div class="leanbox" id="leanStatus">Lean setup not checked.
      <br><button type="button" onclick="checkLean()">Check Lean setup</button>
    </div>
    ${paperField(false)}
    ${runnerFields()}
    <label>Lean command override (optional)</label>
    <input type="text" id="f_leancmd" placeholder="lake env lean">`,
  validate: () => `
    <div class="hint">Select blueprints to validate (none = all).</div>
    ${bpChecks()}`,
  build: () => `
    <div class="hint">Select blueprints to rebuild (none = full rebuild).</div>
    ${bpChecks()}
    <div class="check"><input type="checkbox" id="f_strict"><label for="f_strict">Strict (fail if any blueprint fails)</label></div>`,
};

function renderTabs(){
  el('tabs').innerHTML = TABS.map(t=>
    `<button class="${t.id===active?'active':''}" onclick="setTab('${t.id}')">${t.label}</button>`).join('');
}
function setTab(id){ active = id; renderTabs(); renderForm(); }

function renderForm(){
  el('form').innerHTML = FORMS[active]();
  el('error').textContent = '';
  effortToggle();
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

function effortToggle(){
  const b = el('f_backend'), eff = el('f_effort');
  if (b && eff) eff.disabled = b.value !== 'codex';
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
    reasoning_effort: el('f_effort') && !el('f_effort').disabled ? v('f_effort') : '',
    timeout: v('f_timeout'),
  };
  if (active === 'generate')
    return {action:'generate', paper:v('f_paper'), name:v('f_name'),
            force:c('f_force'), no_build:c('f_nobuild'), ...common};
  if (active === 'refine')
    return {action:'refine', name:v('f_name'), max_trials:v('f_trials'),
            paper:v('f_paper'), lean_command:v('f_leancmd'), ...common};
  const names = [...document.querySelectorAll('.bpcheck:checked')].map(n=>n.value);
  if (active === 'validate') return {action:'validate', names};
  return {action:'build', names, strict:c('f_strict')};
}

async function run(){
  el('error').textContent = '';
  const r = await fetch('/api/run', {method:'POST', headers:{'Content-Type':'application/json'},
    body: JSON.stringify(params())});
  const j = await r.json();
  if (j.error){ el('error').textContent = j.error; return; }
  el('log').textContent = '';
  offset = 0;
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
}

async function checkLean(){
  const box = el('leanStatus');
  if (!box) return;
  box.className = 'leanbox';
  box.innerHTML = 'Checking Lean/Lake/Mathlib setup…';
  try {
    const r = await fetch('/api/lean/status');
    const j = await r.json();
    const cmd = (j.command || []).join(' ');
    const detail = (j.stderr || j.stdout || '').trim().split('\n').slice(-5).join('\n');
    box.className = 'leanbox ' + (j.ok ? 'ok' : 'bad');
    box.innerHTML = `${esc(j.message || (j.ok ? 'Lean setup ready' : 'Lean setup failed'))}` +
      (j.elapsed_s ? ` · ${Number(j.elapsed_s).toFixed(1)}s` : '') +
      (cmd ? `<br><code>${esc(cmd)}</code>` : '') +
      (detail ? `<pre style="white-space:pre-wrap;margin:7px 0 0">${esc(detail)}</pre>` : '') +
      `<br><button type="button" onclick="checkLean()">Check again</button>` +
      (j.ok ? '' : ` <button type="button" onclick="runLeanSetup()">Run Lean setup</button>`);
  } catch (e) {
    box.className = 'leanbox bad';
    box.innerHTML = `Could not check Lean setup: ${esc(String(e))}` +
      `<br><button type="button" onclick="checkLean()">Check again</button>` +
      ` <button type="button" onclick="runLeanSetup()">Run Lean setup</button>`;
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
    if (jobWasRunning && !running) refreshState();
    jobWasRunning = running;
  } catch (e) { /* server briefly unavailable; keep polling */ }
  setTimeout(poll, 1000);
}

async function refreshState(){
  const r = await fetch('/api/state');
  const s = await r.json();
  const firstLoad = !state.backends.length;
  state = s;
  el('bps').innerHTML = s.blueprints.map(b=>`
    <li><span class="dot ${b.built?'built':''}"></span>
        <span>${esc(b.title)}</span> <span class="name">${b.name}</span>
        ${b.built?`<a href="/site/${b.name}/" target="_blank">view</a>`:''}</li>`).join('')
    || '<li class="hint">No blueprints yet — generate one.</li>';
  if (firstLoad){ renderTabs(); renderForm(); }
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
        _stop_stale_pipeline_jobs()

    server = None
    port = args.port
    for candidate in range(args.port, args.port + 20):
        if not args.keep_existing:
            _stop_webui_on_port(candidate)
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
