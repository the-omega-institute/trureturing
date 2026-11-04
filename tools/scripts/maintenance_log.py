#!/usr/bin/env python3
"""Append small, structured maintenance outcomes outside the worktree.

The default destination is the repository's Git common directory.  Linked
worktrees therefore share one history without adding generated files to the
checkout.  The log contains outcomes and timings, never command transcripts.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import threading
import time


ENV_LOG_DIR = "TRURETURING_MAINTENANCE_LOG_DIR"
ENV_LOG_DIAGNOSTICS = "TRURETURING_MAINTENANCE_LOG_DIAGNOSTICS"
EVENTS = {"worktree_disk"}


def _repository(path: Path | None = None) -> Path:
    value = path or Path.cwd()
    result = subprocess.run(
        ["git", "-C", str(value), "rev-parse", "--path-format=absolute", "--git-common-dir"],
        check=True,
        capture_output=True,
        text=True,
    )
    common = Path(result.stdout.strip()).resolve()
    if not common.is_absolute() or not common.exists() or not common.is_dir():
        raise OSError("git common directory is unavailable")
    return common


def log_directory(repository: Path | None = None) -> Path:
    configured = os.environ.get(ENV_LOG_DIR)
    directory = Path(configured).expanduser() if configured else _repository(repository) / "maintenance-logs"
    directory = directory.absolute()
    if directory.exists() and directory.is_symlink():
        raise OSError("maintenance log directory must not be a symlink")
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    if not directory.is_dir():
        raise OSError("maintenance log path is not a directory")
    return directory


def _safe_name(script: str) -> str:
    if not script or any(character not in "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.-" for character in script):
        raise ValueError("invalid maintenance script name")
    return script


def append(script: str, event: str, *, repository: Path | None = None, **fields: object) -> Path:
    """Append one outcome record and return its path."""
    script = _safe_name(script)
    row = {
        "schema": 1,
        "time": datetime.now(timezone.utc).isoformat(timespec="milliseconds"),
        "script": script,
        "event": event,
        **fields,
    }
    path = log_directory(repository) / f"{script}.jsonl"
    with path.open("a", encoding="utf-8") as stream:
        os.chmod(path, 0o600)
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
        try:
            stream.write(json.dumps(row, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n")
            stream.flush()
        finally:
            fcntl.flock(stream.fileno(), fcntl.LOCK_UN)
    return path


def safe_append(script: str, event: str, *, repository: Path | None = None, **fields: object) -> bool:
    """Best-effort logging: maintenance behavior never depends on the logger."""
    try:
        append(script, event, repository=repository, **fields)
        return True
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        if os.environ.get(ENV_LOG_DIAGNOSTICS) == "1":
            print(f"MAINTENANCE_LOG_WARNING event={event} error={error}", file=sys.stderr, flush=True)
        return False


def _forward(stream, target, script: str, repository: Path | None, started: float) -> None:
    for line in iter(stream.readline, ""):
        target.write(line)
        target.flush()
        try:
            row = json.loads(line)
        except (json.JSONDecodeError, TypeError):
            continue
        if not isinstance(row, dict):
            continue
        event = row.get("event")
        if isinstance(event, str) and (event.endswith("_summary") or event.endswith("_warning") or event in EVENTS):
            fields = dict(row)
            fields.pop("event", None)
            safe_append(script, event, repository=repository, **fields)


def run(options: argparse.Namespace) -> int:
    command = list(options.argv)
    if command[:1] == ["--"]:
        command.pop(0)
    if not command:
        print("maintenance-log: run requires a command", file=sys.stderr)
        return 64
    repository = Path(options.repository).absolute() if options.repository else None
    started = time.monotonic()
    safe_append(options.script, "run_started", repository=repository)
    process = subprocess.Popen(command, stdin=None, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1)
    threads = [
        threading.Thread(target=_forward, args=(process.stdout, sys.stdout, options.script, repository, started), daemon=True),
        threading.Thread(target=_forward, args=(process.stderr, sys.stderr, options.script, repository, started), daemon=True),
    ]
    for thread in threads:
        thread.start()
    return_code = process.wait()
    for thread in threads:
        thread.join()
    exit_code = return_code if return_code >= 0 else 128 - return_code
    safe_append(options.script, "run_finished", repository=repository, exit_code=exit_code,
                duration_seconds=round(time.monotonic() - started, 3))
    return exit_code


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="subcommand", required=True)
    runner = commands.add_parser("run", help="run a maintenance command and retain outcome events")
    runner.add_argument("--script", required=True)
    runner.add_argument("--repository", type=Path)
    runner.add_argument("argv", nargs=argparse.REMAINDER)
    options = parser.parse_args(argv)
    if options.subcommand == "run":
        return run(options)
    return 64


if __name__ == "__main__":
    raise SystemExit(main())
