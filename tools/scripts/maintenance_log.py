#!/usr/bin/env python3
"""Best-effort maintenance outcomes outside the worktree.

The default is <git-common-dir>/maintenance-logs; set
TRURETURING_MAINTENANCE_LOG_DIR to choose another destination.
TRURETURING_MAINTENANCE_LOG_DIAGNOSTICS=1 enables logging-failure diagnostics.

The module only records lifecycle observations. It never starts, supervises,
signals, or waits for a business command. Logs retain run identity, outcomes
and timings without intercepting output or saving command arguments or
transcripts.
"""

from __future__ import annotations

import argparse
import base64
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import uuid

ENV_LOG_DIR = "TRURETURING_MAINTENANCE_LOG_DIR"
ENV_LOG_DIAGNOSTICS = "TRURETURING_MAINTENANCE_LOG_DIAGNOSTICS"
ENV_RUN_ID = "TRURETURING_MAINTENANCE_RUN_ID"
ENV_PARENT_RUN_ID = "TRURETURING_MAINTENANCE_PARENT_RUN_ID"


def log_directory(repository: Path) -> Path:
    configured = os.environ.get(ENV_LOG_DIR)
    if configured:
        directory = Path(configured).expanduser().absolute()
    else:
        result = subprocess.run(
            ["git", "-C", str(repository), "rev-parse", "--path-format=absolute", "--git-common-dir"],
            check=True, capture_output=True, text=True,
        )
        directory = Path(result.stdout.strip()) / "maintenance-logs"
        if not directory.is_absolute():
            raise OSError("git common directory is unavailable")
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    return directory


def _warning(event: str, error: Exception) -> None:
    if os.environ.get(ENV_LOG_DIAGNOSTICS) == "1":
        try:
            print(f"MAINTENANCE_LOG_WARNING event={event} error_type={type(error).__name__}",
                  file=sys.stderr, flush=True)
        except OSError:
            pass


class MaintenanceLog:
    """Resolve once, before actions may dispose of the source or current tree."""

    def __init__(self, script: str, repository: Path | None = None,
                 *, run_id: str | None = None, owner_pid: int | None = None,
                 parent_pid: int | None = None):
        self.started = time.monotonic()
        self.run_id = run_id or uuid.uuid4().hex
        self.path = None
        parent_run_id = os.environ.get(ENV_RUN_ID) or os.environ.get(ENV_PARENT_RUN_ID)
        if parent_run_id == self.run_id:
            parent_run_id = os.environ.get(ENV_PARENT_RUN_ID)
        self.context = dict(run_id=self.run_id, parent_run_id=parent_run_id,
                            pid=owner_pid or os.getpid(), parent_pid=parent_pid if parent_pid is not None else
                            (os.getppid() if owner_pid is None else None))
        try:
            if not script or any(character not in
                    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_.-" for character in script):
                raise ValueError("invalid maintenance script name")
            repository = (repository or Path.cwd()).absolute()
            self.context.update(script=script, repository=str(repository))
            self.path = log_directory(repository) / (script + ".jsonl")
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            _warning("initialize", error)

    def emit(self, event: str, **fields: object) -> bool:
        if self.path is None:
            return False
        try:
            row = dict(fields, **self.context,
                       schema=1, time=datetime.now(timezone.utc).isoformat(timespec="milliseconds"), event=event)
            # O_APPEND and flock keep interleaved runs' rows intact; the handle
            # closes after each write and never extends a command's lifetime.
            with self.path.open("a", encoding="utf-8") as stream:
                os.chmod(self.path, 0o600)
                fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
                stream.write(json.dumps(row, ensure_ascii=True, sort_keys=True, separators=(",", ":")) + "\n")
            return True
        except (OSError, TypeError, ValueError) as error:
            _warning(event, error)
            return False

    def finish(self, exit_code: int, **fields: object) -> None:
        self.emit("run_finished", exit_code=exit_code,
                  duration_seconds=round(time.monotonic() - self.started, 3), **fields)

    def child_environment(self, environment=None):
        return dict(os.environ if environment is None else environment, **{ENV_RUN_ID: self.run_id})

    def state(self) -> str:
        payload = dict(context=self.context, path=str(self.path) if self.path else None,
                       started=self.started)
        return self.run_id + ":" + base64.b64encode(json.dumps(payload).encode()).decode()

    @classmethod
    def restore(cls, state: str) -> "MaintenanceLog":
        payload = json.loads(base64.b64decode(state.split(":", 1)[1]))
        log = cls.__new__(cls)
        log.context = payload["context"]
        log.run_id = log.context["run_id"]
        log.path = Path(payload["path"]) if payload["path"] else None
        log.started = payload["started"]
        return log

    @classmethod
    def from_environment(cls) -> "MaintenanceLog | None":
        script = os.environ.get("TRURETURING_MAINTENANCE_SCRIPT")
        if not script:
            return None
        owner_pid = os.environ.get("TRURETURING_MAINTENANCE_OWNER_PID")
        parent_pid = os.environ.get("TRURETURING_MAINTENANCE_PARENT_PID")
        try:
            owner = int(owner_pid) if owner_pid else None
            parent = int(parent_pid) if parent_pid else None
        except ValueError:
            owner = parent = None
        return cls(script, Path(os.environ["TRURETURING_MAINTENANCE_REPOSITORY"])
                   if os.environ.get("TRURETURING_MAINTENANCE_REPOSITORY") else None,
                   run_id=os.environ.get(ENV_RUN_ID), owner_pid=owner, parent_pid=parent)


def _parse_owner(value: str | None) -> int | None:
    if value is None:
        return None
    try:
        return int(value)
    except ValueError:
        raise argparse.ArgumentTypeError("owner pid must be an integer")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="subcommand", required=True)
    start = commands.add_parser("begin", help="record a native owner start and return its state")
    start.add_argument("--script", required=True)
    start.add_argument("--repository", type=Path)
    start.add_argument("--owner-pid", type=_parse_owner)
    start.add_argument("--parent-pid", type=_parse_owner)
    event = commands.add_parser("emit", help="record an observation from loaded state")
    event.add_argument("--state", required=True)
    event.add_argument("--event", required=True)
    event.add_argument("--fields", help="JSON object of bounded observation fields")
    end = commands.add_parser("finish", help="record a native owner result from loaded state")
    end.add_argument("--state", required=True)
    end.add_argument("--exit-code", required=True, type=int)
    end.add_argument("--fields", help="JSON object of bounded outcome fields")
    options = parser.parse_args(argv)
    if options.subcommand == "begin":
        log = MaintenanceLog(options.script, options.repository, owner_pid=options.owner_pid,
                             parent_pid=options.parent_pid)
        log.emit("run_started")
        print(log.state(), flush=True)
    else:
        log = MaintenanceLog.restore(options.state)
        fields = json.loads(options.fields) if options.fields else {}
        if options.subcommand == "finish":
            log.finish(options.exit_code, **fields)
        else:
            log.emit(options.event, **fields)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
