#!/usr/bin/env python3
"""Best-effort maintenance outcomes outside the worktree.

The default is <git-common-dir>/maintenance-logs; set
TRURETURING_MAINTENANCE_LOG_DIR to choose another destination.
TRURETURING_MAINTENANCE_LOG_DIAGNOSTICS=1 enables logging-failure diagnostics.

Commands inherit IO directly. Logs retain run identity, outcomes and timings,
without intercepting output or saving command arguments or transcripts.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import uuid

ENV_LOG_DIR = "TRURETURING_MAINTENANCE_LOG_DIR"
ENV_LOG_DIAGNOSTICS = "TRURETURING_MAINTENANCE_LOG_DIAGNOSTICS"
ENV_RUN_ID = "TRURETURING_MAINTENANCE_RUN_ID"


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

    def __init__(self, script: str, repository: Path | None = None):
        self.started = time.monotonic()
        self.run_id = uuid.uuid4().hex
        self.path = None
        self.context = dict(run_id=self.run_id, parent_run_id=os.environ.get(ENV_RUN_ID),
                            pid=os.getpid(), parent_pid=os.getppid())
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


def run(options: argparse.Namespace) -> int:
    command = list(options.argv)
    if command[:1] == ["--"]:
        command.pop(0)
    if not command:
        print("maintenance-log: run requires a command", file=sys.stderr)
        return 64
    log = MaintenanceLog(options.script, options.repository)
    log.emit("run_started")
    process = None
    pending = []
    previous = {}

    def forward(signum, _frame):
        if process is None:
            pending.append(signum)
        else:
            process.send_signal(signum)

    # Keep the caller's process group, terminal and inherited ignored signals.
    # A handled signal may let the command continue; wait for its actual result.
    for signum in (signal.SIGTERM, signal.SIGHUP, signal.SIGINT, signal.SIGQUIT):
        handler = signal.getsignal(signum)
        if handler != signal.SIG_IGN:
            previous[signum] = handler
            signal.signal(signum, forward)
    try:
        try:
            # Match exec's inheritance of every deliberately inheritable handle,
            # including cooperative scopes and caller-owned cache locks.
            process = subprocess.Popen(command, close_fds=False, env=log.child_environment())
        except OSError as error:
            exit_code = 127 if isinstance(error, FileNotFoundError) else 126
            print(f"maintenance-log: {command[0]}: {error.strerror}", file=sys.stderr)
            log.finish(exit_code, error_type=type(error).__name__, errno=error.errno)
            return exit_code
        for signum in pending:
            process.send_signal(signum)
        return_code = process.wait()
        log.finish(return_code if return_code >= 0 else 128 - return_code,
                   signal=-return_code if return_code < 0 else None)
    finally:
        for signum, handler in previous.items():
            signal.signal(signum, handler)
    if return_code < 0:
        # Preserve native signal termination, including shell $? and Popen's
        # negative return code, after the command has been reaped and logged.
        signal.signal(-return_code, signal.SIG_DFL)
        os.kill(os.getpid(), -return_code)
    return return_code


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="subcommand", required=True)
    runner = commands.add_parser("run", help="run a maintenance command and retain its outcome")
    runner.add_argument("--script", required=True)
    runner.add_argument("--repository", type=Path)
    runner.add_argument("argv", nargs=argparse.REMAINDER)
    options = parser.parse_args(argv)
    return run(options)


if __name__ == "__main__":
    raise SystemExit(main())
