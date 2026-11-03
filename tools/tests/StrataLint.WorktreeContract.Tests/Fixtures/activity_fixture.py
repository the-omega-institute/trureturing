"""Test-owned process inventory with real production cwd, fd and argv observations."""

import argparse
from contextlib import AbstractContextManager
import os
from pathlib import Path
import runpy
import shlex
import subprocess
import sys


class ActivityScope(AbstractContextManager):
    def __init__(self, root_pid):
        self.root_pid = root_pid
        self.previous_iterdir = Path.iterdir
        self.previous_run = subprocess.run
        self.previous_popen = subprocess.Popen
        self.native_popen = getattr(subprocess.Popen, "activity_original", subprocess.Popen)
        self.native_iterdir = getattr(Path.iterdir, "activity_original", Path.iterdir)
        self.native_run = getattr(subprocess.run, "activity_original", subprocess.run)

    def owned_pids(self):
        observed = self.native_run(["ps", "-axo", "pid=,ppid=,pgid="],
                                   capture_output=True, text=True, timeout=10)
        if observed.returncode:
            raise OSError("fixture process inventory unavailable: " + observed.stderr)
        rows = [tuple(map(int, line.split())) for line in observed.stdout.splitlines() if line.strip()]
        owned = {self.root_pid}
        while True:
            current = owned | {pid for pid, parent, _ in rows if parent in owned}
            if current == owned:
                break
            owned = current
        groups = {group for pid, _, group in rows if pid in owned and pid == group}
        root_group = next((group for pid, _, group in rows if pid == self.root_pid), None)
        if os.getpgrp() != root_group:
            groups.add(os.getpgrp())
        # NativeFixture owns new sessions; retain their descendants after reparenting.
        observed = owned | {pid for pid, _, group in rows if group in groups} | {os.getpid()}
        alive = set()
        for pid in observed:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                continue
            except PermissionError:
                pass
            alive.add(pid)
        return alive

    def __enter__(self):
        scope = self
        def iterdir(path):
            if path == Path("/proc"):
                return iter(Path("/proc") / str(pid) for pid in sorted(scope.owned_pids()))
            return scope.native_iterdir(path)

        def run(args, *run_args, **kwargs):
            command = list(map(str, args)) if not isinstance(args, str) else []
            if (len(command) == 3 and command[:2] == ["ps", "-axo"]
                    and "uid=" in command[2] and "args=" in command[2]):
                columns = command[2].split(",")
                if "pid=" not in columns:
                    command[2] = "uid=,pid=,args="
                result = scope.native_run(command, *run_args, **kwargs)
                if result.returncode:
                    return result
                owned = scope.owned_pids()
                actual_columns = command[2].split(",")
                pid_column = actual_columns.index("pid=")
                lines = []
                for line in result.stdout.splitlines():
                    fields = line.strip().split(None, len(actual_columns) - 1)
                    if len(fields) == len(actual_columns) and int(fields[pid_column]) in owned:
                        lines.append(line if "pid=" in columns else fields[0] + " " + fields[-1])
                return subprocess.CompletedProcess(result.args, result.returncode,
                                                   "\n".join(lines) + "\n", result.stderr)
            if command and Path(command[0]).name == "lsof" and "-Fftn" in command:
                owned = scope.owned_pids()
                result = scope.native_run(command, *run_args, **kwargs)
                if result.returncode or result.stdout is None:
                    return result
                prefix = b"p" if isinstance(result.stdout, bytes) else "p"
                rows, selected = [], False
                for row in result.stdout.splitlines(keepends=True):
                    if row.startswith(prefix):
                        selected = row[1:].strip().isdigit() and int(row[1:]) in owned
                    if selected:
                        rows.append(row)
                return subprocess.CompletedProcess(result.args, result.returncode,
                                                   result.stdout[:0].join(rows), result.stderr)
            return scope.native_run(args, *run_args, **kwargs)

        class Popen(scope.native_popen):
            def __init__(self, args, *popen_args, **kwargs):
                if (not isinstance(args, str) and args and str(args[0]) == sys.executable
                        and str(Path(__file__).resolve()) not in list(map(str, args))):
                    args = [sys.executable, "-I", "-B", str(Path(__file__).resolve()),
                            "--root", str(scope.root_pid), "--", *args[1:]]
                super().__init__(args, *popen_args, **kwargs)

        iterdir.activity_original = self.native_iterdir
        run.activity_original = self.native_run
        Popen.activity_original = self.native_popen
        Path.iterdir, subprocess.run, subprocess.Popen = iterdir, run, Popen
        return self

    def __exit__(self, *exc):
        Path.iterdir, subprocess.run, subprocess.Popen = (
            self.previous_iterdir, self.previous_run, self.previous_popen)


class FixtureActivity(ActivityScope):
    def __init__(self, directory):
        super().__init__(os.getpid())
        self.directory = directory

    def __enter__(self):
        self.previous_path = os.environ["PATH"]
        self.directory.mkdir()
        shim = self.directory / "python3"
        command = [sys.executable, "-I", "-B", str(Path(__file__).resolve()),
                   "--root", str(self.root_pid), "--"]
        shim.write_text("#!/bin/sh\nexec " + shlex.join(command) + ' "$@"\n')
        shim.chmod(0o755)
        os.environ["PATH"] = str(self.directory) + os.pathsep + self.previous_path
        return super().__enter__()

    def __exit__(self, *exc):
        super().__exit__(*exc)
        os.environ["PATH"] = self.previous_path


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=int, default=os.getpid())
    parser.add_argument("command", nargs=argparse.REMAINDER)
    options = parser.parse_args()
    command = options.command
    if command[:1] == ["--"]:
        command.pop(0)
    while command and command[0] in ("-I", "-B", "-u", "-s", "-S", "-E"):
        command.pop(0)
    if not command:
        raise ValueError("fixture Python program required")
    with ActivityScope(options.root):
        entry, *arguments = command
        if entry == "-c":
            sys.argv = ["-c", *arguments[1:]]
            exec(compile(arguments[0], "<string>", "exec"), {"__name__": "__main__"})
        elif entry == "-":
            sys.argv = ["-", *arguments]
            exec(compile(sys.stdin.read(), "<stdin>", "exec"),
                 {"__name__": "__main__", "__file__": "<stdin>"})
        elif entry == "-m":
            sys.argv = arguments
            runpy.run_module(arguments[0], run_name="__main__", alter_sys=True)
        else:
            sys.argv = [entry, *arguments]
            sys.path.insert(0, str(Path(entry).resolve().parent))
            runpy.run_path(entry, run_name="__main__")


if __name__ == "__main__":
    main()
