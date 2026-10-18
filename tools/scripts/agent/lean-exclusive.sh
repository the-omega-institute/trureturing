#!/usr/bin/env bash
# Usage: lean-exclusive.sh CMD [ARG...] | --selftest
# Requires Bash 3.2+, Git with --path-format, and Python 3 on macOS or Linux.
# Runs CMD in the current Git worktree under the shared Lean build lock.
set -euo pipefail

if [[ "${1:-}" == --selftest ]]; then
  exec python3 - "${BASH_SOURCE[0]}" <<'PY'
import json
import os
from pathlib import Path
import selectors
import subprocess
import sys
import tempfile

subject = Path(sys.argv[1]).resolve()
waiting = "lean-exclusive: waiting for another Lean build to finish\n"


def check(condition, message):
    if not condition:
        raise AssertionError(message)


with tempfile.TemporaryDirectory(prefix="lean-exclusive test ") as temporary:
    root = Path(temporary)
    env = {key: value for key, value in os.environ.items()
           if not key.startswith("GIT_") and key not in ("BASH_ENV", "ENV")}
    env.update(HOME=str(root), GIT_CONFIG_NOSYSTEM="1",
               GIT_CONFIG_GLOBAL=os.devnull)

    def git(*args):
        return subprocess.run(["git", *map(str, args)], env=env, check=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              text=True).stdout.strip()

    def command(cwd, *args):
        return ["bash", str(subject), *map(str, args)]

    def run(cwd, *args):
        return subprocess.run(command(cwd, *args), cwd=cwd, env=env,
                              capture_output=True, text=True, timeout=10)

    result = run(root)
    check(result.returncode == 2 and
          "lean-exclusive: command is required" in result.stderr,
          f"missing command: {result}")
    print("PASS missing command (exit 2)")

    result = run(root, sys.executable, "-c", "raise SystemExit(99)")
    check(result.returncode == 3 and
          "lean-exclusive: not inside a Git work tree" in result.stderr,
          f"outside worktree: {result}")
    print("PASS outside Git worktree (exit 3)")

    repository = root / "repository with spaces"
    git("init", "-q", repository)
    git("-C", repository, "-c", "user.name=Selftest", "-c",
        "user.email=selftest@example.invalid", "-c", "core.hooksPath=" + os.devnull,
        "commit", "-q", "--allow-empty", "-m", "fixture")
    seats = [root / "seat one", root / "seat two"]
    for seat in seats:
        git("-C", repository, "worktree", "add", "-q", "--detach", seat)
    lock = Path(git("-C", seats[0], "rev-parse", "--path-format=absolute",
                    "--git-common-dir")) / "stratalint-lean-build.lock"
    check(lock.parent == Path(git("-C", seats[1], "rev-parse",
                                 "--path-format=absolute", "--git-common-dir")),
          "linked worktrees must share the lock directory")

    result = run(seats[0], sys.executable, "-c", "raise SystemExit(37)")
    check(result.returncode == 37, f"exit code: {result}")
    print("PASS command exit code (37)")
    check(lock.is_file(), "lock file missing after command exit")
    identity = lock.stat().st_ino

    result = run(seats[0], "lean-exclusive-selftest-command-does-not-exist")
    check(result.returncode == 127 and
          "lean-exclusive: command not found:" in result.stderr,
          f"unavailable executable: {result}")
    print("PASS unavailable executable (exit 127)")

    result = run(seats[1], sys.executable, "-c",
                 "import sys; print(repr(sys.argv[1:]))", "two words", "", "*")
    check(result.returncode == 0 and
          result.stdout == "['two words', '', '*']\n", f"arguments: {result}")
    print("PASS argument preservation")

    stub = root / "timestamp stub.py"
    stub.write_text('''import json
from pathlib import Path
import sys
import time

start = time.monotonic_ns()
if sys.argv[2] == "first":
    print("ready", flush=True)
    sys.stdin.buffer.read(1)
    time.sleep(0.1)
Path(sys.argv[1]).write_text(json.dumps([start, time.monotonic_ns()]))
''')

    def line(stream):
        with selectors.DefaultSelector() as selector:
            selector.register(stream, selectors.EVENT_READ)
            check(selector.select(timeout=10), "timed out waiting for test command")
        return stream.readline()

    processes = []
    try:
        first = subprocess.Popen(command(seats[0], sys.executable, stub,
                                         root / "first.json", "first"),
                                 cwd=seats[0], env=env, stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        processes.append(first)
        check(line(first.stdout) == b"ready\n", "first command did not start")
        second = subprocess.Popen(command(seats[1], sys.executable, stub,
                                          root / "second.json", "second"),
                                  cwd=seats[1], env=env, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE)
        processes.append(second)
        check(line(second.stderr).decode() == waiting, "missing lock contention message")
        first_output = first.communicate(input=b"go", timeout=10)
        second_output = second.communicate(timeout=10)
        check(first.returncode == second.returncode == 0,
              f"concurrent commands failed: {first_output}, {second_output}")
        first_times = json.loads((root / "first.json").read_text())
        second_times = json.loads((root / "second.json").read_text())
        check(first_times[0] <= first_times[1] <= second_times[0] <= second_times[1],
              f"commands overlapped: {first_times}, {second_times}")
        print("PASS linked worktrees serialize commands (timestamp ordering)")
        print("PASS busy lock emits the waiting message")
    finally:
        for process in processes:
            if process.poll() is None:
                process.communicate(input=b"go" if process is first else None, timeout=10)

    check(lock.is_file() and lock.stat().st_ino == identity,
          "lock file was unlinked or replaced")
    print("PASS lock file survives with the same inode")

print("SELFTEST_PASS")
PY
fi

[[ $# -gt 0 ]] || { echo 'lean-exclusive: command is required' >&2; exit 2; }
for tool in git python3; do
  command -v "$tool" >/dev/null || { echo "lean-exclusive: $tool is required" >&2; exit 69; }
done
if [[ "$(git rev-parse --is-inside-work-tree 2>/dev/null)" != true ]]; then
  echo 'lean-exclusive: not inside a Git work tree' >&2
  exit 3
fi
command -v "$1" >/dev/null || { echo "lean-exclusive: command not found: $1" >&2; exit 127; }
lean_common_dir="$(git rev-parse --path-format=absolute --git-common-dir)"
# Keep the append-open descriptor through exec; never unlink the shared lock.
exec 9>>"$lean_common_dir/stratalint-lean-build.lock"
python3 - <<'PY'
import fcntl
import sys

try:
    try:
        fcntl.flock(9, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("lean-exclusive: waiting for another Lean build to finish", file=sys.stderr, flush=True)
        fcntl.flock(9, fcntl.LOCK_EX)
except KeyboardInterrupt:
    raise SystemExit(130)
PY
exec "$@"
