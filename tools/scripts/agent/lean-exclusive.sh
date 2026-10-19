#!/usr/bin/env bash
# Usage: lean-exclusive.sh CMD [ARG...] | --selftest
# Requires Bash 3.2+, Git with --path-format, and Python 3 on macOS or Linux.
# Runs CMD under a shared direct-command slot, separate from the Lean build lock.
# LEAN_EXCLUSIVE_SLOTS: positive integer capacity, default 4; use the same value
# across worktrees sharing a Git common directory.
# LEAN_EXCLUSIVE_MIN_FREE_VNODES: nonnegative integer floor, default 40000.
# Available kern.free_vnodes / kern.maxvnodes counters gate admission every 5 s.
# LEAN_EXCLUSIVE_SYSCTL: test hook overriding the sysctl command path; it receives
# -n and a counter name as its last argument. Missing counters skip the guard.
set -euo pipefail

if [[ "${1:-}" == --selftest ]]; then
  exec python3 - "${BASH_SOURCE[0]}" <<'PY'
import fcntl
import json
import os
from pathlib import Path
import selectors
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile

subject = Path(sys.argv[1]).resolve()
bash = shutil.which("bash")
waiting = "lean-exclusive: waiting for a free Lean command slot\n"
timeout = 0.9


def check(condition, message):
    if not condition:
        raise AssertionError(f"[FAIL] {message}")


with tempfile.TemporaryDirectory(prefix="lean-exclusive test ") as temporary:
    root = Path(temporary)
    env = {key: value for key, value in os.environ.items()
           if not key.startswith(("GIT_", "LEAN_EXCLUSIVE_"))
           and key not in ("BASH_ENV", "ENV", "PYTHONPATH", "PYTHONHOME")}
    env.update(HOME=str(root), GIT_CONFIG_NOSYSTEM="1",
               GIT_CONFIG_GLOBAL=os.devnull,
               LEAN_EXCLUSIVE_SYSCTL=str(root / "absent sysctl"))

    def git(*args):
        return subprocess.run(["git", *map(str, args)], env=env, check=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                              text=True, timeout=timeout).stdout.strip()

    def command(*args):
        return [bash, str(subject), *map(str, args)]

    def run(cwd, *args, overrides=None):
        return subprocess.run(command(*args), cwd=cwd,
                              env=dict(env, **(overrides or {})),
                              capture_output=True, text=True, timeout=timeout)

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

    for missing in ("git", "python3"):
        tool_path = root / ("without " + missing)
        tool_path.mkdir()
        other = "python3" if missing == "git" else "git"
        (tool_path / other).symlink_to(shutil.which(other))
        result = run(root, sys.executable, overrides={"PATH": str(tool_path)})
        check(result.returncode == 69 and
              f"lean-exclusive: {missing} is required" in result.stderr,
              f"missing tool {missing}: {result}")
    print("PASS missing tools (exit 69)")

    repository = root / "repository with spaces"
    git("init", "-q", repository)
    git("-C", repository, "-c", "user.name=Selftest", "-c",
        "user.email=selftest@example.invalid", "-c", "core.hooksPath=" + os.devnull,
        "commit", "-q", "--allow-empty", "-m", "fixture")
    seats = [root / "seat one", root / "seat two"]
    for seat in seats:
        git("-C", repository, "worktree", "add", "-q", "--detach", seat)
    common = Path(git("-C", seats[0], "rev-parse", "--path-format=absolute",
                      "--git-common-dir"))
    check(common == Path(git("-C", seats[1], "rev-parse",
                             "--path-format=absolute", "--git-common-dir")),
          "linked worktrees must share the lock directory")
    lock = common / "stratalint-lean-direct-0.lock"
    build_lock = common / "stratalint-lean-build.lock"

    result = run(seats[0], sys.executable, "-c", "raise SystemExit(37)")
    check(result.returncode == 37, f"exit code: {result}")
    print("PASS command exit code (37)")
    check(lock.is_file(), "slot file missing after command exit")
    identity = lock.stat().st_ino
    result = run(seats[0], "lean-exclusive-selftest-command-does-not-exist")
    check(result.returncode == 127 and
          "lean-exclusive: command not found:" in result.stderr,
          f"unavailable executable: {result}")
    print("PASS unavailable executable (exit 127)")

    arguments = ["two words", "", "*", "a\nb", "$(false)", "--flag", "参数"]
    result = run(seats[1], sys.executable, "-c",
                 "import json, sys; print(json.dumps(sys.argv[1:]))", *arguments)
    check(result.returncode == 0 and json.loads(result.stdout) == arguments,
          f"arguments: {result}")
    plain = root / "executable without shebang"
    plain.write_text('printf "%s\\n" "$1"\n')
    plain.chmod(0o700)
    result = run(seats[0], plain, "two words")
    check(result.returncode == 0 and result.stdout == "two words\n",
          f"Bash exec semantics: {result}")
    print("PASS argument preservation and Bash exec semantics")

    for name, values in (
            ("LEAN_EXCLUSIVE_SLOTS", ("", "0", "-1", "1.5", "two", " 2", "+2")),
            ("LEAN_EXCLUSIVE_MIN_FREE_VNODES", ("", "-1", "1.5", "many", " 0"))):
        for value in values:
            result = run(seats[0], sys.executable, "-c", "pass",
                         overrides={name: value})
            check(result.returncode == 2 and name in result.stderr,
                  f"invalid {name}={value!r}: {result}")
    result = run(seats[0], sys.executable, "-c", "pass", overrides={
        "LEAN_EXCLUSIVE_SLOTS": "01", "LEAN_EXCLUSIVE_MIN_FREE_VNODES": "0"})
    check(result.returncode == 0, f"integer boundaries: {result}")
    print("PASS invalid slot/floor values (exit 2) and integer boundaries")

    stub = root / "timestamp stub.py"
    stub.write_text('''import json
from pathlib import Path
import sys
import time

start = time.clock_gettime_ns(time.CLOCK_MONOTONIC)
print("ready", flush=True)
if sys.argv[2] == "hold":
    sys.stdin.buffer.read(1)
    time.sleep(0.05)
Path(sys.argv[1]).write_text(json.dumps([
    start, time.clock_gettime_ns(time.CLOCK_MONOTONIC)]))
''')

    def line(stream):
        with selectors.DefaultSelector() as selector:
            selector.register(stream, selectors.EVENT_READ)
            check(selector.select(timeout=timeout), "timed out waiting for test command")
        return stream.readline()

    processes = []

    def start(label, seat, slots=None, hold=False, overrides=None):
        options = dict(overrides or {})
        if slots is not None:
            options["LEAN_EXCLUSIVE_SLOTS"] = str(slots)
        process = subprocess.Popen(
            command(sys.executable, stub, root / (label + ".json"),
                    "hold" if hold else "run"), cwd=seat, env=dict(env, **options),
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        processes.append(process)
        return process

    def finish(process, release=False, expected=0):
        output = process.communicate(input=b"go" if release else None, timeout=timeout)
        check(process.returncode == expected,
              f"test command exit {process.returncode}, expected {expected}: {output}")
        return output

    def times(label):
        return json.loads((root / (label + ".json")).read_text())

    try:
        first = start("first", seats[0], 2, hold=True)
        check(line(first.stdout) == b"ready\n", "first command did not start")
        second = start("second", seats[1], 2, hold=True)
        check(line(second.stdout) == b"ready\n", "second slot did not run concurrently")
        second_lock = common / "stratalint-lean-direct-1.lock"
        check(second_lock.is_file(), "second slot file missing")
        second_identity = second_lock.stat().st_ino
        third = start("third", seats[0], 2)
        check(line(third.stderr).decode() == waiting, "missing slot contention message")
        check(not (root / "third.json").exists(), "third command exceeded capacity")
        interrupted = start("interrupted", seats[1], 2)
        check(line(interrupted.stderr).decode() == waiting, "interrupt case did not wait")
        interrupted.send_signal(signal.SIGINT)
        finish(interrupted, expected=130)
        check(not (root / "interrupted.json").exists(), "interrupted command ran")
        finish(second, release=True)
        third_output = finish(third)
        check(third_output[1] == b"", "slot waiting message repeated")
        check(not (root / "first.json").exists(), "first slot released unexpectedly")
        finish(first, release=True)
        first_times, second_times, third_times = map(times, ("first", "second", "third"))
        check(first_times[0] <= second_times[0] < second_times[1] <= first_times[1],
              f"two-slot commands did not overlap: {first_times}, {second_times}")
        check(second_times[1] <= third_times[0] <= third_times[1] <= first_times[1],
              f"third did not use the released second slot: {third_times}")
        print("PASS two slots overlap; third waits once and retries every slot")
        print("PASS Ctrl-C while waiting (exit 130)")

        first = start("serial first", seats[0], 1, hold=True)
        check(line(first.stdout) == b"ready\n", "serial first did not start")
        second = start("serial second", seats[1], 1)
        check(line(second.stderr).decode() == waiting, "single slot did not wait")
        finish(first, release=True)
        output = finish(second)
        check(output[1] == b"", "single-slot waiting message repeated")
        first_times, second_times = times("serial first"), times("serial second")
        check(first_times[0] <= first_times[1] <= second_times[0] <= second_times[1],
              f"single-slot commands overlapped: {first_times}, {second_times}")
        print("PASS one slot serializes linked worktrees (timestamp ordering)")

        holders = []
        for index in range(4):
            process = start(f"default {index}", seats[index % 2], hold=True)
            holders.append(process)
            check(line(process.stdout) == b"ready\n", "default capacity is below four")
        fifth = start("default fifth", seats[0])
        check(line(fifth.stderr).decode() == waiting, "default capacity exceeds four")
        for process in holders:
            finish(process, release=True)
        finish(fifth)
        print("PASS default capacity is four")

        check(not build_lock.exists(), "direct commands touched the build lock")
        with build_lock.open("a") as build_descriptor:
            fcntl.flock(build_descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            result = run(seats[0], sys.executable, "-c", "pass")
            check(result.returncode == 0, f"build lock blocked a direct slot: {result}")
        print("PASS direct slots are independent of the build lock")

        counter = root / "free vnode count"
        counter.write_text("39999")
        sysctl = root / "sysctl stub"
        sysctl.write_text("#!/bin/sh\ncase \"$2\" in\n"
                          "  kern.free_vnodes) cat " + shlex.quote(str(counter)) + ";;\n"
                          "  kern.maxvnodes) echo 263168;;\n  *) exit 1;;\nesac\n")
        sysctl.chmod(0o700)
        # Advance guard sleeps through pipe handshakes inside this fixture.
        clock = root / "test clock"
        clock.mkdir()
        (clock / "sitecustomize.py").write_text(
            "import sys, time\n"
            "def sleep(seconds):\n"
            "    print('sleep ' + str(seconds), flush=True)\n"
            "    if not sys.stdin.buffer.read(1):\n"
            "        raise SystemExit('selftest clock closed')\n"
            "time.sleep = sleep\n")
        guard_env = {"LEAN_EXCLUSIVE_SYSCTL": str(sysctl), "PYTHONPATH": str(clock)}
        guarded = start("guarded", seats[0], overrides=guard_env)
        check(line(guarded.stderr) ==
              b"lean-exclusive: waiting for free vnodes (free=39999 floor=40000)\n",
              "missing vnode guard message")
        check(not (root / "guarded.json").exists(), "low vnode count admitted a command")
        for advance in range(2):
            check(line(guarded.stdout) == b"sleep 5\n",
                  "vnode guard did not request a five-second recheck")
            if advance == 0:
                guarded.stdin.write(b"g")
                guarded.stdin.flush()
        replacement = root / "new vnode count"
        replacement.write_text("40000")
        replacement.replace(counter)
        output = finish(guarded, release=True)
        check(output[0] == b"ready\n" and output[1] == b"", f"guard release: {output}")
        print("PASS vnode guard waits once below floor and resumes at floor (5 s cadence)")

        for missing in ("kern.free_vnodes", "kern.maxvnodes"):
            sysctl.write_text('#!/bin/sh\nif [ "$2" = "' + missing +
                              '" ]; then exit 1; fi\necho 0\n')
            result = run(seats[0], sys.executable, "-c", "pass", overrides={
                "LEAN_EXCLUSIVE_SYSCTL": str(sysctl)})
            check(result.returncode == 0 and not result.stderr,
                  f"missing counter {missing} did not skip guard: {result}")
        result = run(seats[0], sys.executable, "-c", "pass")
        check(result.returncode == 0 and not result.stderr,
              f"missing sysctl did not skip guard: {result}")
        print("PASS missing counters or sysctl skip the vnode guard")
    finally:
        for process in processes:
            if process.poll() is None and process.stdin and not process.stdin.closed:
                process.stdin.close()
                process.stdin = None
        for process in processes:
            if process.poll() is None:
                process.communicate(timeout=timeout)

    check(lock.is_file() and lock.stat().st_ino == identity and
          second_lock.is_file() and second_lock.stat().st_ino == second_identity,
          "slot files were unlinked or replaced")
    print("PASS slot files survive with the same inodes")

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
# Preserve CMD's stdin while the launcher reads its program from the heredoc.
exec 9<&0
exec python3 - "$lean_common_dir" "$BASH" "$@" <<'PY'
import fcntl
import os
import re
import signal
import subprocess
import sys
import time


def integer(name, default, minimum):
    value = os.environ.get(name, str(default))
    try:
        if re.fullmatch(r"[0-9]+", value):
            parsed = int(value)
            if parsed >= minimum:
                return parsed
    except ValueError:
        pass
    print(f"lean-exclusive: {name} must be an integer >= {minimum}", file=sys.stderr)
    raise SystemExit(2)


slots = integer("LEAN_EXCLUSIVE_SLOTS", 4, 1)
floor = integer("LEAN_EXCLUSIVE_MIN_FREE_VNODES", 40000, 0)
counter_command = os.environ.get("LEAN_EXCLUSIVE_SYSCTL", "sysctl")
vnode_wait_reported = False


def free_vnodes():
    values = []
    for counter in ("kern.free_vnodes", "kern.maxvnodes"):
        try:
            result = subprocess.run([counter_command, "-n", counter],
                                    stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                                    stderr=subprocess.DEVNULL, text=True)
            value = result.stdout.strip()
            if result.returncode or not re.fullmatch(r"[0-9]+", value):
                return None
            values.append(int(value))
        except (OSError, ValueError):
            return None
    return values[0]


def wait_for_vnodes():
    global vnode_wait_reported
    while True:
        free = free_vnodes()
        if free is None or free >= floor:
            return
        if not vnode_wait_reported:
            print(f"lean-exclusive: waiting for free vnodes (free={free} floor={floor})",
                  file=sys.stderr, flush=True)
            vnode_wait_reported = True
        time.sleep(5)


try:
    signal.signal(signal.SIGINT, signal.default_int_handler)
    os.dup2(9, 0)
    os.close(9)
    slot_wait_reported = False
    while True:
        wait_for_vnodes()
        for index in range(slots):
            path = os.path.join(sys.argv[1], f"stratalint-lean-direct-{index}.lock")
            descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o666)
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                os.close(descriptor)
                continue
            break
        else:
            if not slot_wait_reported:
                print("lean-exclusive: waiting for a free Lean command slot",
                      file=sys.stderr, flush=True)
                slot_wait_reported = True
            time.sleep(0.2)
            continue
        break
    wait_for_vnodes()
    # Keep the locked descriptor through both execs; never unlink slot files.
    os.set_inheritable(descriptor, True)
    os.execv(sys.argv[2], [sys.argv[2], "-c", 'exec "$@"', "lean-exclusive", *sys.argv[3:]])
except KeyboardInterrupt:
    raise SystemExit(130)
PY
