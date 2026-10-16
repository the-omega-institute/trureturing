"""Charge CI computation to its allowance, carrying current across its source boundary."""
import argparse
import fcntl
import math
import os
from pathlib import Path
import subprocess
import sys
import time

BUDGET = "STRATALINT_CI_COMPUTE_BUDGET"
ACTIVE = "STRATALINT_CI_COMPUTE_ACTIVE"


def current_remainder(value):
    seconds = float(value)
    if not math.isfinite(seconds) or not 0 <= seconds <= 7200:
        raise ValueError("current remainder must be finite and in [0, 7200]")
    return seconds


def resume_current(path, value):
    # Only the existing current allowance crosses the native job boundary.
    # Missing/invalid output cannot grant a fresh 120 minutes; an existing file
    # cannot be reset. Preparation/transport between jobs is not computation.
    seconds = current_remainder(value)
    with path.open("x") as stream:
        stream.write(str(seconds))


def export_current(path):
    with path.open() as stream:
        fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        return str(current_remainder(stream.read()))


def initialize(path, minutes):
    seconds = float(minutes) * 60
    if not math.isfinite(seconds) or not 0 < seconds <= 21600:
        raise ValueError("compute minutes must be in (0, 360]")
    # Never reset an allowance in an existing job.
    with path.open("x") as stream:
        stream.write(str(seconds))


def run(command):
    path = os.environ.get(BUDGET)
    if not path:
        raise ValueError("compute allowance is not initialized")
    if os.environ.get(ACTIVE) == "1":
        return subprocess.call(command)
    with Path(path).open("r+") as stream:
        # CI phases are serial. Refuse overlapping owners instead of granting
        # each a fresh allowance. Nested test commands share their outer timer.
        fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        remaining = float(stream.read())
        if not math.isfinite(remaining) or remaining < 0 or remaining > 21600:
            raise ValueError("invalid remaining compute allowance")
        if remaining == 0:
            print("CI_COMPUTE_BUDGET_EXHAUSTED", file=sys.stderr)
            return 124

        def save(value):
            stream.seek(0)
            stream.truncate()
            stream.write(str(value))
            stream.flush()

        # An interrupted owner cannot leave a reusable uncharged allowance.
        save(0)
        started = time.monotonic()
        result = subprocess.call(
            ["timeout", "--kill-after=5s", str(remaining) + "s", *command],
            env=dict(os.environ, **{ACTIVE: "1"}))
        elapsed = time.monotonic() - started
        left = 0 if result in (124, 137) else max(0, remaining - elapsed)
        save(left)
        if result == 0 and left == 0:
            result = 124
        print(f"CI_COMPUTE elapsed_seconds={elapsed:.3f} remaining_seconds={left:.3f} exit={result}",
              file=sys.stderr)
        return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("init", "run", "resume-current", "export-current"))
    parser.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    try:
        if args.operation == "init":
            path, minutes = args.arguments
            initialize(Path(path), minutes)
            return 0
        if args.operation == "resume-current":
            path, remaining = args.arguments
            resume_current(Path(path), remaining)
            return 0
        if args.operation == "export-current":
            path, = args.arguments
            print("compute_remaining=" + export_current(Path(path)))
            return 0
        command = args.arguments
        if command[:1] == ["--"]:
            command = command[1:]
        if not command:
            raise ValueError("compute command is required")
        return run(command)
    except (OSError, ValueError) as error:
        print("CI_COMPUTE_ERROR " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
