#!/usr/bin/env python3
"""Bounded subprocesses and fail-closed census for the temporary experiment."""
from __future__ import annotations

import argparse
import datetime as dt
import json
import math
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import time

MAX_SECONDS = 1800
MAX_OUTPUT_BYTES = 16 * 1024 * 1024
CENSUS_SECONDS = 2
SAMPLE_SECONDS = 1
LEAN_NAMES = {"lean", "reportInspector"}


class CensusError(ValueError):
    def __init__(self, result):
        super().__init__("census process failed: " + str(result["error"] or result["exit"]))
        self.timed_out = result["timed_out"]


def stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def execute(command, cwd, env, *, timeout, stdout=None, census=False,
            output_limit=None, deadline=None):
    """One deadline includes boundaries, child tree, pipe EOF and cleanup.

    Only the new session/process group created by this call is signalled. A
    small part of the ceiling is reserved for cleanup, never added to it.
    No reader thread or unbounded communicate/wait survives this call.
    """
    started = time.monotonic()
    limit = MAX_OUTPUT_BYTES if output_limit is None else output_limit
    end = min(started + timeout, deadline) if deadline is not None else started + timeout
    reserve = min(0.25, max(0, end - started) * 0.2)
    work_end = end - reserve
    rows, data = [], bytearray()
    error = None
    timed_out = truncated = False
    total = 0
    process = None
    stream = None
    code = None
    selector = selectors.DefaultSelector()
    handle = Path(stdout).open("wb") if stdout is not None else None

    def sample(owner, boundary):
        nonlocal timed_out
        row = observation(owner, deadline=end if boundary == "after" else work_end)
        timed_out = timed_out or row.get("timed_out", False)
        row["phase"] = boundary
        rows.append(row)
        return row

    def kill_owned_group():
        if process is not None:
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

    try:
        if census and not sample(None, "before")["valid"]:
            error = "invalid before census"
        if time.monotonic() >= work_end:
            timed_out = True
            error = error or "deadline exhausted before launch"
        if error is None:
            process = subprocess.Popen(command, cwd=cwd, env=env, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            stream = process.stdout
            os.set_blocking(stream.fileno(), False)
            selector.register(stream, selectors.EVENT_READ)
            next_sample = time.monotonic()
            eof = False
            while True:
                now = time.monotonic()
                if now >= work_end:
                    timed_out = True
                    error = "process/drain deadline"
                    break
                if census and now >= next_sample:
                    observed = sample(process.pid, "scheduled")
                    next_sample += SAMPLE_SECONDS
                    if not observed["valid"]:
                        error = "invalid scheduled census"
                        break
                    if time.monotonic() > next_sample:
                        error = "scheduled census missed"
                        break
                code = process.poll()
                if code is not None and eof:
                    break
                remaining = work_end - time.monotonic()
                if census:
                    remaining = min(remaining, next_sample - time.monotonic())
                for key, _ in selector.select(max(0, min(0.05, remaining))):
                    chunk = os.read(key.fd, 65536)
                    if not chunk:
                        selector.unregister(stream)
                        eof = True
                        continue
                    kept = chunk[:max(0, limit - total)]
                    if handle is not None:
                        handle.write(kept)
                    else:
                        data.extend(kept)
                    total += len(chunk)
                    if total > limit:
                        truncated = True
                        error = "output limit exceeded"
                        break
                if error:
                    break
    except (OSError, ValueError) as exc:
        error = repr(exc)
    finally:
        # Also kill remaining group members when the immediate child exited.
        # A descendant holding stdout cannot extend the deadline.
        kill_owned_group()
        if process is not None:
            try:
                code = process.wait(timeout=max(0, end - time.monotonic()) / 2)
            except subprocess.TimeoutExpired:
                error = error or "cleanup incomplete at deadline"
                timed_out = True
        if stream is not None:
            stream.close()
        selector.close()
        if handle is not None:
            handle.close()
        if census:
            if not sample(None, "after")["valid"]:
                error = error or "invalid after census"
    elapsed = time.monotonic() - started
    within = time.monotonic() <= end and elapsed <= timeout
    if not within:
        timed_out = True
        error = error or "absolute deadline exceeded"
    counts = [r["external_lean_count"] for r in rows if r["valid"]]
    controlled = (len(rows) >= 3 and all(r["valid"] for r in rows)
                  and len(counts) == len(rows) and max(counts, default=1) == 0) if census else True
    result = {
        "argv": command, "cwd": str(cwd), "exit": code, "error": error,
        "process_error": error, "wall_seconds": elapsed, "max_seconds": timeout,
        "within_deadline": within, "timed_out": timed_out, "output_bytes": total,
        "output_limit_bytes": limit, "output_truncated": truncated,
        "controlled": controlled, "load_samples": len(rows),
        "external_lean_min": min(counts) if counts else None,
        "external_lean_max": max(counts) if counts else None,
        "boundary_before": rows[0] if rows else None,
        "boundary_after": rows[-1] if rows else None,
    }
    result["accepted"] = process_ok(result) and controlled
    return result, bytes(data), rows


def process_ok(result, expected_exit=0):
    """Never let exit zero erase a timeout, missing evidence or overflow."""
    return (result.get("exit") == expected_exit and result.get("error") is None
            and result.get("process_error") is None and result.get("timed_out") is False
            and result.get("output_truncated") is False and result.get("within_deadline") is True
            and 0 <= result.get("wall_seconds", -1) <= result.get("max_seconds", -1)
            and 0 <= result.get("output_bytes", -1) <= result.get("output_limit_bytes", -1))


def ps_rows(deadline=None):
    result, data, _ = execute(["ps", "-eo", "pid=,ppid=,pcpu=,comm="], Path.cwd(),
                              os.environ.copy(), timeout=CENSUS_SECONDS,
                              deadline=deadline, output_limit=1024 * 1024)
    if not process_ok(result):
        raise CensusError(result)
    rows = []
    seen = set()
    for line in data.decode("utf-8", errors="strict").splitlines():
        fields = line.strip().split(None, 3)
        if len(fields) != 4:
            raise ValueError("malformed census row")
        pid, ppid, cpu = int(fields[0]), int(fields[1]), float(fields[2])
        if pid <= 0 or ppid < 0 or pid in seen or not math.isfinite(cpu) or cpu < 0:
            raise ValueError("invalid census values")
        seen.add(pid)
        rows.append((pid, ppid, cpu, Path(fields[3]).name))
    if not rows:
        raise ValueError("empty census")
    return rows


def descendants(root, rows):
    owned = {root}
    changed = True
    while changed:
        changed = False
        for pid, ppid, _cpu, _name in rows:
            if ppid in owned and pid not in owned:
                owned.add(pid)
                changed = True
    return owned


def observation(owner, deadline=None):
    try:
        rows = ps_rows(deadline=deadline)
        if not rows:
            raise ValueError("empty census")
        owned = descendants(owner, rows) if owner is not None else set()
        relevant = [(pid, cpu, name) for pid, _ppid, cpu, name in rows if name in LEAN_NAMES]
        external = [{"pid": pid, "name": name, "cpu_percent": cpu}
                    for pid, cpu, name in relevant if pid not in owned]
        return {"utc": stamp(), "valid": True, "external_lean_count": len(external),
                "external_processes": external,
                "own_lean_count": sum(pid in owned for pid, _, _ in relevant),
                "load_average": list(os.getloadavg())}
    except (OSError, ValueError, UnicodeError) as exc:
        return {"utc": stamp(), "valid": False, "error": str(exc),
                "timed_out": getattr(exc, "timed_out", False),
                "external_lean_count": None, "external_processes": None, "own_lean_count": None}


def timed_argv(path, command):
    return ["/usr/bin/time", "-l" if sys.platform == "darwin" else "-v", "-o", str(path), *command]


def measure(command, cwd, env, output, sample, deadline=None):
    output.mkdir(parents=True, exist_ok=True)
    stdout_path = output / f"{sample}.stdout.log"
    time_path = output / f"{sample}.time.txt"
    result, _, samples = execute(timed_argv(time_path, command), cwd, env, timeout=MAX_SECONDS,
                                 stdout=stdout_path, census=True, deadline=deadline)
    result.update(sample=sample, argv=command, stdout=str(stdout_path), time=str(time_path))
    (output / f"{sample}.load.json").write_text(json.dumps(samples) + "\n")
    (output / f"{sample}.result.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--sample", required=True)
    parser.add_argument("--cwd", required=True, type=Path)
    parser.add_argument("--aux", action="store_true")
    parser.add_argument("--seconds", type=float)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if len(args.command) < 2 or args.command[0] != "--":
        parser.error("command must follow --")
    if args.aux:
        if args.seconds is None or not math.isfinite(args.seconds) or not 0 < args.seconds <= MAX_SECONDS:
            parser.error("auxiliary --seconds must be finite, positive and at most 1800")
        args.output.mkdir(parents=True, exist_ok=True)
        job_start = float(os.environ.get("M3_JOB_STARTED_MONOTONIC", time.monotonic()))
        path = args.output / f"{args.sample}.stdout.log"
        result, _, _ = execute(args.command[1:], args.cwd, os.environ.copy(), timeout=args.seconds,
                               stdout=path, deadline=job_start + 32 * 60)
        (args.output / f"{args.sample}.result.json").write_text(json.dumps(result, indent=2) + "\n")
    else:
        if args.seconds is not None:
            parser.error("the fixed original M3 cap is not configurable")
        result = measure(args.command[1:], args.cwd, os.environ.copy(), args.output, args.sample)
    print(json.dumps(result))
    return 0 if result["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
