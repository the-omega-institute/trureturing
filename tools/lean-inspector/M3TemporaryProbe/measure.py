#!/usr/bin/env python3
"""One bounded, directly forced M3 process with per-second interference checks."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time

MAX_SECONDS = 1800
MAX_OUTPUT_BYTES = 16 * 1024 * 1024
LEAN_NAMES = {"lean", "reportInspector"}


def stamp() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def ps_rows() -> list[tuple[int, int, float, str]]:
    try:
        text = subprocess.check_output(
            ["ps", "-eo", "pid=,ppid=,pcpu=,comm="], text=True, stderr=subprocess.STDOUT
        )
    except (OSError, subprocess.CalledProcessError):
        return []
    rows: list[tuple[int, int, float, str]] = []
    for line in text.splitlines():
        fields = line.strip().split(None, 3)
        if len(fields) != 4:
            continue
        try:
            rows.append((int(fields[0]), int(fields[1]), float(fields[2]), Path(fields[3]).name))
        except ValueError:
            continue
    return rows


def descendants(root: int, rows: list[tuple[int, int, float, str]]) -> set[int]:
    owned = {root}
    changed = True
    while changed:
        changed = False
        for pid, ppid, _cpu, _name in rows:
            if ppid in owned and pid not in owned:
                owned.add(pid)
                changed = True
    return owned


def observation(owner: int | None) -> dict:
    rows = ps_rows()
    owned = descendants(owner, rows) if owner is not None else set()
    relevant = [(pid, cpu, name) for pid, _ppid, cpu, name in rows if name in LEAN_NAMES]
    external = [
        {"pid": pid, "name": name, "cpu_percent": cpu}
        for pid, cpu, name in relevant
        if owner is None or pid not in owned
    ]
    inside = [row for row in relevant if owner is not None and row[0] in owned]
    return {
        "utc": stamp(),
        "external_lean_count": len(external),
        "external_processes": external,
        "own_lean_count": len(inside),
        "load_average": list(os.getloadavg()),
    }


def time_file(path: Path) -> list[str]:
    if not path.exists():
        return []
    return path.read_text(errors="replace").splitlines()


def timed_argv(path: Path, command: list[str]) -> list[str]:
    flag = "-l" if sys.platform == "darwin" else "-v"
    return ["/usr/bin/time", flag, "-o", str(path), *command]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--sample", required=True)
    parser.add_argument("--cwd", required=True, type=Path)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not args.command or args.command[0] != "--":
        parser.error("command must follow --")
    command = args.command[1:]
    args.output.mkdir(parents=True, exist_ok=True)
    stdout_path = args.output / f"{args.sample}.stdout.log"
    load_path = args.output / f"{args.sample}.load.json"
    result_path = args.output / f"{args.sample}.result.json"
    time_path = args.output / f"{args.sample}.time.txt"
    env = os.environ.copy()
    env["STRATALINT_LEAN_CACHE_RELEASE_TIMEOUT_SECONDS"] = "5"
    env["GIT_OPTIONAL_LOCKS"] = "0"
    timed_command = timed_argv(time_path, command)
    before = observation(None)
    samples = [before]
    started = time.monotonic()
    timed_out = False
    output_bytes = 0
    output_truncated = False
    exit_code: int | None = None
    process_error: str | None = None
    try:
        process = subprocess.Popen(
            timed_command,
            cwd=args.cwd,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    except OSError as error:
        process = None
        process_error = repr(error)

    def drain(stream, handle) -> None:
        nonlocal output_bytes, output_truncated
        assert stream is not None
        for chunk in iter(lambda: stream.read(65536), b""):
            remaining = MAX_OUTPUT_BYTES - output_bytes
            if remaining > 0:
                handle.write(chunk[:remaining])
                handle.flush()
            output_bytes += len(chunk)
            if output_bytes > MAX_OUTPUT_BYTES:
                output_truncated = True

    if process is not None:
        with stdout_path.open("wb") as handle:
            thread = threading.Thread(target=drain, args=(process.stdout, handle), daemon=True)
            thread.start()
            samples.append(observation(process.pid))
            while True:
                try:
                    exit_code = process.wait(timeout=1)
                    break
                except subprocess.TimeoutExpired:
                    samples.append(observation(process.pid))
                    if time.monotonic() - started > MAX_SECONDS:
                        timed_out = True
                        os.killpg(process.pid, signal.SIGTERM)
                        try:
                            exit_code = process.wait(timeout=10)
                        except subprocess.TimeoutExpired:
                            os.killpg(process.pid, signal.SIGKILL)
                            exit_code = process.wait()
                        break
            thread.join()
    after = observation(None)
    samples.append(after)
    external_counts = [row["external_lean_count"] for row in samples]
    controlled = bool(external_counts) and max(external_counts) == 0
    result = {
        "sample": args.sample,
        "utc_start": samples[0]["utc"],
        "utc_end": after["utc"],
        "argv": command,
        "cwd": str(args.cwd),
        "exit": exit_code,
        "process_error": process_error,
        "wall_seconds": time.monotonic() - started,
        "max_seconds": MAX_SECONDS,
        "timed_out": timed_out,
        "output_bytes": output_bytes,
        "output_limit_bytes": MAX_OUTPUT_BYTES,
        "output_truncated": output_truncated,
        "load_samples": len(samples),
        "external_lean_min": min(external_counts) if external_counts else None,
        "external_lean_max": max(external_counts) if external_counts else None,
        "controlled": controlled,
        "accepted": exit_code == 0 and controlled and not timed_out and not output_truncated,
        "time_output": time_file(time_path),
        "boundary_before": before,
        "boundary_after": after,
    }
    load_path.write_text(json.dumps(samples, separators=(",", ":")) + "\n")
    result_path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, separators=(",", ":")))
    return 0 if result["accepted"] else 1


if __name__ == "__main__":
    sys.exit(main())
