"""Bound census subprocesses and preserve measurements even on rejection."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import signal
import subprocess
import sys
import time


class ResourceRejected(RuntimeError):
    pass


def check_budget(free_percent, rss_bytes, budget_bytes):
    if free_percent < 30:
        raise ResourceRejected(f"free memory {free_percent}% is below 30% before heavy step")
    if rss_bytes > 2 * budget_bytes:
        raise ResourceRejected(f"rss={rss_bytes} exceeds budget={budget_bytes}")


def free_memory():
    if sys.platform == "darwin":
        reading = subprocess.check_output(["memory_pressure"], text=True)
        match = re.search(r"System-wide memory free percentage: (\d+)%", reading)
        if not match:
            raise ResourceRejected("memory_pressure reading unavailable")
        return int(match[1])
    values = dict(line.split(":", 1) for line in pathlib.Path("/proc/meminfo").read_text().splitlines())
    return 100 * int(values["MemAvailable"].split()[0]) // int(values["MemTotal"].split()[0])


def process_tree(pid):
    table = subprocess.check_output(["ps", "-axo", "pid=,ppid=,rss="], text=True)
    processes = [tuple(map(int, line.split())) for line in table.splitlines() if line.strip()]
    descendants = {pid}
    while True:
        expanded = descendants | {child for child, parent, _ in processes if parent in descendants}
        if expanded == descendants:
            break
        descendants = expanded
    return {child: rss * 1024 for child, _, rss in processes if child in descendants}


def kill_tree(pid, known):
    # Receipt replay starts nested sessions, so killing only the outer group leaks workers.
    descendants = set(process_tree(pid)) | known | {pid}
    groups = set()
    for child in descendants:
        try:
            groups.add(os.getpgid(child))
        except ProcessLookupError:
            pass
    for group in groups - {os.getpgrp()}:
        try:
            os.killpg(group, signal.SIGKILL)
        except ProcessLookupError:
            pass
    for child in descendants:
        try:
            os.kill(child, signal.SIGKILL)
        except ProcessLookupError:
            pass


def run(command, directory, label, *, cwd=None, env=None, budget_gb=4, phase_path=None,
        design_limit_gb=None, wall_limit_s=1200):
    """Measure per-process RSS. Build scheduling is exempt from the census budget.

    The acceptance reading is 4 GiB; only a design failure (twice the planned
    phase size) aborts. Heavy census steps run sequentially with 30% free memory.
    """
    directory = pathlib.Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    measurement = {"label": label, "command": command, "rss_budget_gib": budget_gb,
                   "peak_rss_bytes": 0, "memory_readings": [], "status": "rejected", "phases": {}}
    current_phase = "publication_startup" if phase_path else label
    last_sample = started
    proc = None
    known = set()
    child_env = dict(os.environ if env is None else env)
    design_limit = (design_limit_gb or 2 * budget_gb) * 1024 ** 3 if budget_gb else None
    timing_path = directory / f"{label}.time.log"
    try:
        free = free_memory()
        measurement["memory_readings"].append({"seconds": 0, "free_percent": free})
        check_budget(free, 0, (budget_gb or 4) * 1024 ** 3)
        flag = "-l" if sys.platform == "darwin" else "-v"
        with (directory / f"{label}.log").open("w") as output:
            proc = subprocess.Popen(["/usr/bin/time", flag, "-o", str(timing_path), *command],
                                    cwd=cwd, env=child_env, stdout=output, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            next_memory_check = started
            while True:
                processes = process_tree(proc.pid)
                known = set(processes)
                rss = max(processes.values(), default=0)
                measurement["peak_rss_bytes"] = max(measurement["peak_rss_bytes"], rss)
                now = time.monotonic()
                phase = measurement["phases"].setdefault(current_phase,
                    {"wall_seconds": 0, "peak_rss_bytes": 0})
                phase["wall_seconds"] += now - last_sample
                phase["peak_rss_bytes"] = max(phase["peak_rss_bytes"], rss)
                last_sample = now
                if phase_path and pathlib.Path(phase_path).exists():
                    current_phase = pathlib.Path(phase_path).read_text() or current_phase
                if now >= next_memory_check:
                    free = free_memory()
                    measurement["memory_readings"].append(
                        {"seconds": round(now - started, 3), "free_percent": free})
                    next_memory_check = now + 5
                if design_limit and rss > design_limit:
                    raise ResourceRejected(f"phase design bound exceeded: {rss} > {design_limit}")
                if budget_gb and now - started > wall_limit_s:
                    raise ResourceRejected(f"phase wall design bound exceeded: {now - started:.1f}s")
                try:
                    result = proc.wait(timeout=0.2)
                    break
                except subprocess.TimeoutExpired:
                    continue
        measurement["exit_code"] = result
        timing = timing_path.read_text()
        pattern = (r"(\d+)\s+maximum resident set size" if sys.platform == "darwin"
                   else r"Maximum resident set size \(kbytes\):\s*(\d+)")
        match = re.search(pattern, timing)
        if match:
            peak = int(match[1]) * (1 if sys.platform == "darwin" else 1024)
            measurement["peak_rss_bytes"] = max(measurement["peak_rss_bytes"], peak)
        measurement["within_acceptance_rss"] = (not budget_gb or
            measurement["peak_rss_bytes"] <= budget_gb * 1024 ** 3)
        if result:
            raise RuntimeError(f"{label}: command exited {result}; see {directory / (label + '.log')}")
        measurement["status"] = "completed"
        return measurement
    except BaseException as error:
        measurement["error"] = str(error)
        if proc is not None and proc.poll() is None:
            kill_tree(proc.pid, known)
            proc.wait()
        raise
    finally:
        phase = measurement["phases"].setdefault(current_phase,
            {"wall_seconds": 0, "peak_rss_bytes": 0})
        phase["wall_seconds"] += time.monotonic() - last_sample
        for phase in measurement["phases"].values():
            phase["wall_seconds"] = round(phase["wall_seconds"], 3)
        measurement["wall_seconds"] = round(time.monotonic() - started, 3)
        (directory / f"{label}.resources.json").write_text(json.dumps(measurement, indent=2) + "\n")
        print(json.dumps({"step": label, "status": measurement["status"],
                          "seconds": measurement["wall_seconds"],
                          "peak_rss_gib": round(measurement["peak_rss_bytes"] / 1024 ** 3, 3)}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--budget-gib", type=float, default=4)
    parser.add_argument("--design-limit-gib", type=float)
    parser.add_argument("--wall-limit-s", type=float, default=1200)
    parser.add_argument("--phase-path", type=pathlib.Path)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    options = parser.parse_args()
    command = options.command[1:] if options.command[:1] == ["--"] else options.command
    run(command, options.directory, options.label, budget_gb=options.budget_gib,
        design_limit_gb=options.design_limit_gib, wall_limit_s=options.wall_limit_s,
        phase_path=options.phase_path)
