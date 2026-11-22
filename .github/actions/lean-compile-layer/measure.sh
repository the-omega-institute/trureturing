#!/usr/bin/env bash
set -euo pipefail

# Scope report observations to this invocation's preparation streams.
report_tmp=
if [[ ${1:-} == --report ]]; then
  shift
  report_tmp="$(mktemp -d "${RUNNER_TEMP:?}/lean-report-progress.XXXXXXXX")"
  export TMPDIR="$report_tmp"
fi

# Print live readings so a runner shutdown retains the last available sample.
python3 -u - "$report_tmp" <<'PY' &
from pathlib import Path
import json
import os
import re
import shutil
import subprocess
import sys
import time

def read(path):
    try:
        return path.read_text().strip()
    except OSError:
        return ""


def largest_processes():
    try:
        output = subprocess.check_output(["ps", "-eo", "rss=,comm=", "--sort=-rss"],
                                         stderr=subprocess.DEVNULL, text=True, errors="replace", timeout=3)
        processes = []
        for line in output.splitlines()[:5]:
            rss, name = line.split(None, 1)
            processes.append({"comm": name, "rss_KiB": int(rss)})
        return processes
    except (OSError, ValueError, subprocess.SubprocessError):
        return None


lake_progress = re.compile(
    rb"\[([0-9]{1,9}/[0-9]{1,9})\] (?:\(Optional\) )?(Built|Building) ([A-Za-z0-9_][A-Za-z0-9_.:/-]{0,255})(?=\s|$)")
inspector_phase = re.compile(
    rb"^LEAN_INSPECTOR_(?:PHASE|INTERRUPTED|FAILED) phase=([a-z][a-z0-9-]{0,63})(?: status=(started|completed))?(?=\s|$)")


def report_progress(root):
    progress = {}
    # prepare() writes both streams in one TemporaryDirectory. The files can
    # disappear between samples when inspection finishes normally.
    for directory in root.glob("lean-programs.*"):
        progress["preparation"] = "returned" if (directory / "programs.exit.log").is_file() else "entered"
        for stream in ("stdout", "stderr"):
            path = directory / f"programs.{stream}.log"
            try:
                with path.open("rb") as log:
                    log.seek(max(0, os.fstat(log.fileno()).st_size - 16384))
                    tail = log.read(16384)
            except OSError:
                continue
            for line in reversed(tail.splitlines()):
                lake = lake_progress.search(line)
                if lake and stream not in progress:
                    progress[stream] = b" ".join(lake.groups()).decode("ascii")
                if stream == "stderr" and "inspector_phase" not in progress:
                    phase = inspector_phase.match(line)
                    if phase:
                        progress["inspector_phase"] = b" ".join(phase.groups(default=b"")).decode("ascii").strip()
    return progress


report_tmp = Path(sys.argv[1]) if sys.argv[1] else None
cgroup = Path("/sys/fs/cgroup")
while True:
    disk = shutil.disk_usage(".")
    cpus = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count()
    reading = {"unix_seconds": int(time.time()), "disk_available_bytes": disk.free,
               "disk_total_bytes": disk.total, "cpus": cpus}
    if report_tmp:
        reading["report_progress"] = report_progress(report_tmp)
    for line in read(Path("/proc/meminfo")).splitlines():
        field, _, value = line.partition(":")
        if field in {"MemTotal", "MemAvailable"} and value.split() and value.split()[0].isdigit():
            reading[field + "_KiB"] = int(value.split()[0])
    for field in ("memory.current", "memory.max", "memory.events"):
        value = read(cgroup / field)
        if value:
            reading[field] = value
    for line in read(Path("/proc/vmstat")).splitlines():
        fields = line.split()
        if len(fields) == 2 and fields[0] == "oom_kill" and fields[1].isdigit():
            reading["oom_kill"] = int(fields[1])
            break
    pressure = read(Path("/proc/pressure/memory"))
    if pressure:
        reading["memory_pressure"] = pressure
    available = reading.get("MemAvailable_KiB")
    headroom = 4 * 1024**3
    tight = disk.free <= headroom or (available is not None and available * 1024 <= headroom)
    limit, current = reading.get("memory.max", ""), reading.get("memory.current", "")
    if limit.isdigit() and current.isdigit() and int(limit) - int(current) <= headroom:
        tight = True
    if tight:
        processes = largest_processes()
        if processes is not None:
            reading["largest_processes"] = processes
    reading["next_sample_seconds"] = 10 if tight else 60
    print("LEAN_RUNNER_RESOURCES " + json.dumps(reading), flush=True)
    time.sleep(reading["next_sample_seconds"])
PY
sampler=$!
finish() {
  kill "$sampler" 2>/dev/null || true
  wait "$sampler" 2>/dev/null || true
  if [[ -n "$report_tmp" ]]; then rm -rf -- "$report_tmp"; fi
}
trap finish EXIT
"$@"
