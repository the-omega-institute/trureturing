#!/usr/bin/env bash
set -euo pipefail

compile=0
if [[ ${1:-} == --compile ]]; then
  compile=1
  shift
fi

# Print live readings so a runner shutdown retains the last available sample.
python3 -u - "$compile" <<'PY' &
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys
import time

def read(path):
    try:
        return path.read_text().strip()
    except OSError:
        return ""


def lean_module(process, workspace):
    try:
        if (process / "exe").readlink().name != "lean":
            return None
        cwd = (process / "cwd").resolve(strict=True)
        argv = (process / "cmdline").read_bytes().split(b"\0")[1:]
        sources = set()
        for argument in argv:
            if argument.startswith(b"-") or not argument.endswith(b".lean"):
                continue
            source = (cwd / os.fsdecode(argument)).resolve(strict=True)
            if not source.is_file() or not source.is_relative_to(workspace):
                continue
            path = source.relative_to(workspace).with_suffix("")
            if path.parts[:2] in {("tools", "lean-inspector"), ("tools", "lean-inspector-reg"),
                                  ("tools", "lean-inspector-interface")}:
                path = Path(*path.parts[2:])
            elif path.parts[0] not in {"D5", "Reg", "Trureturing"}:
                continue
            if path.name != "lakefile" and all(part.isidentifier() for part in path.parts):
                sources.add(".".join(path.parts))
        return sources.pop() if len(sources) == 1 else None
    except (OSError, RuntimeError, ValueError):
        return None


def largest_processes():
    try:
        output = subprocess.check_output(["ps", "-eo", "pid=,rss=,comm=", "--sort=-rss"],
                                         stderr=subprocess.DEVNULL, text=True, errors="replace", timeout=3)
        processes = []
        for line in output.splitlines()[:5]:
            pid, rss, name = line.split(None, 2)
            process = {"pid": int(pid), "comm": name, "rss_KiB": int(rss)}
            if name == "lean" and (module := lean_module(Path("/proc") / pid, Path.cwd().resolve())):
                process["module"] = module
            processes.append(process)
        return processes
    except (OSError, ValueError, subprocess.SubprocessError):
        return None


compiling = sys.argv[1] == "1"
cgroup = Path("/sys/fs/cgroup")
while True:
    disk = shutil.disk_usage(".")
    cpus = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count()
    reading = {"unix_seconds": int(time.time()), "disk_available_bytes": disk.free,
               "disk_total_bytes": disk.total, "cpus": cpus}
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
    if compiling or tight:
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
}
trap finish EXIT
"$@"
