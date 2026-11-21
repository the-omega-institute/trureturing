#!/usr/bin/env bash
set -euo pipefail

# Print live readings so a runner shutdown retains the last available sample.
python3 -u - <<'PY' &
from pathlib import Path
import json
import os
import shutil
import time

cgroup = Path("/sys/fs/cgroup")
while True:
    disk = shutil.disk_usage(".")
    reading = {"unix_seconds": int(time.time()), "disk_available_bytes": disk.free,
               "disk_total_bytes": disk.total, "cpus": len(os.sched_getaffinity(0))}
    for line in Path("/proc/meminfo").read_text().splitlines():
        field, value = line.split(":", 1)
        if field in {"MemTotal", "MemAvailable"}:
            reading[field + "_KiB"] = int(value.split()[0])
    for field in ("memory.current", "memory.max", "memory.events"):
        path = cgroup / field
        if path.is_file():
            reading[field] = path.read_text().strip()
    print("LEAN_RUNNER_RESOURCES " + json.dumps(reading), flush=True)
    time.sleep(60)
PY
sampler=$!
trap 'kill "$sampler" 2>/dev/null || true; wait "$sampler" 2>/dev/null || true' EXIT
"$@"
