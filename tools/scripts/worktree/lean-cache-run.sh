#!/usr/bin/env bash
# CLAUDE.md 10.1: capacity-derived, jobs = min(q_cpu, q_mem).
# The function's optional positional inputs are for deterministic unit tests;
# the executable always reads static host limits, never an environment override.
lean_jobs_derive() {
  python3 - "$@" <<'PY'
import os
from pathlib import Path
import re
import subprocess
import sys

# Workload owner: repository Lean builds. Named static reserve for the OS,
# runner agent, Lake coordinator and cache-writer .NET process: 2 GiB, excluded
# from elaboration capacity on every host. This is R_mem, not a job-count cap.
LEAN_JOBS_RESERVE_BYTES = 2 * 1024**3
# Benchmark receipt lean-elaboration-rss-v1, 2026-09-14, Lean 4.33.0, #7685.
# Host: macOS 26.6.2, Mac15,14 / Apple M3 Ultra, 103079215104 bytes RAM.
# Source: /Users/auricstudio/.ie0904/reifier-probe-cost/final-result.json
# LEAN_NUM_THREADS=1 /usr/bin/time -l lake env lean -Dprofiler=true
#   -Dtrace.profiler=true -Dtrace.profiler.threshold=1000 <module>.lean
# (receipt also uses a Perl alarm; ReifierShadow needs --root=tools/lean-inspector).
# RSS bytes: ReifierTriggerAdmit 6075465728, ReifierTriggerReject 5992071168,
# PointwiseEqualityRegistrations 6079299584, ReifierShadow 6106791936.
# Use the maximum, rounded UP to the next decimal 0.01 GB: 6.11 GB.
# This fixed workload receipt is used on all hosts; Linux charged memory and
# peaks of other modules are unmeasured. It is not a universal RSS guarantee.
LEAN_JOBS_PER_PROCESS_BYTES = 6110000000


def natural(value, name, positive=False):
    if not re.fullmatch(r"[0-9]+", value):
        raise ValueError(f"{name} is not an unsigned decimal integer")
    result = int(value)
    if positive and result == 0:
        raise ValueError(f"{name} must be positive")
    return result


def cgroup_limits(proc):
    # Locate our cgroup v2 mount, including delegated/container mount roots.
    # Ancestor quotas apply even when the leaf itself says max. An absent v2
    # hierarchy means no v2 upper bound; malformed/unreadable inputs fail closed.
    memberships = [line.split(":", 2)[2] for line in
                   (proc / "self/cgroup").read_text().splitlines()
                   if line.startswith("0::")]
    if not memberships:
        return [], []
    member = Path(memberships[0])
    for line in (proc / "self/mountinfo").read_text().splitlines():
        before, after = line.split(" - ", 1)
        if after.split()[0] != "cgroup2":
            continue
        fields = before.split()
        unescape = lambda s: re.sub(r"\\([0-7]{3})", lambda m: chr(int(m[1], 8)), s)
        mount_root, mount = Path(unescape(fields[3])), Path(unescape(fields[4]))
        try:
            relative = member.relative_to(mount_root)
        except ValueError:
            continue
        if ".." in relative.parts:
            raise ValueError("cgroup membership escapes its visible mount")
        current = mount / relative
        if not current.is_dir():
            raise ValueError("cgroup membership directory is missing")
        cpu, memory = [], []
        while True:
            for name, values in [("cpu.max", cpu), ("memory.max", memory)]:
                path = current / name
                if path.exists():
                    values.append(path.read_text().strip())
            if current == mount:
                return cpu, memory
            current = current.parent
    raise ValueError("cgroup v2 membership has no visible matching mount")


def host_inputs():
    if sys.platform == "darwin":
        cores = subprocess.check_output(["sysctl", "-n", "hw.logicalcpu"], text=True).strip()
        memory = subprocess.check_output(["sysctl", "-n", "hw.memsize"], text=True).strip()
        return cores, memory, [], []
    if sys.platform == "linux":
        # GNU nproc respects affinity/cpuset; OpenMP preferences are not capacity.
        env = {k: v for k, v in os.environ.items()
               if k not in ("OMP_NUM_THREADS", "OMP_THREAD_LIMIT")}
        cores = subprocess.check_output(["nproc"], env=env, text=True).strip()
        proc = Path("/proc")
        match = re.search(r"^MemTotal:\s+([0-9]+) kB$", (proc / "meminfo").read_text(), re.M)
        if match is None:
            raise ValueError("MemTotal is missing or malformed")
        # Linux meminfo kB is KiB; this is a unit conversion, not a capacity cap.
        memory = str(int(match[1]) * 1024)
        cpu_limits, memory_limits = cgroup_limits(proc)
        return cores, memory, cpu_limits, memory_limits
    raise ValueError(f"unsupported host platform {sys.platform}")


def derive(cores_text, memory_text, cpu_limits, memory_limits):
    # Legal domain: positive host cores/bytes and cpu.max period/quota; optional
    # limits are unsigned bytes or max. CPU quota/period is floored to whole
    # cores (r_cpu = one core/job, R_cpu = zero). Memory uses exact integer floor,
    # including negative capacity. No saturation to one is permitted.
    cores = natural(cores_text, "cores", positive=True)
    memory = natural(memory_text, "mem_total_bytes", positive=True)
    q_cpu = cores
    for limit in cpu_limits:
        quota, period = limit.split()
        period = natural(period, "cpu.max period", positive=True)
        if quota != "max":
            q_cpu = min(q_cpu, natural(quota, "cpu.max quota", positive=True) // period)
    for limit in memory_limits:
        if limit != "max":
            memory = min(memory, natural(limit, "memory.max"))
    q_mem = (memory - LEAN_JOBS_RESERVE_BYTES) // LEAN_JOBS_PER_PROCESS_BYTES
    jobs = min(q_cpu, q_mem)
    fields = (f"cores={cores} mem_total_bytes={memory} "
              f"reserve_bytes={LEAN_JOBS_RESERVE_BYTES} "
              f"per_process_bytes={LEAN_JOBS_PER_PROCESS_BYTES} "
              f"q_cpu={q_cpu} q_mem={q_mem} jobs={jobs}")
    if jobs < 1:
        print(f"LEAN_JOBS_CAPACITY_INSUFFICIENT {fields}", file=sys.stderr)
        return 1
    print(f"LEAN_JOBS_DERIVATION {fields}")
    return 0


try:
    if len(sys.argv) == 1:
        inputs = host_inputs()
    elif len(sys.argv) == 5:
        # Tests inject host cores/bytes and newline-separated cgroup limits.
        inputs = (*sys.argv[1:3], sys.argv[3].splitlines(), sys.argv[4].splitlines())
    else:
        raise ValueError("expected no arguments or cores, bytes, cpu.max, memory.max")
    sys.exit(derive(*inputs))
except (OSError, ValueError, subprocess.SubprocessError) as error:
    print(f"LEAN_JOBS_CAPACITY_INVALID {error}", file=sys.stderr)
    sys.exit(1)
PY
}

lean_cache_run() {
  local root receipt command="${1:-}"
  root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)" || return
  if [[ "${command##*/}" == lake && "${2:-}" == build ]]; then
    receipt="$(lean_jobs_derive)" || return
    printf '%s\n' "$receipt" >&2
    # Lake 5.0.0 / Lean 4.33.0 has no build -j option. Its runtime task pool
    # reads LEAN_NUM_THREADS (lean4 d8b1897 src/runtime/object.cpp,
    # get_lean_num_threads); Lake build jobs block in IO.Process.output.
    # Always replace an inherited bare value with the capacity-derived result.
    export LEAN_NUM_THREADS="${receipt##*jobs=}"
  fi
  cd "$root" || return
  exec dotnet run \
    --project "$root/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
    --configuration Release \
    -- \
    worktree with-cache-writer -- "$@"
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  set -u
  lean_cache_run "$@"
fi
