#!/usr/bin/env python3
"""Temporary native cold-report experiment; observations never decide admission."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import subprocess
import sys
import threading
import time

SEALED_INPUTS_SHA256 = "4b4ca902ecee48cf97e9426e3e92301bfc3d084f08734387aa79794a0494c338"


def write_json(path, value):
    path.write_text(json.dumps(value, sort_keys=True, indent=2) + "\n")


def sha(path):
    with path.open("rb") as stream:
        digest = hashlib.file_digest(stream, "sha256") if hasattr(hashlib, "file_digest") else None
        if digest is None:
            digest = hashlib.sha256()
            for block in iter(lambda: stream.read(1024 * 1024), b""):
                digest.update(block)
        return digest.hexdigest()


def stamp():
    return {"monotonic_ns": time.monotonic_ns(), "realtime_ns": time.time_ns()}


def append(path, value):
    # Each compiler owns a separate file; the stage and sampler share no writer.
    with path.open("a") as stream:
        stream.write(json.dumps(value, sort_keys=True) + "\n")


def compiler(args):
    output = Path(os.environ["COLD_COST_OUTPUT"])
    real = os.environ["COLD_COST_REAL_LEAN"]
    sources = [Path(arg).resolve() for arg in args if arg.endswith(".lean") and Path(arg).is_file()]
    if not sources or "--run" in args:
        os.environ["COLD_COST_INTERNAL"] = "1"
        os.execv(real, [real] + args)
    token = f"{os.getpid()}-{time.monotonic_ns()}"
    folder = output / "compilers" / token
    folder.mkdir(parents=True)
    events = folder / "events.jsonl"
    setup = None
    for i, arg in enumerate(args):
        if arg == "--setup" and i + 1 < len(args):
            setup = Path(args[i + 1])
        elif arg.startswith("--setup="):
            setup = Path(arg.split("=", 1)[1])
    if setup and setup.is_file():
        shutil.copyfile(setup, folder / "setup.json")
    actual = [real, "--profile"] + args
    start = {"kind": "compiler-start", **stamp(), "wrapper_pid": os.getpid(),
             "wrapper_role": "compiler-observer-wrapper", "compiler_role": "real-compiler",
             "terminal_accounting": "pending; absent compiler-end means censored status and resources",
             "cwd": os.getcwd(), "original_argv": args, "actual_argv": actual,
             "sources": [{"path": str(p), "sha256": sha(p)} for p in sources],
             "profiling": "Lean --profile, default 100ms individual threshold; exclusive component times"}
    child = subprocess.Popen(actual, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             env=dict(os.environ, COLD_COST_INTERNAL="1"))
    start["spawn_return_monotonic_ns"] = time.monotonic_ns()
    received = []

    def forward(sig, _frame):
        received.append(sig)
        try:
            # wait4 is the sole status owner; Popen.send_signal polls/reaps.
            if child.returncode is None:
                os.kill(child.pid, sig)
        except ProcessLookupError:
            pass

    for sig in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(sig, forward)
    start["compiler_pid"] = child.pid
    if sys.platform == "linux":
        try:
            start["compiler_start_ticks"] = proc_row(Path("/proc") / str(child.pid))["start_ticks"]
        except (OSError, ValueError, IndexError):
            start["compiler_start_ticks"] = None
    append(events, start)
    errors = []

    def relay(pipe, destination, name):
        try:
            with (folder / name).open("wb") as log:
                while True:
                    block = os.read(pipe.fileno(), 65536)
                    if not block:
                        break
                    log.write(block)
                    log.flush()
                    try:
                        destination.write(block)
                        destination.flush()
                    except BrokenPipeError:
                        # Retain evidence even if Lake's output reader was killed.
                        destination = None
                    if destination is None:
                        destination = open(os.devnull, "wb")
        except Exception as error:
            errors.append(repr(error))
        finally:
            pipe.close()

    relays = [threading.Thread(target=relay, args=(child.stdout, sys.stdout.buffer, "stdout.log")),
              threading.Thread(target=relay, args=(child.stderr, sys.stderr.buffer, "stderr.log"))]
    for relay_thread in relays:
        relay_thread.start()
    _, status, usage = os.wait4(child.pid, 0)
    child.returncode = os.waitstatus_to_exitcode(status)
    append(events, {"kind": "compiler-end", **stamp(), "compiler_pid": child.pid,
                    "terminal_accounting": "collected",
                    "wait_status": status, "returncode": child.returncode,
                    "received_signals": received, "rusage_scope": "kernel wait4 child accounting; includes threads and may include waited descendants",
                    "user_cpu_seconds": usage.ru_utime, "system_cpu_seconds": usage.ru_stime,
                    "maxrss": usage.ru_maxrss, "maxrss_unit": "KiB" if sys.platform == "linux" else "bytes",
                    "minor_faults": usage.ru_minflt, "major_faults": usage.ru_majflt,
                    "voluntary_context_switches": usage.ru_nvcsw,
                    "involuntary_context_switches": usage.ru_nivcsw})
    for relay_thread in relays:
        relay_thread.join()
    if errors:
        write_json(folder / "observer-errors.json", errors)
    if child.returncode < 0:
        sig = -child.returncode
        if sig not in (signal.SIGKILL, signal.SIGSTOP):
            signal.signal(sig, signal.SIG_DFL)
        os.kill(os.getpid(), sig)
    return child.returncode


def build_spawn_observer(output):
    library = output / "cold-cost-spawn.so"
    subprocess.run(["cc", "-shared", "-fPIC", "-Wall", "-Wextra", "-Werror", "-O2",
                    str(Path(__file__).with_name("cold_cost_spawn.c")), "-o", str(library), "-ldl"], check=True)
    return library


def proc_row(path):
    text = (path / "stat").read_text()
    # comm may contain spaces and parentheses; fields after its closing ')'.
    fields = text[text.rfind(")") + 2:].split()
    row = {"pid": int(path.name), "state": fields[0], "ppid": int(fields[1]),
           "user_ticks": int(fields[11]), "system_ticks": int(fields[12]),
           "start_ticks": int(fields[19]), "rss_pages": int(fields[21])}
    row["argv"] = (path / "cmdline").read_bytes().decode(errors="replace").split("\0")[:-1]
    for name in ("status", "io", "schedstat"):
        try:
            row[name] = (path / name).read_text()
        except OSError:
            row[name] = None
    return row


def sample(root_pid, proc=Path("/proc"), cgroup_root=Path("/sys/fs/cgroup"), real_lean=None):
    started_ns = time.monotonic_ns()
    rows = {}
    for path in proc.iterdir():
        if path.name.isdigit():
            try:
                rows[int(path.name)] = proc_row(path)
            except (OSError, ValueError, IndexError):
                pass  # /proc processes can disappear between individual reads.
    members = {root_pid}
    while True:
        more = {pid for pid, row in rows.items() if row["ppid"] in members}
        if more <= members:
            break
        members |= more
    wrapper_argv = [str(Path(__file__).resolve()), "compiler"]
    sampler_pid = os.getpid()
    wrappers = {pid for pid, row in rows.items() if row["argv"][1:3] == wrapper_argv}
    processes = []
    for pid in sorted(members):
        if pid not in rows:
            continue
        row = rows[pid]
        if pid == sampler_pid:
            role = "python-stage-sampler"
        elif pid in wrappers:
            role = "compiler-observer-wrapper"
        elif real_lean and row["argv"][:1] == [real_lean] and row["ppid"] in wrappers:
            role = "real-compiler"
        elif pid == root_pid:
            role = "command-root"
        else:
            role = "unclassified-command-descendant"
        processes.append({**row, "role": role})
    kernel = {}
    for name in ("stat", "meminfo", "vmstat", "loadavg", "pressure/cpu", "pressure/memory", "pressure/io"):
        try:
            kernel[name] = (proc / name).read_text()
        except OSError:
            kernel[name] = None
    try:
        entry = next(line[3:] for line in (proc / str(root_pid) / "cgroup").read_text().splitlines()
                     if line.startswith("0::"))
        cgroup = cgroup_root / entry.lstrip("/")
        cg = {"path": str(cgroup)}
        for name in ("cpu.stat", "cpu.max", "cpu.pressure", "memory.current", "memory.peak",
                     "memory.max", "memory.events", "memory.swap.current", "memory.swap.max",
                     "memory.pressure", "io.pressure", "io.stat", "pids.current", "pids.max"):
            try:
                cg[name] = (cgroup / name).read_text()
            except OSError:
                cg[name] = None
    except (OSError, StopIteration):
        cg = None
    return {"kind": "sample", **stamp(),
            "scope": "sampled command root and descendants; includes compiler observer wrappers and canonical shell sampler activity",
            "python_sampler": {"pid": sampler_pid, "role": "python-stage-sampler",
                               "in_processes": sampler_pid in members and sampler_pid in rows},
            "role_basis": "current argv and parent; other descendants, including unidentified shell samplers, remain unclassified",
            "collection_start_monotonic_ns": started_ns, "collection_elapsed_ns": time.monotonic_ns() - started_ns,
            "clock_ticks_per_second": os.sysconf("SC_CLK_TCK"), "page_bytes": os.sysconf("SC_PAGE_SIZE"),
            "processes": processes,
            "kernel_scope": "host cumulative counters/pressure, including observer activity", "kernel": kernel,
            "cgroup_scope": "command cgroup (may include Python observer and other job processes)", "cgroup": cg}


def observe_command(command, cwd, output, name, env, interval=2.0, canonical_resources=False):
    events = output / "stages.jsonl"
    begin = stamp()
    with (output / f"{name}.stdout.log").open("wb") as stdout, (output / f"{name}.stderr.log").open("wb") as stderr:
        actual = command
        if canonical_resources:
            actual = ["bash", "-c", 'source tools/scripts/lib/resource-observation-lib.sh; resource_observe_run_periodic "$@"',
                      "cold-cost"] + command
        child = subprocess.Popen(actual, cwd=cwd, env=env, stdout=stdout, stderr=stderr)
        append(events, {"kind": "stage-start", "name": name, "command": command,
                        "actual_command": actual, "pid": child.pid, **begin})
        while child.poll() is None:
            try:
                append(output / "samples.jsonl", {"stage": name, **sample(child.pid, real_lean=env.get("COLD_COST_REAL_LEAN"))})
            except Exception as error:
                append(output / "observer-errors.jsonl", {"stage": name, **stamp(), "error": repr(error)})
            try:
                child.wait(timeout=interval)
            except subprocess.TimeoutExpired:
                pass
        append(events, {"kind": "stage-end", "name": name, **stamp(), "returncode": child.returncode})
    return child.returncode


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args])


def input_binding(root):
    paths = ["D5", "Reg", "Blueprint", "Golden/Frozen", "Trureturing.lean", "lean-toolchain", "lakefile.toml",
             "lake-manifest.json", "lean-report-inputs.json", "tools/lean-inspector",
             "tools/lean-inspector-interface", "tools/lean-inspector-reg", "tools/scripts/report/report-supervisor.sh",
             "tools/scripts/compiled-judge-test.sh", "tools/scripts/worktree/lean-cache-run.sh"]
    listing = git(root, "ls-tree", "-r", "-z", "HEAD", "--", *paths)
    files = [row.split("\t", 1)[1] for row in listing.decode().split("\0") if row]
    return {"paths": paths, "git_blob_listing_sha256": hashlib.sha256(listing).hexdigest(),
            "listing": listing.decode().split("\0")[:-1],
            "actual_file_sha256": {name: sha(root / name) for name in files}}


def native_binding(root, env):
    event = json.loads(Path(env["GITHUB_EVENT_PATH"]).read_text())
    head = git(root, "rev-parse", "HEAD").decode().strip()
    parents = git(root, "show", "-s", "--format=%P", "HEAD").decode().split()
    if (env.get("GITHUB_ACTIONS") != "true" or env.get("GITHUB_EVENT_NAME") != "pull_request"
            or event.get("action") != "labeled" or head != env.get("GITHUB_SHA")
            or event.get("label", {}).get("name") != "cold-cost-" + head
            or len(parents) != 2 or parents[1] != event["pull_request"]["head"]["sha"]):
        raise ValueError("requires genuine labeled PR merge candidate matching the reviewed merge SHA")
    if git(root, "status", "--porcelain", "--untracked-files=all"):
        raise ValueError("source checkout must be clean")
    inputs = input_binding(root)
    if inputs["git_blob_listing_sha256"] != SEALED_INPUTS_SHA256:
        raise ValueError("registered source/compiler/report inputs differ from the sealed candidate")
    os_release = Path("/etc/os-release").read_text()
    if platform.system() != "Linux" or platform.machine() != "aarch64" or 'VERSION_ID="24.04"' not in os_release or 'ID=ubuntu' not in os_release:
        raise ValueError("requires ubuntu-24.04-arm")
    if (root / ".lake").exists():
        raise ValueError("project must start cold: .lake must be absent, no project seed restore")
    if (root / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.34.1":
        raise ValueError("requires official Lean v4.34.1")
    for path in (root / "lake-manifest.json", root / "Reg/lake-manifest.json",
                 root / "tools/lean-inspector/lake-manifest.json", root / "tools/lean-inspector-interface/lake-manifest.json",
                 root / "tools/lean-inspector-reg/lake-manifest.json"):
        packages = json.loads(path.read_text())["packages"]
        mathlib = next(p for p in packages if p["name"] == "mathlib")
        if mathlib["rev"] != "d13f23b723b8a846827a245b89c10fc7d3f11612":
            raise ValueError(f"wrong mathlib pin: {path}")
    forbidden = [key for key in env if key.startswith("STRATALINT_") and key not in
                 {"STRATALINT_ACCEPT_COLD_BUILD", "STRATALINT_CACHE_WRITES"}]
    if forbidden or any(key in env for key in ("LEAN_SYSROOT", "LEAN", "LAKE_OVERRIDE_LEAN", "LEAN_REPORT", "LEAN_SKIP_LOCK", "LD_PRELOAD", "PREFLIGHT_DEADLINE_AT")):
        raise ValueError(f"unexpected control environment: {forbidden}")
    return {**stamp(), "head": head, "tree": git(root, "rev-parse", "HEAD^{tree}").decode().strip(),
            "protected_base": parents[0], "pr_head": parents[1], "event": event,
            "github": {k: env.get(k) for k in ("GITHUB_REPOSITORY", "GITHUB_EVENT_NAME", "GITHUB_SHA", "GITHUB_REF",
                       "GITHUB_RUN_ID", "GITHUB_RUN_ATTEMPT", "GITHUB_JOB", "GITHUB_WORKFLOW_REF", "GITHUB_WORKFLOW_SHA")},
            "runner": {"os_release": os_release, "machine": platform.machine(), "uname": list(platform.uname())},
            "inputs": inputs, "project_initial_state": "absent .lake", "report_guard_seconds": 7200}


def run(root, output):
    env = dict(os.environ)
    binding = native_binding(root, env)
    output.mkdir(parents=True, exist_ok=False)
    rc = None
    stage = "observer-setup"
    stages = []
    complete = False
    inputs_unchanged = None
    canonical_failure = None
    observer_failure = None

    def result():
        return {**stamp(), "canonical_returncode": rc if observer_failure is None else None,
                "canonical_chain_complete": complete, "canonical_stages": stages,
                "canonical_failure": canonical_failure, "observer_failure": observer_failure,
                "diagnostic_only": True, "native_acceptance_or_integration_units": False,
                "inputs_unchanged": inputs_unchanged}

    try:
        write_json(output / "source.json", binding)
        real = Path(subprocess.check_output(["elan", "which", "lean"], cwd=root).decode().strip()).resolve()
        version = subprocess.check_output([str(real), "--version"]).decode().strip()
        if "version 4.34.1" not in version:
            raise ValueError(f"wrong actual compiler: {version}")
        write_json(output / "compiler.json", {"real_binary": str(real), "sha256": sha(real), "version": version,
                   "githash": subprocess.check_output([str(real), "--githash"]).decode().strip(),
                   "observation_delta": ["LD_PRELOAD process-launch observer; compiler paths unchanged", "Lean --profile"],
                   "admission": "all canonical checks and budgets unchanged; observations are not control inputs"})
        library = build_spawn_observer(output)
        env.update(COLD_COST_OUTPUT=str(output), COLD_COST_REAL_LEAN=str(real), LD_PRELOAD=str(library),
                   COLD_COST_PROGRAM=str(Path(__file__).resolve()), COLD_COST_PYTHON=sys.executable,
                   STRATALINT_ACCEPT_COLD_BUILD="1", STRATALINT_CACHE_WRITES="false")
        env["STRATALINT_LEAN_REPORT_LOG_DIR"] = str(output / "report-phases")
        # Same producer/compiled-judge/full-report chain as the current native job.
        stage = "judge-build"
        rc = observe_command(["make", "-C", "tools", "dotnet", "DOTNET_PROJECT=tools/StrataLint.Cli/StrataLint.Cli.csproj"], root, output, stage, env, canonical_resources=True)
        stages.append({"stage": stage, "returncode": rc})
        if rc == 0:
            stage, rc = "judge-lean-producer", None
            try:
                producer = subprocess.check_output(["bash", "tools/scripts/workflow/judge-lean-producer.sh",
                            str(root / "tools/StrataLint.Cli/bin/Release/net10.0")], cwd=root, env=env).decode().strip()
            except subprocess.CalledProcessError as error:
                rc = error.returncode
                stages.append({"stage": stage, "returncode": rc})
                canonical_failure = {"stage": stage, "returncode": rc, "error": repr(error)}
                raise
            stages.append({"stage": stage, "returncode": 0})
            if producer:
                env["STRATALINT_LEAN_PRODUCER_DLL"] = producer
            stage, rc = "compiled-judge-test", None
            rc = observe_command(["make", "compiled-judge-test"], root, output, stage, env, canonical_resources=True)
            stages.append({"stage": stage, "returncode": rc})
        if rc == 0:
            stage, rc = "full-lean-report", None
            rc = observe_command(["make", "lean-report", "LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build"], root, output, stage, env, canonical_resources=True)
            stages.append({"stage": stage, "returncode": rc})
            complete = True
        if rc != 0:
            canonical_failure = {"stage": stage, "returncode": rc}
    except BaseException as error:
        if canonical_failure is None:
            rc = None
            observer_failure = {"stage": stage, "error": repr(error)}
        raise
    finally:
        try:
            stage = "artifact-collection"
            # Preserve genuine producer origins and receipts; copy bytes, never synthesize.
            report = ".lake/build/stratalint/raw-lean-report.json"
            for relative in tuple(report + suffix for suffix in ("", ".sha256", ".input.attestation", ".provenance.json", ".materials.zip", ".reuse.json")) + (
                             ".lake/build/lean-inspector/inputs.json", "build/lean-cache/build-work.json"):
                path = root / relative
                if path.is_file():
                    target = output / "canonical" / relative
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(path, target)
            inputs_unchanged = input_binding(root) == binding["inputs"]
            if not inputs_unchanged:
                raise ValueError("canonical invocation changed preserved source inputs")
            observer_logs = [p for p in [output / "observer-errors.jsonl", *output.glob("compilers/*/observer-errors.json")]
                             if p.is_file()]
            if observer_logs:
                raise ValueError("observer errors recorded: " + ", ".join(str(p.relative_to(output)) for p in observer_logs))
            write_json(output / "result.json", result())
            inventory = [{"path": str(p.relative_to(output)), "sha256": sha(p), "bytes": p.stat().st_size}
                         for p in sorted(output.rglob("*")) if p.is_file()]
            write_json(output / "inventory.json", inventory)
        except BaseException as error:
            observer_failure = {"stage": stage, "error": repr(error), "prior_observer_failure": observer_failure}
            write_json(output / "result.json", result())
            raise
    return rc if rc >= 0 else 128 - rc


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "compiler":
        return compiler(sys.argv[2:])
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    return run(args.repository.resolve(), args.output.resolve())


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (ValueError, KeyError) as error:
        print(f"COLD_COST_ERROR {error}", file=sys.stderr)
        sys.exit(2)
