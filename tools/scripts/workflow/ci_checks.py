"""Execute the declared CI units and current subchecks for hosted and local callers."""
import argparse
from dataclasses import dataclass
import glob
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile

import ci_compute
from ci_contract import (DetectError, base_commit, candidate_identity, changed_paths,
                         load, read_changed, selection, write_paths)

CLI = "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"
SCRIBE = "tools/StrataLint.Scribe/bin/Release/net10.0/StrataLint.Scribe.dll"
REPORT = ".lake/build/stratalint/raw-lean-report.json"


def result(check, status, raw=None, exit_code=None):
    print("CI_CHECK " + json.dumps({"check": check, "status": status, "raw_exit": raw,
                                    "exit": exit_code}, separators=(",", ":")), flush=True)


def execute(check, command, *, compute=True, delta=False, env=None):
    print("CI_COMMAND " + json.dumps({"check": check, "argv": command}), flush=True)
    previous = os.environ.copy()
    try:
        if env:
            os.environ.update(env)
        try:
            raw = ci_compute.run(command) if compute else subprocess.call(command)
        except (OSError, ValueError) as error:
            print("CI_CHECK_ERROR " + str(error), file=sys.stderr)
            raw = 2
    finally:
        os.environ.clear()
        os.environ.update(previous)
    raw = 128 - raw if raw < 0 else raw
    status = ("protected-only" if delta and raw == 3 else "success" if raw == 0 else
              "timeout" if raw in (124, 137) else "cancelled" if raw in (130, 143) else "failure")
    code = 0 if delta and raw == 3 else raw
    result(check, status, raw, code)
    return code


def prepare_unit(unit):
    if not unit["dotnet"]:
        return 0
    project = unit["project"]
    projects = {Path(project)} if project else {
        csproj for pattern in unit["cache-dependency-path"].splitlines() if pattern.strip()
        for lock in glob.glob(pattern.strip(), recursive=True)
        for csproj in Path(lock).parent.glob("*.csproj")}
    # Command units can also run canonical tests; their declared lock set owns
    # the evidence tool and complementary project filters.
    if project:
        projects.add(Path("tools/StrataLint.TestEvidence/StrataLint.TestEvidence.csproj"))
    if not projects:
        raise DetectError("no projects selected for dependency restoration")
    for target in sorted(projects):
        code = execute("restore:" + str(target), ["dotnet", "restore", str(target), "--locked-mode"], compute=False)
        if code:
            return code
    return 0


def prepare_judge(data):
    if os.environ.get("JUDGE_HIT") != "true":
        code = execute("restore:judge", ["dotnet", "restore", data["current"]["judge_build_args"][0], "--locked-mode"], compute=False)
        if code:
            return code
    return 0


def prepare_current(data, plan):
    judge = prepare_judge(data)
    return judge or (prepare_unit(data["units"]["tests-declared-template"]) if plan["source-evidence"] else 0)


def prepare_local_lean():
    # A persistent local host supplies its installed toolchain. Select the pin
    # explicitly without changing elan's global default as hosted setup does.
    pin = Path("lean-toolchain").read_text().strip()
    if not pin:
        raise DetectError("empty Lean toolchain pin")
    os.environ["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + os.environ["PATH"]
    return execute("prepare:lean-toolchain", ["elan", "run", pin, "lake", "--version"], compute=False)


def unit_run(name, unit, *, current=None):
    if unit["command"] == "acknowledge-current":
        # The canonical report consumer already ran the selected FIB suite.
        # This unit only acknowledges an identified successful current job.
        code = 0 if current == ("success", "current") else 1
        result(name, "success" if code == 0 else "blocked", code, code)
        return code
    command = (["make", "-C", "tools", "test", "TEST_PROJECT=" + unit["project"]]
               if unit["project"] else ["bash", "-e", "-o", "pipefail", "-c", unit["command"]])
    return execute(name, command)


def current_phase(phase, data, plan, base, paths):
    report = os.environ.get("LEAN_REPORT", REPORT)
    if phase == "source":
        if not plan["hits"]["current"]:
            result(phase, "not-applicable")
            return 0
        if plan["theory"]:
            return current_phase("check-delta", data, plan, base, paths)
        if plan["delta"] and not base:
            raise DetectError("selected source delta requires a readable protected base")
        return execute(phase, ["dotnet", CLI, "check-source", "--current",
                              *(["--protected-base", base] if plan["delta"] else [])])
    if phase == "prerequisite":
        prefix = current_prerequisite(data, plan, base, paths)
        if os.environ.get("GITHUB_OUTPUT"):
            with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
                stream.write(f"source_status={prefix.status}\ncontinuation={str(prefix.allowed).lower()}\n"
                             f"judge_ready={str(prefix.judge_ready).lower()}\n")
        return prefix.code
    if phase == "prepare":
        return prepare_current(data, plan)
    if phase == "build-judge":
        return execute(phase, ["dotnet", "build", *data["current"]["judge_build_args"], "--no-restore"])
    if phase == "lean-report":
        if not plan["report"]:
            result(phase, "not-applicable")
            return 0
        producer = subprocess.run(["bash", "tools/scripts/workflow/judge-lean-producer.sh",
                                   str(Path(CLI).parent.resolve())], stdout=subprocess.PIPE, text=True)
        if producer.returncode:
            code = 128 - producer.returncode if producer.returncode < 0 else producer.returncode
            result(phase, "failure", code, code)
            return code
        env = {"STRATALINT_LEAN_PRODUCER_DLL": producer.stdout.strip(), "STRATALINT_BUILD_TIMEOUT_SECONDS": "21600",
               "STRATALINT_FIB_REGRESSIONS_SELECTED": str(plan["fib-regressions"]).lower()}
        return execute(phase, ["make", "lean-report", "LEAN_REPORT_CACHE_MISS_POLICY=fetch-or-fail"], compute=False, env=env)
    if phase == "compiled-audit":
        if not plan[phase]:
            result(phase, "not-applicable")
            return 0
        return execute(phase, ["make", "compiled-judge-test"])
    if phase == "source-evidence":
        if not plan[phase]:
            result(phase, "not-applicable")
            return 0
        return execute(phase, ["make", "-C", "tools", "test",
                              "TEST_PROJECT=tools/tests/StrataLint.DeclaredTemplate.Tests/StrataLint.DeclaredTemplate.Tests.csproj",
                              "TEST_FILTER=FullyQualifiedName~FourierBridgeSourceEvidenceTests"],
                       env={"CI_DOTNET_PREPARED": "1", "FOURIER_BRIDGE_SOURCE_ARTIFACTS": str(Path(".lake/build/lean-inspector/modules").resolve())})
    if phase == "check-delta":
        if not plan["delta"]:
            result(phase, "not-applicable")
            return 0
        if not base:
            raise DetectError("selected delta requires a readable protected base")
        return execute(phase, ["dotnet", CLI, "check-delta", "--protected-base", base,
                              *(["--candidate-lean-report", report] if plan["report"] else [])], delta=True)
    if phase in ("check-current", "scribe"):
        if not plan["report"]:
            result(phase, "not-applicable")
            return 0
        with tempfile.TemporaryDirectory(prefix="ci-scribe-") as directory:
            scope = Path(directory) / "paths"
            with scope.open("wb") as stream:
                scoped = subprocess.run(["bash", "tools/scripts/workflow/scribe-scope-paths.sh", str(paths)], stdout=stream)
            if scoped.returncode:
                code = 128 - scoped.returncode if scoped.returncode < 0 else scoped.returncode
                result(phase, "failure", code, code)
                return code
            command = (["dotnet", CLI, "check-current", "--candidate-lean-report", report, "--scribe-paths-from", str(scope)]
                       if phase == "check-current" else ["bash", "tools/scripts/workflow/scribe-content-checks.sh", report, SCRIBE, str(scope)])
            return execute(phase, command)
    raise DetectError(f"unknown current phase: {phase}")


# These validators consume the report/program outputs, not one another's verdicts.
# The fixed ready order follows the measured 9s source-evidence, 15s Scribe,
# 85s current and 426s compiled-audit phases. Delta has no comparable duration
# in the supplied sample; keep its existing relation to current/Scribe.
READY_PHASES = ("source-evidence", "scribe", "check-current", "check-delta", "compiled-audit")


@dataclass(frozen=True)
class Prerequisite:
    code: int
    status: str
    judge_ready: bool

    @property
    def allowed(self):
        return self.status in ("accepted", "judge-failed", "infrastructure", "not-applicable")


def current_prerequisite(data, plan, base, paths):
    if not plan["hits"]["current"]:
        result("source", "not-applicable")
        return Prerequisite(0, "not-applicable", False)
    prepared = prepare_judge(data)
    judge = prepared or (0 if os.environ.get("JUDGE_HIT") == "true" else
                         current_phase("build-judge", data, plan, base, paths))
    if judge:
        result("source", "blocked")
        if plan["theory"]:
            result("check-delta", "blocked")
        status = "timeout" if judge in (124, 137) else "cancelled" if judge in (130, 143) else "judge-failed"
        return Prerequisite(judge, status, False)
    code = current_phase("source", data, plan, base, paths)
    status = ("accepted" if code == 0 else "rejected" if code == 1 else
              "timeout" if code in (124, 137) else "cancelled" if code in (130, 143) else "infrastructure")
    return Prerequisite(code, status, True)


def applicable_phase(plan, phase):
    return (plan[phase] if phase in ("compiled-audit", "source-evidence") else
            plan["delta"] if phase == "check-delta" else plan["report"])


def current_run(data, plan, base, paths, prefix=None):
    prefix = prefix or current_prerequisite(data, plan, base, paths)
    if not prefix.allowed:
        for phase in ("lean-report", *READY_PHASES):
            if phase == "check-delta" and plan["theory"]:
                continue  # The theory delta is the source phase itself.
            result(phase, "blocked" if applicable_phase(plan, phase) else "not-applicable")
        return prefix.code
    failures = [prefix.code]
    if not plan["report"]:
        return prefix.code
    lean = prepare_local_lean()
    restore = prepare_current(data, plan)
    judge = 0 if prefix.judge_ready else prefix.code
    # Judge bootstrap and selected test restore failures do not erase independently
    # reachable report fallback. Lean preparation alone guards report inputs.
    report = lean or current_phase("lean-report", data, plan, base, paths)
    if lean:
        result("lean-report", "blocked")
    failures += [lean, restore, report]
    for phase in READY_PHASES:
        if not applicable_phase(plan, phase):
            result(phase, "not-applicable")
        elif judge or report or phase == "source-evidence" and restore:
            result(phase, "blocked")
        else:
            failures.append(current_phase(phase, data, plan, base, paths))
            if failures[-1] in (124, 130, 137, 143):
                return failures[-1]
    return next((code for code in failures if code), 0)


def with_budget(path, action):
    previous = os.environ.get(ci_compute.BUDGET)
    ci_compute.initialize(path, 120)
    os.environ[ci_compute.BUDGET] = str(path)
    try:
        return action()
    finally:
        if previous is None:
            os.environ.pop(ci_compute.BUDGET, None)
        else:
            os.environ[ci_compute.BUDGET] = previous


def local(args, data, revision):
    base = base_commit(Path.cwd(), args.base)
    paths = changed_paths(Path.cwd(), base)
    plan = selection(data, paths, args.purpose)
    print("CI_LOCAL " + json.dumps(dict(plan, base=base, candidate=candidate_identity(Path.cwd()),
                                       contract_revision=revision, purpose=args.purpose)), flush=True)
    if args.plan:
        return 0
    failures = []
    current_code = None
    with tempfile.TemporaryDirectory(prefix="ci-local-") as directory:
        work = Path(directory)
        changed = work / "changed"
        write_paths(changed, paths)
        blocked = False
        if plan["hits"]["current"]:
            def run_current():
                nonlocal blocked
                prefix = current_prerequisite(data, plan, base, changed)
                blocked = not prefix.allowed
                return current_run(data, plan, base, changed, prefix)
            code = current_code = with_budget(work / "current-budget", run_current)
            result("current", "success" if code == 0 else "failure", code, code)
            failures.append(code)
        for name, unit in data["units"].items():
            if not plan["hits"][name]:
                result(name, "not-applicable")
                continue
            if blocked or failures and failures[-1] in (130, 143):
                result(name, "blocked")
                continue
            if unit["command"] == "acknowledge-current":
                failures.append(unit_run(name, unit, current=(
                    "success" if current_code == 0 else "failure",
                    "current" if current_code == 0 else "")))
                continue
            prepared = prepare_local_lean() if unit["lean"] != "none" else 0
            prepared = prepared or prepare_unit(unit)
            if prepared:
                result(name, "blocked")
                failures.append(prepared)
            else:
                env = os.environ.get("CI_DOTNET_PREPARED")
                os.environ["CI_DOTNET_PREPARED"] = "1" if unit["dotnet"] else "0"
                try:
                    failures.append(with_budget(work / (name + "-budget"), lambda: unit_run(name, unit)))
                finally:
                    if env is None:
                        os.environ.pop("CI_DOTNET_PREPARED", None)
                    else:
                        os.environ["CI_DOTNET_PREPARED"] = env
    code = next((code for code in failures if code), 0)
    result("local-gate", "success" if code == 0 else "failure", code, code)
    return code


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="operation", required=True)
    gate = sub.add_parser("local")
    gate.add_argument("--base", required=True)
    gate.add_argument("--purpose", choices=("pull-request", "push"), default="pull-request")
    gate.add_argument("--plan", action="store_true")
    sub.add_parser("judge-recipe")
    describe = sub.add_parser("describe")
    describe.add_argument("unit")
    unit = sub.add_parser("unit")
    unit.add_argument("unit")
    unit.add_argument("--prepare", action="store_true")
    unit.add_argument("--current-result", default="")
    unit.add_argument("--current-unit", default="")
    local_unit = sub.add_parser("local-unit")
    local_unit.add_argument("unit")
    current = sub.add_parser("current")
    current.add_argument("phase")
    current.add_argument("--changed", type=Path, default=Path(os.environ.get("CI_CHANGED_PATHS_FILE", str(Path(os.environ.get("RUNNER_TEMP", "/nonexistent")) / "changed-paths"))))
    current.add_argument("--base", default="")
    current.add_argument("--purpose", choices=("pull-request", "push"), default="pull-request" if os.environ.get("GITHUB_EVENT_NAME") == "pull_request" else "push")
    args = parser.parse_args()
    try:
        data, revision = load(Path.cwd())
        if args.operation == "judge-recipe":
            print(shlex.join(data["current"]["judge_build_args"]))
            return 0
        if args.operation == "local":
            return local(args, data, revision)
        if args.operation in ("unit", "describe", "local-unit"):
            if args.unit not in data["units"]:
                raise DetectError(f"unknown unit: {args.unit}")
            unit = data["units"][args.unit]
            if args.operation == "describe":
                # JSON safely carries multiline lock declarations through Actions.
                text = json.dumps(unit, separators=(",", ":"))
                with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
                    stream.write("definition=" + text + "\n")
                return 0
            if args.operation == "local-unit":
                if unit["command"] == "acknowledge-current":
                    return unit_run(args.unit, unit)
                prepared = prepare_local_lean() if unit["lean"] != "none" else 0
                prepared = prepared or prepare_unit(unit)
                if prepared:
                    result(args.unit, "blocked")
                    return prepared
                with tempfile.TemporaryDirectory(prefix="ci-unit-") as directory:
                    os.environ["CI_DOTNET_PREPARED"] = "1" if unit["dotnet"] else "0"
                    return with_budget(Path(directory) / "budget", lambda: unit_run(args.unit, unit))
            if args.prepare:
                return prepare_unit(unit)
            code = unit_run(args.unit, unit, current=(args.current_result, args.current_unit))
            if code == 0 and os.environ.get("GITHUB_OUTPUT"):
                with open(os.environ["GITHUB_OUTPUT"], "a") as stream:
                    stream.write("unit=" + args.unit + "\n")
            return code
        paths = read_changed(args.changed)
        plan = selection(data, paths, args.purpose)
        base = args.base
        if not base and plan["delta"]:
            base = base_commit(Path.cwd(), "HEAD^1") if args.purpose == "pull-request" else os.environ.get("CI_PUSH_BEFORE", "")
        return current_phase(args.phase, data, plan, base, args.changed)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print("CI_CHECK_ERROR " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
