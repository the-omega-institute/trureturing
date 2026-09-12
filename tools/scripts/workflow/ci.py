"""Fixed candidate resolution, stage transport bootstrap, and CI diagnostics."""
import argparse
import base64
import json
import os
import pathlib
import re
import subprocess
import sys
import tarfile

RUNNER = "tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll"
CLI = "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"


def run(root, *command):
    return subprocess.run(command, cwd=root, check=True, capture_output=True, text=True).stdout.strip()


def outputs(values):
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as stream:
            stream.write("".join(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n" for key, value in values.items()))
    print(json.dumps(values, sort_keys=True))


def oid(value):
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise ValueError("expected immutable 40-hex commit")
    return value


def checkout(root, commit):
    workflow_candidate = os.environ.get("CI_WORKFLOW_CANDIDATE_SHA", "")
    # The reusable push workflow supplies this immutable candidate input to
    # its stage jobs. The PR resolver runs in the caller workflow and has no
    # reusable input; an absent value therefore means that there is nothing
    # additional to compare, while a supplied value is always checked.
    if workflow_candidate and oid(workflow_candidate) != oid(commit):
        raise ValueError("checkout does not match the reusable workflow candidate input")
    if run(root, "git", "rev-parse", "HEAD") != oid(commit):
        raise ValueError("checkout does not match the fixed candidate")
    for remote in run(root, "git", "remote").splitlines():
        run(root, "git", "remote", "remove", remote)
    for ref in run(root, "git", "for-each-ref", "--format=%(refname)", "refs/remotes/").splitlines():
        run(root, "git", "update-ref", "-d", ref)
    outputs({"candidate_sha": commit})
    print("CI_WORKFLOW_IDENTITY " + json.dumps({name.lower(): os.environ.get("GITHUB_" + name, "")
          for name in ("WORKFLOW_REF", "WORKFLOW_SHA", "EVENT_NAME", "JOB", "RUN_ID", "RUN_ATTEMPT", "SHA")}, sort_keys=True))
    print("CI_CACHE_WRITES enabled=" + os.environ.get("STRATALINT_CACHE_WRITES", "false"))


def resolve(root, head):
    # One commit metadata read fixes M and B; later jobs never resolve merge refs.
    fields = run(root, "git", "show", "-s", "--format=%H %P", "HEAD").split()
    if len(fields) != 3 or fields[2] != oid(head):
        raise ValueError("merge candidate is absent or does not contain the triggering PR head")
    candidate, base, _ = map(oid, fields)
    checkout(root, candidate)
    import ci_plan
    outputs(ci_plan.plan_pr(root, candidate, base, head))


def extract(root, archive, stage):
    with tarfile.open(archive) as source:
        members = source.getmembers()
        for member in members:
            path = pathlib.PurePosixPath(member.name)
            if (path.is_absolute() or any(part in ("", ".", "..") for part in member.name.split("/"))
                    or not member.isfile()):
                raise ValueError("invalid stage archive member")
            if not (member.name.startswith("build/ci/") or member.name.startswith("tools/") and (
                    "/bin/Release/" in member.name or re.search(r"/obj/Release/[^/]+/ref/[^/]+\.dll$", member.name))
                    or member.name.startswith(".lake/build/stratalint/raw-lean-report.json")
                    or stage == "current" and member.name == "Meta/ci-checks.json"):
                raise ValueError("unexpected stage archive destination")
            if any((root / parent).is_symlink() for parent in (path, *path.parents)):
                raise ValueError("symlink stage archive destination")
        # This is the native producer's transport list, not another stage selector.
        # Native transport-verify still owns schema, identity, hash and mode verdicts.
        manifest = f"build/ci/{stage}-transport.json"
        names = [member.name for member in members]
        if len(names) != len(set(names)):
            raise ValueError("duplicate stage archive member")
        with source.extractfile(manifest) as stream:
            declared = [item["path"] for item in json.load(stream)["materials"]]
        if len(declared) != len(set(declared)) or set(names) != set(declared) | {manifest}:
            raise ValueError("stage archive differs from declared transport materials")
        source.extractall(root, members=members)


def transport(args):
    if args.command == "restore":
        extract(args.repository, args.archive, args.stage)
    command = ["dotnet", RUNNER, "transport-pack" if args.command == "pack" else "transport-verify",
               "--repository", str(args.repository), "--stage", args.stage, "--commit", oid(args.commit),
               "--run-id", args.run_id, "--run-attempt", args.run_attempt]
    if args.command == "pack":
        command.extend(["--archive", str(args.archive)])
    # The runner is the upstream candidate runtime. Validation precedes the
    # downstream stage; the non-adversarial runtime bootstrap does not rebuild.
    subprocess.run(command, cwd=args.repository, check=True)


def advisory(root, branch):
    result = subprocess.run(["dotnet", CLI, "worktree", "validate-branch", "--branch", branch], cwd=root, capture_output=True, text=True)
    expected = "canonical" if result.returncode == 0 else "BRANCH_GRAMMAR_NONCONFORMING"
    value = json.loads(result.stdout)
    if (result.returncode not in (0, 1) or value.get("event") != "branch_validation" or value.get("status") != expected
            or value.get("branch") != branch or value.get("canonical") != (result.returncode == 0)):
        raise ValueError("branch grammar detector failed: " + result.stderr)
    print("BRANCH_GRAMMAR_SIGNAL " + json.dumps(value, sort_keys=True))
    if result.returncode == 1:
        print("::warning title=PR head branch grammar::Nonconforming branch name")


def stage_input(args):
    import ci_plan
    root, stage = args.repository, args.stage
    ci_plan.validate_stage(root, stage, args.base)
    needs = ci_plan.strict_json_bytes(os.environ.get("CI_NEEDS", "{}").encode())
    if not isinstance(needs, dict):
        raise ValueError("CI_NEEDS must be a job-result object")
    for job, result in needs.items():
        if not isinstance(result, dict) or result.get("result") != "success":
            raise ValueError("required prerequisite did not succeed: " + job)
    commit = ci_plan.checked_head(root, args.commit or os.environ.get("CANDIDATE_SHA", ""))
    plan = args.plan or (pathlib.Path(os.environ["CI_PLAN_PATH"]) if os.environ.get("CI_PLAN_PATH") else None)
    changes = args.changes or (pathlib.Path(os.environ["CI_CHANGES_PATH"]) if os.environ.get("CI_CHANGES_PATH") else None)
    encoded_plan, encoded_changes = os.environ.get("CI_PLAN_B64", ""), os.environ.get("CI_CHANGES_B64", "")
    if encoded_plan or encoded_changes:
        if not encoded_plan or not encoded_changes:
            raise ValueError("both serialized plan and changed-path input are required")
        plan, changes = root / "build/ci/plan.json", root / "build/ci/changes.json"
        # Decode both before writing either; strict object/identity checks follow.
        values = [ci_plan.strict_json_bytes(base64.b64decode(value, validate=True)) for value in (encoded_plan, encoded_changes)]
        for destination, value in zip((plan, changes), values):
            ci_plan.write(destination, value)
    native_push = ci_plan.native_push()
    if plan is None and changes is None:
        if args.allow_direct:
            return {"required": True}
        if not native_push:
            raise ValueError("explicit complete changed-path input and validated plan are required")
    if (plan is None) != (changes is None):
        raise ValueError("both plan and changed-path input are required")
    plan = root / plan if plan is not None else None
    changes = root / changes if changes is not None else None
    if (native_push and not encoded_plan and not encoded_changes
            and (plan is None or not plan.is_file()) and (changes is None or not changes.is_file())):
        plan = plan or root / "build/ci/plan.json"
        changes = changes or root / "build/ci/changes.json"
        ci_plan.plan_push(root, commit, plan, changes)
    value = ci_plan.validate_plan(root, commit, plan, changes)
    if stage == "delta" and (value["mode"] != "pr" or value["base"] != args.base):
        raise ValueError("delta requires the validated plan's explicit immutable base")
    requirements = ci_plan.stage_requirements(root, value, stage)
    result = {"required": requirements["required"], "cache_layers": " ".join(requirements["cache_layers"]),
              "dotnet": "dotnet" in requirements["tools"], "lake": "lake" in requirements["tools"],
              "artifact_required": requirements["required"],
              "report_required": stage == "current" and "lean-report" in value["execution"]["steps"]}
    for upstream in ("build", "engineering", "current"):
        result[upstream + "_required"] = requirements["required"] and value["stages"][upstream]["status"] == "required"
    if not requirements["required"]:
        clear_stages = ("build", "engineering", "current") if stage == "build" else (stage,)
        for name in clear_stages:
            for suffix in (".json", "-checks.json", "-paths.nul", "-transport.json", "-result.json", "-no-work.json"):
                (root / "build/ci" / (name + suffix)).unlink(missing_ok=True)
        if stage in ("build", "engineering"):
            (root / "build/ci/tests.json").unlink(missing_ok=True)
        if stage in ("build", "current"):
            (root / "build/ci/scribe-markdown.paths").unlink(missing_ok=True)
        receipt = ci_plan.no_work(value, stage)
        ci_plan.write(root / "build/ci" / (stage + "-no-work.json"), receipt)
        ci_plan.write(root / "build/ci" / (stage + "-result.json"), {
            "stage": stage, "candidate": commit, "git_candidate": value["candidate"], "scope": value,
            "status": "not-required", "exit": 0, "error": None, "steps": [], "artifacts": [],
            "report": None, "current_evidence": None, "base_sha": args.base or None})
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("resolve", "checkout", "pack", "restore", "verify", "advisory", "summary",
                                           "plan", "pr-paths", "pr-plan", "push-plan", "validate-plan", "no-work", "validate-no-work", "stage-input"))
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    parser.add_argument("--commit", default="")
    parser.add_argument("--head", default="")
    parser.add_argument("--base", default="")
    parser.add_argument("--before", default="")
    parser.add_argument("--after", default="")
    parser.add_argument("--changes", type=pathlib.Path)
    parser.add_argument("--plan", type=pathlib.Path)
    parser.add_argument("--result", type=pathlib.Path)
    parser.add_argument("--output", type=pathlib.Path)
    parser.add_argument("--stage", choices=("build", "engineering", "current", "delta", "engineering-seed", "current-seed"))
    parser.add_argument("--allow-direct", action="store_true")
    parser.add_argument("--dispatch", action="store_true")
    parser.add_argument("--archive", type=pathlib.Path)
    parser.add_argument("--run-id", default=os.environ.get("GITHUB_RUN_ID", ""))
    parser.add_argument("--run-attempt", default=os.environ.get("GITHUB_RUN_ATTEMPT", ""))
    args = parser.parse_args()
    args.repository = args.repository.resolve()
    try:
        if args.command == "stage-input":
            values = stage_input(args)
            if args.dispatch:
                print(json.dumps(values, sort_keys=True))
                return 10 if values["required"] else 0
            outputs(values)
        elif args.command == "pr-plan":
            import ci_plan
            outputs(ci_plan.plan_pr(args.repository, args.commit, args.base, args.head))
        elif args.command == "push-plan":
            import ci_plan
            if args.base or args.head or args.plan or args.changes:
                raise ValueError("push-plan accepts only fixed event endpoints and output paths")
            outputs(ci_plan.plan_push(args.repository, args.commit, before=args.before, after=args.after))
        elif args.command in ("plan", "pr-paths", "validate-plan", "no-work", "validate-no-work"):
            import ci_plan
            print(json.dumps(ci_plan.command(args), sort_keys=True, ensure_ascii=False))
        elif args.command == "resolve": resolve(args.repository, args.head)
        elif args.command == "checkout": checkout(args.repository, args.commit)
        elif args.command in ("pack", "restore", "verify"): transport(args)
        elif args.command == "advisory": advisory(args.repository, args.head)
        else:
            text = (args.repository / "build/ci" / (args.stage + "-result.json")).read_text()
            if os.environ.get("GITHUB_STEP_SUMMARY"):
                with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as stream:
                    stream.write("```json\n" + text + "\n```\n")
            print(text)
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError, tarfile.TarError) as error:
        if args.command == "stage-input" and args.stage in ("build", "engineering", "current", "delta"):
            import ci_plan
            ci_plan.write(args.repository / "build/ci" / (args.stage + "-result.json"), {
                "stage": args.stage, "status": "failed", "exit": 2, "error": str(error), "steps": [], "artifacts": []})
        print("CI_INPUT_FAILED " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
