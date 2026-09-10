"""Fixed candidate resolution, stage transport bootstrap, and CI diagnostics."""
import argparse
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
    inputs = json.loads(os.environ.get("CI_WORKFLOW_INPUTS", "null"))
    if inputs not in (None, ""):
        if not isinstance(inputs, dict):
            raise ValueError("workflow inputs must be an object")
        if "candidate_sha" in inputs and oid(inputs["candidate_sha"]) != oid(commit):
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
    outputs({"candidate_sha": candidate, "base_sha": base})


def extract(root, archive):
    with tarfile.open(archive) as source:
        members = source.getmembers()
        for member in members:
            path = pathlib.PurePosixPath(member.name)
            if path.is_absolute() or ".." in path.parts or not (member.isfile() or member.isdir()):
                raise ValueError("invalid stage archive member")
            if not (member.name.startswith("build/ci/") or member.name.startswith("tools/") and (
                    "/bin/Release/" in member.name or re.search(r"/obj/Release/[^/]+/ref/[^/]+\.dll$", member.name))
                    or member.name.startswith(".lake/build/stratalint/raw-lean-report.json")):
                raise ValueError("unexpected stage archive destination")
        source.extractall(root, members=members)


def transport(args):
    if args.command == "restore":
        extract(args.repository, args.archive)
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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("resolve", "checkout", "pack", "restore", "verify", "advisory", "summary"))
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    parser.add_argument("--commit", default="")
    parser.add_argument("--head", default="")
    parser.add_argument("--stage", choices=("build", "engineering", "current", "delta"))
    parser.add_argument("--archive", type=pathlib.Path)
    parser.add_argument("--run-id", default=os.environ.get("GITHUB_RUN_ID", ""))
    parser.add_argument("--run-attempt", default=os.environ.get("GITHUB_RUN_ATTEMPT", ""))
    args = parser.parse_args()
    args.repository = args.repository.resolve()
    try:
        if args.command == "resolve": resolve(args.repository, args.head)
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
        print("CI_INPUT_FAILED " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
