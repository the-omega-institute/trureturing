#!/usr/bin/env python3
"""Bind CI observations to the checked object and actual Actions workflow.

PR admission binds the merge parent. Push planning binds the fixed event endpoints;
its before object is planning data only. Workflow identity is recorded separately.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def checked_identity(repository, environment, acquire_pinned=False, report_source=None):
    def required(name):
        value = environment.get(name, "")
        if not value:
            raise ValueError("missing " + name)
        return value

    def sha(name):
        value = required(name)
        if not re.fullmatch(r"[0-9a-f]{40}", value):
            raise ValueError("invalid " + name)
        return value

    def revision(ref):
        return subprocess.run(["git", "rev-parse", "--verify", ref], cwd=repository,
            check=True, capture_output=True, text=True).stdout.strip()

    event = required("GITHUB_EVENT_NAME")
    publisher = event in {"schedule", "repository_dispatch"} and report_source is not None
    if event not in {"pull_request", "pull_request_target", "push"} and not publisher:
        raise ValueError("unsupported event " + event)
    head = revision("HEAD")
    base = None
    workflow = sha("GITHUB_WORKFLOW_SHA")
    event_sha = sha("GITHUB_SHA")
    if publisher:
        if report_source != head:
            raise ValueError("selected report source differs from checkout HEAD")
        if subprocess.run(["git", "symbolic-ref", "-q", "HEAD"], cwd=repository,
                          capture_output=True).returncode != 1:
            raise ValueError("selected report source requires detached checkout")
    elif event != "pull_request_target" and event_sha != head:
        raise ValueError("event must name the checked commit")
    if event == "pull_request" and workflow != head:
        raise ValueError("PR workflow must name the checked commit")
    pr_head, pr_base, before, after = None, None, None, None
    payload = json.loads(Path(required("GITHUB_EVENT_PATH")).read_text())
    if event == "push":
        before, after = payload["before"], payload["after"]
        if not all(isinstance(oid, str) and re.fullmatch(r"[0-9a-f]{40}", oid) for oid in (before, after)):
            raise ValueError("push before/after must be complete fixed object IDs")
        if payload["deleted"] or after == "0" * 40:
            raise ValueError("deletion event has no candidate current tree")
        if after != head:
            raise ValueError("push event.after differs from checkout HEAD")
        if not isinstance(payload["created"], bool) or not isinstance(payload["deleted"], bool):
            raise ValueError("push created/deleted must be booleans")
        if (before == "0" * 40) != payload["created"]:
            raise ValueError("zero before requires an initial branch event")
        if before != "0" * 40:
            try:
                pinned = revision(before + "^{commit}")
            except subprocess.CalledProcessError:
                if not acquire_pinned:
                    raise ValueError("missing pinned push before commit " + before)
                subprocess.run(["git", "fetch", "--no-tags", "--no-write-fetch-head", "origin", before],
                    cwd=repository, check=True)
                pinned = revision(before + "^{commit}")
            if pinned != before:
                raise ValueError("push before does not name a commit")
    elif not publisher:
        base = revision("HEAD^1")
        pr_head = payload["pull_request"]["head"]["sha"]
        pr_base = payload["pull_request"]["base"]["sha"]
        if revision("HEAD^2") != pr_head:
            raise ValueError("checked merge second parent differs from event PR head")
    workflow_ref = required("GITHUB_WORKFLOW_REF")
    entry, separator, _ = workflow_ref.partition("@")
    parts = entry.split("/", 2)
    if not separator or len(parts) != 3:
        raise ValueError("invalid entry workflow repository/path identity")
    if publisher and ("/".join(parts[:2]) != required("GITHUB_REPOSITORY")
            or parts[2] != ".github/workflows/truth-release-publish.yml" or required("GITHUB_JOB") != "produce"):
        raise ValueError("selected report source requires the truth-release publisher producer")
    return dict(workflow_repository="/".join(parts[:2]), workflow_path=parts[2], event=event, event_sha=event_sha, tested_head=head,
        selected_source=report_source if publisher else None,
        protected_base=base, push_before=before, push_after=after,
        planning_mode="initial" if before == "0" * 40 else "endpoints",
        pr_head=pr_head, event_pr_base=pr_base,
        reusable_workflow=None,
        workflow_ref=workflow_ref, workflow_sha=workflow,
        candidate_workflow=workflow == head, run_id=required("GITHUB_RUN_ID"),
        run_attempt=required("GITHUB_RUN_ATTEMPT"), job=required("GITHUB_JOB"))


def planning_paths(repository, before, head):
    """Transport complete Git endpoint paths; registered manifests own selection."""
    def git(*args):
        return subprocess.run(["git", *args], cwd=repository, check=True, capture_output=True).stdout
    if not all(isinstance(oid, str) and re.fullmatch(r"(?:[0-9a-f]{40}|[0-9a-f]{64})", oid)
               for oid in (before, head)) or len(before) != len(head):
        raise ValueError("immutable before/head OIDs are required")
    if git("rev-parse", "--verify", "HEAD^{commit}").decode().strip() != head:
        raise ValueError("head differs from checked HEAD")
    if before == "0" * len(before):
        paths = git("ls-files", "--cached", "--others", "--exclude-standard", "-z").split(b"\0")
        paths = [path for path in paths if path and (repository / os.fsdecode(path)).is_file()]
    else:
        if git("cat-file", "-t", before).strip() != b"commit":
            raise ValueError("before is not a commit")
        paths = git("diff", "--name-only", "--no-renames", "-z", before, head, "--").split(b"\0")
        paths += git("diff", "--name-only", "--no-renames", "-z", head, "--").split(b"\0")
        paths += git("ls-files", "--others", "--exclude-standard", "-z").split(b"\0")
    return sorted(set(path for path in paths if path))


def report_source_arguments(repository, environment, bases, befores, heads, acquire_pinned=False):
    """Resolve the public report boundary; shell callers only transport these arguments."""
    def single(values, name):
        values = list(values or [])
        if environment.get(name):
            values.append(environment[name])
        if any(not value for value in values) or len(set(values)) > 1:
            raise ValueError("conflicting or empty " + name)
        return values[0] if values else None

    base = single(bases, "STRATALINT_SOURCE_BASE")
    before = single(befores, "STRATALINT_PUSH_BEFORE")
    head = single(heads, "STRATALINT_PUSH_HEAD")
    if (before is None) != (head is None) or (base is not None and before is not None):
        raise ValueError("choose protected base or complete push range")
    publisher = (environment.get("GITHUB_ACTIONS") == "true"
                 and environment.get("GITHUB_EVENT_NAME") in {"schedule", "repository_dispatch"})
    # This caller reports an already gate-verified immutable source, independently
    # of the commit that triggered publication. H is its data reference; it does
    # not invent a push range or rerun historical delta admission.
    if publisher and (base is None or not re.fullmatch(r"[0-9a-f]{40}", base)):
        raise ValueError("publisher requires an explicit immutable selected report source")
    if base is not None:
        base = subprocess.run(["git", "rev-parse", "--verify", base + "^{commit}"],
            cwd=repository, check=True, capture_output=True, text=True).stdout.strip()

    identity = None
    if environment.get("GITHUB_ACTIONS") == "true":
        identity = checked_identity(repository, environment, acquire_pinned, base if publisher else None)
        expected = (identity["selected_source"] or identity["protected_base"], identity["push_before"], identity["push_after"])
        if (base is not None or before is not None) and (base, before, head) != expected:
            raise ValueError("explicit report source mode differs from checked Actions identity")
        base, before, head = expected
    if base is not None:
        return ["--base", base], identity
    if before is None:
        raise ValueError("explicit protected base or push range is required outside Actions")
    planning_paths(repository, before, head)
    return ["--push-before", before, "--push-head", head], identity


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", required=True, type=Path)
    parser.add_argument("--acquire-pinned", action="store_true")
    parser.add_argument("--engineering-arguments", action="store_true",
        help="emit validated make arguments, with the identity observation on stderr")
    parser.add_argument("--report-source-arguments", action="store_true",
        help="emit one validated source argument per line for report callers")
    parser.add_argument("--base", action="append")
    parser.add_argument("--push-before", action="append")
    parser.add_argument("--push-head", action="append")
    parser.add_argument("--planning-before")
    parser.add_argument("--planning-head")
    parser.add_argument("--paths", action="store_true")
    parser.add_argument("--github-output", action="store_true")
    parser.add_argument("--github-env", action="store_true")
    arguments = parser.parse_args()
    if arguments.report_source_arguments:
        try:
            if (arguments.paths or arguments.planning_before or arguments.planning_head
                    or arguments.engineering_arguments or arguments.github_output or arguments.github_env):
                raise ValueError("report source arguments require a single output mode")
            source, identity = report_source_arguments(arguments.repository, os.environ, arguments.base,
                arguments.push_before, arguments.push_head, arguments.acquire_pinned)
        except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
            print("CI_REPORT_SOURCE_INVALID " + str(error), file=sys.stderr)
            return 2
        if identity is not None:
            print("CI_CHECKED_IDENTITY " + json.dumps(identity, sort_keys=True), file=sys.stderr)
        print("\n".join(source))
        return 0
    if arguments.base or arguments.push_before or arguments.push_head:
        print("CI_CHECKED_IDENTITY_INVALID source flags require --report-source-arguments", file=sys.stderr)
        return 2
    if arguments.paths:
        try:
            paths = planning_paths(arguments.repository, arguments.planning_before, arguments.planning_head)
        except (ValueError, OSError, subprocess.CalledProcessError) as error:
            print("PUSH_RANGE_INVALID " + str(error), file=sys.stderr)
            return 2
        sys.stdout.buffer.write(b"".join(path + b"\0" for path in paths))
        return 0
    try:
        result = checked_identity(arguments.repository, os.environ, arguments.acquire_pinned)
    except (ValueError, KeyError, TypeError, OSError, subprocess.CalledProcessError) as error:
        print("CI_CHECKED_IDENTITY_INVALID " + str(error), file=sys.stderr)
        return 2
    print("CI_CHECKED_IDENTITY " + json.dumps(result, sort_keys=True),
        file=sys.stderr if arguments.engineering_arguments else sys.stdout, flush=True)
    if arguments.github_output:
        with open(os.environ["GITHUB_OUTPUT"], "a") as output:
            for name in ("protected_base", "push_before", "push_after", "tested_head", "planning_mode"):
                output.write(name + "=" + (result[name] or "") + "\n")
    if arguments.github_env:
        with open(os.environ["GITHUB_ENV"], "a") as output:
            for name, value in {
                "STRATALINT_SOURCE_BASE": result["protected_base"],
                "STRATALINT_SCRIBE_BASE": result["protected_base"],
                "STRATALINT_PUSH_BEFORE": result["push_before"],
                "STRATALINT_PUSH_HEAD": result["push_after"],
            }.items():
                output.write(name + "=" + (value or "") + "\n")
    if arguments.engineering_arguments:
        event = "push" if result["event"] == "push" else "pull-request"
        before = result["push_before"] if event == "push" else result["protected_base"]
        print("HEAD=" + result["tested_head"])
        print("EVENT=" + event)
        print(("BEFORE=" if event == "push" else "BASE=") + before)
    return 0


if __name__ == "__main__":
    sys.exit(main())
