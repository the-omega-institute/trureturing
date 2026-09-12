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


def checked_identity(repository, environment, acquire_pinned=False):
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
    if event not in {"pull_request", "pull_request_target", "push"}:
        raise ValueError("unsupported event " + event)
    head = revision("HEAD")
    base = None
    workflow = sha("GITHUB_WORKFLOW_SHA")
    event_sha = sha("GITHUB_SHA")
    if event != "pull_request_target" and event_sha != head:
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
    else:
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
    return dict(workflow_repository="/".join(parts[:2]), workflow_path=parts[2], event=event, event_sha=event_sha, tested_head=head,
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


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", required=True, type=Path)
    parser.add_argument("--acquire-pinned", action="store_true")
    parser.add_argument("--run-engineering", action="store_true")
    parser.add_argument("--planning-before")
    parser.add_argument("--planning-head")
    parser.add_argument("--paths", action="store_true")
    parser.add_argument("--github-output", action="store_true")
    parser.add_argument("--github-env", action="store_true")
    arguments = parser.parse_args()
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
    print("CI_CHECKED_IDENTITY " + json.dumps(result, sort_keys=True), flush=True)
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
    if arguments.run_engineering:
        event = "push" if result["event"] == "push" else "pull-request"
        before = result["push_before"] if event == "push" else result["protected_base"]
        return subprocess.call(["/bin/bash", str(arguments.repository.resolve() / "tools/scripts/workflow/engineering-test-execution-harness.sh"),
            str(arguments.repository.resolve()), event, before, result["tested_head"]])
    return 0


if __name__ == "__main__":
    sys.exit(main())
