#!/usr/bin/env python3
"""Bind CI observations to the checked object and actual Actions workflow.

Git supplies the tested tree and protected first parent. Event metadata identifies
the PR head and workflow; it never substitutes a different base for judging.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def checked_identity(repository, environment):
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
    head, base = revision("HEAD"), revision("HEAD^1")
    workflow = sha("GITHUB_WORKFLOW_SHA")
    event_sha = sha("GITHUB_SHA")
    if event != "pull_request_target" and (event_sha != head or workflow != head):
        raise ValueError("push/PR event and workflow must name the checked commit")
    pr_head, pr_base = None, None
    if event != "push":
        payload = json.loads(Path(required("GITHUB_EVENT_PATH")).read_text())
        pr_head = payload["pull_request"]["head"]["sha"]
        pr_base = payload["pull_request"]["base"]["sha"]
        if revision("HEAD^2") != pr_head:
            raise ValueError("checked merge second parent differs from event PR head")
    return dict(event=event, event_sha=event_sha, tested_head=head,
        protected_base=base, pr_head=pr_head, event_pr_base=pr_base,
        workflow_ref=required("GITHUB_WORKFLOW_REF"), workflow_sha=workflow,
        candidate_workflow=workflow == head, run_id=required("GITHUB_RUN_ID"),
        run_attempt=required("GITHUB_RUN_ATTEMPT"), job=required("GITHUB_JOB"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", required=True, type=Path)
    arguments = parser.parse_args()
    try:
        result = checked_identity(arguments.repository, os.environ)
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        print("CI_CHECKED_IDENTITY_INVALID " + str(error), file=sys.stderr)
        return 2
    print("CI_CHECKED_IDENTITY " + json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
