"""Build a pinned PR candidate once, in its protected target's Actions scope."""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
from urllib.parse import quote, urlencode

import lean_actions as actions

WORKFLOW = "lean-cache-publish.yml"
IDENTITY_FIELDS = {"repository", "pr", "head", "merge", "base", "source_run", "source_attempt", "target_ref"}


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def git(root, *args):
    return subprocess.run(["git", "-C", str(root), *args], check=True,
                          capture_output=True, text=True).stdout.strip()


def api(repository, path, body=None):
    command = ["gh", "api", ("repos/" + repository + "/" + path).rstrip("/")]
    if body is not None:
        command += ["--method", "POST", "--input", "-"]
    result = subprocess.run(command, input=None if body is None else json.dumps(body),
                            check=True, capture_output=True, text=True, timeout=60)
    return json.loads(result.stdout)


def validate_identity(value):
    require(isinstance(value, dict) and set(value) == IDENTITY_FIELDS, "invalid source identity fields")
    require(isinstance(value["repository"], str) and
            re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", value["repository"])
            and value["repository"].split("/")[1] not in (".", ".."), "invalid repository")
    for name in ("pr", "source_run", "source_attempt"):
        require(isinstance(value[name], str) and re.fullmatch(r"[1-9][0-9]*", value[name]), "invalid " + name)
    for name in ("head", "merge", "base"):
        require(isinstance(value[name], str) and re.fullmatch(r"[0-9a-f]{40}", value[name])
                and value[name] != "0" * 40, "invalid " + name)
    require(isinstance(value["target_ref"], str) and
            re.fullmatch(r"refs/heads/(dev|integration-[A-Za-z0-9._/-]+)", value["target_ref"]),
            "target outside protected dev/integration scope")
    subprocess.run(["git", "check-ref-format", value["target_ref"]], check=True, capture_output=True)
    return value


def checkout_identity(root, identity):
    require(git(root, "rev-parse", "HEAD") == identity["merge"], "checkout is not source merge M")
    require(git(root, "show", "-s", "--format=%P", "HEAD").split() ==
            [identity["base"], identity["head"]], "source M parents are not B,H")


def source_identity(root):
    event = json.loads(pathlib.Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    require(os.environ["GITHUB_EVENT_NAME"] == "pull_request" and event.get("action") == "labeled"
            and event.get("label", {}).get("name") == "lean-cache-produce", "not a labelled PR dispatch")
    pr = event["pull_request"]
    identity = validate_identity(dict(repository=os.environ["GITHUB_REPOSITORY"], pr=str(event["number"]),
        head=pr["head"]["sha"], merge=os.environ["GITHUB_SHA"],
        base=git(root, "rev-parse", "HEAD^1"), target_ref="refs/heads/" + pr["base"]["ref"],
        source_run=os.environ["GITHUB_RUN_ID"], source_attempt=os.environ["GITHUB_RUN_ATTEMPT"]))
    require(os.environ["GITHUB_REF"] == "refs/pull/" + identity["pr"] + "/merge", "PR event ref mismatch")
    checkout_identity(root, identity)
    return identity


def validate_remote(identity):
    validate_identity(identity)
    repository = identity["repository"]
    require(repository == os.environ["GITHUB_REPOSITORY"], "foreign source repository")
    branch = identity["target_ref"].removeprefix("refs/heads/")
    target = api(repository, "branches/" + quote(branch, safe=""))
    require(target.get("protected") is True, "producer target is not protected")
    comparison = api(repository, "compare/" + identity["base"] + "..." + quote(branch, safe=""))
    require(comparison["merge_base_commit"]["sha"] == identity["base"], "B is not in the target history")
    # B may be old. M is an unmerged candidate, never claimed to be target history.
    pr = api(repository, "pulls/" + identity["pr"])
    require(pr["state"] == "open" and pr["head"]["sha"] == identity["head"]
            and pr["base"]["ref"] == branch and pr["base"]["repo"]["full_name"] == repository,
            "PR head or target changed, or PR is no longer open")
    run = api(repository, "actions/runs/" + identity["source_run"] + "/attempts/" + identity["source_attempt"])
    # run.pull_requests can be reassociated with a same-head Draft. The event
    # identity captured by the dispatch, not that mutable association, is used.
    require(str(run["id"]) == identity["source_run"] and str(run["run_attempt"]) == identity["source_attempt"]
            and run["event"] == "pull_request" and run["head_sha"] == identity["head"]
            and run["path"] == ".github/workflows/" + WORKFLOW,
            "source run does not bind the PR head and workflow")


def receipt(status, identity, **fields):
    value = dict(status=status, source=identity, **fields)
    print("LEAN_PR_CACHE " + json.dumps(value, sort_keys=True), flush=True)
    return value


def dispatch(root):
    identity = source_identity(root)
    validate_remote(identity)
    response = api(identity["repository"], "actions/workflows/" + WORKFLOW + "/dispatches", dict(
        ref=identity["target_ref"], return_run_details=True, inputs=dict(operation="pr",
        source_ref=identity["target_ref"], source_sha=identity["merge"],
        pr_source=json.dumps(identity, separators=(",", ":")))))
    run = response.get("workflow_run_id")
    require(type(run) is int and run > 0, "dispatch returned no exact producer run id")
    actions.output({"producer_run": run})
    # Dispatch success is not build, publication, restore or required success.
    return receipt("dispatched", identity, producer_ref=identity["target_ref"], producer_run=run)


def producer_context(root, identity):
    require(os.environ["GITHUB_EVENT_NAME"] == "workflow_dispatch"
            and os.environ["GITHUB_REF"] == identity["target_ref"], "producer is outside the target dispatch scope")
    require(os.environ["SOURCE_REF"] == identity["target_ref"] and os.environ["SOURCE_SHA"] == identity["merge"],
            "dispatch inputs differ from PR source")
    runtime_sha = os.environ["GITHUB_SHA"]
    require(re.fullmatch(r"[0-9a-f]{40}", runtime_sha) and runtime_sha != "0" * 40, "invalid workflow runtime SHA")
    require(os.environ["GITHUB_WORKFLOW_REF"] == identity["repository"] + "/.github/workflows/" + WORKFLOW
            + "@" + identity["target_ref"] and os.environ["GITHUB_WORKFLOW_SHA"] == runtime_sha,
            "workflow is not the pinned target runtime")
    checkout_identity(root, identity)
    validate_remote(identity)
    comparison = api(identity["repository"], "compare/" + runtime_sha + "..." +
                     quote(identity["target_ref"].removeprefix("refs/heads/"), safe=""))
    require(comparison["merge_base_commit"]["sha"] == runtime_sha, "workflow runtime is outside target history")
    return dict(ref=os.environ["GITHUB_REF"], sha=runtime_sha, workflow_ref=os.environ["GITHUB_WORKFLOW_REF"],
                workflow_sha=os.environ["GITHUB_WORKFLOW_SHA"], run=os.environ["GITHUB_RUN_ID"],
                attempt=os.environ["GITHUB_RUN_ATTEMPT"])


def prepare(root, identity):
    runtime = producer_context(root, identity)
    actions.output({"STRATALINT_CACHE_PR_SOURCE_VALIDATED": True,
        "STRATALINT_CACHE_SOURCE_REF": "refs/pull/" + identity["pr"] + "/merge",
        "STRATALINT_CACHE_SOURCE_COMMIT": identity["merge"],
        "STRATALINT_CACHE_TARGET_REF": identity["target_ref"],
        "STRATALINT_CACHE_CHECKED_OUT_SHA": identity["merge"]}, "GITHUB_ENV")
    return receipt("validated", identity, runtime=runtime)


def confirm(root, identity):
    runtime = producer_context(root, identity)
    # Keys come from the shared producer: newly saved or actually restored and
    # validated by it. A retained default-branch seed is also target-readable.
    default = api(identity["repository"], "")["default_branch"]
    refs = list(dict.fromkeys([identity["target_ref"], "refs/heads/" + default]))
    keys = actions.actions_keys(root)
    caches = {}
    for layer in ("project", "dependency", "elan"):
        key = os.environ[layer.upper() + "_CACHE_KEY"]
        expected = (keys[layer]["restore_prefix"] + r"[1-9][0-9]*-[1-9][0-9]*" if layer != "elan"
                    else re.escape(actions.elan_key(root)))
        require(re.fullmatch(expected, key), "invalid produced " + layer + " key")
        for ref in refs:
            listing = api(identity["repository"], "actions/caches?" + urlencode(dict(key=key, ref=ref)))
            matches = [row for row in listing["actions_caches"] if row["key"] == key and row["ref"] == ref]
            if matches:
                require(len(matches) == 1, "ambiguous target-readable cache: " + layer)
                caches[layer] = dict(key=key, ref=ref, id=matches[0]["id"])
                break
        require(layer in caches, "target-readable cache publication missing: " + layer)
    return receipt("published", identity, runtime=runtime, caches=caches)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("dispatch", "prepare", "confirm"))
    parser.add_argument("--repository", type=pathlib.Path, required=True)
    args = parser.parse_args()
    try:
        root = args.repository.resolve()
        if args.command == "dispatch":
            dispatch(root)
        else:
            identity = validate_identity(json.loads(os.environ["PR_SOURCE"]))
            (prepare if args.command == "prepare" else confirm)(root, identity)
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print("PR_CACHE_ERROR " + str(error), file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and error.stderr:
            print(error.stderr, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
