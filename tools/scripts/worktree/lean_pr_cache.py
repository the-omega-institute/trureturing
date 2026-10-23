"""Prepare native PR artifacts; adopt only for that head or its actual merge."""
from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import shutil
import tarfile
import tempfile
import zipfile
from datetime import datetime
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
    action = event.get("action")
    require(os.environ["GITHUB_EVENT_NAME"] == "pull_request"
            and action in ("opened", "reopened", "synchronize", "labeled")
            and (action != "labeled" or event.get("label", {}).get("name") == "lean-cache-produce"),
            "not a PR preparation event")
    require(any(label.get("name") == "lean-cache-produce"
                for label in event["pull_request"].get("labels", [])), "PR is not opted-in for preparation")
    pr = event["pull_request"]
    identity = validate_identity(dict(repository=os.environ["GITHUB_REPOSITORY"], pr=str(event["number"]),
        head=pr["head"]["sha"], merge=os.environ["GITHUB_SHA"],
        base=git(root, "rev-parse", "HEAD^1"), target_ref="refs/heads/" + pr["base"]["ref"],
        source_run=os.environ["GITHUB_RUN_ID"], source_attempt=os.environ["GITHUB_RUN_ATTEMPT"]))
    require(os.environ["GITHUB_REF"] == "refs/pull/" + identity["pr"] + "/merge", "PR event ref mismatch")
    checkout_identity(root, identity)
    return identity


def validate_remote(identity, *, allow_merged=False, require_opt_in=False):
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
    require(pr["number"] == int(identity["pr"]), "source PR identity differs")
    require((pr["state"] == "open" or allow_merged and pr.get("merged") is True)
            and pr["head"]["sha"] == identity["head"]
            and pr["base"]["ref"] == branch and pr["base"]["repo"]["full_name"] == repository,
            "PR head or target changed, or PR is no longer open")
    if require_opt_in:
        require(any(label.get("name") == "lean-cache-produce" for label in pr.get("labels", [])),
                "PR is no longer opted-in for preparation")
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
    validate_remote(identity, require_opt_in=True)
    inputs = dict(operation="pr", source_ref=identity["target_ref"], source_sha=identity["merge"],
                  pr_source=json.dumps(identity, separators=(",", ":")))
    if os.environ.get("STRATALINT_RUNNER_DIAGNOSTICS") == "true":
        inputs["runner_diagnostics"] = "true"
    response = api(identity["repository"], "actions/workflows/" + WORKFLOW + "/dispatches", dict(
        ref=identity["target_ref"], return_run_details=True, inputs=inputs))
    run = response.get("workflow_run_id")
    require(type(run) is int and run > 0, "dispatch returned no exact producer run id")
    actions.output({"producer_run": run})
    # Dispatch success is not build, publication, restore or required success.
    return receipt("dispatched", identity, producer_ref=identity["target_ref"], producer_run=run)


def producer_context(root, identity, *, allow_merged=False):
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
    validate_remote(identity, allow_merged=allow_merged, require_opt_in=not allow_merged)
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


def artifact_name(identity):
    return "lean-pr-preparation-" + identity["pr"] + "-" + identity["head"]


def native_paths(root, registration_root=None):
    """Expand the same registered paths used by Actions native cache transport."""
    paths = set()
    for patterns in actions.native_archive_paths(registration_root or root, actions.LAYERS).values():
        for pattern in patterns:
            for path in root.glob(pattern):
                paths.add(path.relative_to(root))
    return sorted(path for path in paths if not any(parent in paths for parent in path.parents))


def pack(root, identity, directory):
    runtime = producer_context(root, identity, allow_merged=True)
    require(actions.project_work(root) is not None, "preparation has no current build-work fact")
    paths = native_paths(root)
    require((root / ".lake/packages").is_dir() and (root / ".lake/build").is_dir(),
            "preparation native directories are unavailable")
    directory.mkdir(parents=True, exist_ok=True)
    with tarfile.open(directory / "native.tar.gz", "w:gz", compresslevel=1) as archive:
        for path in paths:
            archive.add(root / path, arcname=str(path))
    actions.write_small_record(directory / "preparation.json", dict(source=identity, runtime=runtime,
        partition=actions.partition_path(root), elan_key=actions.elan_key(root)))
    actions.output(dict(artifact_name=artifact_name(identity), artifact_path=str(directory)))
    return receipt("packed", identity, runtime=runtime)


def artifact_metadata(repository, artifact_id, identity, runtime):
    artifact = api(repository, "actions/artifacts/" + str(artifact_id))
    require(type(artifact["id"]) is int and artifact["id"] == artifact_id
            and artifact["name"] == artifact_name(identity) and artifact["expired"] is False
            and str(artifact["workflow_run"]["id"]) == runtime["run"]
            and artifact["workflow_run"]["head_sha"] == runtime["sha"],
            "artifact is expired or does not bind the producer run")
    return artifact


def confirm(root, identity, artifact_id):
    runtime = producer_context(root, identity, allow_merged=True)
    artifact_metadata(identity["repository"], artifact_id, identity, runtime)
    return receipt("prepared", identity, runtime=runtime, artifact=artifact_id)


def paged(repository, path, field=None):
    rows, page = [], 1
    while True:
        value = api(repository, path + ("&" if "?" in path else "?") + urlencode(dict(per_page=100, page=page)))
        batch = value[field] if field else value
        require(isinstance(batch, list), "invalid API listing: " + path)
        rows.extend(batch)
        if len(batch) < 100:
            return rows
        page += 1


def consumer_context(root):
    event = json.loads(pathlib.Path(os.environ["GITHUB_EVENT_PATH"]).read_text())
    repository, kind = os.environ["GITHUB_REPOSITORY"], os.environ["GITHUB_EVENT_NAME"]
    checkout, ref = git(root, "rev-parse", "HEAD"), os.environ["GITHUB_REF"]
    if kind == "pull_request":
        require(checkout == os.environ["GITHUB_SHA"] and ref == "refs/pull/" + str(event["number"]) + "/merge",
                "source consumer event checkout mismatch")
        source = event["pull_request"]
        parents = git(root, "show", "-s", "--format=%P", "HEAD").split()
        require(len(parents) == 2 and parents[1] == source["head"]["sha"], "consumer M parents differ from event H")
        pr = api(repository, "pulls/" + str(event["number"]))
        require(pr["number"] == event["number"], "source PR identity differs")
        require(pr["state"] == "open" and pr["head"]["sha"] == source["head"]["sha"]
                and pr["base"]["ref"] == source["base"]["ref"], "source PR head or target changed, or is closed")
        merged = False
    elif kind == "push" or kind == "workflow_dispatch" and actions.manual_source_is_valid():
        if kind == "push":
            require(checkout == os.environ["GITHUB_SHA"] == event["after"] and ref == event["ref"],
                    "target consumer event checkout mismatch")
        else:
            require(checkout == os.environ["STRATALINT_CACHE_CHECKED_OUT_SHA"], "manual consumer checkout mismatch")
        require(re.fullmatch(r"refs/heads/(dev|integration-[A-Za-z0-9._/-]+)", ref), "invalid target consumer ref")
        prs = paged(repository, "commits/" + checkout + "/pulls")
        matching = [pr for pr in prs if pr.get("merged_at") and pr.get("merge_commit_sha") == checkout
                    and "refs/heads/" + pr["base"]["ref"] == ref
                    and pr["base"]["repo"]["full_name"] == repository]
        if not matching:
            return None
        require(len(matching) == 1, "ambiguous merged PR for event checkout")
        pr = api(repository, "pulls/" + str(matching[0]["number"]))
        require(pr.get("merged") is True and pr["merge_commit_sha"] == checkout
                and "refs/heads/" + pr["base"]["ref"] == ref, "actual merge does not bind target checkout")
        merged = True
    else:
        return None
    target = "refs/heads/" + pr["base"]["ref"]
    require(pr["base"]["repo"]["full_name"] == repository, "foreign PR target")
    require(re.fullmatch(r"refs/heads/(dev|integration-[A-Za-z0-9._/-]+)", target), "invalid PR target")
    require(api(repository, "branches/" + quote(pr["base"]["ref"], safe=""))["protected"] is True,
            "consumer target is not protected")
    return dict(repository=repository, pr=str(pr["number"]), head=pr["head"]["sha"], target_ref=target,
                checkout=checkout, merged=merged)


def download(repository, artifact_id, destination):
    with destination.open("wb") as stream:
        subprocess.run(["gh", "api", "repos/" + repository + "/actions/artifacts/" + str(artifact_id) + "/zip"],
                       stdout=stream, check=True)


def validate_preparation(root, value, context, artifact):
    require(isinstance(value, dict) and set(value) == {"source", "runtime", "partition", "elan_key"},
            "invalid preparation identity fields")
    identity, runtime = validate_identity(value["source"]), value["runtime"]
    require(all(identity[key] == context[key] for key in ("repository", "pr", "head", "target_ref")),
            "preparation PR/head/target mismatch")
    require(all(isinstance(value[key], str) and value[key] for key in ("partition", "elan_key")),
            "invalid preparation native identity")
    require(isinstance(runtime, dict) and set(runtime) == {"ref", "sha", "workflow_ref", "workflow_sha", "run", "attempt"}
            and runtime["ref"] == identity["target_ref"] and runtime["sha"] == runtime["workflow_sha"]
            and re.fullmatch(r"[0-9a-f]{40}", runtime["sha"])
            and all(isinstance(runtime[key], str) and re.fullmatch(r"[1-9][0-9]*", runtime[key]) for key in ("run", "attempt"))
            and runtime["workflow_ref"] == identity["repository"] + "/.github/workflows/" + WORKFLOW + "@" + runtime["ref"],
            "invalid producer runtime identity")
    repository = identity["repository"]
    run = api(repository, "actions/runs/" + runtime["run"] + "/attempts/" + runtime["attempt"])
    require(str(run["id"]) == runtime["run"] and str(run["run_attempt"]) == runtime["attempt"]
            and run["event"] == "workflow_dispatch" and run["path"] == ".github/workflows/" + WORKFLOW
            and run["head_sha"] == runtime["sha"] and run["head_branch"] == runtime["ref"].removeprefix("refs/heads/"),
            "preparation producer attempt identity differs")
    artifact_metadata(repository, artifact["id"], identity, runtime)
    if run["status"] != "completed" or run["conclusion"] != "success":
        receipt("not-ready", identity, runtime=runtime, artifact=artifact["id"], reason="producer attempt has not succeeded")
        return None
    require(datetime.fromisoformat(run["run_started_at"].replace("Z", "+00:00")) <=
            datetime.fromisoformat(artifact["created_at"].replace("Z", "+00:00")) <=
            datetime.fromisoformat(run["updated_at"].replace("Z", "+00:00")),
            "artifact does not belong to producer attempt interval")
    validate_remote(identity, allow_merged=context["merged"])
    commit = api(repository, "git/commits/" + identity["merge"])
    require(commit["sha"] == identity["merge"] and [p["sha"] for p in commit["parents"]] ==
            [identity["base"], identity["head"]], "prepared M parents are not B,H")
    comparison = api(repository, "compare/" + runtime["sha"] + "..." + quote(identity["target_ref"].removeprefix("refs/heads/"), safe=""))
    require(comparison["merge_base_commit"]["sha"] == runtime["sha"], "producer runtime is outside target history")
    current = dict(partition=actions.partition_path(root), elan_key=actions.elan_key(root))
    prepared = {key: value[key] for key in current}
    if prepared != current:
        receipt("incompatible", identity, runtime=runtime, artifact=artifact["id"],
                reason="preparation native partition or toolchain mismatch", prepared=prepared, current=current)
        return None
    return identity, runtime


def unpack(root, archive_path, directory):
    with tarfile.open(archive_path, "r:gz") as archive:
        members = archive.getmembers()
        names = [member.name for member in members]
        require(len(names) == len(set(names)), "duplicate native archive member")
        for member in members:
            path = pathlib.PurePosixPath(member.name)
            require(not path.is_absolute() and ".." not in path.parts and
                    (member.name in (".lake/build", ".lake/packages") or member.name.startswith(".lake/build/")
                     or member.name.startswith(".lake/packages/")), "native archive member outside cache roots")
        archive.extractall(directory, filter="data")
    selected = set(native_paths(directory, root))
    require(selected, "empty native preparation")
    for member in members:
        if member.isdir():
            continue
        relative = pathlib.Path(member.name)
        require(relative in selected or any(parent in selected for parent in relative.parents),
                "native archive member outside registered membership: " + str(relative))
    for name in ("packages", "build"):
        source = directory / ".lake" / name
        require(source.is_dir() and not source.is_symlink(), "missing native preparation directory: " + name)
    # Staging finishes before replacing either native directory. Consumer report
    # validation remains in the existing report/Lean entry, with its own errors.
    for name in ("packages", "build"):
        target = root / ".lake" / name
        if target.is_symlink() or target.is_file():
            target.unlink()
        elif target.exists():
            shutil.rmtree(target)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(directory / ".lake" / name), target)


def adopt(root):
    record = root / "build/lean-cache/pr-adopted.json"
    record.unlink(missing_ok=True)
    actions.output(dict(adopted=False))
    context = consumer_context(root)
    if context is None:
        return receipt("miss", None, reason="no matching merged PR at event checkout")
    repository = context["repository"]
    candidates = paged(repository, "actions/artifacts?" + urlencode(dict(name=artifact_name(context))), "artifacts")
    candidates = [a for a in candidates if a["name"] == artifact_name(context) and a["expired"] is False]
    for artifact in sorted(candidates, key=lambda a: a["id"], reverse=True):
        with tempfile.TemporaryDirectory(prefix="lean-pr-preparation-") as temporary:
            directory = pathlib.Path(temporary)
            download(repository, artifact["id"], directory / "artifact.zip")
            with zipfile.ZipFile(directory / "artifact.zip") as archive:
                require(sorted(archive.namelist()) == ["native.tar.gz", "preparation.json"], "invalid preparation artifact members")
                archive.extractall(directory)
            value = json.loads((directory / "preparation.json").read_text())
            validated = validate_preparation(root, value, context, artifact)
            if validated is None:
                continue
            identity, runtime = validated
            unpack(root, directory / "native.tar.gz", directory / "native")
        actions.stamp_restored_dependency(root, actions.actions_keys(root))
        actions.write_small_record(record, dict(run=os.environ["GITHUB_RUN_ID"], attempt=os.environ["GITHUB_RUN_ATTEMPT"],
            repository=str(root.resolve()), checkout=context["checkout"], ref=os.environ["GITHUB_REF"],
            artifact=artifact["id"], merged=context["merged"]))
        actions.output(dict(adopted=True))
        actions.output(dict(STRATALINT_ACTIONS_CACHE_SEEDED="0"), "GITHUB_ENV")
        return receipt("adopted", identity, runtime=runtime, artifact=artifact["id"],
                       checkout=context["checkout"], actual_merge=context["checkout"] if context["merged"] else None)
    return receipt("miss", context, reason="no unexpired preparation from a successful producer")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("dispatch", "prepare", "pack", "confirm", "adopt"))
    parser.add_argument("--repository", type=pathlib.Path, required=True)
    parser.add_argument("--directory", type=pathlib.Path)
    parser.add_argument("--artifact-id", type=int)
    args = parser.parse_args()
    try:
        root = args.repository.resolve()
        if args.command == "dispatch":
            dispatch(root)
        elif args.command == "adopt":
            adopt(root)
        else:
            identity = validate_identity(json.loads(os.environ["PR_SOURCE"]))
            if args.command == "prepare":
                prepare(root, identity)
            elif args.command == "pack":
                require(args.directory is not None, "pack requires directory")
                pack(root, identity, args.directory)
            else:
                require(args.artifact_id is not None and args.artifact_id > 0, "confirm requires immutable artifact ID")
                confirm(root, identity, args.artifact_id)
        return 0
    except (OSError, ValueError, KeyError, TypeError, tarfile.TarError, zipfile.BadZipFile, subprocess.SubprocessError) as error:
        print("PR_CACHE_ERROR " + str(error), file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError) and error.stderr:
            print(error.stderr, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
