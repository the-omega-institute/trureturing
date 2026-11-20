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
import time
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


def require_target_ancestor(repository, ancestor, target, reason):
    if ancestor == target:
        return
    # The history endpoint can establish ancestry without computing changed files.
    history = api(repository, "commits?" + urlencode({"sha": target, "per_page": 100}))
    require(isinstance(history, list) and history and history[0].get("sha") == target,
            "commit history does not bind the protected target")
    if any(commit.get("sha") == ancestor for commit in history):
        return
    comparison = api(repository, "compare/" + ancestor + "..." + target)
    require(comparison["merge_base_commit"]["sha"] == ancestor, reason)


def validate_remote(identity, *, allow_merged=False, require_opt_in=False):
    validate_identity(identity)
    repository = identity["repository"]
    require(repository == os.environ["GITHUB_REPOSITORY"], "foreign source repository")
    branch = identity["target_ref"].removeprefix("refs/heads/")
    target = api(repository, "branches/" + quote(branch, safe=""))
    require(target.get("protected") is True, "producer target is not protected")
    target_head = target.get("commit", {}).get("sha")
    require(isinstance(target_head, str) and re.fullmatch(r"[0-9a-f]{40}", target_head),
            "protected target has no commit identity")
    require_target_ancestor(repository, identity["base"], target_head, "B is not in the target history")
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
    return target_head


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
    target_head = validate_remote(identity, allow_merged=allow_merged, require_opt_in=not allow_merged)
    require_target_ancestor(identity["repository"], runtime_sha, target_head, "workflow runtime is outside target history")
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


def artifact_name(identity, *, sharded=False):
    prefix = "lean-pr-preparation-shards-v1-" if sharded else "lean-pr-preparation-"
    return prefix + identity["pr"] + "-" + identity["head"]


def native_paths(root, registration_root=None, layers=actions.LAYERS):
    """Expand the same registered paths used by Actions native cache transport."""
    paths = set()
    for patterns in actions.native_archive_paths(registration_root or root, layers).values():
        for pattern in patterns:
            for path in root.glob(pattern):
                paths.add(path.relative_to(root))
    return sorted(path for path in paths if not any(parent in paths for parent in path.parents))


def pack(root, identity, directory, *, anchor=None, previous_index=None):
    runtime = producer_context(root, identity, allow_merged=True)
    require(actions.project_work(root) is not None, "preparation has no current build-work fact")
    require((root / ".lake/packages").is_dir() and (root / ".lake/build").is_dir(),
            "preparation native directories are unavailable")
    directory.mkdir(parents=True, exist_ok=True)
    layers = actions.LAYERS
    material = {}
    if anchor is not None:
        import lean_actions_shards as shards

        require(re.fullmatch(r"[0-9a-f]{40}", anchor), "sharded preparation requires a fixed dev history anchor")
        binding = shards.binding(root, "complete")
        previous = None
        if previous_index is not None:
            previous = shards.read_index(previous_index, binding, "complete")
            require(previous is not None and previous["owner"]["ref"] == identity["target_ref"],
                    "preparation base index belongs to a different target")
        index = shards.prepare(root, binding, "complete", previous, anchor, preparation=True)
        needed = set(index["entries"].values())
        payloads = directory / "shards"
        payloads.mkdir(exist_ok=True)
        for digest in sorted(needed):
            source = root / shards.transport_payload(digest)
            shutil.move(source, payloads / source.name)
        (directory / "project.json").write_text(json.dumps(index, separators=(",", ":")) + "\n")
        material = dict(referenced=0, bundled=len(needed),
                        bundled_bytes=sum(path.stat().st_size for path in payloads.iterdir()))
        layers = ("dependency",)
    with tarfile.open(directory / "native.tar.gz", "w:gz", compresslevel=1) as archive:
        for path in native_paths(root, layers=layers):
            archive.add(root / path, arcname=str(path))
    actions.write_small_record(directory / "preparation.json", dict(source=identity, runtime=runtime,
        partition=actions.partition_path(root), elan_key=actions.elan_key(root)))
    actions.output(dict(artifact_name=artifact_name(identity, sharded=anchor is not None),
                        artifact_path=str(directory)))
    return receipt("packed", identity, runtime=runtime, **material)


def artifact_metadata(repository, artifact_id, identity, runtime, *, sharded=None):
    artifact = api(repository, "actions/artifacts/" + str(artifact_id))
    variants = (False, True) if sharded is None else (sharded,)
    require(type(artifact["id"]) is int and artifact["id"] == artifact_id
            and artifact["name"] in {artifact_name(identity, sharded=variant) for variant in variants}
            and artifact["expired"] is False
            and str(artifact["workflow_run"]["id"]) == runtime["run"]
            and artifact["workflow_run"]["head_sha"] == runtime["sha"],
            "artifact is expired or does not bind the producer run")
    return artifact


def confirm(root, identity, artifact_id):
    runtime = producer_context(root, identity, allow_merged=True)
    artifact_metadata(identity["repository"], artifact_id, identity, runtime)
    return receipt("prepared", identity, runtime=runtime, artifact=artifact_id)


class InterruptedAssociationRead(ValueError):
    """The association page can be fetched again within its original deadline."""


def association_response(result):
    # gh prints the status line before the headers and body, including on HTTP errors.
    headers, separator, body = result.stdout.replace(b"\r\n", b"\n").partition(b"\n\n")
    status_line = re.fullmatch(rb"HTTP/\d+(?:\.\d+)? ([1-5]\d\d)(?: .*)?",
                              headers.split(b"\n", 1)[0])
    status = int(status_line[1]) if status_line else None
    if status in (500, 502, 503, 504):
        raise InterruptedAssociationRead(f"HTTP {status} (gh exit {result.returncode})")
    if status is not None and status != 200:
        raise ValueError(f"HTTP {status} (gh exit {result.returncode})")
    if result.returncode and (status == 200 or not result.stdout):
        transport = re.search(rb"(?:^|: )(unexpected EOF|connection reset by peer|i/o timeout|TLS handshake timeout)$",
                              result.stderr.strip())
        if transport:
            response = "HTTP 200" if status == 200 else "no HTTP status"
            raise InterruptedAssociationRead(f"{response} (gh exit {result.returncode}): {transport[1].decode('ascii')}")
    require(status is not None, f"no HTTP status (gh exit {result.returncode})")
    require(separator and not result.returncode, f"HTTP 200 response incomplete (gh exit {result.returncode})")
    if not body.strip():
        raise InterruptedAssociationRead("HTTP 200 with empty body")
    try:
        value = json.loads(body.decode("utf-8"))
    except json.JSONDecodeError as error:
        tail = error.doc[error.pos:].rstrip()
        if (not tail or error.msg.startswith("Unterminated string")
                or error.msg == "Expecting value" and any(word.startswith(tail) for word in ("true", "false", "null", "-"))):
            raise InterruptedAssociationRead("HTTP 200 with truncated JSON") from None
        raise ValueError(f"HTTP 200 with invalid JSON at character {error.pos}") from None
    except UnicodeDecodeError as error:
        if error.reason == "unexpected end of data" and error.end == len(body):
            raise InterruptedAssociationRead("HTTP 200 with truncated JSON encoding") from None
        raise ValueError("HTTP 200 with invalid JSON encoding") from None
    require(isinstance(value, list) and all(isinstance(pr, dict) for pr in value),
            "HTTP 200 with invalid API listing")
    return value


def association_page(repository, path, page):
    command = ["gh", "api", "repos/" + repository + "/" + path, "--include"]
    deadline = time.monotonic() + 60
    delay = 0.25
    for attempt in (1, 2):
        try:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise ValueError("page deadline exceeded")
            return association_response(subprocess.run(command, capture_output=True, timeout=remaining))
        except (InterruptedAssociationRead, subprocess.TimeoutExpired) as error:
            reason = "gh timed out" if isinstance(error, subprocess.TimeoutExpired) else str(error)
            detail = f"commit PR association page {page}, attempt {attempt}: {reason}"
            if attempt == 2 or time.monotonic() + delay >= deadline:
                raise ValueError(detail) from None
            print("PR_CACHE_RETRY " + detail, file=sys.stderr)
            time.sleep(delay)
        except ValueError as error:
            raise ValueError(f"commit PR association page {page}, attempt {attempt}: {error}") from None


def paged(repository, path, field=None, *, read_association=False):
    rows, page = [], 1
    while True:
        page_path = path + ("&" if "?" in path else "?") + urlencode(dict(per_page=100, page=page))
        value = association_page(repository, page_path, page) if read_association else api(repository, page_path)
        batch = value[field] if field else value
        require(isinstance(batch, list), "invalid API listing: " + path)
        rows.extend(batch)
        if len(batch) < 100:
            return rows
        page += 1


def consumer_context(root, *, require_pr_opt_in=False):
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
        if require_pr_opt_in and not any(label.get("name") == "lean-cache-produce"
                                         for label in pr.get("labels", [])):
            return None
        merged = False
    elif kind == "push" or kind == "workflow_dispatch" and actions.manual_source_is_valid():
        if kind == "push":
            require(checkout == os.environ["GITHUB_SHA"] == event["after"] and ref == event["ref"],
                    "target consumer event checkout mismatch")
        else:
            require(checkout == os.environ["STRATALINT_CACHE_CHECKED_OUT_SHA"], "manual consumer checkout mismatch")
        require(re.fullmatch(r"refs/heads/(dev|integration-[A-Za-z0-9._/-]+)", ref), "invalid target consumer ref")
        prs = paged(repository, "commits/" + checkout + "/pulls", read_association=True)
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
    command = ["gh", "api", "repos/" + repository + "/actions/artifacts/" + str(artifact_id) + "/zip"]
    for attempt in (1, 2):
        try:
            with destination.open("wb") as stream:
                subprocess.run(command, stdout=stream, stderr=subprocess.PIPE, check=True)
            return
        except subprocess.CalledProcessError as error:
            interrupted = re.search(
                rb"(?:^|: )(unexpected EOF|connection timed out|connection reset by peer|i/o timeout|TLS handshake timeout)$",
                (error.stderr or b"").strip(),
            )
            if attempt == 2 or interrupted is None:
                raise
            print(f"PR_CACHE_RETRY artifact {artifact_id}: {interrupted[1].decode('ascii')}", file=sys.stderr)


def validate_preparation(root, value, context, artifact, *, sharded=False):
    require(isinstance(value, dict) and set(value) == {"source", "runtime", "partition", "elan_key"},
            "invalid preparation identity fields")
    identity, runtime = validate_identity(value["source"]), value["runtime"]
    require(all(identity[key] == context[key] for key in ("repository", "pr", "head", "target_ref")),
            "preparation PR/head/target mismatch")
    require(isinstance(value["partition"], str) and
            re.fullmatch(r"[0-9a-f]{40}/[a-z0-9_]+-[a-z0-9_]+", value["partition"]) and
            isinstance(value["elan_key"], str) and
            re.fullmatch(r"elan-pinned-[a-z0-9_]+-[a-z0-9_]+-[0-9a-f]{64}", value["elan_key"]),
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
    artifact_metadata(repository, artifact["id"], identity, runtime, sharded=sharded)
    if run["status"] != "completed" or run["conclusion"] != "success":
        receipt("not-ready", identity, runtime=runtime, artifact=artifact["id"], reason="producer attempt has not succeeded")
        return None
    require(datetime.fromisoformat(run["run_started_at"].replace("Z", "+00:00")) <=
            datetime.fromisoformat(artifact["created_at"].replace("Z", "+00:00")) <=
            datetime.fromisoformat(run["updated_at"].replace("Z", "+00:00")),
            "artifact does not belong to producer attempt interval")
    target_head = validate_remote(identity, allow_merged=context["merged"])
    commit = api(repository, "git/commits/" + identity["merge"])
    require(commit["sha"] == identity["merge"] and [p["sha"] for p in commit["parents"]] ==
            [identity["base"], identity["head"]], "prepared M parents are not B,H")
    require_target_ancestor(repository, runtime["sha"], target_head, "producer runtime is outside target history")
    current = dict(partition=actions.partition_path(root), elan_key=actions.elan_key(root))
    prepared = {key: value[key] for key in current}
    if prepared != current:
        receipt("incompatible", identity, runtime=runtime, artifact=artifact["id"],
                reason="preparation native partition or toolchain mismatch", prepared=prepared, current=current)
        return None
    return identity, runtime


def unpack(root, archive_path, directory, *, dependency_only=False):
    names = set()
    files = []
    layers = ("dependency",) if dependency_only else actions.LAYERS
    directories = ("packages",) if dependency_only else ("packages", "build")
    allowed_roots = tuple(".lake/" + name for name in directories)

    def checked_members(archive):
        for member in archive:
            path = pathlib.PurePosixPath(member.name)
            require(member.name not in names, "duplicate native archive member")
            require(not path.is_absolute() and ".." not in path.parts and any(
                member.name == prefix or member.name.startswith(prefix + "/") for prefix in allowed_roots),
                "native archive member outside cache roots")
            names.add(member.name)
            if not member.isdir():
                files.append(pathlib.Path(member.name))
            yield member

    with tarfile.open(archive_path, "r:gz") as archive:
        archive.extractall(directory, members=checked_members(archive), filter="data")
    selected = set(native_paths(directory, root, layers))
    require(selected, "empty native preparation")
    for relative in files:
        require(relative in selected or any(parent in selected for parent in relative.parents),
                "native archive member outside registered membership: " + str(relative))
    for name in directories:
        source = directory / ".lake" / name
        require(source.is_dir() and not source.is_symlink(), "missing native preparation directory: " + name)


def install_native(root, directory):
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


def restore_project(root, directory, cache_action, identity, runtime):
    import lean_actions_shards as shards

    try:
        index = shards.read_index(directory / "project.json", shards.binding(root, "complete"), "complete")
    except shards.IncompatibleShardBinding:
        return False
    owner = dict(commit=identity["merge"], ref=identity["target_ref"], run=runtime["run"], attempt=runtime["attempt"])
    require(index is not None and index["owner"] == owner, "preparation index owner differs from validated source")
    packed = directory / "shards"
    expected = {digest + ".tar.gz" for digest in index["entries"].values()}
    bundled = {path.name for path in packed.iterdir()} if packed.is_dir() else set()
    require(bundled <= expected, "preparation contains an unreferenced shard")
    if bundled == expected:
        return shards.install(root, index, require_complete=True, preparation=directory,
                              payload_directory=packed)["complete"]
    # Earlier artifacts can still carry references to Actions cache entries.
    result = subprocess.run([*cache_action, "restore-preparation", str(directory)])
    if result.returncode == 3:
        return False
    result.check_returncode()
    return True


def adopt(root, cache_action=None, *, require_pr_opt_in=False):
    record = root / "build/lean-cache/pr-adopted.json"
    record.unlink(missing_ok=True)
    actions.output(dict(adopted=False))
    context = consumer_context(root, require_pr_opt_in=require_pr_opt_in)
    if context is None:
        reason = ("PR is not opted-in for preparation" if require_pr_opt_in
                  and os.environ["GITHUB_EVENT_NAME"] == "pull_request"
                  else "no matching merged PR at event checkout")
        return receipt("miss", None, reason=reason)
    repository = context["repository"]
    candidates = []
    variants = (True, False) if cache_action else (False,)
    for sharded in variants:
        name = artifact_name(context, sharded=sharded)
        rows = paged(repository, "actions/artifacts?" + urlencode(dict(name=name)), "artifacts")
        candidates.extend((row, sharded) for row in rows if row["name"] == name and row["expired"] is False)
    for artifact, sharded in sorted(candidates, key=lambda candidate: candidate[0]["id"], reverse=True):
        with tempfile.TemporaryDirectory(prefix="lean-pr-preparation-") as temporary:
            directory = pathlib.Path(temporary)
            artifact_zip = directory / "artifact.zip"
            download_started = time.monotonic()
            download(repository, artifact["id"], artifact_zip)
            downloaded_bytes = artifact_zip.stat().st_size
            download_seconds = time.monotonic() - download_started
            unpack_started = time.monotonic()
            with zipfile.ZipFile(artifact_zip) as archive:
                names = archive.namelist()
                native_members = {"native.tar.gz", "preparation.json"}
                require(sharded == ("project.json" in names) and len(set(names)) == len(names)
                    and native_members <= set(names) and all(
                    name in native_members or sharded and (name == "project.json"
                        or re.fullmatch(r"shards/[0-9a-f]{64}\.tar\.gz", name))
                    for name in names), "invalid preparation artifact members")
                archive.extractall(directory)
            # The native archive is the only input needed after validation.  Keep
            # the downloaded zip from occupying another full cache-sized copy
            # while the native payload is staged and unpacked.
            artifact_zip.unlink()
            value = json.loads((directory / "preparation.json").read_text())
            validated = validate_preparation(root, value, context, artifact, sharded=sharded)
            if validated is None:
                continue
            identity, runtime = validated
            if sharded and not restore_project(root, directory, cache_action, identity, runtime):
                receipt("unavailable", identity, runtime=runtime, artifact=artifact["id"],
                        reason="preparation project material is incompatible or unavailable")
                continue
            unpack(root, directory / "native.tar.gz", directory / "native", dependency_only=sharded)
            install_native(root, directory / "native")
            unpack_seconds = time.monotonic() - unpack_started
        actions.stamp_restored_dependency(root, actions.actions_keys(root))
        actions.write_small_record(record, dict(run=os.environ["GITHUB_RUN_ID"], attempt=os.environ["GITHUB_RUN_ATTEMPT"],
            repository=str(root.resolve()), checkout=context["checkout"], ref=os.environ["GITHUB_REF"],
            artifact=artifact["id"], merged=context["merged"]))
        actions.output(dict(adopted=True))
        if sharded:
            actions.output(dict(sharded=True))
        actions.output(dict(STRATALINT_ACTIONS_CACHE_SEEDED="0"), "GITHUB_ENV")
        return receipt("adopted", identity, runtime=runtime, artifact=artifact["id"],
                       downloaded_bytes=downloaded_bytes, download_seconds=round(download_seconds, 3),
                       unpack_seconds=round(unpack_seconds, 3),
                       checkout=context["checkout"], actual_merge=context["checkout"] if context["merged"] else None)
    return receipt("miss", context, reason="no unexpired preparation from a successful producer")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("dispatch", "prepare", "pack", "confirm", "adopt"))
    parser.add_argument("--repository", type=pathlib.Path, required=True)
    parser.add_argument("--directory", type=pathlib.Path)
    parser.add_argument("--artifact-id", type=int)
    parser.add_argument("--anchor")
    parser.add_argument("--previous-index", type=pathlib.Path)
    parser.add_argument("--cache-action", nargs=2)
    parser.add_argument("--require-pr-opt-in", action="store_true")
    args = parser.parse_args()
    try:
        root = args.repository.resolve()
        if args.command == "dispatch":
            dispatch(root)
        elif args.command == "adopt":
            adopt(root, args.cache_action, require_pr_opt_in=args.require_pr_opt_in)
        else:
            identity = validate_identity(json.loads(os.environ["PR_SOURCE"]))
            if args.command == "prepare":
                prepare(root, identity)
            elif args.command == "pack":
                require(args.directory is not None, "pack requires directory")
                require(args.previous_index is None or args.anchor is not None,
                        "a previous layout requires a sharded preparation")
                pack(root, identity, args.directory, anchor=args.anchor, previous_index=args.previous_index)
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
