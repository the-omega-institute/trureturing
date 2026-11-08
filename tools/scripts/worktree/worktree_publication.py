"""Ordinary checkpoints and publication using native Git objects."""
import json
import os
from pathlib import Path

from worktree_protocol import (Refused, GitFailure, git, identity, inventory,
                               remote_endpoint, read_input, value)


def confirm(root, remote, branch, commit, endpoint=None):
    endpoint = endpoint or remote_endpoint(root, remote, push=True)
    reference = "refs/heads/" + branch
    git(root, "check-ref-format", reference)
    advertised = git(root, "ls-remote", "--exit-code", "--heads", "--", endpoint,
                     reference).stdout.splitlines()
    if len(advertised) != 1:
        raise Refused("remote_tip_unknown")
    tip, actual = advertised[0].split(b"\t")
    if os.fsdecode(actual) != reference:
        raise Refused("remote_identity")
    tip = tip.decode("ascii")
    git(root, "fetch", "--no-write-fetch-head", "--no-tags", "--", endpoint, tip)
    if git(root, "merge-base", "--is-ancestor", commit, tip, check=False).returncode:
        raise Refused("remote_does_not_retain_commit:" + commit)
    return dict(remote=remote, endpoint=endpoint, branch=branch,
                required_commit=commit, observed_tip=tip,
                relation="equal" if commit == tip else "ancestor")


def ordinary_snapshot(path, metadata, branch, message):
    del metadata
    if git(path, "ls-files", "--unmerged").stdout:
        raise Refused("unmerged_index")
    parent = value(path, "rev-parse", "--verify", "HEAD^{commit}")
    git(path, "add", "-A", "--", ".")
    difference = git(path, "diff", "--cached", "--quiet", "--exit-code", check=False)
    if difference.returncode not in (0, 1):
        raise GitFailure(difference.stderr.decode(errors="replace").strip() or "index_comparison_failed")
    if difference.returncode:
        git(path, "commit", "-F", "-", input=message)
    commit = value(path, "rev-parse", "HEAD")
    return dict(event="worktree_checkpoint", status="committed" if difference.returncode else "unchanged",
                commit=commit, parent=parent, branch=branch)


def commit_snapshot(path, metadata, branch, message, stack=None, source=None):
    del stack, source
    return ordinary_snapshot(path, metadata, branch, message)


def checkpoint(options):
    path = Path(options.path).resolve()
    item, metadata = identity(options.source, path)
    branch = item.get("branch")
    if not branch or branch == "HEAD":
        raise Refused("checkpoint_current_branch_required")
    message = (read_input(options.source, options.message_file)
               if options.message_file else b"Checkpoint working tree before publication\n")
    return commit_snapshot(path, metadata, branch, message)


def publish(options):
    path = Path(options.path).resolve()
    item, _ = identity(options.source, path)
    actual = item.get("branch", "").removeprefix("refs/heads/")
    if options.branch != actual:
        raise Refused("publication_branch_mismatch")
    commit = value(path, "rev-parse", "--verify", options.commit + "^{commit}")
    if git(path, "merge-base", "--is-ancestor", commit, "HEAD", check=False).returncode:
        raise Refused("publication_commit_outside_branch")
    endpoint = remote_endpoint(path, options.remote, push=True)
    try:
        evidence = confirm(path, options.remote, options.branch, commit, endpoint)
    except Refused:
        git(path, "push", "--", endpoint, commit + ":refs/heads/" + options.branch)
        evidence = confirm(path, options.remote, options.branch, commit, endpoint)
    return dict(event="worktree_publication", status="confirmed", **evidence)


def finalize(options):
    result = checkpoint(options)
    options.commit = result["commit"]
    return publish(options)


def validate_mirror(root, head, integration_tip, landing, message):
    head = value(root, "rev-parse", "--verify", head + "^{commit}")
    landing = value(root, "rev-parse", "--verify", landing + "^{commit}")
    parents = value(root, "show", "-s", "--format=%P", head).split()
    if len(parents) != 1:
        raise Refused("mirror_requires_single_parent:" + head)
    original = value(root, "show", "-s", "--format=%(trailers:key=Original-Dev-Commit,valueonly)", head)
    if original != landing or value(root, "show", "-s", "--format=%s", head) != message:
        raise Refused("mirror_identity_changed:" + head)
    if git(root, "merge-base", "--is-ancestor", parents[0], integration_tip, check=False).returncode:
        raise Refused("mirror_base_outside_integration:" + head)
    return dict(commit=head, base=parents[0], original_commit=landing)


def prepare_mirror(options):
    # Mirror callers retain their source/pin/publication checks; temporary
    # checkout allocation uses ordinary native Git registration.
    endpoint = remote_endpoint(options.source, options.remote, push=True)
    path = Path(options.path)
    if path.exists() or path.is_symlink():
        raise Refused("mirror_destination_occupied")
    reference = "refs/heads/" + options.branch
    git(options.source, "check-ref-format", reference)
    existing = git(options.source, "rev-parse", "--verify", reference, check=False)
    args = [] if existing.returncode == 0 else ["-b", options.branch]
    git(options.source, "worktree", "add", "--no-checkout", *args, "--", path,
        options.branch if not args else options.base)
    from worktree_agent_state import record
    record(options.source, path, created=True, branch=reference)
    git(path, "reset", "--hard", "--no-recurse-submodules", "HEAD")
    identity(options.source, path)
    landing = value(path, "rev-parse", "--verify", options.merge + "^{commit}")
    if value(path, "rev-parse", "HEAD") == value(options.source, "rev-parse", options.base):
        parents = value(path, "show", "-s", "--format=%P", landing).split()
        mainline = ["--mainline", "1"] if len(parents) > 1 else []
        git(path, "cherry-pick", "--no-commit", *mainline, landing)
        git(path, "commit", "--allow-empty", "-m", options.message +
            "\n\nOriginal-Dev-Commit: " + landing)
    head = value(path, "rev-parse", "HEAD")
    validate_mirror(path, head, options.base, landing, options.message)
    git(path, "push", "--", endpoint, head + ":" + reference)
    evidence = confirm(path, options.remote, options.branch, head, endpoint)
    return dict(event="worktree_mirror", status="confirmed", commit=head, **evidence)
