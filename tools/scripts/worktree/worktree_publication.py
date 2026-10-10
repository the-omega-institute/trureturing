"""Ordinary checkpoints and non-force publication, using native Git objects."""

from contextlib import ExitStack
import os
from pathlib import Path

from worktree_protocol import (Refused, git, value, identity, tree_scope,
                               git_scope, acquire, remote_endpoint, read_input)


def confirm(root, remote, branch, commit, endpoint=None):
    endpoint = endpoint or remote_endpoint(root, remote, push=True)
    reference = "refs/heads/" + branch
    git(root, "check-ref-format", reference)
    advertised = git(root, "ls-remote", "--exit-code", "--heads", "--", endpoint, reference).stdout.splitlines()
    if len(advertised) != 1:
        raise Refused("remote_tip_unknown")
    tip, actual = advertised[0].split(b"\t")
    if os.fsdecode(actual) != reference:
        raise Refused("remote_identity")
    tip = tip.decode("ascii")
    # Fetch the observed object, without updating tracking refs or FETCH_HEAD.
    git(root, "fetch", "--no-write-fetch-head", "--no-tags", "--", endpoint, tip)
    if git(root, "merge-base", "--is-ancestor", commit, tip, check=False).returncode:
        raise Refused("remote_does_not_retain_commit:" + commit)
    return dict(remote=remote, endpoint=endpoint, branch=branch, required_commit=commit, observed_tip=tip,
                relation="equal" if commit == tip else "ancestor")


def commit_snapshot(path, metadata, branch, message):
    """Consume the ordinary index under the caller's Git operation scope."""
    if not branch.startswith("refs/heads/"):
        raise Refused("checkpoint_current_branch_required")
    if git(path, "ls-files", "--unmerged").stdout:
        raise Refused("unmerged_index")
    for marker in ("MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD", "rebase-merge", "rebase-apply", "sequencer"):
        if (metadata / marker).exists():
            raise Refused("unfinished_operation:" + marker)
    parent = value(path, "rev-parse", "--verify", "HEAD^{commit}")
    git(path, "add", "-A", "--", ".")
    difference = git(path, "diff", "--cached", "--quiet", "--exit-code", check=False)
    if difference.returncode not in (0, 1):
        raise Refused(difference.stderr.decode(errors="replace").strip() or "index_comparison_failed")
    if difference.returncode:
        git(path, "commit", "-F", "-", input=message)
    commit = value(path, "rev-parse", "HEAD")
    return dict(event="worktree_checkpoint", status="committed" if difference.returncode else "unchanged",
                commit=commit, parent=parent, branch=branch)


def checkpoint(options):
    with ExitStack() as stack:
        path = tree_scope(stack, options.source, options.path)
        _, metadata = identity(options.source, path)
        branch = git_scope(stack, options.source, path)
        message = (read_input(options.source, options.message_file) if options.message_file
                   else b"Checkpoint working tree before publication\n")
        return commit_snapshot(path, metadata, branch, message)


def publish(options):
    with ExitStack() as stack:
        path = tree_scope(stack, options.source, options.path)
        identity(options.source, path)
        branch = git_scope(stack, options.source, path)
        actual_branch = branch.removeprefix("refs/heads/")
        if options.branch != actual_branch:
            raise Refused("publication_branch_mismatch")
        commit = value(path, "rev-parse", "--verify", options.commit + "^{commit}")
        if git(path, "merge-base", "--is-ancestor", commit, "HEAD", check=False).returncode:
            raise Refused("publication_commit_outside_branch")
        endpoint = remote_endpoint(path, options.remote, push=True)
        # A newer remote tip already retaining this unit is sufficient; no rewind.
        try:
            evidence = confirm(path, options.remote, options.branch, commit, endpoint)
        except Refused:
            git(path, "push", "--", endpoint, commit + ":refs/heads/" + options.branch)
            evidence = confirm(path, options.remote, options.branch, commit, endpoint)
        return dict(event="worktree_publication", status="confirmed", **evidence)


def finalize(options):
    # Job creation, descendant ownership and joining belong to the host. This
    # synchronous command runs only after the owning host has joined its handles.
    # Other participants keep their shared entry and independent edit scopes.
    if not options.writers_joined:
        raise Refused("host_must_join_task_writers")
    result = checkpoint(options)
    options.commit = result["commit"]
    return publish(options)


def prepare_mirror(options):
    """Producer-owned temporary checkout operation; failure leaves its source."""
    import uuid
    with ExitStack() as stack:
        endpoint = remote_endpoint(options.source, options.remote, push=True)
        if options.path.exists() or options.path.is_symlink():
            raise Refused("mirror_destination_occupied")
        path = tree_scope(stack, options.source, options.path, True)
        reference = "refs/heads/" + options.branch
        git(options.source, "check-ref-format", reference)
        acquire(stack, options.source, "ref:" + reference, True)
        existing = git(options.source, "rev-parse", "--verify", reference, check=False)
        args = [] if existing.returncode == 0 else ["-b", options.branch]
        token = "worktree-init:" + uuid.uuid4().hex
        git(options.source, "worktree", "add", "--lock", "--reason", token,
            *args, path, options.branch if not args else options.base)
        _, metadata = identity(options.source, path)
        acquire(stack, options.source, "index:" + str(metadata), True)
        if value(path, "rev-parse", "HEAD") == value(options.source, "rev-parse", options.base):
            git(path, "merge", "--no-ff", "-m", options.message, options.merge)
        head = value(path, "rev-parse", "HEAD")
        parents = value(path, "show", "-s", "--format=%P", head).split()
        if len(parents) != 2 or parents[1] != options.merge or value(path, "show", "-s", "--format=%s", head) != options.message:
            raise Refused("mirror_identity_changed")
        if git(path, "merge-base", "--is-ancestor", parents[0], options.base, check=False).returncode:
            raise Refused("mirror_base_outside_integration")
        git(path, "push", "--", endpoint, head + ":" + reference)
        evidence = confirm(path, options.remote, options.branch, head, endpoint)
        if (metadata / "locked").read_text().strip() != token:
            raise Refused("mirror_initialization_identity_changed")
        git(options.source, "worktree", "unlock", path)
        return dict(event="worktree_mirror", status="confirmed", commit=head, **evidence)
