"""Attributed checkpoints and non-force publication, using native Git objects."""

from contextlib import ExitStack
import json
import os
from pathlib import Path
import subprocess
import tempfile

from worktree_protocol import (Refused, git, value, identity, tree_scope,
                               path_scopes, git_scope, acquire)


def confirm(root, remote, branch, commit):
    reference = "refs/heads/" + branch
    git(root, "check-ref-format", reference)
    advertised = git(root, "ls-remote", "--exit-code", "--heads", remote, reference).stdout.splitlines()
    if len(advertised) != 1:
        raise Refused("remote_tip_unknown")
    tip, actual = advertised[0].split(b"\t")
    if os.fsdecode(actual) != reference:
        raise Refused("remote_identity")
    tip = tip.decode("ascii")
    # Fetch the observed object, without updating tracking refs or FETCH_HEAD.
    git(root, "fetch", "--no-write-fetch-head", "--no-tags", remote, tip)
    if git(root, "merge-base", "--is-ancestor", commit, tip, check=False).returncode:
        raise Refused("remote_does_not_retain_commit:" + commit)
    return dict(remote=remote, branch=branch, required_commit=commit, observed_tip=tip,
                relation="equal" if commit == tip else "ancestor")


def checkpoint(options):
    with ExitStack() as stack:
        path = tree_scope(stack, options.source, options.path)
        _, metadata = identity(options.source, path)
        paths = options.write
        if not options.message_file:
            raise Refused("checkpoint_message_required")
        if not paths or any(name in (".", "") for name in paths):
            raise Refused("explicit_checkpoint_paths_required")
        path_scopes(stack, options.source, path, options.read, paths)
        branch = git_scope(stack, options.source, path)
        if git(path, "ls-files", "--unmerged").stdout:
            raise Refused("unmerged_index")
        for marker in ("MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD", "rebase-merge", "rebase-apply"):
            if (metadata / marker).exists():
                raise Refused("unfinished_operation:" + marker)
        parent = value(path, "rev-parse", "HEAD")
        # This index is crash recovery material until deleted by this invocation.
        fd, index = tempfile.mkstemp(prefix="checkpoint-index-", dir=metadata)
        os.close(fd)
        os.unlink(index)
        env = dict(GIT_INDEX_FILE=index, GIT_LITERAL_PATHSPECS="1")
        completed = False
        try:
            git(path, "read-tree", parent, env=env)
            git(path, "add", "-A", "--", *paths, env=env)
            tree = value_with_env(path, env, "write-tree")
            if tree == value(path, "rev-parse", parent + "^{tree}"):
                completed = True
                return dict(event="worktree_checkpoint", status="unchanged", commit=parent)
            message = Path(options.message_file).read_bytes()
            commit = git(path, "commit-tree", tree, "-p", parent, env=env, input=message).stdout.decode().strip()
            git(path, "update-ref", "-m", "worktree checkpoint", branch, commit, parent)
            # Update only attributed entries. Native index locking preserves concurrent
            # insertions outside this scope even from an ordinary git add.
            old = git(path, "ls-files", "-z", "--", *paths, env=dict(GIT_LITERAL_PATHSPECS="1")).stdout
            zero = "0" * len(parent)
            deletions = b"".join(b"0 " + zero.encode() + b"\t" + name + b"\0"
                                 for name in old.split(b"\0") if name)
            entries = git(path, "ls-files", "--stage", "-z", "--", *paths, env=env).stdout
            git(path, "update-index", "-z", "--index-info", input=deletions + entries)
            completed = True
            return dict(event="worktree_checkpoint", status="committed", commit=commit,
                        parent=parent, branch=branch, paths=paths)
        finally:
            # Failure retains the private index as native Git recovery material.
            # Only a completely acknowledged checkpoint removes its own files.
            if completed:
                for candidate in (index, index + ".lock"):
                    if os.path.exists(candidate):
                        os.unlink(candidate)


def value_with_env(root, env, *arguments):
    return git(root, *arguments, env=env).stdout.decode().strip()


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
        # A newer remote tip already retaining this unit is sufficient; no rewind.
        try:
            evidence = confirm(path, options.remote, options.branch, commit)
        except Refused:
            git(path, "push", "--", options.remote, commit + ":refs/heads/" + options.branch)
            evidence = confirm(path, options.remote, options.branch, commit)
        return dict(event="worktree_publication", status="confirmed", **evidence)


def finalize(options):
    # Job creation, descendant ownership and joining belong to the host. This
    # synchronous command runs only after the owning host has joined its handles.
    # Other participants keep their shared entry and independent edit scopes.
    if not options.writers_joined:
        raise Refused("host_must_join_task_writers")
    if options.write:
        result = checkpoint(options)
        options.commit = result["commit"]
    return publish(options)


def prepare_mirror(options):
    """Producer-owned temporary checkout operation; failure leaves its source."""
    import uuid
    with ExitStack() as stack:
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
        git(path, "push", "--", options.remote, head + ":" + reference)
        evidence = confirm(path, options.remote, options.branch, head)
        if (metadata / "locked").read_text().strip() != token:
            raise Refused("mirror_initialization_identity_changed")
        git(options.source, "worktree", "unlock", path)
        return dict(event="worktree_mirror", status="confirmed", commit=head, **evidence)
