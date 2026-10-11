"""User-directed worktree removal and independent non-worktree retention policies."""

from contextlib import ExitStack
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from worktree_protocol import (Refused, git, value, common, inventory, identity,
                               acquire, git_scope, remote_endpoint)


def remote_roots(source, branch):
    roots = []
    for remote in value(source, "remote").splitlines():
        endpoint = remote_endpoint(source, remote)
        refs = ["refs/heads/dev"]
        if branch:
            refs.append(branch)
        result = git(source, "ls-remote", "--heads", "--", endpoint, *refs)
        for row in result.stdout.splitlines():
            oid, reference = row.split(b"\t")
            if os.fsdecode(reference) not in refs:
                raise Refused("unexpected_remote_ref")
            tip = oid.decode("ascii")
            git(source, "fetch", "--no-write-fetch-head", "--no-tags", "--", endpoint, tip)
            roots.append(tip)
    if not roots:
        raise Refused("remote_preservation_unknown")
    return roots


def retained(source, oid, roots):
    if not oid or set(oid) == {"0"}:
        return
    if git(source, "cat-file", "-t", oid).stdout.strip() != b"commit":
        raise Refused("noncommit_recovery_object:" + oid)
    if not any(git(source, "merge-base", "--is-ancestor", oid, root, check=False).returncode == 0
               for root in roots):
        raise Refused("local_only_history:" + oid)


def reflog_oids(path):
    for line in path.read_bytes().splitlines():
        fields = line.split(b" ", 2)
        if len(fields) != 3 or not all(re.fullmatch(rb"[0-9a-f]{40}|[0-9a-f]{64}", field)
                                      for field in fields[:2]):
            raise Refused("unknown_reflog:" + str(path))
        yield from (field.decode("ascii") for field in fields[:2])


LOCK_AGE_SECONDS = 24 * 60 * 60


def qualify(source, path):
    """Validate identity and Git lock age, without inspecting users or contents."""
    if Path(path).is_symlink():
        raise Refused("linked_tree")
    path = Path(path).resolve()
    item, metadata = identity(source, path)
    rows = inventory(source)
    if path == Path(rows[0]["worktree"]).resolve():
        raise Refused("main_worktree")
    if any(path in Path(row["worktree"]).resolve().parents for row in rows):
        raise Refused("nested_worktree")
    if "locked" in item:
        lock = metadata / "locked"
        if lock.is_symlink() or not lock.is_file():
            raise Refused("locked_age_unknown")
        age = time.time() - lock.stat().st_mtime
        if age < LOCK_AGE_SECONDS:
            raise Refused("locked_recent")
    return item


def remove(options):
    names = list(dict.fromkeys(options.names.split()))
    if not names and not options.path:
        raise Refused("names_or_paths_required")
    rows = inventory(options.source)
    source = Path(rows[0]["worktree"]).resolve()
    targets = []
    for name in names:
        matches = [row for row in rows if Path(row["worktree"]).name == name]
        if len(matches) != 1:
            raise Refused("name_not_found_or_ambiguous:" + name)
        targets.append(Path(matches[0]["worktree"]))
    for path in options.path:
        if path.is_symlink():
            raise Refused("linked_tree")
        matches = [row for row in rows if Path(row["worktree"]).resolve() == path.resolve()]
        if len(matches) != 1:
            raise Refused("path_not_registered:" + str(path))
        targets.append(Path(matches[0]["worktree"]))
    targets = list(dict.fromkeys(targets))
    outcomes = []
    # Resolve and preflight the entire batch before any checkpoint mutation.
    qualified = {}
    for target in targets:
        item = qualify(source, target)
        expected_rows = [json.loads(raw) for raw in options.expected]
        matches = [row for row in expected_rows if Path(row["path"]).resolve() == target.resolve()]
        if expected_rows and len(matches) != 1:
            raise Refused("observed_path_changed")
        for expected in matches:
            if (item.get("HEAD") != expected["head"] or item.get("branch") != expected.get("branch")
                    or "locked" in expected and item.get("locked") != expected["locked"]):
                raise Refused("observed_identity_changed")
        qualified[target] = item
    for target in targets:
        if options.preview:
            outcomes.append(dict(path=str(target), outcome="would_remove"))
            continue
        checkpoint = None
        removing = False
        try:
            with ExitStack() as stack:
                # Only the compound Git operation is coordinated. No entry,
                # activity, file-use or cache-use lock qualifies disposal.
                branch = git_scope(stack, source, target)
                if qualify(source, target) != qualified[target]:
                    raise Refused("observed_identity_changed")
                _, metadata = identity(source, target)
                from worktree_publication import commit_snapshot
                checkpoint = commit_snapshot(target, metadata, branch,
                    b"Checkpoint working tree before recycling\n")
                refreshed = qualify(source, target)
                expected = dict(qualified[target], HEAD=checkpoint["commit"])
                if refreshed != expected:
                    raise Refused("observed_identity_changed_after_checkpoint")
                # Concurrent edits or hook changes after staging need another
                # snapshot; do not silently discard ordinary outstanding files.
                if git(target, "status", "--porcelain", "--untracked-files=all").stdout:
                    raise Refused("working_tree_changed_after_checkpoint")
                flags = ["--force", "--force"] if "locked" in refreshed else ["--force"]
                removing = True
                git(source, "worktree", "remove", *flags, "--", target,
                    timeout=None if options.force else 300)
                outcomes.append(dict(path=str(target), outcome="removed", checkpoint=checkpoint,
                                     recovery_branch=branch))
        except (Refused, OSError, subprocess.SubprocessError) as error:
            outcomes.append(dict(path=str(target),
                outcome="partial_or_indeterminate" if removing else "checkpoint_failed",
                error=str(error), checkpoint=checkpoint))

    return dict(event="worktree_removal", items=outcomes,
                status="failed" if any(item["outcome"] not in ("removed", "would_remove") for item in outcomes) else "succeeded")


def retire_branch(options):
    reference = "refs/heads/" + options.branch
    git(options.source, "check-ref-format", reference)
    with ExitStack() as stack:
        acquire(stack, options.source, "ref:" + reference, True)
        if any(row.get("branch") == reference for row in inventory(options.source)):
            raise Refused("branch_in_use")
        current = value(options.source, "rev-parse", "--verify", reference)
        if current != options.commit:
            raise Refused("branch_identity_changed")
        if value(options.source, "for-each-ref", "--format=%(symref)", reference):
            raise Refused("symbolic_branch")
        roots = remote_roots(options.source, reference)
        retained(options.source, current, roots)
        log = common(options.source) / "logs" / reference
        if options.expected_reflog_sha256 is not None:
            if (not re.fullmatch(r"[0-9a-f]{64}", options.expected_reflog_sha256)
                    or not log.is_file() or log.is_symlink()
                    or hashlib.sha256(log.read_bytes()).hexdigest() != options.expected_reflog_sha256):
                raise Refused("branch_reflog_changed")
        if log.exists():
            for oid in set(reflog_oids(log)):
                retained(options.source, oid, roots)
        if not options.preview:
            try:
                git(options.source, "update-ref", "--no-deref", "-d", reference, current)
            except (Refused, OSError, subprocess.SubprocessError) as error:
                return dict(event="worktree_branch_retirement", branch=options.branch, commit=current,
                            status="partial_or_indeterminate", error=str(error))
        return dict(event="worktree_branch_retirement", branch=options.branch, commit=current,
                    status="would_remove" if options.preview else "removed")
