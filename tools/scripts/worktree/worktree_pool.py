"""Native idle branches, bounded retention, merged-task return and atomic claim."""

from contextlib import ExitStack
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
from types import SimpleNamespace
import uuid

from worktree_protocol import (Refused, acquire, common, git, git_environment, git_scope,
                               identity, inventory, remote_endpoint, scope_fds, tree_scope, value)
from worktree_publication import commit_snapshot, confirm
from worktree_preservation import qualify, remove

IDLE_PREFIX = "refs/heads/lane/governance/idle-"
IDLE_CAPACITY = 4
PINS = ("lean-toolchain", "lake-manifest.json")
OPERATIONS = ("MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD", "rebase-merge", "rebase-apply", "sequencer")


def idle_reference(reference):
    return reference.startswith(IDLE_PREFIX) and len(reference) > len(IDLE_PREFIX)


def clean(path, metadata):
    for marker in OPERATIONS:
        if (metadata / marker).exists():
            raise Refused("unfinished_operation:" + marker)
    if git(path, "status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none").stdout:
        raise Refused("idle_dirty")


def idle_state(source, path, dev):
    item = qualify(source, path)
    _, metadata = identity(source, path)
    if "locked" in item:
        raise Refused("idle_locked")
    reference = item.get("branch", "")
    if not idle_reference(reference):
        raise Refused("not_idle")
    head = value(path, "rev-parse", "--verify", "HEAD^{commit}")
    if item.get("HEAD") != head or value(path, "rev-parse", "--verify", reference) != head:
        raise Refused("idle_identity_changed")
    clean(path, metadata)
    if git(path, "merge-base", "--is-ancestor", head, dev, check=False).returncode:
        raise Refused("idle_outside_dev")
    log = common(source) / "logs" / reference
    if log.is_symlink():
        raise Refused("idle_creation_unknown")
    rows = log.read_bytes().splitlines()
    if not rows:
        raise Refused("idle_creation_unknown")
    fields, _ = rows[0].split(b"\t", 1)
    old, new, rest = fields.split(b" ", 2)
    timestamp = int(rest.rsplit(b" ", 2)[1])
    if old != b"0" * len(head) or new.decode("ascii") != head or not 0 <= timestamp <= time.time():
        raise Refused("idle_creation_unknown")
    return dict(path=str(Path(path).resolve()), branch=reference, head=head, created=timestamp)


def available_fraction(source):
    disk = shutil.disk_usage(source)
    return disk.free / disk.total


def sweep_locked(source, dev, force=False):
    """The caller holds the clone's pool operation scope."""
    source = Path(inventory(source)[0]["worktree"])
    candidates, outcomes = [], []
    for item in inventory(source):
        if not idle_reference(item.get("branch", "")):
            continue
        path = Path(item["worktree"])
        try:
            with ExitStack() as stack:
                tree_scope(stack, source, path, True)
                git_scope(stack, source, path)
                candidates.append(idle_state(source, path, dev))
        except (Refused, OSError, ValueError) as error:
            outcomes.append(dict(path=str(path), branch=item.get("branch"), head=item.get("HEAD"),
                                 outcome="retained", reason=str(error)))
    candidates.sort(key=lambda row: (row["created"], row["path"]))
    remaining = len(candidates)
    for observed in candidates:
        pressure = available_fraction(source) < 0.05
        reason = "idle_disk_pressure" if pressure else "idle_capacity" if remaining > IDLE_CAPACITY else "idle_pool"
        if reason == "idle_pool":
            outcomes.append(dict(observed, outcome="retained", reason=reason))
            continue
        path = Path(observed["path"])
        try:
            with ExitStack() as stack:
                tree_scope(stack, source, path, True)
                current = idle_state(source, path, dev)
                if current != observed:
                    raise Refused("idle_identity_changed")
                # Common removal owns the index/ref scopes and snapshot rules.
                result = remove(SimpleNamespace(source=source, names="", path=[path], force=False,
                    preview=not force, expected=[json.dumps(dict(path=str(path), head=observed["head"],
                                                               branch=observed["branch"]))]))
                removal = result["items"][0]
                if removal["outcome"] not in ("removed", "would_remove"):
                    raise Refused(removal.get("error", "idle_removal_failed"))
                remaining -= 1
                outcomes.append(dict(observed, outcome=removal["outcome"], reason=reason))
        except (Refused, OSError, ValueError) as error:
            outcomes.append(dict(observed, outcome="retained", reason=str(error)))
    return dict(event="worktree_pool", capacity=IDLE_CAPACITY, items=outcomes)


def sweep(source, dev, force=False):
    with ExitStack() as stack:
        acquire(stack, source, "operation:idle-pool", True)
        return sweep_locked(source, dev, force)


def pr_evidence(path, number):
    if number <= 0:
        raise Refused("pr_number_required")
    result = subprocess.run(["gh", "pr", "view", str(number), "--json",
                             "state,baseRefName,headRefName,headRefOid,mergeCommit,autoMergeRequest"],
                            cwd=path, env=git_environment(), pass_fds=scope_fds(),
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False, timeout=300)
    if result.returncode:
        raise Refused("pr_evidence_unavailable:" + result.stderr.decode(errors="replace").strip())
    evidence = json.loads(result.stdout)
    if evidence.get("state") != "MERGED":
        reason = ("pr_closed_not_merged" if evidence.get("state") == "CLOSED" else
                  "pr_auto_merge_pending" if evidence.get("autoMergeRequest") is not None else
                  "pr_open_not_merged" if evidence.get("state") == "OPEN" else "pr_state_unknown")
        raise Refused(reason)
    if evidence.get("baseRefName") != "dev":
        raise Refused("pr_base_mismatch")
    merge = (evidence.get("mergeCommit") or {}).get("oid")
    if not merge:
        raise Refused("pr_merge_commit_missing")
    for oid in (merge, evidence.get("headRefOid", "")):
        if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", oid):
            raise Refused("pr_commit_invalid")
    return evidence


def return_tree(options):
    if not options.writers_joined:
        raise Refused("host_must_join_task_writers")
    with ExitStack() as stack:
        acquire(stack, options.source, "operation:idle-pool", True)
        result = returned_snapshot(options)
        result["pool"] = sweep_locked(options.source, result["dev_commit"], True)
        return result


def returned_snapshot(options):
    with ExitStack() as stack:
        if options.path.is_symlink():
            raise Refused("linked_tree")
        path = tree_scope(stack, options.source, options.path, True)
        item = qualify(options.source, path)
        if "locked" in item:
            raise Refused("intentional_or_initialization_lock")
        _, metadata = identity(options.source, path)
        branch = git_scope(stack, options.source, path)
        evidence = pr_evidence(path, options.pr)
        endpoint = remote_endpoint(path, "origin", push=True)
        remote = confirm(path, "origin", "dev", evidence["mergeCommit"]["oid"], endpoint)
        dev = remote["observed_tip"]
        already = idle_reference(branch)
        task = "refs/heads/" + evidence["headRefName"]
        if already:
            idle_state(options.source, path, dev)
            acquire(stack, options.source, "ref:" + task, True)
            tip = value(path, "rev-parse", "--verify", "--end-of-options", task + "^{commit}")
        else:
            if branch != task:
                raise Refused("pr_head_mismatch")
            tip = value(path, "rev-parse", "HEAD")
        if git(path, "merge-base", "--is-ancestor", evidence["headRefOid"], tip, check=False).returncode:
            raise Refused("pr_head_outside_tree")
        if already and value(path, "rev-parse", "HEAD") == dev:
            return dict(event="worktree_return", status="already_idle", path=str(path), dev_commit=dev,
                        task_branch=task, idle_branch=branch)
        if not branch.startswith("refs/heads/"):
            raise Refused("return_current_branch_required")
        checkpoint = commit_snapshot(path, metadata, branch, b"Checkpoint post-merge working tree before return\n")
        clean(path, metadata)
        outstanding = value(path, "rev-list", dev + ".." + checkpoint["commit"]).splitlines()
        idle = IDLE_PREFIX + uuid.uuid4().hex
        acquire(stack, options.source, "ref:" + idle, True)
        git(path, "-c", "core.logAllRefUpdates=true", "switch", "--no-overwrite-ignore", "--no-track", "-c", idle.removeprefix("refs/heads/"), dev)
        idle_state(options.source, path, dev)
        if already:
            git(path, "update-ref", "-d", branch, checkpoint["commit"])
        return dict(event="worktree_return", status="returned", path=str(path), dev_commit=dev,
                    task_branch=task, idle_branch=idle, checkpoint=checkpoint,
                    commits_not_in_dev=outstanding, remote=remote)


def allocation_record(path, metadata, commit):
    timestamp = int(time.time())
    message = "worktree-allocation:" + uuid.uuid4().hex
    git(path, "-c", "core.logAllRefUpdates=true", "update-ref", "-m", message, "HEAD", commit, commit,
        env={"GIT_COMMITTER_DATE": "@" + str(timestamp) + " +0000"})
    fields, actual = (metadata / "logs/HEAD").read_bytes().splitlines()[-1].split(b"\t", 1)
    old, new, rest = fields.split(b" ", 2)
    if (old.decode("ascii") != commit or new.decode("ascii") != commit
            or int(rest.rsplit(b" ", 2)[1]) != timestamp or actual.decode("ascii") != message):
        raise Refused("allocation_record_verification_failed")
    return timestamp


def claim(options):
    with ExitStack() as pool_scope:
        acquire(pool_scope, options.source, "operation:idle-pool", True)
        rows = inventory(options.source)
        candidates = ([options.path] if options.path else
                      [Path(row["worktree"]) for row in rows if idle_reference(row.get("branch", ""))])
        if not candidates:
            return dict(event="worktree_init", status="no_idle")
        base = value(options.source, "rev-parse", "--verify", "--end-of-options", options.base + "^{commit}")
        # Idle state is relative to dev, independently of the requested base.
        dev = value(options.source, "rev-parse", "--verify", "refs/remotes/origin/dev^{commit}")
        expected = {pin: git(options.source, "show", base + ":" + pin).stdout for pin in PINS}
        reference = "refs/heads/" + options.branch
        git(options.source, "check-ref-format", reference)
        for candidate in candidates:
            allocated_branch = False
            try:
                with ExitStack() as stack:
                    if candidate.is_symlink():
                        raise Refused("linked_tree")
                    path = tree_scope(stack, options.source, candidate, True)
                    tip = value(path, "rev-parse", "--verify", "HEAD^{commit}")
                    if git(path, "merge-base", "--is-ancestor", tip, dev, check=False).returncode:
                        dev = confirm(path, "origin", "dev", tip)["observed_tip"]
                    state = idle_state(options.source, path, dev)
                    _, metadata = identity(options.source, path)
                    git_scope(stack, options.source, path)
                    acquire(stack, options.source, "ref:" + reference, True)
                    if (path / ".lake").is_symlink():
                        raise Refused("linked_cache")
                    for pin in PINS:
                        if (path / pin).read_bytes() != expected[pin]:
                            raise Refused("incompatible_pin:" + pin)
                    # Native branch creation preserves Git's tracking policy.
                    # Compare with the pinned object before switching the tree.
                    git(path, "-c", "core.logAllRefUpdates=true", "branch", "--", options.branch, options.base)
                    allocated_branch = True
                    if value(path, "rev-parse", "--verify", reference) != base:
                        raise Refused("claim_base_changed")
                    git(path, "switch", "--no-overwrite-ignore", "--", options.branch)
                    attached, _ = identity(options.source, path)
                    if attached.get("branch") != reference or attached.get("HEAD") != base:
                        raise Refused("claim_identity_changed")
                    allocated = allocation_record(path, metadata, base)
                    git(path, "update-ref", "-d", state["branch"], state["head"])
                    scaffold = path / ".gitignore"
                    content = scaffold.read_text() if scaffold.exists() else ""
                    missing = [pattern for pattern in (".caller-review-prompt.md", ".echo-review.md", ".sshx-*")
                               if pattern not in content.splitlines()]
                    if missing:
                        with scaffold.open("a") as output:
                            output.write(("\n" if content and not content.endswith("\n") else "") + "\n".join(missing) + "\n")
                    if not options.skip_restore:
                        result = subprocess.run(["dotnet", "restore", "tools/StrataLint.sln", "--locked-mode"],
                            cwd=path, env=git_environment(), pass_fds=scope_fds(), stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=1800, check=False)
                        if result.returncode:
                            raise Refused("claim_restore_failed:" + result.stderr.decode(errors="replace"))
                    attached, _ = identity(options.source, path)
                    if attached.get("branch") != reference or attached.get("HEAD") != base:
                        raise Refused("claim_identity_changed")
                    for pin in PINS:
                        if (path / pin).read_bytes() != expected[pin]:
                            raise Refused("claim_pin_changed:" + pin)
                    for marker in OPERATIONS:
                        if (metadata / marker).exists():
                            raise Refused("unfinished_operation:" + marker)
                    return dict(event="worktree_init", status="claimed", path=str(path), branch=options.branch,
                                base_revision=base, allocation_time=allocated,
                                dotnet_restore="skipped" if options.skip_restore else "restored")
            except (Refused, OSError, ValueError) as error:
                # A failure after attaching a task branch has allocated material;
                # never try another candidate or create another tree afterward.
                attached = git(candidate, "symbolic-ref", "--quiet", "HEAD", check=False)
                if options.path or allocated_branch or attached.stdout.strip() == reference.encode():
                    raise
                if not isinstance(error, Refused):
                    raise
        return dict(event="worktree_init", status="no_idle")
