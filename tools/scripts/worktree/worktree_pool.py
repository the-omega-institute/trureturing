"""Native idle branches, bounded retention, task return and atomic claim."""

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

from worktree_protocol import (GitFailure, Refused, acquire, common, git, git_environment, git_scope,
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
    created = idle_creation(source, reference, head)
    clean(path, metadata)
    ancestry = git(path, "merge-base", "--is-ancestor", head, dev, check=False).returncode
    if ancestry == 1:
        dev = confirm(path, "origin", "dev", head)["observed_tip"]
    elif ancestry:
        raise Refused("idle_dev_ancestry_unknown")
    return dict(path=str(Path(path).resolve()), branch=reference, head=head, created=created, dev_commit=dev)


def idle_creation(source, reference, head):
    log = common(source) / "logs" / reference
    if log.is_symlink():
        raise Refused("idle_creation_unknown")
    rows = log.read_bytes().splitlines()
    if not rows:
        raise Refused("idle_creation_unknown")
    fields, message = rows[0].split(b"\t", 1)
    token = reference[len(IDLE_PREFIX):]
    if message != ("worktree-idle:" + token).encode("ascii"):
        raise Refused("not_idle")
    old, new, rest = fields.split(b" ", 2)
    timestamp = int(rest.rsplit(b" ", 2)[1])
    if (not re.fullmatch(r"[0-9a-f]{32}", token) or old != b"0" * len(head)
            or new.decode("ascii") != head or not 0 <= timestamp <= time.time()):
        raise Refused("idle_creation_unknown")
    return timestamp


def available_fraction(source):
    disk = shutil.disk_usage(source)
    return disk.free / disk.total


def pool_receipt():
    return dict(event="worktree_pool", capacity=IDLE_CAPACITY, items=[], status="succeeded")


def sweep_failure(receipt, observed, stage, error):
    receipt["items"].append(dict(observed, outcome="sweep_failed", reason="idle_sweep_failed",
                                 stage=stage, error=str(error), error_type=type(error).__name__))
    receipt["status"] = "failed"


def sweep_locked(source, dev, force=False):
    """The caller holds the clone's pool operation scope; effects survive every failure."""
    receipt = pool_receipt()
    outcomes = receipt["items"]
    rows, candidates = [], []
    observed = dict(path=str(source), branch=None, head=dev)
    stage = "inventory"
    try:
        inventory_rows = inventory(source)
        source = Path(inventory_rows[0]["worktree"])
        rows = [dict(path=item["worktree"], branch=item.get("branch"), head=item.get("HEAD"))
                for item in inventory_rows if idle_reference(item.get("branch", ""))]
        for observed in rows:
            path = Path(observed["path"])
            stage = "inspect"
            try:
                with ExitStack() as stack:
                    tree_scope(stack, source, path, True)
                    git_scope(stack, source, path)
                    candidates.append(idle_state(source, path, dev))
            except GitFailure:
                raise
            except Refused as error:
                outcomes.append(dict(observed, outcome="not_idle" if str(error) == "not_idle" else "retained",
                                     reason=str(error)))
        candidates.sort(key=lambda row: (row["created"], row["path"]))
        remaining = len(candidates)
        for observed in candidates:
            stage = "disk_pressure"
            pressure = available_fraction(source) < 0.05
            reason = "idle_disk_pressure" if pressure else "idle_capacity" if remaining > IDLE_CAPACITY else "idle_pool"
            if reason == "idle_pool":
                outcomes.append(dict(observed, outcome="retained", reason=reason))
                continue
            path = Path(observed["path"])
            stage = "revalidate"
            with ExitStack() as stack:
                tree_scope(stack, source, path, True)
                current = idle_state(source, path, dev)
                if current != observed:
                    raise Refused("idle_identity_changed")
                # Common removal owns the index/ref scopes and snapshot rules.
                stage = "remove"
                result = remove(SimpleNamespace(source=source, names="", path=[path], force=False,
                    preview=not force, expected=[json.dumps(dict(path=str(path), head=observed["head"],
                                                               branch=observed["branch"]))]))
                for removal in result["items"]:
                    row = dict(observed, **dict(removal,
                        outcome="retained" if removal["outcome"] == "refused" else removal["outcome"],
                        reason=removal.get("reason", reason)))
                    if removal["outcome"] not in ("removed", "would_remove"):
                        row.setdefault("stage", stage)
                    if removal["outcome"] == "refused":
                        row.update(stage=stage, error=removal.get("error") or row["reason"], error_type="Refused")
                        receipt["status"] = "failed"
                    outcomes.append(row)
                    if removal["outcome"] in ("removed", "would_remove"):
                        remaining -= 1
                if result["status"] in ("failed", "refused"):
                    receipt["status"] = "failed"
                    break
                stage = "release"
    except Exception as error:
        # This is the batch receipt boundary, including pressure reads and scope
        # release. The common remover retains its own checkpoint/recovery fields.
        if stage in ("revalidate", "remove") and isinstance(error, Refused) and not isinstance(error, GitFailure):
            outcomes.append(dict(observed, outcome="retained", reason=str(error), stage=stage,
                                 error=str(error), error_type=type(error).__name__))
            receipt["status"] = "failed"
        else:
            sweep_failure(receipt, observed, stage, error)
    if receipt["status"] == "failed":
        reported = {row["path"] for row in outcomes}
        outcomes.extend(dict(row, outcome="retained", reason="idle_sweep_deferred")
                        for row in rows if row["path"] not in reported)
    return receipt


def sweep(source, dev, force=False):
    receipt = pool_receipt()
    try:
        with ExitStack() as stack:
            acquire(stack, source, "operation:idle-pool", True)
            receipt = sweep_locked(source, dev, force)
    except Exception as error:
        receipt["failure"] = dict(scope="operation:idle-pool", stage="pool_scope",
                                  outcome="refused" if isinstance(error, Refused) and not isinstance(error, GitFailure) else "failed",
                                  error=str(error), error_type=type(error).__name__)
        receipt["status"] = "failed"
    return receipt


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


def unused_base(source, path, branch, head):
    """Creation and claim both create the task ref at the allocated base."""
    if not branch.startswith("refs/heads/"):
        raise Refused("return_current_branch_required")
    log = common(source) / "logs" / branch
    try:
        if log.is_symlink():
            raise ValueError("linked branch log")
        raw = log.read_bytes()
        rows = raw.split(b"\n", 1)
        if len(rows) != 2:
            raise ValueError("incomplete branch creation")
        creation = re.fullmatch(rb"([0-9a-f]{40}|[0-9a-f]{64}) ([0-9a-f]{40}|[0-9a-f]{64}) "
                                rb"[^<>\n]+ <[^<>\n]*> [0-9]+ [+-][0-9]{4}\t.*", rows[0])
        if creation is None:
            raise ValueError("missing or malformed branch creation")
        base = creation[2]
        if creation[1] != b"0" * len(base):
            raise ValueError("missing branch creation")
    except (OSError, ValueError) as error:
        raise Refused("unused_allocation_unknown") from error
    if (base.decode("ascii") != head
            or value(path, "rev-parse", "--verify", branch + "^{commit}") != head):
        raise Refused("unused_task_commits_require_pr")
    return base.decode("ascii")


def return_tree(options):
    if not options.writers_joined:
        raise Refused("host_must_join_task_writers")
    result = None
    try:
        with ExitStack() as stack:
            acquire(stack, options.source, "operation:idle-pool", True)
            result = returned_snapshot(options)
            result["pool"] = sweep_locked(options.source, result["dev_commit"], True)
    except Exception as error:
        if result is None:
            raise
        receipt = result.setdefault("pool", pool_receipt())
        sweep_failure(receipt, dict(path=str(options.source), branch=None, head=result["dev_commit"]),
                      "pool_scope", error)
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
        evidence = pr_evidence(path, options.pr) if options.pr is not None else None
        already = False
        if idle_reference(branch):
            try:
                idle_creation(options.source, branch, value(path, "rev-parse", "HEAD"))
                already = True
            except Refused as error:
                if str(error) != "not_idle":
                    raise
        allocation_base = None
        if evidence is None:
            clean(path, metadata)
            if already:
                raise Refused("unused_return_already_idle")
            allocation_base = unused_base(options.source, path, branch, value(path, "rev-parse", "HEAD"))
        endpoint = remote_endpoint(path, "origin", push=True)
        remote = confirm(path, "origin", "dev",
                         evidence["mergeCommit"]["oid"] if evidence else allocation_base, endpoint)
        dev = remote["observed_tip"]
        task = "refs/heads/" + evidence["headRefName"] if evidence else branch
        if already:
            idle_state(options.source, path, dev)
            acquire(stack, options.source, "ref:" + task, True)
            tip = value(path, "rev-parse", "--verify", "--end-of-options", task + "^{commit}")
        else:
            if branch != task:
                raise Refused("pr_head_mismatch")
            tip = value(path, "rev-parse", "HEAD")
        if evidence and git(path, "merge-base", "--is-ancestor", evidence["headRefOid"], tip, check=False).returncode:
            raise Refused("pr_head_outside_tree")
        if already and value(path, "rev-parse", "HEAD") == dev:
            return dict(event="worktree_return", status="already_idle", path=str(path), dev_commit=dev,
                        task_branch=task, idle_branch=branch)
        if not branch.startswith("refs/heads/"):
            raise Refused("return_current_branch_required")
        checkpoint = commit_snapshot(path, metadata, branch,
                                     b"Checkpoint post-merge working tree before return\n", stack, options.source)
        clean(path, metadata)
        outstanding = value(path, "rev-list", dev + ".." + checkpoint["commit"]).splitlines()
        token = uuid.uuid4().hex
        idle = IDLE_PREFIX + token
        acquire(stack, options.source, "ref:" + idle, True)
        git(path, "update-ref", "--create-reflog", "-m", "worktree-idle:" + token,
            idle, dev, "0" * len(dev))
        git(path, "switch", "--no-overwrite-ignore", "--", idle.removeprefix("refs/heads/"))
        idle_state(options.source, path, dev)
        if already:
            git(path, "update-ref", "-d", branch, checkpoint["commit"])
        result = dict(event="worktree_return", status="returned", path=str(path), dev_commit=dev,
                      task_branch=task, idle_branch=idle, checkpoint=checkpoint,
                      commits_not_in_dev=outstanding, remote=remote)
        if allocation_base is not None:
            result["allocation_base"] = allocation_base
        return result


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
        try:
            acquire(pool_scope, options.source, "operation:idle-pool", True)
        except Refused as error:
            if options.path is not None or str(error) != "busy_scope:operation:idle-pool":
                raise
            return dict(event="worktree_init", status="no_idle", reason=str(error))
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
                if isinstance(error, GitFailure) or not isinstance(error, Refused):
                    raise
                attached = git(candidate, "symbolic-ref", "--quiet", "HEAD", check=False)
                if options.path or allocated_branch or attached.stdout.strip() == reference.encode():
                    raise
        return dict(event="worktree_init", status="no_idle")
