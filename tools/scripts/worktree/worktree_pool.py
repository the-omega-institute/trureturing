"""Native idle branches, bounded retention, task return and atomic claim."""

from contextlib import ExitStack
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from types import SimpleNamespace
import uuid

from worktree_protocol import (GitFailure, Refused, acquire, common, git, git_environment, git_scope,
                               identity, inventory, remote_endpoint, scope_fds, tree_scope, value)
from worktree_publication import commit_snapshot, confirm, recovery_root
from worktree_preservation import REMOVAL_RECORD, finished_operations, interrupted_removal, qualify, remove

IDLE_PREFIX = "refs/heads/lane/governance/idle-"
IDLE_CAPACITY = 4
PINS = ("lean-toolchain", "lake-manifest.json")
TASK_REUSE_SECONDS = 4 * 60 * 60
_HOST_CLEANUP = None


def idle_reference(reference):
    return reference.startswith(IDLE_PREFIX) and len(reference) > len(IDLE_PREFIX)


def clean(path, metadata):
    finished_operations(metadata)
    if git(path, "status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none").stdout:
        raise Refused("idle_dirty")


def idle_state(source, path, dev, removal_stack=None):
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
    pending = False
    if (metadata / REMOVAL_RECORD).exists():
        if removal_stack is None:
            raise Refused("idle_removal_pending")
        pending = interrupted_removal(path, metadata, removal_stack, source, reference,
                                      reconverge=False) is not None
    if not pending:
        clean(path, metadata)
    ancestry = git(path, "merge-base", "--is-ancestor", head, dev, check=False).returncode
    if ancestry == 1:
        dev = confirm(path, "origin", "dev", head)["observed_tip"]
    elif ancestry:
        raise Refused("idle_dev_ancestry_unknown")
    return dict(path=str(Path(path).resolve()), branch=reference, head=head, created=created,
                dev_commit=dev, removal_pending=pending)


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


def pool_failure(receipt, stage, error):
    receipt["failure"] = dict(scope="operation:idle-pool", stage=stage,
                              outcome="refused" if isinstance(error, Refused) and not isinstance(error, GitFailure) else "failed",
                              error=str(error), error_type=type(error).__name__)
    receipt["status"] = "failed"


def sweep_locked(source, dev, force=False, exclude_paths=()):
    """The caller holds the clone's pool operation scope; effects survive every failure."""
    receipt = pool_receipt()
    outcomes = receipt["items"]
    rows, candidates = [], []
    observed = dict(path=str(source), branch=None, head=dev)
    stage = "inventory"
    try:
        inventory_rows = inventory(source)
        source = Path(inventory_rows[0]["worktree"])
        excluded = {str(Path(path).resolve()) for path in exclude_paths}
        rows = []
        for item in inventory_rows:
            if not idle_reference(item.get("branch", "")):
                continue
            if excluded:
                try:
                    if str(Path(item["worktree"]).resolve()) in excluded:
                        continue
                except (OSError, RuntimeError):
                    # Candidate inspection owns this path's failure and continuation.
                    pass
            rows.append(dict(path=item["worktree"], branch=item.get("branch"), head=item.get("HEAD")))
        for observed in rows:
            path = Path(observed["path"])
            stage = "inspect"
            try:
                with ExitStack() as stack:
                    tree_scope(stack, source, path, True)
                    git_scope(stack, source, path)
                    candidates.append(idle_state(source, path, dev, stack))
            except Exception as error:
                if isinstance(error, Refused) and not isinstance(error, GitFailure):
                    outcomes.append(dict(observed, outcome="not_idle" if str(error) == "not_idle" else "retained",
                                         reason=str(error)))
                else:
                    sweep_failure(receipt, observed, stage, error)
        candidates.sort(key=lambda row: (row["created"], row["path"]))
        remaining = sum(not row["removal_pending"] for row in candidates)
        for observed in candidates:
            stage = "disk_pressure"
            pressure = available_fraction(source) < 0.05
            reason = ("idle_interrupted_removal" if observed["removal_pending"] else
                      "idle_disk_pressure" if pressure else "idle_capacity" if remaining > IDLE_CAPACITY else "idle_pool")
            if reason == "idle_pool":
                outcomes.append(dict(observed, outcome="retained", reason=reason))
                continue
            path = Path(observed["path"])
            try:
                stage = "revalidate"
                with ExitStack() as stack:
                    tree_scope(stack, source, path, True)
                    with ExitStack() as inspection:
                        git_scope(inspection, source, path)
                        current = idle_state(source, path, dev, inspection)
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
                            remaining -= not observed["removal_pending"]
                    if result["status"] in ("failed", "refused"):
                        receipt["status"] = "failed"
                    stage = "release"
            except Exception as error:
                if isinstance(error, Refused) and not isinstance(error, GitFailure):
                    outcomes.append(dict(observed, outcome="retained", reason=str(error), stage=stage,
                                         error=str(error), error_type=type(error).__name__))
                    receipt["status"] = "failed"
                else:
                    sweep_failure(receipt, observed, stage, error)
    except Exception as error:
        pool_failure(receipt, stage, error)
    if "failure" in receipt:
        reported = {row["path"] for row in outcomes}
        outcomes.extend(dict(row, outcome="retained", reason="idle_sweep_deferred")
                        for row in rows if row["path"] not in reported)
    return receipt


def sweep(source, dev, force=False, exclude_paths=()):
    receipt = pool_receipt()
    try:
        with ExitStack() as stack:
            acquire(stack, source, "operation:idle-pool", True)
            receipt = sweep_locked(source, dev, force, exclude_paths)
    except Exception as error:
        pool_failure(receipt, "pool_scope", error)
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


def host_cleanup():
    global _HOST_CLEANUP
    if _HOST_CLEANUP is None and "worktree_host_cleanup" in sys.modules:
        _HOST_CLEANUP = sys.modules["worktree_host_cleanup"]
    if _HOST_CLEANUP is None:
        location = Path(__file__).resolve().parent.parent / "host-cleanup.py"
        spec = importlib.util.spec_from_file_location("worktree_host_cleanup", location)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        _HOST_CLEANUP = module
    return _HOST_CLEANUP


def no_idle(options, reason=None, candidate_refusals=()):
    # The implicit creator defers its disk gate until reuse has been exhausted.
    if os.environ.get("WORKTREE_REQUIRE_DISK_CHECK") == "1":
        try:
            source = Path(options.source).resolve()
            host_cleanup().check_disk((source, source.parent))
        except (OSError, RuntimeError) as error:
            raise Refused(str(error)) from error
    result = dict(event="worktree_init", status="no_idle")
    if reason is not None:
        result["reason"] = reason
    if candidate_refusals:
        result["candidate_refusals"] = list(candidate_refusals)
    return result


def task_users(paths):
    codex = Path(os.environ.get("CODEX_HOME", str(Path.home() / ".codex")))
    return host_cleanup().active_paths(codex, scopes=paths)


def candidate_activity(paths):
    # Only eligibility reads before checkpointing or branch allocation may skip a candidate.
    try:
        return task_users(paths)
    except OSError as error:
        # Linux can expose a matched process identity while a proc inventory
        # is transitioning.  The diagnostic is never admission evidence:
        # wait only on the retained pidfd for complete group exit, then repeat
        # the same full activity inventory.  Persistent or ambiguous failures
        # remain fail-closed refusals.
        if host_cleanup().wait_for_linux_activity_transition(error):
            try:
                return task_users(paths)
            except OSError as retry_error:
                error = retry_error
        raise Refused("task_activity_unavailable:" + str(error)) from error


def no_task_users(path, paths):
    if any(held == path or path in held.parents for held in paths):
        raise Refused("task_active_process")


def dormant_state(source, path, metadata):
    """Inspect actual Git use, then ordinary changed paths; never scan ignored caches."""
    snapshot = (inventory(source), common(source))
    item = qualify(source, path, snapshot=snapshot)
    current, current_metadata = identity(source, path, snapshot=snapshot)
    if current != item or current_metadata != metadata:
        raise Refused("task_identity_changed")
    if "locked" in item:
        raise Refused("intentional_or_initialization_lock")
    finished_operations(metadata)
    if (metadata / REMOVAL_RECORD).exists():
        raise Refused("task_removal_pending")
    head = value(path, "rev-parse", "--verify", "HEAD^{commit}")
    branch = item.get("branch", "HEAD")
    if branch != "HEAD" and any(row.get("branch") == branch and
            Path(row["worktree"]).resolve() != path for row in snapshot[0]):
        raise Refused("task_branch_shared")
    if item.get("HEAD") != head or (branch != "HEAD" and
            value(path, "rev-parse", "--verify", branch) != head):
        raise Refused("task_identity_changed")
    log = metadata / "logs/HEAD"
    if log.is_symlink():
        raise Refused("task_last_use_unknown")
    try:
        raw = log.read_bytes()
    except OSError as error:
        raise Refused("task_last_use_unknown:" + str(error)) from error
    rows = raw.split(b"\n")
    if not rows[-1] and len(rows) > 1:
        rows.pop()
    stamps = []
    for row in rows:
        record = re.fullmatch(rb"([0-9a-f]{40}|[0-9a-f]{64}) ([0-9a-f]{40}|[0-9a-f]{64}) "
                              rb"[^<>\n]+ <[^<>\n]*> ([0-9]+) [+-][0-9]{4}(?:\t.*)?", row)
        if record is None:
            raise Refused("task_last_use_unknown")
        stamps.append(int(record[3]))
    if not stamps or record[2].decode("ascii") != head:
        raise Refused("task_last_use_unknown")
    stamps.append(int(value(path, "show", "-s", "--format=%ct", head)))
    last_use = max(stamps)
    if time.time() - last_use <= TASK_REUSE_SECONDS:
        raise Refused("task_recently_used")
    status = git(path, "status", "--porcelain=v1", "-z", "--untracked-files=all",
                 "--ignore-submodules=none", "--no-renames").stdout
    changed = []
    for row in status.split(b"\0"):
        if not row:
            continue
        if len(row) < 4 or row[2:3] != b" ":
            raise Refused("task_status_unknown")
        target = path / os.fsdecode(row[3:])
        while True:
            try:
                info = target.lstat()
                break
            except FileNotFoundError:
                if target == path:
                    raise Refused("task_identity_changed")
                target = target.parent
        last_use = max(last_use, info.st_mtime)
        changed.append((str(target), info.st_dev, info.st_ino, info.st_mode,
                        info.st_size, info.st_mtime_ns, info.st_ctime_ns))
    if time.time() - last_use <= TASK_REUSE_SECONDS:
        raise Refused("task_recently_used")
    return dict(path=str(path), branch=branch, head=head, last_use=last_use,
                head_log=raw, status=status, changed=changed)


def claim(options):
    with ExitStack() as pool_scope:
        try:
            acquire(pool_scope, options.source, "operation:idle-pool", True)
        except Refused as error:
            if options.path is not None or str(error) != "busy_scope:operation:idle-pool":
                raise
            return no_idle(options, str(error))
        rows = inventory(options.source)
        candidates = ([options.path] if options.path else
                      [Path(row["worktree"]) for idle in (True, False) for row in rows[1:]
                       if idle_reference(row.get("branch", "")) == idle])
        if not candidates:
            return no_idle(options)
        base = value(options.source, "rev-parse", "--verify", "--end-of-options", options.base + "^{commit}")
        # Only idle state depends on dev; qualify a target before reading it.
        dev = None
        expected = {pin: git(options.source, "show", base + ":" + pin).stdout for pin in PINS}
        reference = "refs/heads/" + options.branch
        git(options.source, "check-ref-format", reference)
        activity = None
        refusals = []
        for candidate in candidates:
            allocated_branch = prepared = False
            stage = "qualification"
            try:
                with ExitStack() as stack:
                    if candidate.is_symlink():
                        raise Refused("linked_tree")
                    path = tree_scope(stack, options.source, candidate, True)
                    item = qualify(options.source, path)
                    _, metadata = identity(options.source, path)
                    branch = git_scope(stack, options.source, path)
                    if (path / ".lake").is_symlink():
                        raise Refused("linked_cache")
                    idle = False
                    if idle_reference(item.get("branch", "")):
                        if dev is None:
                            dev = value(options.source, "rev-parse", "--verify", "refs/remotes/origin/dev^{commit}")
                        try:
                            state = idle_state(options.source, path, dev)
                            idle = True
                        except Refused as error:
                            if isinstance(error, GitFailure) or str(error) != "not_idle":
                                raise
                    if not idle:
                        state = dormant_state(options.source, path, metadata)
                    if state["branch"] != branch:
                        raise Refused("claim_identity_changed")
                    acquire(stack, options.source, "ref:" + reference, True)
                    if idle:
                        for pin in PINS:
                            if (path / pin).read_bytes() != expected[pin]:
                                raise Refused("incompatible_pin:" + pin)
                    stage = "activity"
                    if activity is None:
                        activity = candidate_activity(candidates)
                    no_task_users(path, activity)
                    checkpoint = None
                    retained_branch = branch
                    if idle:
                        stage = "activity_recheck"
                        no_task_users(path, candidate_activity((path,)))
                        stage = "state_recheck"
                        if idle_state(options.source, path, dev) != state:
                            raise Refused("idle_identity_changed")
                    else:
                        stage = "state_recheck"
                        if dormant_state(options.source, path, metadata) != state:
                            raise Refused("task_identity_changed")
                        stage = "activity_recheck"
                        no_task_users(path, candidate_activity((path,)))
                        prepared = True
                        checkpoint = commit_snapshot(path, metadata, branch,
                            b"WIP checkpoint dormant worktree before reuse\n", stack, options.source)
                        if branch == "HEAD":
                            retained_branch = recovery_root(stack, options.source, path, checkpoint["commit"])
                        clean(path, metadata)
                        no_task_users(path, task_users((path,)))
                        current, current_metadata = identity(options.source, path)
                        if (current.get("branch", "HEAD") != branch or current.get("HEAD") != checkpoint["commit"]
                                or current_metadata != metadata or "locked" in current
                                or value(path, "rev-parse", retained_branch) != checkpoint["commit"]):
                            raise Refused("claim_identity_changed")
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
                    if idle:
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
                    finished_operations(metadata)
                    result = dict(event="worktree_init", status="claimed", path=str(path), branch=options.branch,
                                  base_revision=base, allocation_time=allocated,
                                  dotnet_restore="skipped" if options.skip_restore else "restored")
                    if checkpoint is not None:
                        result.update(previous_branch=retained_branch, checkpoint=checkpoint,
                                      previous_last_use=state["last_use"])
                    return result
            except (Refused, OSError, ValueError) as error:
                # Once checkpointing or allocation starts, never allocate another tree.
                if isinstance(error, GitFailure) or not isinstance(error, Refused):
                    raise
                attached = git(candidate, "symbolic-ref", "--quiet", "HEAD", check=False)
                if options.path or allocated_branch or prepared or attached.stdout.strip() == reference.encode():
                    raise
                refusals.append(dict(path=str(candidate), stage=stage, reason=str(error)))
        return no_idle(options, candidate_refusals=refusals)
