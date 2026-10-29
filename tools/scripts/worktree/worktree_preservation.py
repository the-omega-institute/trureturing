"""User-directed worktree removal and independent non-worktree retention policies."""

from contextlib import ExitStack, contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import time
import uuid

from worktree_protocol import (Refused, GitFailure, git, value, common, inventory, identity,
                               acquire, git_scope, remote_endpoint, tree_scope)


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


REMOVAL_RECORD = "worktree-removal"


def reject_nested_git(target):
    """Refuse repository boundaries before checkpointing or deleting payload."""
    for entry in git(target, "ls-files", "--stage", "-z").stdout.split(b"\0"):
        if entry.startswith(b"160000 "):
            raise Refused("nested_git_boundary:" + os.fsdecode(entry.split(b"\t", 1)[1]))
    def unreadable(error):
        raise error
    for directory, folders, files in os.walk(target, followlinks=False, onerror=unreadable):
        path = Path(directory)
        if path == target:
            folders[:] = [name for name in folders if name != ".git"]
        elif ".git" in folders or ".git" in files:
            raise Refused("nested_git_boundary:" + str(path.relative_to(target)))
        if "HEAD" in files and git(target, "rev-parse", "--resolve-git-dir", path,
                                   check=False).returncode == 0:
            raise Refused("nested_git_boundary:" + str(path.relative_to(target)))


def record_removal(metadata, commit, recovery_branch, predecessors=None, native_locks=None):
    """Keep the verified snapshot in Git metadata until content deletion succeeds."""
    staged = metadata / (REMOVAL_RECORD + ".tmp")
    staged.write_text(json.dumps(dict(commit=commit, recovery_branch=recovery_branch,
                                     predecessors=predecessors or [], native_locks=native_locks or [])))
    os.replace(staged, metadata / REMOVAL_RECORD)


def remove_payload(target):
    """Retain the Git link and registration throughout fallible content deletion."""
    reject_nested_git(target)
    for child in target.iterdir():
        if child.name == ".git":
            continue
        if child.is_dir() and not child.is_symlink():
            shutil.rmtree(child)
        else:
            child.unlink()
    if any(child.name != ".git" for child in target.iterdir()):
        raise Refused("worktree_payload_changed_during_removal")


def interrupted_removal(target, metadata, stack, source, branch):
    """Return the record of an earlier removal whose deletion stopped part way."""
    record = metadata / REMOVAL_RECORD
    if not record.exists():
        return None
    removal = json.loads(record.read_text())
    commit = removal["commit"]
    predecessors = removal.get("predecessors", [])
    stack.recovery_roots = getattr(stack, "recovery_roots", []) + [
        root["recovery_branch"] for root in predecessors]
    stack.native_locks = getattr(stack, "native_locks", []) + removal.get("native_locks", [])
    for root in predecessors:
        reference = root["recovery_branch"]
        git(source, "check-ref-format", reference)
        if not any(handle.scope_key == "ref:" + reference
                   for handle in getattr(stack, "scope_handles", [])):
            acquire(stack, source, "ref:" + reference, True)
        if value(target, "rev-parse", "--verify", reference + "^{commit}") != root["commit"]:
            raise Refused("interrupted_removal_recovery_root_changed")
    if removal["recovery_branch"] != branch:
        acquire(stack, source, "ref:" + removal["recovery_branch"], True)
    recorded_tip = git(target, "rev-parse", "--verify", removal["recovery_branch"] + "^{commit}", check=False)
    if (value(target, "rev-parse", "--verify", "HEAD^{commit}") != commit
            or recorded_tip.returncode or os.fsdecode(recorded_tip.stdout).strip() != commit):
        from worktree_publication import commit_snapshot, recovery_root
        # Pin the old object before checkpointing; its former branch can have moved.
        predecessor = dict(commit=commit, recovery_branch=recovery_root(stack, source, target, commit))
        predecessors = predecessors + [predecessor]
        snapshot = commit_snapshot(target, metadata, branch,
            b"Checkpoint current work after interrupted removal\n", stack, source)
        current_root = recovery_root(stack, source, target, snapshot["commit"])
        for root in predecessors + [dict(commit=snapshot["commit"], recovery_branch=current_root)]:
            if value(target, "rev-parse", "--verify", root["recovery_branch"] + "^{commit}") != root["commit"]:
                raise Refused("interrupted_removal_recovery_root_changed")
        if git(target, "status", "--porcelain", "--untracked-files=all").stdout:
            raise Refused("working_tree_changed_after_checkpoint")
        record_removal(metadata, snapshot["commit"], current_root, predecessors,
                       getattr(stack, "native_locks", []))
        return dict(commit=snapshot["commit"], recovery_branch=current_root, reconverged=True,
                    native_locks=getattr(stack, "native_locks", []))
    # Content deletion only deletes files; other differences may be later changes.
    status = git(target, "status", "--porcelain", "--untracked-files=all").stdout.splitlines()
    if any(not line.startswith(b" D ") for line in status):
        raise Refused("interrupted_removal_tree_changed")
    return removal


LOCK_AGE_SECONDS = 24 * 60 * 60


def qualify(source, path, stack=None, snapshot=None, deadline=None):
    """Validate identity, nested repositories and Git lock age without activity checks."""
    if Path(path).is_symlink():
        raise Refused("linked_tree")
    path = Path(path).resolve()
    if not path.is_dir():
        raise Refused("missing_or_linked_tree")
    snapshot = snapshot if snapshot is not None else (inventory(source), common(source))
    item, metadata = identity(source, path, snapshot=snapshot, deadline=deadline)
    rows = snapshot[0]
    if path == Path(rows[0]["worktree"]).resolve():
        raise Refused("main_worktree")
    if any(path in Path(row["worktree"]).resolve().parents for row in rows):
        raise Refused("nested_worktree")
    reject_nested_git(path)
    if "locked" in item:
        if item["locked"].startswith("worktree-init:"):
            try:
                if stack is None:
                    with ExitStack() as probe:
                        tree_scope(probe, source, path, True)
                else:
                    tree_scope(stack, source, path, True)
            except Refused as error:
                if not str(error).startswith("busy_scope:"):
                    raise
                raise Refused("initialization_in_progress") from error
            return item
        lock = metadata / "locked"
        if lock.is_symlink():
            raise Refused("locked_age_unknown")
        observed = None
        def lock_changed(current):
            return observed is not None and any(
                getattr(current, field) != getattr(observed, field)
                for field in ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns", "st_ctime_ns"))
        try:
            observed = lock.stat()
            if not stat.S_ISREG(observed.st_mode):
                raise Refused("locked_age_unknown")
            current = lock.stat()
            if lock.is_symlink() or lock_changed(current):
                raise Refused("observed_identity_changed")
        except OSError as error:
            try:
                current = lock.lstat()
                changed = stat.S_ISLNK(current.st_mode) or lock_changed(current)
            except FileNotFoundError:
                changed = True
            except OSError:
                changed = False
            if changed:
                raise Refused("observed_identity_changed") from error
            raise
        age = time.time() - current.st_mtime
        if age < LOCK_AGE_SECONDS:
            raise Refused("locked_recent")
    return item


def bounded_diagnostic(value, limit=4096):
    text = str(value)
    return text if len(text) <= limit else text[:limit // 2] + "...[truncated]..." + text[-limit // 2:]


def qualification_failure(error):
    kind = "timeout" if isinstance(error, subprocess.TimeoutExpired) else "unavailable"
    detail = type(error).__name__ + ":" + str(error)
    if isinstance(error, subprocess.TimeoutExpired) and error.stderr:
        stderr = error.stderr
        detail += ":stderr=" + (stderr.decode(errors="replace") if isinstance(stderr, bytes) else stderr)
    return "qualification_failed:" + kind + ":" + bounded_diagnostic(detail)


@contextmanager
def qualification_deadline(seconds):
    def expired(signum, frame):
        raise subprocess.TimeoutExpired(["qualify"], seconds, stderr=b"batch qualification deadline expired")
    handler = signal.signal(signal.SIGALRM, expired)
    previous = signal.setitimer(signal.ITIMER_REAL, seconds)
    try:
        yield
    finally:
        signal.setitimer(signal.ITIMER_REAL, *previous)
        signal.signal(signal.SIGALRM, handler)


def qualify_batch(options, emit=None, emit_started=None):
    """Qualify independently within min(600 seconds per path, 3600 seconds).

    Completed rows are emitted immediately. The deadline covers snapshot reads
    and qualification; native Git termination may additionally take 30 seconds.
    Preview grants no mutation authority and only probes cooperative entry.
    """
    paths = list(dict.fromkeys(options.path))
    outcomes = []
    budget = getattr(options, "budget_seconds", None)
    budget = min(budget if budget is not None else 600 * len(paths), 600 * len(paths), 3600)
    if budget <= 0:
        raise ValueError("qualification budget must be positive")
    deadline = time.monotonic() + budget
    def report(path, outcome, reason):
        row = dict(path=str(path), outcome=outcome, reason=reason)
        outcomes.append(row)
        if emit:
            emit(row)
    try:
        with qualification_deadline(budget):
            snapshot = inventory(options.source), common(options.source)
    except Exception as error:
        for path in paths:
            report(path, "failed", qualification_failure(error))
    else:
        for path in paths:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                report(path, "deferred", "qualification_failed:deferred:batch qualification deadline expired")
                continue
            try:
                if emit_started:
                    emit_started(path)
                with qualification_deadline(remaining):
                    qualify(options.source, path, snapshot=snapshot, deadline=deadline)
                report(path, "qualified", None)
            except GitFailure as error:
                report(path, "failed", qualification_failure(error))
            except Refused as error:
                report(path, "refused", str(error))
            except Exception as error:
                report(path, "failed", qualification_failure(error))
    return dict(event="worktree_qualification", items=outcomes,
                status="failed" if any(item["outcome"] in ("failed", "deferred") for item in outcomes) else "succeeded")


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
        recovery_branch = None
        recovery_branch_candidate = None
        removing = False
        qualifying = True
        try:
            with ExitStack() as stack:
                # Initialization needs the dead initializer's exclusive entry.
                # Ordinary removal has no participation or activity prerequisite.
                if qualify(source, target, stack) != qualified[target]:
                    raise Refused("observed_identity_changed")
                qualifying = False
                branch = git_scope(stack, source, target)
                _, metadata = identity(source, target)
                resumed = interrupted_removal(target, metadata, stack, source, branch)
                if resumed:
                    # The earlier removal verified this snapshot clean before content
                    # deletion began; missing files are its effects, not changes.
                    checkpoint = dict(event="worktree_checkpoint", status="reconverged" if resumed.get("reconverged") else "resumed",
                                      commit=resumed["commit"], branch=branch,
                                      native_locks=resumed.get("native_locks", []))
                    recovery_branch = resumed["recovery_branch"]
                    refreshed = identity(source, target)[0]
                else:
                    from worktree_publication import commit_snapshot
                    checkpoint = commit_snapshot(target, metadata, branch,
                        b"Checkpoint working tree before recycling\n", stack, source)
                    if branch.startswith("refs/heads/"):
                        recovery_branch = branch
                    else:
                        # Keep detached HEAD/index coordination until removal. Native
                        # branch creation never replaces an existing ref, even on collision.
                        recovery_branch_candidate = "refs/heads/lane/governance/recovery-" + uuid.uuid4().hex
                        acquire(stack, source, "ref:" + recovery_branch_candidate, True)
                        git(target, "branch", "--", recovery_branch_candidate.removeprefix("refs/heads/"),
                            checkpoint["commit"])
                        recovery_branch = recovery_branch_candidate
                    refreshed = identity(source, target)[0]
                    expected = dict(qualified[target], HEAD=checkpoint["commit"])
                    if refreshed != expected:
                        raise Refused("observed_identity_changed_after_checkpoint")
                    # Concurrent edits or hook changes after staging need another
                    # snapshot; do not silently discard ordinary outstanding files.
                    if git(target, "status", "--porcelain", "--untracked-files=all").stdout:
                        raise Refused("working_tree_changed_after_checkpoint")
                    record_removal(metadata, checkpoint["commit"], recovery_branch,
                                   native_locks=checkpoint.get("native_locks", []))
                flags = ["--force", "--force"] if "locked" in refreshed else ["--force"]
                removing = True
                remove_payload(target)
                git(source, "worktree", "remove", *flags, "--", target,
                    timeout=None if options.force else 300)
                outcomes.append(dict(path=str(target), outcome="removed", checkpoint=checkpoint,
                                     recovery_branch=recovery_branch,
                                     recovery_roots=getattr(stack, "recovery_roots", [])))
        except Exception as error:
            if qualifying:
                refused = isinstance(error, Refused) and not isinstance(error, GitFailure)
                reason = str(error) if refused else qualification_failure(error)
                outcomes.append(dict(path=str(target), outcome="refused" if refused else "qualification_failed",
                                     reason=reason, error=reason))
                continue
            outcomes.append(dict(path=str(target),
                outcome="partial_or_indeterminate" if removing else "checkpoint_failed",
                error=str(error), checkpoint=checkpoint, recovery_branch=recovery_branch,
                recovery_branch_candidate=recovery_branch_candidate,
                native_locks=getattr(error, "native_locks", []) or getattr(stack, "native_locks", []),
                recovery_roots=getattr(stack, "recovery_roots", [])))

    return dict(event="worktree_removal", items=outcomes,
                status="failed" if any(item["outcome"] not in ("removed", "would_remove", "refused") for item in outcomes)
                else "refused" if any(item["outcome"] == "refused" for item in outcomes) else "succeeded")


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
