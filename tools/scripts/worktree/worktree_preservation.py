"""User-directed worktree removal and independent non-worktree retention policies."""

from contextlib import ExitStack, contextmanager
from contextvars import ContextVar
import json
import os
from pathlib import Path
import re
import shutil
import signal
import stat
import subprocess
import tempfile
import time
import uuid

from worktree_protocol import (Refused, GitFailure, git, value, common, inventory, identity,
                               acquire, git_scope, tree_scope)


REMOVAL_RECORD = "worktree-removal"
_PAYLOAD_PLAN = ContextVar("worktree_removal_payload_plan", default=None)


def _declared_lake_dependency(path, target):
    """Recognize one manifest-declared checkout under a Lake project."""
    packages = path.parent
    lake = packages.parent
    project = lake.parent
    if (packages.name != "packages" or lake.name != ".lake" or not path.name
            or not project.is_relative_to(target)):
        return None
    manifest = project / "lake-manifest.json"
    try:
        info = manifest.lstat()
        if stat.S_ISLNK(info.st_mode) or not stat.S_ISREG(info.st_mode):
            return None
        document = json.loads(manifest.read_text(encoding="utf-8"))
        entries = document.get("packages") if isinstance(document, dict) else None
        if not isinstance(entries, list):
            return None
        names = []
        for entry in entries:
            if not isinstance(entry, dict) or not isinstance(entry.get("name"), str):
                return None
            names.append(entry["name"])
        return entries[names.index(path.name)] if names.count(path.name) == 1 else None
    except (OSError, UnicodeError, json.JSONDecodeError, TypeError):
        return None


LAKE_CONFIG_KEYS = frozenset({
    "core.repositoryformatversion", "core.filemode", "core.bare", "core.logallrefupdates",
    "core.ignorecase", "core.precomposeunicode", "core.symlinks", "remote.origin.url",
    "remote.origin.fetch", "remote.origin.promisor", "remote.origin.partialclonefilter",
    "extensions.partialclone", "extensions.objectformat",
})
GIT_DEFAULT_DESCRIPTION = b"Unnamed repository; edit this file 'description' to name the repository.\n"


def _lake_git_directory_problem(directory):
    """Inspect bounded metadata entries without traversing their payload trees."""
    if directory.name == "hooks":
        for entry in directory.iterdir():
            if not (entry.name.endswith(".sample") and stat.S_ISREG(entry.lstat().st_mode)):
                return "hooks_entry:" + entry.name
    elif directory.name == "info":
        for entry in directory.iterdir():
            if entry.name != "exclude" or not stat.S_ISREG(entry.lstat().st_mode):
                return "info_entry:" + entry.name
            if any(line and not line.startswith(b"#")
                   for line in entry.read_bytes().splitlines()):
                return "info_exclude"
    elif directory.name == "objects":
        for entry in directory.iterdir():
            if (not stat.S_ISDIR(entry.lstat().st_mode)
                    or not (entry.name in {"pack", "info"} or re.fullmatch(r"[0-9a-f]{2}", entry.name))):
                return "objects_entry:" + entry.name
            if entry.name == "info":
                for child in entry.iterdir():
                    mode = child.lstat().st_mode
                    if child.name in {"packs", "commit-graph"} and stat.S_ISREG(mode):
                        continue
                    if child.name == "commit-graphs" and stat.S_ISDIR(mode):
                        continue
                    return "objects_info_entry:" + child.name
    elif directory.name == "logs":
        for entry in directory.iterdir():
            mode = entry.lstat().st_mode
            if entry.name == "HEAD" and stat.S_ISREG(mode):
                continue
            if entry.name == "refs" and stat.S_ISDIR(mode):
                continue
            return "logs_entry:" + entry.name
    return None


def _lake_git_shape_problem(path):
    """Recognize only ordinary detached Lake clone metadata and visible indexes."""
    metadata = path / ".git"
    if not stat.S_ISDIR(metadata.lstat().st_mode):
        return "git_directory"
    files = {"HEAD", "config", "description", "index", "FETCH_HEAD", "packed-refs"}
    directories = {"hooks", "info", "logs", "objects", "refs", "worktree-operations"}
    for entry in metadata.iterdir():
        mode = entry.lstat().st_mode
        if entry.name in files and stat.S_ISREG(mode):
            if entry.name == "description" and entry.read_bytes() != GIT_DEFAULT_DESCRIPTION:
                return "description"
            continue
        if entry.name not in directories or not stat.S_ISDIR(mode):
            return "git_entry:" + entry.name
        if entry.name == "worktree-operations":
            for lock in entry.iterdir():
                info = lock.lstat()
                if not (lock.name.endswith(".lock") and stat.S_ISREG(info.st_mode)
                        and info.st_size == 0):
                    return "scope_lock:" + lock.name
        problem = _lake_git_directory_problem(entry)
        if problem:
            return problem
    config = git(path, "config", "--local", "--no-includes", "--null", "--name-only", "--list")
    if config.stderr:
        raise Refused("config_inspection:" + os.fsdecode(config.stderr).strip())
    for key in config.stdout.split(b"\0"):
        if key and os.fsdecode(key) not in LAKE_CONFIG_KEYS:
            return "config_key:" + os.fsdecode(key)
    head = git(path, "symbolic-ref", "--quiet", "HEAD", check=False)
    if head.returncode == 0:
        return "attached_head"
    if head.returncode != 1:
        raise Refused("symbolic_ref_failed")
    refs = git(path, "for-each-ref", "--format=%(refname)")
    if refs.stderr:
        raise Refused("reference_inspection:" + os.fsdecode(refs.stderr).strip())
    if any(not ref.startswith((b"refs/tags/", b"refs/remotes/"))
           for ref in refs.stdout.splitlines()):
        return "reference_namespace"
    for entry in git(path, "ls-files", "-v", "-z").stdout.split(b"\0"):
        if entry and (entry[:1] == b"S" or entry[:1].islower()):
            return "index_flags"
    return None


def reject_lake_local_content(path, target, package):
    """Exempt only recognized Lake clones with fully covered visible content."""
    relative = str(path.relative_to(target))
    revision = package.get("rev")
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-fA-F]{40}|[0-9a-fA-F]{64}", revision):
        raise Refused("lake_dependency_check_failed:" + relative + ":manifest_revision")
    try:
        shape_problem = _lake_git_shape_problem(path)
    except (Refused, OSError, subprocess.SubprocessError, UnicodeError) as error:
        raise Refused("lake_dependency_check_failed:" + relative + ":" + str(error)) from error
    if shape_problem:
        raise Refused("lake_dependency_unknown_shape:" + relative + ":" + shape_problem)
    try:
        status = git(path, "status", "--porcelain=v1", "-z", "--untracked-files=all",
                     "--ignore-submodules=none").stdout
        manifest_type = git(path, "cat-file", "--batch-check=%(objecttype)",
                            input=(revision + "\n").encode("ascii")).stdout.strip()
        if manifest_type == b"commit":
            manifest_commits = [revision]
        elif manifest_type == revision.encode("ascii") + b" missing":
            manifest_commits = []
        else:
            raise Refused("manifest_revision_object")
        history = git(path, "rev-list", "--max-count=1", "HEAD", "--all", "--reflog",
                      "--not", "--remotes", "--tags", *manifest_commits, "--")
        if history.stderr:
            raise Refused("history_inspection:" + os.fsdecode(history.stderr).strip())
    except (Refused, OSError, subprocess.SubprocessError, UnicodeError) as error:
        raise Refused("lake_dependency_check_failed:" + relative + ":" + str(error)) from error
    if status:
        raise Refused("lake_dependency_dirty:" + relative)
    if history.stdout.strip():
        raise Refused("lake_dependency_local_history:" + relative)


def reject_nested_git(target):
    """Refuse owner, device and repository boundaries before payload mutation."""
    root_stat = target.lstat()
    if root_stat.st_uid != os.getuid():
        raise Refused("owner_boundary:" + str(target))
    def unreadable(error):
        raise error
    for directory, folders, files in os.walk(target, followlinks=False, onerror=unreadable):
        path = Path(directory)
        if path == target:
            folders[:] = [name for name in folders if name != ".git"]
        for name in folders:
            child = path / name
            info = child.lstat()
            if stat.S_ISDIR(info.st_mode) and info.st_dev != root_stat.st_dev:
                raise Refused("device_boundary:" + str(child))
        if path != target and (".git" in folders or ".git" in files):
            package = _declared_lake_dependency(path, target)
            if package is None:
                raise Refused("nested_git_boundary:" + str(path.relative_to(target)))
            reject_lake_local_content(path, target, package)
            folders[:] = [name for name in folders if name != ".git"]
        if "HEAD" in files and git(target, "rev-parse", "--resolve-git-dir", path,
                                   check=False).returncode == 0:
            raise Refused("nested_git_boundary:" + str(path.relative_to(target)))

    for entry in git(target, "ls-files", "--stage", "-z").stdout.split(b"\0"):
        if entry.startswith(b"160000 "):
            raise Refused("nested_git_boundary:" + os.fsdecode(entry.split(b"\t", 1)[1]))


def record_removal(metadata, commit, recovery_branch, predecessors=None, native_locks=None):
    """Keep the verified snapshot in Git metadata until content deletion succeeds."""
    staged = metadata / (REMOVAL_RECORD + ".tmp")
    staged.write_text(json.dumps(dict(commit=commit, recovery_branch=recovery_branch,
                                     predecessors=predecessors or [], native_locks=native_locks or [])))
    os.replace(staged, metadata / REMOVAL_RECORD)


def remove_payload(target):
    """Retain the Git link and registration throughout fallible content deletion."""
    planned = _PAYLOAD_PLAN.get()
    payload = planned[1] if planned is not None and planned[0] == target else tuple(
        (child, child.is_dir() and not child.is_symlink())
        for child in target.iterdir() if child.name != ".git")
    for child, directory in payload:
        if directory:
            shutil.rmtree(child)
        else:
            child.unlink()
    if payload and any(child.name != ".git" for child in target.iterdir()):
        raise Refused("worktree_payload_changed_during_removal")


def native_removal_preflight(source, target, flags, stack=None):
    """Recheck every native refusal condition immediately before payload deletion."""
    # The tree walk must finish before the final qualification so a concurrent
    # lock is observed by the last refusal check before payload deletion.
    reject_nested_git(target)
    item = qualify(source, target, stack)
    if "locked" in item and flags.count("--force") < 2:
        raise Refused("native_locked:" + item["locked"])
    return item


@contextmanager
def payload_removal_budget(force):
    """Bound interruptible payload deletion and share its deadline with Git."""
    if force:
        yield None
        return
    deadline = time.monotonic() + 1800
    def expired(signum, frame):
        raise subprocess.TimeoutExpired(["worktree", "remove"], 1800,
                                        stderr=b"payload removal deadline expired")
    handler = signal.signal(signal.SIGALRM, expired)
    previous = signal.setitimer(signal.ITIMER_REAL, 1800)
    try:
        yield deadline
    finally:
        signal.setitimer(signal.ITIMER_REAL, *previous)
        signal.signal(signal.SIGALRM, handler)


def ignored_by_snapshot(target, metadata, commit, paths):
    """Evaluate untracked paths against the checkpoint's tracked ignore files."""
    with tempfile.TemporaryDirectory(prefix="worktree-removal-ignore-") as directory:
        rules = Path(directory).resolve()
        for entry in git(target, "ls-tree", "-r", "-z", commit).stdout.split(b"\0"):
            if not entry:
                continue
            header, name = entry.split(b"\t", 1)
            mode, kind, oid = header.split(b" ")
            if Path(os.fsdecode(name)).name == ".gitignore" and mode in (b"100644", b"100755"):
                file = rules / os.fsdecode(name)
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_bytes(git(target, "cat-file", "blob", oid.decode("ascii")).stdout)
        result = git(rules, "--git-dir=" + str(metadata), "--work-tree=" + str(rules),
                     "check-ignore", "--no-index", "-z", "--stdin",
                     input=b"\0".join(paths) + b"\0", check=False)
        if result.returncode not in (0, 1):
            raise GitFailure(result.stderr.decode(errors="replace").strip() or "ignore inspection failed")
        return set(result.stdout.split(b"\0")) >= set(paths)


def finished_operations(metadata):
    for marker in ("MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD", "rebase-merge", "rebase-apply", "sequencer"):
        if (metadata / marker).exists():
            raise Refused("unfinished_operation:" + marker)


def removal_pending(options):
    """Observe resumability without checkpointing or changing the removal record."""
    target = options.path
    with ExitStack() as stack:
        qualify(options.source, target, stack)
        branch = git_scope(stack, options.source, target)
        _, metadata = identity(options.source, target)
        removal = interrupted_removal(target, metadata, stack, options.source, branch,
                                      reconverge=False)
        return dict(event="worktree_removal_pending", path=str(target),
                    commit=removal["commit"] if removal else None, pending=removal is not None)


def interrupted_removal(target, metadata, stack, source, branch, *, reconverge=True):
    """Return the record of an earlier removal whose deletion stopped part way."""
    record = metadata / REMOVAL_RECORD
    if not record.exists():
        return None
    finished_operations(metadata)
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
        if not reconverge:
            raise Refused("interrupted_removal_identity_changed")
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
    status = git(target, "status", "--porcelain", "-z", "--untracked-files=all").stdout.split(b"\0")
    changed = [line for line in status if line and not line.startswith(b" D ")]
    if changed and (any(not line.startswith(b"?? ") for line in changed)
                    or not ignored_by_snapshot(target, metadata, commit, [line[3:] for line in changed])):
        raise Refused("interrupted_removal_tree_changed")
    return removal


LOCK_AGE_SECONDS = 24 * 60 * 60


def qualify(source, path, stack=None, snapshot=None, deadline=None):
    """Validate identity and Git lock age, without inspecting users or contents."""
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
    if "locked" in item:
        if item["locked"].startswith("worktree-init:"):
            try:
                if stack is None:
                    with ExitStack() as probe:
                        tree_scope(probe, source, path, True)
                elif not any(not handle.closed
                             and handle.scope_key == "tree:" + str(path)
                             and handle.scope_exclusive
                             for handle in getattr(stack, "scope_handles", [])):
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
        reject_nested_git(target)
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
                payload = tuple((child, child.is_dir() and not child.is_symlink())
                                for child in target.iterdir() if child.name != ".git")
                payload_token = _PAYLOAD_PLAN.set((target, payload))
                try:
                    qualifying = True
                    native_removal_preflight(source, target, flags, stack)
                    qualifying = False
                    removing = True
                    with payload_removal_budget(options.force) as deadline:
                        remove_payload(target)
                finally:
                    _PAYLOAD_PLAN.reset(payload_token)
                remaining = None if deadline is None else deadline - time.monotonic()
                if remaining is not None and remaining <= 0:
                    raise subprocess.TimeoutExpired(["worktree", "remove"], 1800)
                git(source, "worktree", "remove", *flags, "--", target,
                    timeout=remaining)
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
