"""One fail-closed qualification for registered worktree destruction."""

from contextlib import ExitStack
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import subprocess
import time

from worktree_protocol import (Refused, git, value, common, inventory, identity,
                               acquire, tree_scope, lock_file)


def unreadable(error):
    raise Refused("unreadable_material:" + str(error)) from error


def remote_roots(source, branch):
    roots = []
    for remote in value(source, "remote").splitlines():
        refs = ["refs/heads/dev"]
        if branch:
            refs.append(branch)
        result = git(source, "ls-remote", "--heads", remote, *refs)
        for row in result.stdout.splitlines():
            oid, reference = row.split(b"\t")
            if os.fsdecode(reference) not in refs:
                raise Refused("unexpected_remote_ref")
            tip = oid.decode("ascii")
            git(source, "fetch", "--no-write-fetch-head", "--no-tags", remote, tip)
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


def recovery_objects(source, metadata, branch, head):
    oids = {head}
    files = {"HEAD", "index", "index.lock", "commondir", "gitdir", "locked", "ORIG_HEAD", "COMMIT_EDITMSG"}
    directories = {"logs", "refs"}
    for entry in metadata.iterdir():
        if entry.is_symlink():
            raise Refused("linked_private_metadata")
        if entry.name in directories and entry.is_dir():
            for parent, dirs, names in os.walk(entry, followlinks=False, onerror=unreadable):
                for name in dirs + names:
                    if (Path(parent) / name).is_symlink():
                        raise Refused("linked_private_metadata")
                for name in names:
                    file = Path(parent) / name
                    if entry.name == "logs":
                        oids.update(reflog_oids(file))
                    else:
                        raw = file.read_text().strip()
                        if not re.fullmatch(r"[0-9a-f]{40}|[0-9a-f]{64}", raw):
                            raise Refused("unknown_private_ref")
                        oids.add(raw)
        elif entry.name not in files or not entry.is_file():
            raise Refused("unknown_or_unfinished_metadata:" + entry.name)
    original = metadata / "ORIG_HEAD"
    index_lock = metadata / "index.lock"
    if index_lock.exists() and index_lock.stat().st_size:
        raise Refused("unfinished_index_lock")
    if original.exists():
        oids.add(original.read_text().strip())
    message = metadata / "COMMIT_EDITMSG"
    if message.exists():
        expected = git(source, "show", "-s", "--format=%B", head).stdout
        if message.read_bytes().rstrip(b"\n") != expected.rstrip(b"\n"):
            raise Refused("unpublished_commit_message")
    if branch:
        log = common(source) / "logs" / branch
        if log.exists():
            oids.update(reflog_oids(log))
    return oids


def clean_content(path, metadata, head, object_source=None):
    source = object_source or path
    expected = {}
    for entry in git(source, "ls-tree", "-r", "-z", head).stdout.split(b"\0"):
        if not entry:
            continue
        fields, name = entry.split(b"\t", 1)
        mode, kind, oid = fields.split(b" ")
        if kind != b"blob":
            raise Refused("nested_repository_or_submodule")
        expected[name] = (mode, oid)
    index = {}
    if (metadata / "index").exists():
        for entry in git(path, "ls-files", "--stage", "-z").stdout.split(b"\0"):
            if not entry:
                continue
            fields, name = entry.split(b"\t", 1)
            mode, oid, stage = fields.split(b" ")
            if stage != b"0":
                raise Refused("unmerged_index")
            index[name] = (mode, oid)
        if index != expected:
            raise Refused("staged_material")
    # Inspect actual bytes, ignoring assume-unchanged, skip-worktree and filters.
    # Missing checkout fragments are safe only for a locked interrupted initialization.
    seen = set()
    for parent, dirs, names in os.walk(path, followlinks=False, onerror=unreadable):
        if Path(parent) == path:
            dirs[:] = [name for name in dirs if name != ".git"]
            names = [name for name in names if name != ".git"]
        for name in dirs[:]:
            candidate = Path(parent) / name
            if candidate.is_symlink():
                dirs.remove(name)
                names.append(name)
            elif not any(key.startswith(os.fsencode(str(candidate.relative_to(path))) + b"/")
                         for key in expected):
                if any(candidate.iterdir()):
                    raise Refused("unknown_directory:" + str(candidate.relative_to(path)))
        for name in names:
            file = Path(parent) / name
            key = os.fsencode(str(file.relative_to(path)))
            if key not in expected:
                raise Refused("untracked_or_ignored_material:" + os.fsdecode(key))
            mode, oid = expected[key]
            info = file.lstat()
            if stat.S_ISLNK(info.st_mode) and mode == b"120000":
                actual = git(source, "hash-object", "--stdin", input=os.fsencode(os.readlink(file))).stdout.strip()
            elif stat.S_ISREG(info.st_mode) and mode in (b"100644", b"100755"):
                if bool(info.st_mode & stat.S_IXUSR) != (mode == b"100755"):
                    raise Refused("modified_mode:" + os.fsdecode(key))
                # Hash raw bytes directly: same native Git blob framing, no per-file process.
                algorithm = hashlib.sha1 if len(oid) == 40 else hashlib.sha256
                digest = algorithm()
                digest.update(b"blob " + str(info.st_size).encode("ascii") + b"\0")
                with file.open("rb") as stream:
                    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                        digest.update(chunk)
                actual = digest.hexdigest().encode("ascii")
            else:
                raise Refused("unknown_file_kind:" + os.fsdecode(key))
            if actual != oid:
                raise Refused("dirty_material:" + os.fsdecode(key))
            seen.add(key)
    if seen != set(expected) and (metadata / "index").exists():
        raise Refused("missing_checkout_material")


def cache_exclusion(stack, path):
    # The existing Lean cache guard has its own owner and key. Acquire that exact
    # OS lock as well; participation cannot replace donor/build exclusion.
    address = str((path / ".lake").resolve())
    directory = Path.home() / ".cache" / "stratalint-lean-cache-guards"
    try:
        stack.enter_context(lock_file(directory, address, True))
    except BlockingIOError as error:
        raise Refused("cache_in_use") from error


def qualify(stack, source, path, allow_initialization=False):
    if Path(path).is_symlink():
        raise Refused("linked_tree")
    path = tree_scope(stack, source, path, True)
    item, metadata = identity(source, path)
    rows = inventory(source)
    source_root = Path(value(source, "rev-parse", "--show-toplevel")).resolve()
    if path == source_root or path == Path(rows[0]["worktree"]).resolve():
        raise Refused("current_or_main_worktree")
    if path in Path.cwd().resolve().parents or path == Path.cwd().resolve():
        raise Refused("current_worktree")
    if any(path in Path(row["worktree"]).resolve().parents for row in rows):
        raise Refused("nested_worktree")
    if "locked" in item and not (allow_initialization and
            re.fullmatch(r"worktree-init:[0-9a-f]{32}", item["locked"])):
        raise Refused("intentional_or_unknown_lock")
    branch = item.get("branch")
    if branch:
        acquire(stack, source, "ref:" + branch, True)
    cache_exclusion(stack, path)
    head = value(path, "rev-parse", "HEAD")
    if item.get("HEAD") != head:
        raise Refused("head_changed")
    clean_content(path, metadata, head)
    roots = remote_roots(source, branch)
    for oid in recovery_objects(source, metadata, branch, head):
        retained(source, oid, roots)
    # Observations detect existing nonparticipants; OS entry exclusion supplies
    # continuity for cooperative participants, including inherited descendants.
    sampler = Path(__file__).resolve().parents[1] / "host-cleanup.py"
    result = subprocess.run([sys_executable(), "-B", str(sampler), "active-paths",
                            "--scope", str(path), "--scope", str(metadata)],
                            capture_output=True, timeout=120, check=True)
    for active in json.loads(result.stdout):
        active = Path(active).resolve()
        if active == path or path in active.parents or active == metadata or metadata in active.parents:
            raise Refused("host_activity:" + str(active))
    if identity(source, path) != (item, metadata):
        raise Refused("identity_changed")
    return item


def sys_executable():
    import sys
    return sys.executable


def remove(options):
    names = list(dict.fromkeys(options.names.split()))
    if not names and not options.path:
        raise Refused("names_or_paths_required")
    rows = inventory(options.source)
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
    # All qualifications are held for the full batch. Refusal makes no deletions.
    with ExitStack() as stack:
        for target in sorted(targets):
            item = qualify(stack, options.source, target, options.initialization)
            for raw in options.expected:
                expected = json.loads(raw)
                if Path(expected["path"]).resolve() == target.resolve():
                    if (item.get("HEAD") != expected["head"] or item.get("branch") != expected.get("branch")
                            or "locked" in expected and item.get("locked") != expected["locked"]):
                        raise Refused("observed_identity_changed")
            if options.expected and not any(Path(json.loads(raw)["path"]).resolve() == target.resolve()
                                            for raw in options.expected):
                raise Refused("observed_path_changed")
        for target in targets:
            if options.preview:
                outcomes.append(dict(path=str(target), outcome="would_remove"))
                continue
            try:
                # Never unlock an intentional or initialization lock. The latter
                # qualifies only with the explicit preserved-content path above.
                flags = ["--force", "--force"] if options.initialization else []
                git(options.source, "worktree", "remove", *flags, "--", target,
                    timeout=None if options.force else 300)
                outcomes.append(dict(path=str(target), outcome="removed"))
            except (Refused, OSError, subprocess.SubprocessError) as error:
                outcomes.append(dict(path=str(target), outcome="partial_or_indeterminate", error=str(error)))
    return dict(event="worktree_removal", items=outcomes,
                status="failed" if any(item["outcome"] == "partial_or_indeterminate" for item in outcomes) else "succeeded")


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


def remove_snapshot(options):
    with ExitStack() as stack:
        if options.path.is_symlink():
            raise Refused("linked_snapshot")
        path = tree_scope(stack, options.source, options.path, True)
        if not path.is_dir() or path.is_symlink() or path == Path.cwd().resolve():
            raise Refused("snapshot_identity")
        if any(Path(row["worktree"]).resolve() == path or path in Path(row["worktree"]).resolve().parents
               for row in inventory(options.source)):
            raise Refused("registered_or_nested_tree")
        if (path / ".git").exists() or (path / ".git").is_symlink():
            raise Refused("unregistered_metadata_unknown")
        cache_exclusion(stack, path)
        base = value(options.source, "rev-parse", "--verify", options.base + "^{commit}")
        retained(options.source, base, remote_roots(options.source, None))
        # Use source Git objects for a gitless, partial checkout; every existing
        # byte must match a retained object, and every unknown file is retained.
        clean_content(path, path / ".absent-git-metadata", base, object_source=options.source)
        sampler = Path(__file__).resolve().parents[1] / "host-cleanup.py"
        result = subprocess.run([sys_executable(), "-B", str(sampler), "active-paths", "--scope", str(path)],
                                capture_output=True, check=True, timeout=120)
        if any(Path(active).resolve() == path or path in Path(active).resolve().parents
               for active in json.loads(result.stdout)):
            raise Refused("snapshot_host_activity")
        if not options.preview:
            import shutil
            try:
                shutil.rmtree(path)
            except OSError as error:
                return dict(event="worktree_snapshot", path=str(path),
                            status="partial_or_indeterminate", error=str(error))
        return dict(event="worktree_snapshot", path=str(path),
                    status="would_remove" if options.preview else "removed")
