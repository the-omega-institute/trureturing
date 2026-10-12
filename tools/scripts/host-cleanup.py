#!/usr/bin/env python3
"""Host artifact cleanup and worktree disk preflight; Python 3.9+, macOS/Linux."""

import argparse
from collections import Counter
from contextlib import ExitStack
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import re
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
import time

REPOSITORY = Path(__file__).resolve().parents[2]
# BSD file flags by which the owner or the system marks an entry as not to be removed or changed.
PROTECTED_FLAGS = (stat.UF_IMMUTABLE | stat.UF_APPEND | stat.UF_NOUNLINK |
                   stat.SF_IMMUTABLE | stat.SF_APPEND | stat.SF_NOUNLINK)


def worktree_modules():
    """Load the canonical Git preservation and physical cache-lock owners on demand."""
    directory = str(Path(__file__).resolve().parent / "worktree")
    if directory not in sys.path:
        sys.path.insert(0, directory)
    import worktree_preservation
    import lean_cache_release
    return worktree_preservation, lean_cache_release


def directory_skeleton(path):
    """Only directories, including every descendant, do not establish a Git boundary."""
    pending = [path]
    while pending:
        entry = pending.pop()
        if not stat.S_ISDIR(entry.lstat().st_mode):
            return False
        pending.extend(entry.iterdir())
    return True


def source_object_directories(source, removal_root, preservation):
    """Require complete source history whose object storage survives this removal."""
    config = preservation.git(source, "config", "--get-regexp",
                              r"extensions\.partialclone|remote\..*\.promisor", check=False)
    if (config.returncode not in (0, 1) or config.stdout
            or preservation.value(source, "rev-parse", "--is-shallow-repository") != "false"):
        raise preservation.Refused("repository_unverifiable:source_incomplete_objects")
    pending = [preservation.common(source) / "objects"]
    visited = set()
    removal_root = removal_root.resolve()
    def surviving_path(path):
        physical = path.resolve(strict=True)
        for dependency in (path.absolute(), physical):
            if dependency == removal_root or removal_root in dependency.parents:
                raise preservation.Refused("repository_source_dependency:" + str(dependency))
        return physical
    while pending:
        objects = surviving_path(pending.pop())
        if objects in visited:
            continue
        visited.add(objects)
        if not objects.is_dir() or any((objects / "pack").glob("*.promisor")):
            raise preservation.Refused("repository_unverifiable:source_incomplete_objects")
        alternates = objects / "info/alternates"
        if os.path.lexists(alternates):
            surviving_path(alternates)
            for raw in alternates.read_text().splitlines():
                if not raw or raw.startswith('"'):
                    raise preservation.Refused("repository_unverifiable:source_alternate_path")
                pending.append(objects / raw)
    return sorted(map(str, visited))


def repository_snapshot(path, source, removal_root=None):
    """Certify all local recovery history against the main checkout's retained refs."""
    preservation, _ = worktree_modules()
    git = preservation.git
    source_objects = source_object_directories(source, removal_root or path, preservation)
    metadata = path / ".git"
    if not metadata.is_dir() or metadata.is_symlink():
        raise preservation.Refused("repository_unverifiable:external_gitdir")
    registrations = registered_worktrees(source)
    if any(path == tree or path in tree.parents or tree in path.parents for tree in registrations):
        raise preservation.Refused("protected")
    attachments = registered_worktrees(path)
    if (attachments != [path.resolve()] or (metadata / "worktrees").exists()
            and any((metadata / "worktrees").iterdir())):
        raise preservation.Refused("repository_unverifiable:external_worktree")
    if (Path(preservation.value(path, "rev-parse", "--absolute-git-dir")).resolve() != metadata.resolve()
            or preservation.common(path) != metadata.resolve()
            or Path(preservation.value(path, "rev-parse", "--show-toplevel")).resolve() != path.resolve()):
        raise preservation.Refused("repository_unverifiable:external_gitdir")
    config = git(path, "config", "--get-regexp", r"extensions\.partialclone|remote\..*\.promisor",
                 check=False)
    if config.returncode not in (0, 1) or config.stdout or (metadata / "shallow").exists():
        raise preservation.Refused("repository_unverifiable:incomplete_objects")
    object_directories, visited = [metadata / "objects"], set()
    while object_directories:
        objects = object_directories.pop().resolve()
        if objects in visited:
            continue
        visited.add(objects)
        if metadata.resolve() not in objects.parents or not objects.is_dir():
            raise preservation.Refused("repository_unverifiable:external_alternates")
        alternates = objects / "info/alternates"
        if alternates.exists():
            for raw in alternates.read_text().splitlines():
                if not raw or raw.startswith('"'):
                    raise preservation.Refused("repository_unverifiable:alternate_path")
                object_directories.append(objects / raw)
    for name in ("MERGE_HEAD", "rebase-apply", "rebase-merge", "CHERRY_PICK_HEAD",
                 "REVERT_HEAD", "sequencer", "BISECT_LOG"):
        if (metadata / name).exists():
            raise preservation.Refused("repository_operation")
    if any(metadata.rglob("*.lock")):
        raise preservation.Refused("repository_lock")
    refs = git(path, "for-each-ref", "--format=%(objectname) %(refname)").stdout
    if any(row.endswith(b" refs/stash") for row in refs.splitlines()):
        raise preservation.Refused("repository_stash")
    if git(path, "-c", "core.fsmonitor=false", "status", "--porcelain", "--untracked-files=all",
           env={"GIT_OPTIONAL_LOCKS": "0"}).stdout:
        raise preservation.Refused("repository_dirty")
    oids = {row.split(b" ", 1)[0].decode("ascii") for row in refs.splitlines()}
    head = preservation.value(path, "rev-parse", "--verify", "HEAD")
    oids.add(head)
    logs = metadata / "logs"
    if logs.exists():
        for log in logs.rglob("*"):
            if log.is_file():
                oids.update(preservation.reflog_oids(log))
    fsck = git(path, "fsck", "--full", "--unreachable", "--no-reflogs")
    for row in fsck.stdout.splitlines():
        fields = row.split()
        if len(fields) == 3 and fields[0] in (b"unreachable", b"dangling") and fields[1] == b"commit":
            oids.add(fields[2].decode("ascii"))
    roots = git(source, "for-each-ref", "--format=%(objectname)",
                "refs/heads/", "refs/remotes/", "refs/tags/").stdout.decode("ascii").splitlines()
    root_set = set(roots)
    reachable_objects = None
    required = sorted(oid for oid in oids if set(oid) != {"0"})
    kinds = git(source, "cat-file", "--batch-check=%(objectname) %(objecttype)",
                input=("\n".join(required) + "\n").encode("ascii")).stdout.splitlines()
    if len(kinds) != len(required):
        raise preservation.Refused("repository_unverifiable:object_inventory")
    for oid, row in zip(required, kinds):
        fields = row.decode("ascii").split()
        if len(fields) != 2 or fields[0] != oid:
            raise preservation.Refused("repository_unverifiable:object_inventory")
        if fields[1] == "missing":
            raise preservation.Refused("repository_unique_commits:" + oid)
        # Every retained ref tip is itself a preservation root.
        if oid in root_set:
            continue
        if fields[1] == "commit":
            try:
                containing = [oid] if oid in root_set else sorted(root_set.intersection(
                    git(source, "for-each-ref", "--contains", oid, "--format=%(objectname)",
                        "refs/heads/", "refs/remotes/", "refs/tags/").stdout.decode("ascii").splitlines()))
                preservation.retained(source, oid, containing[:1])
            except preservation.Refused as error:
                raise preservation.Refused("repository_unique_commits:" + oid) from error
        else:
            if reachable_objects is None:
                reachable_objects = set(git(source, "rev-list", "--objects", "--no-object-names",
                                            *roots, "--").stdout.decode("ascii").splitlines()) if roots else set()
            if oid not in reachable_objects:
                raise preservation.Refused("repository_unique_commits:" + oid)
    return dict(path=str(path), head=head, refs=os.fsdecode(refs), roots=sorted(roots), oids=sorted(oids),
                registrations=sorted(map(str, registrations)), attachments=list(map(str, attachments)),
                source_objects=source_objects)


def macos_active_paths(strict_ipc=False):
    """Read typed lsof names; ambiguous named IPC cannot certify inactivity."""
    try:
        result = subprocess.run(["lsof", "-nP", "-a", "-u", str(os.getuid()), "-Fftn"],
                                capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError) as error:
        raise OSError("ipc_activity_unobservable") from error
    if (result.returncode == 0 and (result.stdout or not strict_ipc)
            and (not result.stderr or not strict_ipc)):
        observed, kind = set(), None
        for row in result.stdout.splitlines():
            if row.startswith(("p", "f")):
                kind = None
            elif row.startswith("t"):
                kind = row[1:]
            elif row.startswith("n"):
                raw = row[1:]
                if strict_ipc and kind in (None, "unix", "FIFO"):
                    unnamed = not raw or re.fullmatch(r"->0x[0-9a-fA-F]+", raw)
                    if not unnamed and (not raw.startswith("/") or "\\" in raw):
                        raise OSError("ipc_activity_unobservable:ambiguous_lsof_name")
                if not raw.startswith("/"):
                    continue
                observed.add(Path(raw.removesuffix(" (deleted)")))
        return observed
    if strict_ipc and result.returncode == 1 and not result.stdout and not result.stderr:
        return set()
    raise OSError("ipc_activity_unobservable")


def ipc_paths():
    """Observe named IPC endpoints without opening or connecting to them."""
    if sys.platform != "darwin":
        raise OSError("ipc_activity_unobservable")
    observed, parents = set(), {}
    for endpoint in macos_active_paths(strict_ipc=True):
        if endpoint.parent not in parents:
            parents[endpoint.parent] = endpoint.parent.resolve()
        observed.add(parents[endpoint.parent] / endpoint.name)
    return observed


class LowDiskSpace(RuntimeError):
    pass


def emit(event, **fields):
    print(json.dumps(dict(event=event, **fields), ensure_ascii=True), flush=True)


def check_disk(paths, allow_low_disk=False):
    """Check caller-available bytes, without creating the destination directory."""
    reports = []
    for path in paths:
        existing = Path(path).absolute()
        while not existing.exists():
            existing = existing.parent
        usage = shutil.disk_usage(existing)
        if usage.total <= 0 or not 0 <= usage.free <= usage.total:
            raise OSError("invalid disk usage for " + str(existing))
        low = usage.free * 100 < usage.total * 5
        report = dict(path=str(path), measured_path=str(existing), total_bytes=usage.total,
                      available_bytes=usage.free, available_percent=100 * usage.free / usage.total,
                      overridden=low and allow_low_disk)
        reports.append(report)
        if low and not allow_low_disk:
            raise LowDiskSpace(
                "WORKTREE_LOW_DISK " + json.dumps(report) +
                "; need at least 5% available space; run make -C tools clean-all FORCE=1 "
                "or explicitly pass ALLOW_LOW_DISK=1")
    return reports


class ProtectedPaths:
    def __init__(self, paths):
        self.prefixes = set()
        for path in paths:
            path = Path(path).absolute()
            self.prefixes.update((path, *path.parents))

    def __contains__(self, path):
        return path in self.prefixes


def inspect_candidate(path, cutoff, protected, repository=None, reclaim=True, ipc_observed=False):
    """Fingerprint owned, inactive trees without following links or crossing mounts."""
    path = Path(path).absolute()
    if path.name == ".git" and (not reclaim or not directory_skeleton(path)):
        return dict(reason="repository")
    if not isinstance(protected, ProtectedPaths):
        protected = ProtectedPaths(protected)
    if path in protected:
        return dict(reason="protected")
    if repository is not None:
        try:
            governing = containing_repository(path)
        except OSError as error:
            return dict(reason="repository_unverifiable", detail=str(error))
        if governing is not None and governing != path:
            return dict(reason="repository_unverifiable", detail="partial_repository")
    root_stat = path.lstat()
    if stat.S_ISLNK(root_stat.st_mode):
        return dict(reason="symlink")
    if reclaim and root_stat.st_dev != path.parent.stat().st_dev:
        return dict(reason="mount")
    digest = hashlib.sha256()
    apparent_bytes = 0
    repositories = []
    ipc_observation = None
    has_ipc = False
    lakes = []
    pending = [path]
    while pending:
        entry = pending.pop()
        info = entry.lstat()
        if info.st_uid != os.getuid():
            return dict(reason="not_owned")
        if info.st_dev != root_stat.st_dev:
            return dict(reason="mount")
        if getattr(info, "st_flags", 0) & PROTECTED_FLAGS:
            return dict(reason="protected_flag")
        if "\n" in str(entry) or "\r" in str(entry):
            return dict(reason="unrepresentable_path")
        ipc = reclaim and (stat.S_ISFIFO(info.st_mode) or stat.S_ISSOCK(info.st_mode))
        if not (stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode) or stat.S_ISLNK(info.st_mode) or ipc):
            return dict(reason="special_file")
        if info.st_mtime > (min(cutoff, time.time() - 24 * 3600) if ipc else cutoff):
            return dict(reason="recent")
        if ipc and not ipc_observed:
            try:
                if ipc_observation is None:
                    ipc_observation = ipc_paths()
                if entry.parent.resolve() / entry.name in ipc_observation:
                    return dict(reason="protected")
            except OSError:
                return dict(reason="ipc_activity_unobservable")
        has_ipc = has_ipc or ipc
        digest.update(os.fsencode(str(entry.relative_to(path))))
        digest.update(str((info.st_dev, info.st_ino, info.st_mode, info.st_size,
                           info.st_mtime_ns, info.st_ctime_ns)).encode())
        if stat.S_ISREG(info.st_mode):
            apparent_bytes += info.st_size
        elif stat.S_ISDIR(info.st_mode):
            with os.scandir(entry) as children:
                names = sorted(child.name for child in children)
            if reclaim and entry.name != ".git" and {"HEAD", "objects", "refs"}.issubset(names):
                return dict(reason="repository_unverifiable", detail="bare_repository")
            if ".git" in names:
                if not reclaim or not directory_skeleton(entry / ".git"):
                    if repository is None:
                        return dict(reason="repository")
                    repositories.append(entry)
            if reclaim and entry.name == ".lake":
                lakes.append(str(entry))
            pending.extend(entry / name for name in names)
    minimum_cutoff = time.time() - 24 * 3600
    if repositories and cutoff > minimum_cutoff:
        return inspect_candidate(path, minimum_cutoff, protected, repository=repository, reclaim=reclaim)
    try:
        repositories = [repository_snapshot(entry, repository, path) for entry in repositories]
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        reason = str(error).split(":", 1)[0]
        if reason not in ("protected", "repository_dirty", "repository_stash", "repository_operation",
                          "repository_lock", "repository_unique_commits", "repository_source_dependency"):
            reason = "repository_unverifiable"
        return dict(reason=reason, detail=str(error))
    return dict(reason=None, fingerprint=digest.hexdigest(), apparent_bytes=apparent_bytes,
                repositories=repositories, lakes=lakes, has_ipc=has_ipc)


def remove_tree(path):
    """Remove an inspected owned tree, first granting its owner access to read-only directories."""
    # os.walk does not descend into directory links, so only directories inside the tree change mode.
    for directory, _, _ in os.walk(path):
        mode = stat.S_IMODE(os.lstat(directory).st_mode)
        if mode & stat.S_IRWXU != stat.S_IRWXU:
            os.chmod(directory, mode | stat.S_IRWXU)
    shutil.rmtree(path)


def clean_candidate(path, cutoff, protected, delete=False, repository=None, activity=None,
                    reclaim=True, refresh_activity=False, qualification=None, ipc_observed=False,
                    initial=None):
    path = Path(path).absolute()
    result = dict(path=str(path), action="kept", reason=None, apparent_bytes=0)
    removal_started = False
    try:
        kwargs = {} if repository is None else dict(repository=repository)
        if not reclaim:
            kwargs["reclaim"] = False
        if ipc_observed:
            kwargs["ipc_observed"] = True
        def observe(protection):
            snapshot = inspect_candidate(path, cutoff, protection, **kwargs)
            if snapshot["reason"] is None and qualification:
                qualified = qualification()
                if qualified["reason"] is not None:
                    return qualified
                snapshot["qualification"] = qualified
            return snapshot
        before = observe(protected) if initial is None else initial
        result.update({key: before[key] for key in ("reason", "detail", "apparent_bytes") if key in before})
        if before["reason"] is not None:
            return result
        if not delete:
            result["action"] = "would_remove"
            return result
        with ExitStack() as stack:
            for lake in before.get("lakes", []):
                _, release = worktree_modules()
                stack.enter_context(release.cache_guard(Path(lake).parent))
            refreshed = ProtectedPaths(activity()) if activity and (before.get("repositories") or before.get("has_ipc") or refresh_activity) else protected
            after = observe(refreshed)
            if after != before:
                result["reason"] = "changed"
                return result
            removal_started = True
            if path.is_dir():
                remove_tree(path)
            else:
                path.unlink()
            result["action"] = "removed"
    except BlockingIOError:
        result["reason"] = "cache_busy"
    except FileNotFoundError as error:
        result.update(action="failed" if removal_started else "kept", reason="vanished", detail=str(error))
    except PermissionError as error:
        if removal_started:
            result.update(action="failed", reason=str(error))
        else:
            result.update(action="kept", reason="unreadable", detail=str(error))
    except OSError as error:
        if ipc_observed and not removal_started:
            result.update(action="kept", reason="ipc_activity_unobservable", detail=str(error))
        else:
            result.update(action="failed", reason=str(error))
    return result


def clean_ipc_batch(paths, cutoff, protected, delete, activity, repository=None):
    """Share complete IPC observations across a batch, then recheck each endpoint's identity."""
    base = protected if isinstance(protected, ProtectedPaths) else ProtectedPaths(protected)
    def protection():
        observed = ProtectedPaths(activity())
        observed.prefixes.update(base.prefixes)
        return observed
    snapshots = []
    try:
        observed = protection()
        for path in paths:
            try:
                snapshots.append((path, inspect_candidate(path, cutoff, observed,
                                                         repository=repository, ipc_observed=True)))
            except OSError as error:
                snapshots.append((path, dict(reason="unreadable", detail=str(error))))
    except (OSError, subprocess.SubprocessError) as error:
        for path in paths:
            yield dict(path=str(path), action="kept", reason="ipc_activity_unobservable",
                       detail=str(error), apparent_bytes=0)
        return
    for path, before in snapshots:
        try:
            yield clean_candidate(path, cutoff, observed, delete=delete, initial=before, ipc_observed=True,
                                  repository=repository,
                                  activity=lambda: protection().prefixes, refresh_activity=True)
        except (OSError, subprocess.SubprocessError) as error:
            yield dict(path=str(path), action="kept", reason="ipc_activity_unobservable",
                       detail=str(error), apparent_bytes=0)


def children(root):
    if root.is_symlink():
        raise OSError("artifact root must not be a symlink: " + str(root))
    if root.exists():
        yield from root.iterdir()


def superseded_releases(package):
    """Yield a Codex package's releases other than the one its current link selects."""
    current = package / "current"
    if package.is_symlink():
        return
    releases = package / "releases"
    selected = current.resolve()
    # Without a resolvable current release in this package, no release can be called superseded.
    if selected.parent != releases.resolve() or not selected.is_dir():
        return
    for release in children(releases):
        if release.name != selected.name:
            yield release


def candidates(codex, sshx, tmp_roots):
    for name in ("sessions", "archived_sessions"):
        root = codex / name
        if root.is_symlink():
            raise OSError("artifact root must not be a symlink: " + str(root))
        for path in root.rglob("rollout-*.jsonl"):
            yield "codex", path
    for name in ("shell_snapshots", "log"):
        for path in children(codex / name):
            yield "codex", path
    for path in children(codex / "tmp"):
        if path.name == "arg0" and path.is_dir() and not path.is_symlink():
            for run in children(path):
                yield "codex", run
        else:
            yield "codex", path
    for package in children(codex / "packages"):
        for release in superseded_releases(package):
            yield "codex", release
    for path in children(sshx):
        if re.fullmatch(r"[0-9a-f]{24}", path.name):
            yield "sshx", path
    for root in tmp_roots:
        for path in children(root):
            yield "tmp", path


def linux_observation_unavailable(process, boundary, error):
    """Only a completely observed terminal thread group has no active handles."""
    try:
        process.stat()
    except (FileNotFoundError, ProcessLookupError):
        return
    status = {}
    try:
        for line in (process / "status").read_text().splitlines():
            key, separator, value = line.partition(":")
            if separator and key in ("State", "Threads", "Uid"):
                status[key] = value.strip()
        if status.get("State", "").split()[:1] in (["Z"], ["X"]):
            # A terminal leader alone does not certify surviving threads.
            tasks = list((process / "task").iterdir())
            if status.get("Threads") == "1" and [task.name for task in tasks] == [process.name]:
                observed = (tasks[0] / "status").read_text()
                fields = dict(line.split(":", 1) for line in observed.splitlines() if ":" in line)
                if (fields.get("State", "").split()[:1] in (["Z"], ["X"])
                        and fields.get("Threads", "").strip() == "1"):
                    return
    except (OSError, ValueError):
        # A missing status/task file is not proof of process disappearance.
        try:
            process.stat()
        except (FileNotFoundError, ProcessLookupError):
            return
    raise OSError("linux_activity_unavailable " + json.dumps(dict(
        process=str(process), boundary=boundary, status=status, error=str(error)))) from error


def active_paths(codex, scopes=(), strict_ipc=False):
    """Read open files/cwds and process arguments for the current user only."""
    protected = {Path.cwd().resolve(), Path(__file__).resolve()}
    scopes = tuple(str(Path(scope).resolve()) for scope in scopes)

    physical_parents = {}

    def open_path(raw):
        # Kernel observations already resolve the endpoint. Canonicalize parent
        # aliases once per directory; symbolic process argv is resolved below.
        normalized = os.path.normpath(raw)
        if not scopes or any(normalized == scope or normalized.startswith(scope + os.sep) for scope in scopes):
            path = Path(normalized)
            if path.parent not in physical_parents:
                physical_parents[path.parent] = path.parent.resolve()
            protected.add(physical_parents[path.parent] / path.name)
    if sys.platform.startswith("linux"):
        for process in Path("/proc").iterdir():
            if not process.name.isdigit():
                continue
            try:
                if process.stat().st_uid != os.getuid():
                    continue
            except (FileNotFoundError, ProcessLookupError):
                continue
            try:
                descriptors = list((process / "fd").iterdir())
            except (FileNotFoundError, ProcessLookupError, PermissionError) as error:
                linux_observation_unavailable(process, "fd_inventory", error)
                continue
            cwd = process / "cwd"
            missing_cwd = None
            for link in [cwd, *descriptors]:
                try:
                    target = os.readlink(link).removesuffix(" (deleted)")
                except PermissionError as error:
                    linux_observation_unavailable(process, "cwd" if link == cwd else "fd", error)
                    break
                except (FileNotFoundError, ProcessLookupError) as error:
                    # Closing one handle must not hide the remaining handles.
                    if link == cwd:
                        missing_cwd = error
                    continue
                if target.startswith("/"):
                    open_path(target)
            if missing_cwd is not None:
                linux_observation_unavailable(process, "cwd", missing_cwd)
    elif sys.platform == "darwin":
        for path in macos_active_paths(strict_ipc=strict_ipc):
            open_path(str(path))
    else:
        raise OSError("host cleanup supports macOS and Linux")
    result = subprocess.run(["ps", "-axo", "uid=,pid=,args=" if scopes else "uid=,args="],
                            capture_output=True, text=True, timeout=30)
    if result.returncode != 0:
        raise OSError("cannot inspect process arguments: " + result.stderr.strip())
    for line in result.stdout.splitlines():
        fields = line.strip().split(None, 2 if scopes else 1)
        if scopes:
            # The sampler and its inspecting caller name their target in argv.
            # Their real cwd/open handles remain inspected; argv is not a user.
            if len(fields) != 3 or fields[1] in (str(os.getpid()), str(os.getppid())):
                continue
            fields = [fields[0], fields[2]]
        if len(fields) != 2 or fields[0] != str(os.getuid()):
            continue
        try:
            tokens = shlex.split(fields[1])
        except ValueError:
            # ps does not preserve argv quoting; open-file and cwd evidence is primary.
            tokens = fields[1].split()
        for token in tokens:
            value = token.split("=", 1)[-1] if token.startswith("--") else token
            if value.startswith("/"):
                protected.add(Path(value).resolve())
    active_ids = {os.environ.get("CODEX_THREAD_ID", ""), os.environ.get("CODEX_SESSION_ID", "")}
    for lock in children(codex / "thread-writer-locks"):
        if lock.is_symlink() or not lock.is_file():
            continue
        with lock.open("rb") as handle:
            try:
                fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                fcntl.flock(handle, fcntl.LOCK_UN)
            except BlockingIOError:
                active_ids.add(lock.stem)
    for name in ("sessions", "archived_sessions", "shell_snapshots"):
        for path in (codex / name).rglob("*"):
            if path.is_file() and any(identity and identity in path.name for identity in active_ids):
                protected.add(path.resolve())
    return protected


def registered_worktrees(repository):
    preservation, _ = worktree_modules()
    result = preservation.git(repository, "worktree", "list", "--porcelain", "-z", timeout=60)
    # Git lists the main worktree first; it survives registered-tree cleanup.
    return [Path(os.fsdecode(field[len(b"worktree "):])).resolve()
            for field in result.stdout.split(b"\0") if field.startswith(b"worktree ")]


def containing_repository(path):
    """Find the governing Git boundary, including nested project directories."""
    for parent in (path, *path.parents):
        marker = parent / ".git"
        if os.path.lexists(marker) and not directory_skeleton(marker):
            return parent
        if all((parent / name).exists() for name in ("HEAD", "objects", "refs")):
            raise OSError("repository_unverifiable:bare_repository")
    return None


def artifact_lakes(path, protected, worktrees):
    """Find private cache roots without splitting ordinary siblings or entering Git metadata."""
    device, pending = path.lstat().st_dev, [path]
    while pending:
        entry = pending.pop()
        info = entry.lstat()
        if (not stat.S_ISDIR(info.st_mode) or info.st_dev != device or info.st_uid != os.getuid()
                or getattr(info, "st_flags", 0) & PROTECTED_FLAGS
                or entry in protected or any(tree == entry or tree in entry.parents for tree in worktrees)):
            continue
        if entry.name == ".lake":
            yield entry, containing_repository(entry.parent) is not None
        else:
            pending.extend(child for child in entry.iterdir() if child.name != ".git")


def clean_generated_build(lake, cutoff, protected, source, delete, activity):
    """Reclaim only build output under its physical cache guard, retaining registered trees."""
    path = lake / "build"
    result = dict(path=str(path), action="kept", reason=None, apparent_bytes=0)
    try:
        _, release = worktree_modules()
        with release.cache_guard(lake.parent):
            def qualify():
                registrations = registered_worktrees(source)
                if any(tree == path or tree in path.parents for tree in registrations):
                    return dict(reason="protected")
                info = lake.lstat()
                if stat.S_ISLNK(info.st_mode):
                    return dict(reason="symlink")
                if info.st_uid != os.getuid():
                    return dict(reason="not_owned")
                if info.st_dev != lake.parent.stat().st_dev:
                    return dict(reason="mount")
                if getattr(info, "st_flags", 0) & PROTECTED_FLAGS:
                    return dict(reason="protected_flag")
                governing = containing_repository(lake.parent)
                attachments = []
                if governing is not None:
                    preservation, _ = worktree_modules()
                    attachments = registered_worktrees(governing)
                    if (not (governing / ".git").is_dir()
                            or attachments != [governing.resolve()]):
                        return dict(reason="protected")
                    top = Path(preservation.value(governing, "rev-parse", "--show-toplevel")).resolve()
                    if top != governing.resolve():
                        return dict(reason="repository_unverifiable")
                    if preservation.git(top, "ls-files", "--", str(path.relative_to(top))).stdout:
                        return dict(reason="protected")
                return dict(reason=None, registrations=sorted(map(str, registrations)),
                            attachments=list(map(str, attachments)),
                            lake=(info.st_dev, info.st_ino, info.st_mode, info.st_ctime_ns),
                            repository=str(governing) if governing is not None else None)
            if delete:
                protected = ProtectedPaths(activity())
            return clean_candidate(path, min(cutoff, time.time() - 24 * 3600), protected, delete=delete,
                                   activity=activity, refresh_activity=True, qualification=qualify)
    except BlockingIOError:
        result["reason"] = "cache_busy"
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        result.update(reason="unreadable", detail=str(error))
    return result


def clean_worktrees(repository, base, delete, active_paths=(), working_directory=None):
    arguments = ["/bin/bash", str(repository / "tools/scripts/clean-lanes.sh"),
                 "--base", base, "--lanes-only"]
    if delete:
        arguments.append("--force")
    return subprocess.run(arguments, cwd=working_directory or repository).returncode


def nonnegative_hours(value):
    hours = float(value)
    if not math.isfinite(hours) or hours < 0:
        raise argparse.ArgumentTypeError("age must be a finite nonnegative number of hours")
    return hours


def run_clean(options):
    caller = Path.cwd().resolve()
    options.repository = options.repository.absolute()
    options.codex_home = options.codex_home.absolute()
    options.sshx_home = options.sshx_home.absolute()
    options.tmp_root = [path.absolute() for path in options.tmp_root]
    # Worktree removal may unlink both the caller and the repository. Keep
    # filesystem measurements on the same volume through an OS-owned handle.
    descriptor = os.open(options.repository, os.O_RDONLY)
    try:
        os.chdir("/")
        return clean_from_anchor(options, caller, descriptor)
    finally:
        os.close(descriptor)
        if caller.is_dir():
            os.chdir(caller)


def clean_from_anchor(options, caller, disk_descriptor):
    codex = options.codex_home.absolute()
    sshx = options.sshx_home.absolute()
    if codex.is_symlink() or sshx.is_symlink():
        raise OSError("Codex and sshx roots must not be symlinks")
    codex, sshx = codex.resolve(), sshx.resolve()
    roots = {path.resolve() for path in options.tmp_root}
    forbidden = {Path("/"), Path.home().resolve(), options.repository.resolve(), codex, sshx}
    if roots & forbidden:
        raise OSError("temporary root must not be /, the home, repository, Codex or sshx root")
    for root in roots | {codex, sshx}:
        if root.exists() and not root.is_dir():
            raise OSError("artifact root must be a directory: " + str(root))
    roots = {path for path in roots if not any(parent in roots for parent in path.parents)}
    # Registered-tree disposal can remove this program's source checkout.
    worktree_modules()
    inventory = registered_worktrees(options.repository)
    worktrees = set(inventory)
    lanes_exit = clean_worktrees(options.repository, options.base, options.delete,
                                working_directory=next(iter(inventory), options.repository))
    try:
        active = active_paths(codex)
    except OSError as error:
        emit("host_cleanup_summary", status="failed", worktree_exit=lanes_exit,
             inventory_error=str(error), artifact_sweep="not_started")
        return 1
    protected = active | worktrees | {caller}
    protections = {"codex": ProtectedPaths(protected), "sshx": ProtectedPaths(protected),
                   "tmp": ProtectedPaths(protected | {codex, sshx})}
    now = time.time()
    cutoff = now - options.min_age_hours * 3600
    before = shutil.disk_usage(disk_descriptor).free
    counts, skipped = Counter(), Counter()
    apparent_bytes = 0
    seen = set()
    inventory_error = None
    main_checkout = next(iter(inventory), options.repository)
    seen_lakes = set()
    ipc_candidates = []
    def record(category, result):
        nonlocal apparent_bytes
        counts[category + ":" + result["action"]] += 1
        if result["action"] in ("would_remove", "removed"):
            apparent_bytes += result["apparent_bytes"]
        elif result["action"] == "kept":
            skipped[result["reason"]] += 1
        if options.verbose or result["action"] == "failed" or result["reason"] == "unreadable":
            emit("host_cleanup_item", category=category, **result)

    def fresh_protection():
        return active_paths(codex) | set(registered_worktrees(main_checkout)) | {caller}

    def clean_staging(lake):
        if lake in seen_lakes:
            return
        seen_lakes.add(lake)
        _, release = worktree_modules()
        def inspect(path):
            protection = ProtectedPaths(active_paths(codex) | {caller}) if options.delete else ProtectedPaths(active | {caller})
            return inspect_candidate(path, cutoff, protection)
        for result in release.clean_staging(lake, cutoff=cutoff, now=now,
                                          delete=options.delete, inspect=inspect):
            record("lean_staging", result)
    try:
        for tree in inventory:
            lake = tree / ".lake"
            if lake.is_dir() and not lake.is_symlink():
                clean_staging(lake)
        for category, path in candidates(codex, sshx, roots):
            if path in seen:
                continue
            seen.add(path)
            if any(parent in worktrees for parent in path.parents):
                result = dict(path=str(path), action="kept", reason="protected", apparent_bytes=0)
            elif category != "codex" and any(parent.name == ".lake" for parent in path.parents):
                lake = next(parent for parent in path.parents if parent.name == ".lake")
                clean_staging(lake)
                if path == lake / "build":
                    result = clean_generated_build(lake, cutoff, protections[category],
                                                   main_checkout, options.delete, fresh_protection)
                else:
                    result = dict(path=str(path), action="kept", reason="protected", apparent_bytes=0)
            else:
                if category != "codex" and sys.platform == "darwin":
                    try:
                        mode = path.lstat().st_mode
                    except FileNotFoundError:
                        record(category, dict(path=str(path), action="kept", reason="vanished", apparent_bytes=0))
                        continue
                    except PermissionError as error:
                        record(category, dict(path=str(path), action="kept", reason="unreadable",
                                              detail=str(error), apparent_bytes=0))
                        continue
                    if stat.S_ISFIFO(mode) or stat.S_ISSOCK(mode):
                        ipc_candidates.append((category, path))
                        continue
                result = clean_candidate(path, cutoff, protections[category], options.delete,
                                         repository=None if category == "codex" else main_checkout,
                                         activity=fresh_protection, reclaim=category != "codex")
            record(category, result)
            if category != "codex" and result["action"] == "kept" and (
                    result["reason"] == "recent" or result["reason"].startswith("repository")):
                for lake, repository in artifact_lakes(path, protections[category], worktrees):
                    if repository:
                        clean_staging(lake)
                    if (lake / "build").exists():
                        record(category, clean_generated_build(lake, cutoff, protections[category],
                                                              main_checkout, options.delete, fresh_protection))
        if ipc_candidates:
            categories = dict((path, category) for category, path in ipc_candidates)
            def ipc_activity():
                registrations = set(registered_worktrees(main_checkout))
                active = active_paths(codex, strict_ipc=True) | {caller, codex, sshx}
                active.update(path for path in categories if any(parent in registrations for parent in path.parents))
                return active
            for result in clean_ipc_batch(list(categories), cutoff, protections["tmp"], options.delete,
                                         ipc_activity, repository=main_checkout):
                record(categories[Path(result["path"])], result)
    except OSError as error:
        inventory_error = str(error)
    failed = inventory_error is not None or lanes_exit != 0 or any(key.endswith(":failed") for key in counts)
    emit("host_cleanup_summary", mode="delete" if options.delete else "dry_run",
         min_age_hours=options.min_age_hours, counts=dict(counts), skipped=dict(skipped),
         candidate_apparent_bytes=apparent_bytes, worktree_exit=lanes_exit,
         inventory_error=inventory_error,
         disk_available_before=before, disk_available_after=shutil.disk_usage(disk_descriptor).free,
         status="failed" if failed else "succeeded")
    return 1 if failed else 0


def main(arguments=None):
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    disk = commands.add_parser("check-disk", help="reject worktree creation below 5%% available disk space")
    disk.add_argument("--path", type=Path, action="append", required=True)
    disk.add_argument("--allow-low-disk", action="store_true")
    activity = commands.add_parser("active-paths", help="read current host activity for worktree reclamation")
    activity.add_argument("--scope", type=Path, action="append", default=[])
    clean = commands.add_parser("clean", help="preview inactive owned artifacts; --delete executes")
    clean.add_argument("--repository", type=Path, default=REPOSITORY)
    clean.add_argument("--base", default="origin/dev")
    clean.add_argument("--codex-home", type=Path,
                       default=Path(os.environ.get("CODEX_HOME") or Path.home() / ".codex"))
    clean.add_argument("--sshx-home", type=Path,
                       default=Path(os.environ.get("SSHX_HOME") or Path.home() / ".sshx"))
    clean.add_argument("--tmp-root", type=Path, action="append")
    clean.add_argument("--min-age-hours", type=nonnegative_hours, default=24)
    clean.add_argument("--delete", action="store_true")
    clean.add_argument("--verbose", action="store_true", help="list individual paths, including kept artifacts")
    options = parser.parse_args(arguments)
    try:
        if options.command == "active-paths":
            codex = Path(os.environ.get("CODEX_HOME") or Path.home() / ".codex")
            print(json.dumps(sorted(str(path) for path in active_paths(codex, options.scope))))
            return 0
        if options.command == "check-disk":
            for report in check_disk(options.path, options.allow_low_disk):
                emit("worktree_disk", **report)
            return 0
        if options.tmp_root is None:
            options.tmp_root = [Path("/tmp"), Path(tempfile.gettempdir())]
        # Use a named, per-user lock so concurrent sweeps cannot delete the same tree.
        lock_path = Path(tempfile.gettempdir()) / ("trureturing-clean-all-" + str(os.getuid()) + ".lock")
        descriptor = os.open(lock_path, os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
        with os.fdopen(descriptor, "r+") as lock:
            info = os.fstat(lock.fileno())
            if info.st_uid != os.getuid() or info.st_nlink != 1 or not stat.S_ISREG(info.st_mode):
                raise OSError("invalid cleanup lock")
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            return run_clean(options)
    except LowDiskSpace as error:
        print(str(error), file=sys.stderr)
        return 73
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print("HOST_CLEANUP_FAILED " + str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
