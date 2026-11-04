#!/usr/bin/env python3
"""Host artifact cleanup and worktree disk preflight; Python 3.9+, macOS/Linux."""

import argparse
from collections import Counter
from contextlib import ExitStack
import ctypes
import errno
import fcntl
import hashlib
import json
import math
import os
from pathlib import Path
import re
import select
import shlex
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import uuid

try:
    from maintenance_log import safe_append
except (ImportError, OSError):
    def safe_append(script, event, *, repository=None, **fields):
        return False

REPOSITORY = Path(__file__).resolve().parents[2]
LOG_REPOSITORY = REPOSITORY
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


def macos_active_paths():
    """Read absolute paths held by the current user's processes."""
    try:
        result = subprocess.run(["lsof", "-nP", "-l", "-a", "-u", str(os.getuid()), "-Fftn"],
                                capture_output=True, text=True, timeout=120)
    except (OSError, subprocess.SubprocessError) as error:
        raise OSError("activity_unobservable") from error
    if result.returncode == 0 and result.stdout:
        observed = set()
        for row in result.stdout.splitlines():
            if row.startswith("n") and row[1:].startswith("/"):
                observed.add(Path(row[1:].removesuffix(" (deleted)")))
        return observed
    if result.returncode == 1 and not result.stdout and not result.stderr:
        return set()
    raise OSError("activity_unobservable")


class LowDiskSpace(RuntimeError):
    pass


def emit(event, **fields):
    row = dict(event=event, **fields)
    print(json.dumps(row, ensure_ascii=True), flush=True)
    if event.endswith("_summary") or event.endswith("_warning") or event == "worktree_disk":
        safe_append("host-cleanup", event, repository=LOG_REPOSITORY, **fields)


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


class RecoverySearchLimit(ValueError):
    pass


class RefRecovery:
    """Check intact path/blob pairs using sampled trees and bounded retained-history lookups."""
    REF_TIP_LIMIT = 16
    HISTORY_LIMIT = 32
    HISTORY_LOOKUP_LIMIT = 128
    HISTORY_LOOKUP_SECONDS = 15
    HISTORY_SEARCH_SECONDS = 120

    def __init__(self, repository):
        self.repository = repository
        self.candidate = None
        self.refs = None
        self.roots = []
        self.scanned = set()
        self.reachable = set()
        self._algorithm = None

    @property
    def algorithm(self):
        if self._algorithm is None:
            preservation, _ = worktree_modules()
            self._algorithm = preservation.git(self.repository, "rev-parse", "--show-object-format").stdout.strip().decode("ascii")
        return self._algorithm

    def close(self):
        self.refs = None
        self.roots.clear()
        self.scanned.clear()
        self.reachable.clear()

    def selected_roots(self):
        # Names prioritize evidence only; even an exact match certifies no bytes.
        name = os.fsencode(self.candidate.name) if self.candidate is not None else b""
        name = re.sub(rb"(?:-cleanup-[0-9a-f]{32})+$", b"", name)
        def priority(root):
            ref = root[0]
            leaf = ref.rsplit(b"/", 1)[-1]
            matches = name == leaf or name.endswith(b"-" + leaf)
            return (-len(leaf) if matches else 0, ref)
        return list(dict.fromkeys(oid for _, oid in sorted(self.roots, key=priority)))[:self.REF_TIP_LIMIT]

    def scan_commit(self, commit):
        if commit in self.scanned:
            return
        preservation, _ = worktree_modules()
        listing = preservation.git(self.repository, "--no-replace-objects", "ls-tree", "-r", "-z",
                                   "--full-tree", commit.decode("ascii"), "--", "Blueprint", timeout=60).stdout
        for row in listing.split(b"\0"):
            if not row:
                continue
            metadata, separator, path = row.partition(b"\t")
            fields = metadata.split()
            if not separator or len(fields) != 3:
                raise ValueError("recovery_tree_unreadable")
            if fields[1] == b"blob":
                self.reachable.add((path, fields[2]))
        self.scanned.add(commit)

    def find_history(self, missing):
        """Raw diffs certify a path's blob in a reachable commit or its reachable parent."""
        if len(missing) > self.HISTORY_LOOKUP_LIMIT:
            raise RecoverySearchLimit("lookup_count=" + str(len(missing)) +
                                      " limit=" + str(self.HISTORY_LOOKUP_LIMIT))
        preservation, _ = worktree_modules()
        roots = b"\n".join(dict.fromkeys(oid for _, oid in self.roots)) + b"\n"
        deadline = time.monotonic() + self.HISTORY_SEARCH_SECONDS
        for path, oid in sorted(missing):
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise RecoverySearchLimit("history_deadline")
            try:
                evidence = preservation.git(self.repository, "--no-replace-objects", "--literal-pathspecs",
                    "log", "--full-history", "-m", "--raw", "-z", "--no-abbrev", "--no-renames",
                    "--no-ext-diff", "--no-textconv", "--format=", "--max-count=1",
                    "--find-object=" + oid.decode("ascii"), "--stdin", "--", os.fsdecode(path),
                    input=roots, timeout=min(remaining, self.HISTORY_LOOKUP_SECONDS)).stdout
            except subprocess.TimeoutExpired as error:
                raise RecoverySearchLimit("history_timeout") from error
            if time.monotonic() >= deadline:
                raise RecoverySearchLimit("history_deadline")
            if not evidence:
                continue
            rows = evidence.split(b"\0")
            if rows[-1] or len(rows) % 2 != 1:
                raise ValueError("recovery_history_unreadable")
            for metadata, name in zip(rows[0:-1:2], rows[1:-1:2]):
                fields = re.fullmatch(rb":([0-7]{6}) ([0-7]{6}) ([0-9a-f]{40}|[0-9a-f]{64}) "
                                      rb"([0-9a-f]{40}|[0-9a-f]{64}) [AMDT]", metadata.lstrip(b"\n"))
                if fields is None:
                    raise ValueError("recovery_history_unreadable")
                old_mode, new_mode, old_oid, new_oid = fields.groups()
                blob_modes = (b"100644", b"100755", b"120000")
                if name == path and (old_oid == oid and old_mode in blob_modes or
                                     new_oid == oid and new_mode in blob_modes):
                    self.reachable.add((path, oid))

    def check(self, wanted):
        preservation, _ = worktree_modules()
        from worktree_protocol import git_environment, scope_fds
        refs = preservation.git(self.repository, "for-each-ref", "--format=%(refname) %(objectname)").stdout
        if refs != self.refs:
            # Peel snapshot OIDs, so a moving ref cannot substitute another root.
            records = [row.split(b" ", 1) for row in refs.splitlines()]
            names = [oid + b"^{commit}\n" for _, oid in records]
            peeled = preservation.git(self.repository, "--no-replace-objects", "cat-file",
                                      "--batch-check=%(objectname) %(objecttype)", input=b"".join(names)).stdout
            rows = peeled.splitlines()
            if len(rows) != len(records):
                raise ValueError("recovery_roots_unreadable")
            self.roots = [(record[0], row.split()[0]) for record, row in zip(records, rows)
                          if row.endswith(b" commit")]
            self.refs, self.reachable, self.scanned = refs, set(), set()
        roots = self.selected_roots()
        for root in roots:
            if wanted <= self.reachable:
                break
            self.scan_commit(root)
        if roots and not wanted <= self.reachable:
            # Sample commit history without enumerating the reachable object database.
            history = preservation.git(self.repository, "--no-replace-objects", "rev-list",
                                       "--max-count=" + str(self.HISTORY_LIMIT), "--stdin",
                                       input=b"\n".join(roots) + b"\n", timeout=60).stdout
            for commit in history.splitlines():
                self.scan_commit(commit)
                if wanted <= self.reachable:
                    break
        missing = set(wanted) - self.reachable
        if missing and self.roots:
            self.find_history(missing)
            missing -= self.reachable
        if not missing:
            # Listing a blob does not establish that its bytes are present and intact.
            wanted_blobs = sorted({oid for _, oid in wanted})
            with tempfile.TemporaryFile() as blobs:
                subprocess.run(["git", "--no-replace-objects", "-C", str(self.repository), "cat-file", "--batch"],
                               input=b"\n".join(wanted_blobs) + b"\n", stdout=blobs,
                               stderr=subprocess.PIPE, check=True, timeout=60,
                               env=git_environment(), pass_fds=scope_fds())
                blobs.seek(0)
                for oid in wanted_blobs:
                    header = blobs.readline().split()
                    if len(header) != 3 or header[:2] != [oid, b"blob"]:
                        raise ValueError("recovery_blob_unreadable")
                    size = int(header[2])
                    digest = hashlib.new(self.algorithm, b"blob " + header[2] + b"\0")
                    remaining = size
                    while remaining > 0:
                        chunk = blobs.read(min(remaining, 1024 * 1024))
                        if not chunk:
                            raise ValueError("recovery_blob_truncated")
                        digest.update(chunk)
                        remaining -= len(chunk)
                    if blobs.read(1) != b"\n" or digest.hexdigest().encode("ascii") != oid:
                        missing.update(pair for pair in wanted if pair[1] == oid)
        if preservation.git(self.repository, "for-each-ref", "--format=%(refname) %(objectname)").stdout != refs:
            raise ValueError("recovery_refs_changed")
        return missing


def inspect_candidate(path, cutoff, protected, repository=None, reclaim=True, remnant=False, recovery=None,
                      verify_recovery=True, rollout_files=None):
    """Fingerprint owned, inactive trees without following links or crossing mounts."""
    path = Path(path).absolute()
    if path.name == ".git" and not reclaim:
        return dict(reason="repository")
    if not isinstance(protected, ProtectedPaths):
        protected = ProtectedPaths(protected)
    if path in protected:
        return dict(reason="protected")
    if repository is not None:
        try:
            registrations = registered_worktrees(repository)
            if any(path == tree or path in tree.parents or tree in path.parents for tree in registrations):
                return dict(reason="protected")
        except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
            return dict(reason="repository_unverifiable", detail=str(error))
    root_stat = path.lstat()
    if stat.S_ISLNK(root_stat.st_mode):
        return dict(reason="symlink")
    if rollout_files is not None and not stat.S_ISDIR(root_stat.st_mode):
        return dict(reason="rollout_shape")
    if remnant and not stat.S_ISDIR(root_stat.st_mode):
        return dict(reason="not_directory")
    if reclaim and root_stat.st_dev != path.parent.stat().st_dev:
        return dict(reason="mount")
    digest = hashlib.sha256()
    apparent_bytes = 0
    lakes = []
    blueprint = set()
    shape_reason = None
    pending = [path]
    while pending:
        entry = pending.pop()
        info = entry.lstat()
        if info.st_uid != os.getuid():
            return dict(reason="not_owned")
        if info.st_dev != root_stat.st_dev:
            return dict(reason="mount")
        if rollout_files is not None and entry != path and not stat.S_ISREG(info.st_mode):
            return dict(reason="rollout_shape")
        if remnant and stat.S_ISLNK(info.st_mode):
            return dict(reason="symlink")
        if getattr(info, "st_flags", 0) & PROTECTED_FLAGS:
            return dict(reason="protected_flag")
        if "\n" in str(entry) or "\r" in str(entry):
            return dict(reason="unrepresentable_path")
        # FIFOs and sockets hold no data; reclaimable trees treat them like empty files.
        if not (stat.S_ISREG(info.st_mode) or stat.S_ISDIR(info.st_mode) or stat.S_ISLNK(info.st_mode)
                or reclaim and not remnant and (stat.S_ISFIFO(info.st_mode) or stat.S_ISSOCK(info.st_mode))):
            return dict(reason="special_file")
        if info.st_mtime > cutoff:
            return dict(reason="recent")
        digest.update(os.fsencode(str(entry.relative_to(path))))
        digest.update(str((info.st_dev, info.st_ino, info.st_mode, info.st_size,
                           info.st_mtime_ns, None if remnant and entry == path else info.st_ctime_ns)).encode())
        if stat.S_ISREG(info.st_mode):
            apparent_bytes += info.st_size
            if remnant:
                with entry.open("rb") as handle:
                    if path / "Blueprint" in entry.parents:
                        blob = hashlib.new(recovery.algorithm)
                        blob.update(b"blob " + str(info.st_size).encode("ascii") + b"\0")
                        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                            blob.update(chunk)
                        blueprint.add((os.fsencode(str(entry.relative_to(path))),
                                       blob.hexdigest().encode("ascii")))
                        digest.update(blob.digest())
                if entry.parent == path:
                    shape_reason = "lake_content" if entry.name == ".lake" else "unknown_top_level"
                if entry == path / ".lake/build":
                    shape_reason = "lake_content"
        elif stat.S_ISDIR(info.st_mode):
            with os.scandir(entry) as children:
                names = sorted(child.name for child in children)
            if rollout_files is not None and tuple(names) != rollout_files:
                return dict(reason="rollout_shape")
            if not reclaim and ".git" in names:
                return dict(reason="repository")
            if remnant:
                if ".git" in names or {"HEAD", "objects", "refs"}.issubset(names):
                    return dict(reason="repository")
                if entry == path and set(names) - {".lake", "Blueprint"}:
                    return dict(reason="unknown_top_level")
                if entry == path / ".lake" and set(names) - {"build"}:
                    return dict(reason="lake_content")
            if reclaim and entry.name == ".lake":
                lakes.append(str(entry.relative_to(path)) if remnant else str(entry))
            pending.extend(entry / name for name in names)
    if shape_reason:
        return dict(reason=shape_reason)
    result = dict(reason=None, fingerprint=digest.hexdigest(), apparent_bytes=apparent_bytes, lakes=lakes)
    if rollout_files is not None:
        result["root_identity"] = (root_stat.st_dev, root_stat.st_ino)
    if remnant and blueprint and verify_recovery:
        missing = recovery.check(blueprint)
        if missing:
            return dict(reason="blueprint_unrecoverable")
        current = inspect_candidate(path, cutoff, protected, repository=repository, reclaim=reclaim,
                                    remnant=True, recovery=recovery, verify_recovery=False)
        if current != result:
            return dict(reason="changed")
        return current
    return result


def remove_tree(path):
    """Remove an inspected owned tree, first granting its owner access to read-only directories."""
    # os.walk does not descend into directory links, so only directories inside the tree change mode.
    for directory, _, _ in os.walk(path):
        mode = stat.S_IMODE(os.lstat(directory).st_mode)
        if mode & stat.S_IRWXU != stat.S_IRWXU:
            os.chmod(directory, mode | stat.S_IRWXU)
    shutil.rmtree(path)


def remove_rollout_group(path, filenames, identity):
    """Unlink only snapshotted rollout names; retain any later directory entries."""
    descriptor = os.open(path, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        info = os.fstat(descriptor)
        if (info.st_dev, info.st_ino) != identity:
            raise OSError("rollout_root_changed")
        mode = stat.S_IMODE(info.st_mode)
        if mode & stat.S_IRWXU != stat.S_IRWXU:
            os.fchmod(descriptor, mode | stat.S_IRWXU)
        for name in filenames:
            os.unlink(name, dir_fd=descriptor)
        current = path.lstat()
        if (current.st_dev, current.st_ino) != identity:
            raise OSError("rollout_root_changed")
        path.rmdir()
    finally:
        os.close(descriptor)


def rename_exclusive(source, destination):
    """Atomically move a sibling without replacing any destination entry."""
    native = ctypes.CDLL(None, use_errno=True)
    if sys.platform == "darwin" and hasattr(native, "renamex_np"):
        rename = native.renamex_np
        rename.argtypes = (ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint)
        arguments = (os.fsencode(source), os.fsencode(destination), 4)  # RENAME_EXCL
    elif sys.platform.startswith("linux") and hasattr(native, "renameat2"):
        rename = native.renameat2
        rename.argtypes = (ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint)
        arguments = (-100, os.fsencode(source), -100, os.fsencode(destination), 1)  # AT_FDCWD, RENAME_NOREPLACE
    else:
        raise OSError(errno.ENOTSUP, "exclusive_rename_unavailable")
    rename.restype = ctypes.c_int
    if rename(*arguments) != 0:
        error = ctypes.get_errno()
        raise OSError(error, os.strerror(error), str(destination))


def clean_candidate(path, cutoff, protected, delete=False, repository=None, activity=None,
                    reclaim=True, refresh_activity=False, remnant=False, recovery=None, rollout_files=None):
    path = Path(path).absolute()
    result = dict(path=str(path), action="kept", reason=None, apparent_bytes=0)
    removal_started = False
    original, isolated = path, None
    owned_recovery = None
    try:
        kwargs = {} if repository is None else {"repository": repository}
        if remnant:
            if recovery is None:
                owned_recovery = recovery = RefRecovery(repository)
            recovery.candidate = path
            kwargs.update(remnant=True, recovery=recovery)
        if not reclaim:
            kwargs["reclaim"] = False
        if rollout_files is not None:
            kwargs["rollout_files"] = rollout_files
        def observe(protection, **options):
            return inspect_candidate(path, cutoff, protection, **kwargs, **options)
        before = observe(protected)
        result.update({key: before[key] for key in ("reason", "detail", "apparent_bytes") if key in before})
        if before["reason"] is not None:
            return result
        if not delete:
            result["action"] = "would_remove"
            return result
        with ExitStack() as stack:
            for lake in before.get("lakes", []):
                _, release = worktree_modules()
                lake_path = path / lake if remnant else Path(lake)
                stack.enter_context(release.cache_guard(lake_path.parent))
            refreshed = ProtectedPaths(activity()) if activity and (repository is not None or refresh_activity) else protected
            after = observe(refreshed, verify_recovery=False) if remnant else observe(refreshed)
            if after != before:
                result["reason"] = "changed"
                return result
            if remnant:
                destination = path.with_name(path.name + "-cleanup-" + uuid.uuid4().hex)
                rename_exclusive(path, destination)
                isolated = path = destination
                # Original-path opens are now closed off; existing handles and cwd
                # resolve to the isolated tree in the fresh activity observation.
                refreshed = ProtectedPaths(activity()) if activity else protected
                after = observe(refreshed)
                if after != before:
                    result["reason"] = "changed"
                    return result
            removal_started = True
            if rollout_files is not None:
                remove_rollout_group(path, rollout_files, before["root_identity"])
            elif path.is_dir():
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
        result.update(action="failed", reason=str(error))
    except RecoverySearchLimit as error:
        result.update(action="kept", reason="recovery_search_limit", detail=str(error))
    except (RuntimeError, ValueError, subprocess.SubprocessError) as error:
        if not remnant:
            raise
        result.update(action="kept", reason="recovery_unverifiable", detail=str(error))
    finally:
        if isolated is not None and result["action"] != "removed":
            try:
                rename_exclusive(isolated, original)
            except OSError as error:
                result.update(retained_path=str(isolated), retention_reason=result["reason"],
                              reason="restore_destination_exists" if isinstance(error, FileExistsError)
                              else "restore_failed", restore_detail=str(error))
        if owned_recovery is not None:
            owned_recovery.close()
    return result


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


def candidates(codex, sshx, tmp_roots, on_error=None):
    def inventory(category, root, entries):
        try:
            yield from entries()
        except (OSError, RuntimeError) as error:
            if on_error is None:
                raise
            on_error(category, root, error)

    for name in ("sessions", "archived_sessions"):
        root = codex / name
        def rollouts():
            if root.is_symlink():
                raise OSError("artifact root must not be a symlink: " + str(root))
            yield from root.rglob("rollout-*.jsonl")
        for path in inventory("codex", root, rollouts):
            yield "codex", path
    for name in ("shell_snapshots", "log"):
        root = codex / name
        for path in inventory("codex", root, lambda: children(root)):
            yield "codex", path
    root = codex / "tmp"
    for path in inventory("codex", root, lambda: children(root)):
        if path.name == "arg0" and path.is_dir() and not path.is_symlink():
            for run in inventory("codex", path, lambda: children(path)):
                yield "codex", run
        else:
            yield "codex", path
    root = codex / "packages"
    for package in inventory("codex", root, lambda: children(root)):
        for release in inventory("codex", package, lambda: superseded_releases(package)):
            yield "codex", release
    for path in inventory("sshx", sshx, lambda: children(sshx)):
        if re.fullmatch(r"[0-9a-f]{24}", path.name):
            yield "sshx", path
    for root in tmp_roots:
        for path in inventory("tmp", root, lambda: children(root)):
            yield "tmp", path


def rollout_group_files(path, codex):
    """Snapshot a session subdirectory containing only direct regular rollout files."""
    parent, sessions = path.parent, codex / "sessions"
    if sessions not in parent.parents:
        return None
    try:
        if parent.resolve() != parent or not stat.S_ISDIR(parent.lstat().st_mode):
            return None
        with os.scandir(parent) as entries:
            names = []
            for entry in entries:
                if (not entry.name.startswith("rollout-") or not entry.name.endswith(".jsonl")
                        or not stat.S_ISREG(entry.stat(follow_symlinks=False).st_mode)):
                    return None
                names.append(entry.name)
        return tuple(sorted(names)) if len(names) > 1 else None
    except (OSError, RuntimeError):
        return None


def observation_error(error):
    return dict(error=type(error).__name__, errno=getattr(error, "errno", None), detail=str(error))


class LinuxProcessObserver:
    """Diagnostic descriptors only; no observation here grants activity admission."""
    def __init__(self, process):
        self.process, self.proc_fd, self.pidfd = process, None, None
        self.binding = dict(identity="unknown")
        try:
            if os.uname().sysname != "Linux" or process.parent != Path("/proc"):
                self.binding["unavailable"] = "not_native_linux_proc"
                return
            self.proc_fd = os.open(process, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
            before = self.identity(self.proc_fd)
            self.binding["anchor"] = before
            if not hasattr(os, "pidfd_open"):
                self.binding["unavailable"] = "pidfd_open_unsupported"
                return
            self.pidfd = os.pidfd_open(int(process.name), 0)
            self.binding["pidfd_pid"] = self.pidfd_pid()
            # Compare the current numeric path with the retained proc inode and
            # starttime, on both sides of pidfd binding. A vanished/reused PID
            # or an unobservable identity never becomes terminal evidence.
            current = os.open(process, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
            try:
                after = self.identity(current)
            finally:
                os.close(current)
            self.binding["current"] = after
            if (before == after == self.identity(self.proc_fd)
                    and self.binding["pidfd_pid"] == self.pidfd_pid() == int(process.name)
                    and before["pid"] == int(process.name)):
                self.binding["identity"] = "matched"
        except (OSError, ValueError, AttributeError, KeyError, IndexError) as error:
            self.binding["failure"] = observation_error(error)

    @staticmethod
    def read(fd, name):
        descriptor = os.open(name, os.O_RDONLY | os.O_CLOEXEC, dir_fd=fd)
        with os.fdopen(descriptor) as source:
            return source.read()

    @classmethod
    def identity(cls, fd):
        info = os.fstat(fd)
        raw = cls.read(fd, "stat")
        fields = raw[raw.rindex(")") + 2:].split()
        return dict(device=info.st_dev, inode=info.st_ino,
                    pid=int(raw.split(" ", 1)[0]), starttime=int(fields[19]))

    def pidfd_pid(self):
        # fdinfo describes our own retained descriptor, not a numeric target PID.
        fields = dict(line.split(":", 1) for line in
                      Path("/proc/self/fdinfo", str(self.pidfd)).read_text().splitlines() if ":" in line)
        return int(fields["Pid"].strip())

    def sample(self, *, check_current=False):
        result = dict(wall_time_ns=time.time_ns(), monotonic_ns=time.monotonic_ns(),
                      identity=self.binding["identity"], group_exit="unknown")
        if self.pidfd is None:
            result["unavailable"] = self.binding
            return result
        try:
            poller = select.poll()
            poller.register(self.pidfd, select.POLLIN)
            result["revents"] = sum(events for _, events in poller.poll(0))
            result["poll_finished_monotonic_ns"] = time.monotonic_ns()
            if check_current:
                current = os.open(self.process, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
                try:
                    identity = self.identity(current)
                finally:
                    os.close(current)
                result["current"] = identity
                if identity != self.binding.get("anchor"):
                    result["identity"] = "unknown"
                    result["unavailable"] = "boundary_proc_identity_changed"
            if result["identity"] == "matched":
                if result["revents"] & (select.POLLERR | select.POLLNVAL):
                    pass
                elif result["revents"] & select.POLLIN:
                    result["group_exit"] = "observed"
                elif result["revents"] == 0:
                    result["group_exit"] = "not_observed"
        except (OSError, ValueError, AttributeError, KeyError, IndexError) as error:
            result["identity"] = "unknown"
            result["failure"] = observation_error(error)
        return result

    def wait_for_group_exit(self, timeout_ms):
        """Wait for the retained process identity to become fully terminal.

        This is a synchronization aid for a complete re-inventory after an
        observed incomplete proc transition.  The pidfd event is never activity
        evidence: callers must perform a fresh active_paths scan after this
        method returns True.
        """
        if self.pidfd is None or self.binding.get("identity") != "matched":
            return False
        try:
            current = self.sample(check_current=True)
            if (current.get("identity") != "matched"
                    or current.get("current") != self.binding.get("anchor")):
                return False
            if (current.get("revents", 0) & select.POLLIN
                    and not current.get("revents", 0) & (select.POLLERR | select.POLLNVAL)):
                return True
            poller = select.poll()
            poller.register(self.pidfd, select.POLLIN)
            return any(fd == self.pidfd and events & select.POLLIN
                       and not events & (select.POLLERR | select.POLLNVAL)
                       for fd, events in poller.poll(timeout_ms))
        except (OSError, ValueError, AttributeError, KeyError, IndexError):
            return False

    @staticmethod
    def capture(operation):
        try:
            return dict(value=operation())
        except (OSError, ValueError) as error:
            return observation_error(error)

    @staticmethod
    def metadata(info):
        return dict(uid=info.st_uid, gid=info.st_gid, mode=oct(stat.S_IMODE(info.st_mode)))

    def resources(self, fd):
        def status():
            return {key: value.strip() for line in self.read(fd, "status").splitlines()
                    for key, separator, value in [line.partition(":")]
                    if separator and key in ("State", "Threads", "Pid", "Tgid", "PPid", "Uid", "Gid", "NSpid")}
        result = dict(status=self.capture(status),
                      cwd=self.capture(lambda: os.readlink("cwd", dir_fd=fd)),
                      proc=self.capture(lambda: self.metadata(os.fstat(fd))),
                      fd_directory=self.capture(lambda: self.metadata(os.stat("fd", dir_fd=fd))))
        def inventory():
            directory = os.open("fd", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC, dir_fd=fd)
            try:
                return {name: self.capture(lambda: os.readlink(name, dir_fd=directory))
                        for name in os.listdir(directory)}
            finally:
                os.close(directory)
        result["fds"] = self.capture(inventory)
        return result

    def fault(self, boundary, error):
        return dict(fault=self.sample(check_current=True), binding=self.binding, boundary=boundary,
                      original_error=observation_error(error),
                      kernel=dict(zip(("sysname", "nodename", "release", "version", "machine"), os.uname())))

    def details(self, result):
        result.update(task_inventory="partial_non_atomic", tasks={}, inventory_started=self.sample())
        if self.proc_fd is not None:
            result["leader"] = self.resources(self.proc_fd)
            def tasks():
                directory = os.open("task", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC,
                                    dir_fd=self.proc_fd)
                try:
                    for name in os.listdir(directory):
                        def task():
                            fd = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC,
                                         dir_fd=directory)
                            try:
                                return self.resources(fd)
                            finally:
                                os.close(fd)
                        result["tasks"][name] = self.capture(task)
                finally:
                    os.close(directory)
            result["task_listing"] = self.capture(tasks)

    def close(self):
        for name in ("pidfd", "proc_fd"):
            fd = getattr(self, name)
            if fd is not None:
                os.close(fd)
                setattr(self, name, None)


def linux_observation_unavailable(process, boundary, error, observer=None):
    """Only a completely observed terminal thread group has no active handles."""
    diagnostic = observer.fault(boundary, error) if observer is not None else None
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
    if diagnostic is not None:
        diagnostic["refusal"] = observer.sample(check_current=True)
        diagnostic["inventory"] = observer.capture(lambda: observer.details(diagnostic))
    raise OSError("linux_activity_unavailable " + json.dumps(dict(
        process=str(process), boundary=boundary, status=status, error=str(error),
        diagnostic=diagnostic))) from error


def wait_for_linux_activity_transition(error, timeout_ms=1000):
    """Synchronize one captured proc teardown before a complete re-inventory.

    The returned boolean only authorizes the caller to run active_paths again.
    It never supplies paths or grants activity admission.  A retry is limited
    to the diagnostic shape produced by linux_observation_unavailable when a
    matched process identity was still live, its non-atomic inventory was
    incomplete, and its flags=0 pidfd had not observed group exit.  Persistent
    or identity-ambiguous failures return False and remain refusals.
    """
    prefix = "linux_activity_unavailable "
    text = str(error)
    if not text.startswith(prefix):
        return False
    try:
        payload = json.loads(text[len(prefix):])
        diagnostic = payload["diagnostic"]
        binding = diagnostic["binding"]
        anchor = binding["anchor"]
        if (payload.get("boundary") != "fd_inventory"
                or diagnostic.get("task_inventory") != "partial_non_atomic"
                or binding.get("identity") != "matched"
                or binding.get("current") != anchor
                or binding.get("pidfd_pid") != anchor["pid"]):
            return False
        for name in ("fault", "refusal"):
            sample = diagnostic[name]
            if (sample.get("identity") != "matched"
                    or sample.get("group_exit") != "not_observed"
                    or sample.get("revents") != 0
                    or sample.get("current") != anchor):
                return False
        # This sample was captured without check_current, so it must not be
        # treated as an identity observation at all.
        inventory_started = diagnostic["inventory_started"]
        if (inventory_started.get("identity") != "matched"
                or inventory_started.get("group_exit") != "not_observed"
                or inventory_started.get("revents") != 0
                or "current" in inventory_started):
            return False
        process = Path(payload["process"])
        try:
            process.stat()
        except (FileNotFoundError, ProcessLookupError):
            # The next active_paths scan will observe this disappearance
            # directly; no diagnostic state is used as admission evidence.
            return True
        except OSError:
            return False
    except (KeyError, TypeError, ValueError, json.JSONDecodeError):
        return False

    observer = LinuxProcessObserver(process)
    try:
        if (observer.binding.get("identity") != "matched"
                or observer.binding.get("anchor") != anchor
                or observer.binding.get("current") != anchor
                or observer.binding.get("pidfd_pid") != anchor["pid"]):
            return False
        return observer.wait_for_group_exit(timeout_ms)
    finally:
        observer.close()


def active_paths(codex, scopes=(), *, include_sampler_argv=False):
    """Read open files/cwds and process arguments for the current user only."""
    protected = {Path.cwd().resolve(), Path(__file__).resolve()}
    scope_paths = tuple(Path(scope).resolve() for scope in scopes)
    scopes = tuple(map(str, scope_paths))

    physical_parents = {}
    argument_paths = {}

    def relevant(path):
        return not scope_paths or any(path == scope or scope in path.parents for scope in scope_paths)

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
            observer = LinuxProcessObserver(process)
            try:
                try:
                    if process.stat().st_uid != os.getuid():
                        continue
                except (FileNotFoundError, ProcessLookupError):
                    continue
                try:
                    descriptors = list((process / "fd").iterdir())
                except (FileNotFoundError, ProcessLookupError, PermissionError) as error:
                    linux_observation_unavailable(process, "fd_inventory", error, observer)
                    continue
                cwd = process / "cwd"
                missing_cwd = None
                for link in [cwd, *descriptors]:
                    try:
                        target = os.readlink(link).removesuffix(" (deleted)")
                    except PermissionError as error:
                        linux_observation_unavailable(process, "cwd" if link == cwd else "fd", error, observer)
                        break
                    except (FileNotFoundError, ProcessLookupError) as error:
                        # Closing one handle must not hide the remaining handles.
                        if link == cwd:
                            missing_cwd = error
                        continue
                    if target.startswith("/"):
                        open_path(target)
                if missing_cwd is not None:
                    linux_observation_unavailable(process, "cwd", missing_cwd, observer)
            finally:
                observer.close()
    elif sys.platform == "darwin":
        for path in macos_active_paths():
            open_path(str(path))
    else:
        raise OSError("host cleanup supports macOS and Linux")
    result = subprocess.run(["ps", "-axo", "uid=,pid=,ppid=,args=" if scopes else "uid=,args="],
                            capture_output=True, text=True, timeout=30)
    if result.returncode != 0:
        raise OSError("cannot inspect process arguments: " + result.stderr.strip())
    process_rows = [line.strip().split(None, 3 if scopes else 1) for line in result.stdout.splitlines()]
    samplers = {str(os.getpid()), str(os.getppid())}
    if scopes and not include_sampler_argv:
        parents = {row[1]: row[2] for row in process_rows if len(row) == 4}
        ancestor = str(os.getppid())
        while ancestor in parents and parents[ancestor] not in samplers:
            ancestor = parents[ancestor]
            samplers.add(ancestor)
    for fields in process_rows:
        if scopes:
            # The sampler's launch chain names its own target in argv. Its real
            # cwd/open handles remain inspected independently of these arguments.
            if len(fields) != 4 or (not include_sampler_argv and fields[1] in samplers):
                continue
            fields = [fields[0], fields[3]]
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
                if value not in argument_paths:
                    argument_paths[value] = Path(value).resolve()
                resolved = argument_paths[value]
                if relevant(resolved):
                    protected.add(resolved)
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
    active_ids.discard("")
    if active_ids:
        for name in ("sessions", "archived_sessions", "shell_snapshots"):
            root = codex / name
            if scope_paths:
                scan_roots = {root if root == scope or scope in root.parents else scope
                              for scope in scope_paths
                              if root == scope or scope in root.parents or root in scope.parents}
            else:
                scan_roots = {root}
            for scan_root in scan_roots:
                paths = scan_root.rglob("*") if scan_root.is_dir() else (scan_root,)
                for path in paths:
                    if any(identity in path.name for identity in active_ids) and path.is_file():
                        protected.add(path.resolve())
    return protected


def registered_worktrees(repository):
    preservation, _ = worktree_modules()
    result = preservation.git(repository, "worktree", "list", "--porcelain", "-z", timeout=60)
    # Git lists the main worktree first; it survives registered-tree cleanup.
    return [Path(os.fsdecode(field[len(b"worktree "):])).resolve()
            for field in result.stdout.split(b"\0") if field.startswith(b"worktree ")]


def remnant_candidates(repository, inventory):
    """Select only physical siblings of the inventory's verified main checkout."""
    if not inventory:
        return
    main = next(iter(inventory))
    siblings = [path for path in children(main.parent)
                if path.name.startswith(main.name + "-") and (path.is_symlink() or path.is_dir())]
    if not siblings:
        return
    preservation, _ = worktree_modules()
    try:
        top = preservation.git(main, "rev-parse", "--show-toplevel").stdout.removesuffix(b"\n")
        if (Path(os.fsdecode(top)).resolve() != main or not (main / ".git").is_dir()
                or preservation.common(main) != (main / ".git").resolve()
                or preservation.common(repository) != preservation.common(main)):
            raise OSError("main_checkout_unverifiable")
    except (OSError, RuntimeError, ValueError, subprocess.SubprocessError) as error:
        raise OSError("main_checkout_unverifiable: " + str(error)) from error
    yield from sorted(siblings)


def containing_repository(path):
    """Find the governing Git boundary, including nested project directories."""
    for parent in (path, *path.parents):
        marker = parent / ".git"
        if os.path.lexists(marker):
            return parent
        if all((parent / name).exists() for name in ("HEAD", "objects", "refs")):
            return parent
    return None


def artifact_lakes(path, protected, worktrees, unobservable):
    """Find private cache roots without splitting ordinary siblings or entering Git metadata.

    An entry that vanished or cannot be read is reported and skipped; it holds no reachable staging.
    """
    device, pending = None, [path]
    while pending:
        entry = pending.pop()
        try:
            info = entry.lstat()
            device = info.st_dev if device is None else device
            if (not stat.S_ISDIR(info.st_mode) or info.st_dev != device or info.st_uid != os.getuid()
                    or getattr(info, "st_flags", 0) & PROTECTED_FLAGS
                    or entry in protected or any(tree == entry or tree in entry.parents for tree in worktrees)):
                continue
            if entry.name == ".lake":
                found = containing_repository(entry.parent) is not None
            else:
                pending.extend(child for child in entry.iterdir() if child.name != ".git")
                continue
        except (FileNotFoundError, PermissionError) as error:
            unobservable(entry, error)
            continue
        yield entry, found


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
    global LOG_REPOSITORY
    LOG_REPOSITORY = options.repository
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
    def record(category, result):
        nonlocal apparent_bytes
        counts[category + ":" + result["action"]] += 1
        if result["action"] in ("would_remove", "removed"):
            apparent_bytes += result["apparent_bytes"]
        elif result["action"] == "kept":
            skipped[result["reason"]] += 1
        if (options.verbose or category == "worktree_remnant" or result["action"] == "failed"
                or result["reason"] == "unreadable"):
            emit("host_cleanup_item", category=category, **result)
        if result["action"] == "failed":
            print(json.dumps(dict(event="host_cleanup_warning", path=result["path"],
                                  action=result["action"], reason=result["reason"],
                                  diagnostic=result.get("detail") or result["reason"])), file=sys.stderr)
            safe_append("host-cleanup", "host_cleanup_warning", repository=LOG_REPOSITORY,
                        path=result["path"], action=result["action"], reason=result["reason"],
                        diagnostic=result.get("detail") or result["reason"])

    def unobservable(path, error):
        reason = "vanished" if isinstance(error, FileNotFoundError) else "unreadable"
        record("lean_staging", dict(path=str(path), action="kept", reason=reason, detail=str(error),
                                    apparent_bytes=0))

    def fresh_protection(path):
        protection = active_paths(codex, (path,), include_sampler_argv=True)
        registrations = set(registered_worktrees(main_checkout))
        if any(tree == path or tree in path.parents or path in tree.parents for tree in registrations):
            protection.add(path)
        return protection | registrations | {caller}

    def inventory_failure(category, path, error):
        nonlocal inventory_error
        detail = str(error)
        inventory_error = detail if inventory_error is None else inventory_error + "; " + detail
        record(category, dict(path=str(path), action="failed", reason="inventory_unavailable",
                              detail=detail, apparent_bytes=0))

    def clean_staging(lake):
        if lake in seen_lakes:
            return
        seen_lakes.add(lake)
        _, release = worktree_modules()
        def inspect(path):
            protection = ProtectedPaths(active_paths(codex, (path,), include_sampler_argv=True) | {caller}) if options.delete else ProtectedPaths(active | {caller})
            return inspect_candidate(path, cutoff, protection)
        for result in release.clean_staging(lake, cutoff=cutoff, now=now,
                                          delete=options.delete, inspect=inspect):
            record("lean_staging", result)
    try:
        for tree in inventory:
            lake = tree / ".lake"
            if lake.is_dir() and not lake.is_symlink():
                clean_staging(lake)
        with ExitStack() as remnant_stack:
            recovery = None
            for path in remnant_candidates(main_checkout, inventory):
                if recovery is None:
                    recovery = RefRecovery(main_checkout)
                    remnant_stack.callback(recovery.close)
                seen.add(path)
                result = clean_candidate(path, cutoff, protections["sshx"], options.delete,
                                         repository=main_checkout, activity=lambda: fresh_protection(path.parent),
                                         remnant=True, recovery=recovery)
                record("worktree_remnant", result)
        attempted_rollout_groups = set()
        for category, path in candidates(codex, sshx, roots, on_error=inventory_failure):
            if path in seen:
                continue
            if (category == "codex" and path.parent not in attempted_rollout_groups
                    and not any(parent in worktrees for parent in path.parents)):
                attempted_rollout_groups.add(path.parent)
                rollout_files = rollout_group_files(path, codex)
                if rollout_files is not None:
                    group = path.parent
                    result = clean_candidate(group, cutoff, protections["codex"], options.delete,
                                             activity=lambda: fresh_protection(group),
                                             reclaim=False, refresh_activity=True, rollout_files=rollout_files)
                    if result["action"] in ("would_remove", "removed"):
                        record("codex", result)
                        seen.update(group / name for name in rollout_files)
                        continue
                    if result["action"] == "failed":
                        record("codex", result)
            seen.add(path)
            if any(parent in worktrees for parent in path.parents):
                result = dict(path=str(path), action="kept", reason="protected", apparent_bytes=0)
            elif category != "codex" and any(parent.name == ".lake" for parent in path.parents):
                lake = next(parent for parent in path.parents if parent.name == ".lake")
                clean_staging(lake)
                result = dict(path=str(path), action="kept", reason="protected", apparent_bytes=0)
            else:
                # Temporary candidates rely on the registrations and activity read at sweep start.
                refresh = category != "tmp"
                result = clean_candidate(path, cutoff, protections[category], options.delete,
                                         repository=main_checkout if category == "sshx" else None,
                                         activity=(lambda: fresh_protection(path)) if refresh else None,
                                         reclaim=category != "codex", refresh_activity=refresh)
            record(category, result)
            if category != "codex" and result["action"] == "kept" and result["reason"] == "recent":
                for lake, repository in artifact_lakes(path, protections[category], worktrees, unobservable):
                    if repository:
                        clean_staging(lake)
    except OSError as error:
        inventory_error = str(error)
    failed = inventory_error is not None or lanes_exit != 0
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
    global LOG_REPOSITORY
    if options.command == "clean":
        LOG_REPOSITORY = options.repository
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
        safe_append("host-cleanup", "run_finished", repository=LOG_REPOSITORY,
                    exit_code=73, error=str(error))
        return 73
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print("HOST_CLEANUP_FAILED " + str(error), file=sys.stderr)
        safe_append("host-cleanup", "run_finished", repository=LOG_REPOSITORY,
                    exit_code=1, error=str(error))
        return 1


if __name__ == "__main__":
    sys.exit(main())
