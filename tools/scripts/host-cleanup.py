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


def macos_active_paths():
    """Read absolute paths held by the current user's processes."""
    try:
        result = subprocess.run(["lsof", "-nP", "-a", "-u", str(os.getuid()), "-Fftn"],
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


class RefRecovery:
    """Check byte recovery from retained commit refs, with a sweep-local object listing."""
    def __init__(self, repository):
        self.repository = repository
        self.refs = None
        self.objects = tempfile.TemporaryFile()
        self.reachable = set()
        self._algorithm = None

    @property
    def algorithm(self):
        if self._algorithm is None:
            preservation, _ = worktree_modules()
            self._algorithm = preservation.git(self.repository, "rev-parse", "--show-object-format").stdout.strip().decode("ascii")
        return self._algorithm

    def close(self):
        self.objects.close()

    def check(self, wanted):
        preservation, _ = worktree_modules()
        from worktree_protocol import git_environment, scope_fds
        refs = preservation.git(self.repository, "for-each-ref", "--format=%(refname) %(objectname)").stdout
        if refs != self.refs:
            # Peeling to commits excludes blob/tree-only refs and includes annotated tags.
            names = [row.split(b" ", 1)[0] + b"^{commit}\n" for row in refs.splitlines()]
            peeled = preservation.git(self.repository, "cat-file", "--batch-check=%(objectname) %(objecttype)",
                                      input=b"".join(names)).stdout
            roots = [row.split()[0] for row in peeled.splitlines() if row.endswith(b" commit")]
            self.objects.seek(0)
            self.objects.truncate()
            if roots:
                subprocess.run(["git", "--no-replace-objects", "-C", str(self.repository), "rev-list",
                                "--objects", "--no-object-names", "--stdin"],
                               input=b"\n".join(roots) + b"\n", stdout=self.objects,
                               stderr=subprocess.PIPE, check=True, timeout=60,
                               env=git_environment(), pass_fds=scope_fds())
            self.refs, self.reachable = refs, set()
        missing = set(wanted) - self.reachable
        if missing:
            self.objects.seek(0)
            for row in self.objects:
                oid = row.strip()
                if oid in missing:
                    missing.remove(oid)
                    self.reachable.add(oid)
                    if not missing:
                        break
        if not missing:
            # Listing a blob does not establish that its bytes are present and intact.
            with tempfile.TemporaryFile() as blobs:
                subprocess.run(["git", "--no-replace-objects", "-C", str(self.repository), "cat-file", "--batch"],
                               input=b"\n".join(sorted(wanted)) + b"\n", stdout=blobs,
                               stderr=subprocess.PIPE, check=True, timeout=60,
                               env=git_environment(), pass_fds=scope_fds())
                blobs.seek(0)
                for oid in sorted(wanted):
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
                        missing.add(oid)
        if preservation.git(self.repository, "for-each-ref", "--format=%(refname) %(objectname)").stdout != refs:
            raise ValueError("recovery_refs_changed")
        return missing


def inspect_candidate(path, cutoff, protected, repository=None, reclaim=True, remnant=False, recovery=None,
                      verify_recovery=True):
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
                           info.st_mtime_ns, info.st_ctime_ns)).encode())
        if stat.S_ISREG(info.st_mode):
            apparent_bytes += info.st_size
            if remnant:
                with entry.open("rb") as handle:
                    if path / "Blueprint" in entry.parents:
                        blob = hashlib.new(recovery.algorithm)
                        blob.update(b"blob " + str(info.st_size).encode("ascii") + b"\0")
                        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                            blob.update(chunk)
                        blueprint.add(blob.hexdigest().encode("ascii"))
                        digest.update(blob.digest())
                if entry.parent == path:
                    shape_reason = "lake_content" if entry.name == ".lake" else "unknown_top_level"
                if entry == path / ".lake/build":
                    shape_reason = "lake_content"
        elif stat.S_ISDIR(info.st_mode):
            with os.scandir(entry) as children:
                names = sorted(child.name for child in children)
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
                lakes.append(str(entry))
            pending.extend(entry / name for name in names)
    if shape_reason:
        return dict(reason=shape_reason)
    result = dict(reason=None, fingerprint=digest.hexdigest(), apparent_bytes=apparent_bytes, lakes=lakes)
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


def clean_candidate(path, cutoff, protected, delete=False, repository=None, activity=None,
                    reclaim=True, refresh_activity=False, remnant=False, recovery=None):
    path = Path(path).absolute()
    result = dict(path=str(path), action="kept", reason=None, apparent_bytes=0)
    removal_started = False
    owned_recovery = None
    try:
        kwargs = {} if repository is None else {"repository": repository}
        if remnant:
            if recovery is None:
                owned_recovery = recovery = RefRecovery(repository)
            kwargs.update(remnant=True, recovery=recovery)
        if not reclaim:
            kwargs["reclaim"] = False
        def observe(protection):
            return inspect_candidate(path, cutoff, protection, **kwargs)
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
                stack.enter_context(release.cache_guard(Path(lake).parent))
            refreshed = ProtectedPaths(activity()) if activity and (repository is not None or refresh_activity) else protected
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
        result.update(action="failed", reason=str(error))
    except (RuntimeError, ValueError, subprocess.SubprocessError) as error:
        if not remnant:
            raise
        result.update(action="kept", reason="recovery_unverifiable", detail=str(error))
    finally:
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


def active_paths(codex, scopes=()):
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
        for path in macos_active_paths():
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

    def unobservable(path, error):
        reason = "vanished" if isinstance(error, FileNotFoundError) else "unreadable"
        record("lean_staging", dict(path=str(path), action="kept", reason=reason, detail=str(error),
                                    apparent_bytes=0))

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
        with ExitStack() as remnant_stack:
            recovery = None
            for path in remnant_candidates(main_checkout, inventory):
                if recovery is None:
                    recovery = RefRecovery(main_checkout)
                    remnant_stack.callback(recovery.close)
                seen.add(path)
                result = clean_candidate(path, cutoff, protections["sshx"], options.delete,
                                         repository=main_checkout, activity=fresh_protection,
                                         remnant=True, recovery=recovery)
                record("worktree_remnant", result)
        for category, path in candidates(codex, sshx, roots):
            if path in seen:
                continue
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
                                         activity=fresh_protection if refresh else None,
                                         reclaim=category != "codex", refresh_activity=refresh)
            record(category, result)
            if category != "codex" and result["action"] == "kept" and result["reason"] == "recent":
                for lake, repository in artifact_lakes(path, protections[category], worktrees, unobservable):
                    if repository:
                        clean_staging(lake)
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
