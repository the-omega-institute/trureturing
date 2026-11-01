#!/usr/bin/env python3
"""Cooperative worktree scopes. Locks are OS descriptors, never custody records.

Participants must enter before using a tree, declare overlapping reads/writes,
and preserve inherited descriptors in descendants that continue using it.
Programs that close inherited descriptors must enter again before accessing it.
"""

import argparse
from contextlib import ExitStack, contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import time
from urllib.parse import unquote, urlsplit

if __name__ == "__main__":
    sys.modules["worktree_protocol"] = sys.modules[__name__]

OPEN_SCOPES = []
GIT_TERMINATION_GRACE_SECONDS = 30
# An empty core.fsmonitor disables it both where Git reads a boolean and where
# older Git reads a hook path; "false" would name a hook program there.
SCOPED_GIT_CONFIG = (("core.fsmonitor", ""), ("maintenance.auto", "false"), ("gc.auto", "0"))
SCOPED_PROCESS_ENVIRONMENT = {"MSBUILDDISABLENODEREUSE": "1",
                              "DOTNET_CLI_USE_MSBUILD_SERVER": "0",
                              "UseSharedCompilation": "false",
                              "UseRazorBuildServer": "false",
                              "_RazorForceBuildServer": "false"}


def scope_fds():
    descriptors = {handle.fileno() for handle in OPEN_SCOPES if not handle.closed}
    for raw in os.environ.get("WORKTREE_SCOPE_FDS", "").split(","):
        if raw.isdigit():
            fd = int(raw)
            try:
                os.fstat(fd)
                if os.get_inheritable(fd):
                    descriptors.add(fd)
            except OSError:
                pass
    return tuple(sorted(descriptors))


class Refused(RuntimeError):
    def __init__(self, reason, native_locks=None):
        super().__init__(reason)
        self.native_locks = native_locks or []


class GitFailure(Refused):
    """A failed Git operation, distinct from an eligibility refusal."""


def inherited_environment():
    # Ambient location/index/object overrides must never redirect canonical
    # inspection. Keep transport and author identity settings.
    permitted = {"GIT_SSH", "GIT_SSH_COMMAND", "GIT_SSH_VARIANT", "GIT_ASKPASS",
                 "GIT_TERMINAL_PROMPT", "GIT_AUTHOR_NAME", "GIT_AUTHOR_EMAIL",
                 "GIT_AUTHOR_DATE", "GIT_COMMITTER_NAME", "GIT_COMMITTER_EMAIL",
                 "GIT_COMMITTER_DATE"}
    return {key: val for key, val in os.environ.items()
            if not key.startswith("GIT_") or key in permitted}


def scoped_process_environment():
    # Background Git and .NET servers would retain inherited scope descriptors
    # after the foreground command returns. Active descendants keep inheriting.
    environment = dict(SCOPED_PROCESS_ENVIRONMENT)
    for index, (key, setting) in enumerate(SCOPED_GIT_CONFIG):
        environment[f"GIT_CONFIG_KEY_{index}"] = key
        environment[f"GIT_CONFIG_VALUE_{index}"] = setting
    environment["GIT_CONFIG_COUNT"] = str(len(SCOPED_GIT_CONFIG))
    return environment


def git_environment(overrides=None):
    environment = inherited_environment()
    environment.update(overrides or {})
    environment.update(scoped_process_environment())
    return environment


def git(root, *args, env=None, input=None, check=True, timeout=300):
    command = ["git", "-C", str(root), *map(str, args)]
    with subprocess.Popen(command, stdin=subprocess.PIPE if input is not None else None,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          env=git_environment(env), pass_fds=scope_fds()) as process:
        try:
            stdout, stderr = process.communicate(input, timeout=timeout)
        except subprocess.TimeoutExpired:
            # Git removes its lock files on SIGTERM; SIGKILL would leave index.lock behind.
            process.terminate()
            try:
                process.wait(timeout=GIT_TERMINATION_GRACE_SECONDS)
            except subprocess.TimeoutExpired:
                process.kill()
            except BaseException:
                process.kill()
                raise
            raise
        except BaseException:
            process.kill()
            raise
    result = subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
    if check and result.returncode:
        raise GitFailure(result.stderr.decode(errors="replace").strip() or "git failed")
    return result


def value(root, *args):
    return os.fsdecode(git(root, *args).stdout).strip()


def common(root):
    return Path(value(root, "rev-parse", "--path-format=absolute", "--git-common-dir")).resolve()


def remote_endpoint(root, remote, push=False):
    flags = ["--push", "--all"] if push else []
    result = git(root, "remote", "get-url", *flags, "--", remote, check=False)
    endpoints = os.fsdecode(result.stdout).splitlines() if result.returncode == 0 else [remote]
    if len(endpoints) != 1 or not endpoints[0]:
        raise Refused("single_remote_endpoint_required")
    endpoint = endpoints[0]
    parsed = urlsplit(endpoint)
    if parsed.scheme == "file" or not parsed.scheme and ":" not in endpoint:
        path = Path(unquote(parsed.path) if parsed.scheme == "file" else endpoint)
        path = (Path(root) / path).resolve()
        if common(path) == common(root):
            raise Refused("remote_is_local_repository")
        return str(path)
    return endpoint


def inventory(root):
    records = []
    for raw in git(root, "worktree", "list", "--porcelain", "-z").stdout.split(b"\0\0"):
        item = {}
        for field in raw.split(b"\0"):
            key, _, val = os.fsdecode(field).partition(" ")
            if key:
                item[key] = val
        if item:
            records.append(item)
    return records


def identity(source, path, snapshot=None, deadline=None):
    """Preserve native failures unless a fresh observation confirms identity drift."""
    path = Path(path).absolute()
    if path.is_symlink() or not path.is_dir():
        raise Refused("missing_or_linked_tree")
    path = path.resolve()
    marker = path / ".git"
    def pointer_target(data):
        lines = os.fsdecode(data).splitlines()
        return (path / lines[0][8:]).resolve() if len(lines) == 1 and lines[0].startswith("gitdir: ") else None
    pointer = None
    try:
        pointer = marker.read_bytes() if marker.is_file() and not marker.is_symlink() else None
        snapshot = snapshot if snapshot is not None else (inventory(source), common(source))
        return _read_identity(path, snapshot)
    except (GitFailure, OSError, subprocess.TimeoutExpired):
        if path.is_symlink() or not path.is_dir():
            raise Refused("missing_or_linked_tree")
        if marker.is_symlink() or not marker.exists():
            raise Refused("git_pointer")
        try:
            previous_target = pointer_target(pointer) if pointer is not None else None
            current = marker.read_bytes() if marker.is_file() else b""
            changed = previous_target is not None and pointer_target(current) != previous_target
        except OSError:
            changed = False
        if changed:
            raise Refused("git_pointer_identity")
        # The batch alarm still bounds native rechecks. An exhausted alarm must
        # not start another native read after its execution budget has expired.
        if deadline is None or time.monotonic() < deadline:
            try:
                rows = inventory(source)
                previous = [row for row in snapshot[0] if Path(row["worktree"]).resolve() == path] if snapshot is not None else None
                current = [row for row in rows if Path(row["worktree"]).resolve() == path]
            except Exception:
                pass
            else:
                if not current:
                    raise Refused("repository_identity")
                if previous is not None and current != previous:
                    raise Refused("observed_identity_changed")
        raise


def _read_identity(path, snapshot):
    rows, source_common = snapshot
    match = [r for r in rows if Path(r["worktree"]).resolve() == path]
    if len(match) != 1 or common(path) != source_common:
        raise Refused("repository_identity")
    if Path(value(path, "rev-parse", "--show-toplevel")).resolve() != path:
        raise Refused("tree_identity")
    metadata = Path(value(path, "rev-parse", "--absolute-git-dir")).resolve()
    if metadata != source_common:
        pointer = path / ".git"
        if pointer.is_symlink() or not pointer.is_file():
            raise Refused("git_pointer")
        lines = os.fsdecode(pointer.read_bytes()).splitlines()
        if len(lines) != 1 or not lines[0].startswith("gitdir: "):
            raise Refused("unknown_git_pointer_material")
        if (path / lines[0][8:]).resolve() != metadata:
            raise Refused("git_pointer_identity")
        if (metadata / "gitdir").read_text().strip() != str(pointer):
            # Git can write a physical path while the caller uses /tmp's alias.
            if Path((metadata / "gitdir").read_text().strip()).resolve() != pointer.resolve():
                raise Refused("git_backlink")
    return match[0], metadata


def lock_file(directory, key, exclusive):
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / (hashlib.sha256(os.fsencode(key)).hexdigest() + ".lock")
    fd = os.open(path, os.O_CREAT | os.O_RDWR | getattr(os, "O_NOFOLLOW", 0), 0o600)
    try:
        fcntl.flock(fd, (fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH) | fcntl.LOCK_NB)
        os.set_inheritable(fd, True)
        handle = os.fdopen(fd, "rb", buffering=0)
        handle.scope_key = key
        handle.scope_exclusive = exclusive
        OPEN_SCOPES.append(handle)
        return handle
    except BaseException:
        os.close(fd)
        raise


def acquire(stack, source, key, exclusive):
    try:
        directory = getattr(stack, "scope_directory", None)
        if directory is None:
            directory = stack.scope_directory = common(source) / "worktree-operations"
        handle = stack.enter_context(lock_file(directory, key, exclusive))
        stack.scope_handles = getattr(stack, "scope_handles", []) + [handle]
        return handle
    except BlockingIOError as error:
        raise Refused("busy_scope:" + key) from error


def tree_scope(stack, source, path, exclusive=False):
    path = Path(path).resolve()
    # Nested participants share ancestor entry scopes so checkout-wide
    # operations exclude conflicting cooperative use at their affected scope.
    for parent in reversed(path.parents):
        acquire(stack, source, "tree:" + str(parent), False)
    acquire(stack, source, "tree:" + str(path), exclusive)
    return path


def path_scopes(stack, source, path, reads=(), writes=()):
    scopes = {}
    for names, exclusive in ((reads, False), (writes, True)):
        for name in names:
            relative = Path(name)
            target = (path / relative).resolve()
            if relative.is_absolute() or target != path and path not in target.parents:
                raise Refused("path_outside_tree:" + name)
            # Resolving aliases makes symlink-target and directory/file overlaps conflict.
            for parent in target.parents:
                if parent == path.parent:
                    break
                scopes.setdefault(str(parent), False)
            # Reads protect their entire named subtree against descendant writes.
            # Same-scope readers serialize; disjoint scopes remain concurrent.
            scopes[str(target)] = True
    for name, exclusive in sorted(scopes.items()):
        acquire(stack, source, "file:" + name, exclusive)


def git_scope(stack, source, path):
    metadata = value(path, "rev-parse", "--absolute-git-dir")
    result = git(path, "symbolic-ref", "--quiet", "HEAD", check=False)
    if result.returncode not in (0, 1):
        raise GitFailure(result.stderr.decode(errors="replace").strip() or "git failed")
    branch = os.fsdecode(result.stdout).strip() if result.returncode == 0 else "HEAD"
    for reference in sorted({metadata + ":HEAD", branch if branch != "HEAD" else metadata + ":HEAD"}):
        acquire(stack, source, "ref:" + reference, True)
    acquire(stack, source, "index:" + metadata, True)
    return branch


@contextmanager
def exclusive_tree(stack, source, path):
    """Promote this operation's entry only for a native-lock recovery attempt."""
    key = "tree:" + str(Path(path).resolve())
    local = next((handle for handle in getattr(stack, "scope_handles", [])
                  if not handle.closed and handle.scope_key == key), None)
    if local is None:
        with ExitStack() as recovery:
            tree_scope(recovery, source, path, True)
            yield
    elif local.scope_exclusive:
        yield
    else:
        try:
            fcntl.flock(local, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise Refused("busy_scope:" + key) from error
        local.scope_exclusive = True
        try:
            yield
        finally:
            fcntl.flock(local, fcntl.LOCK_SH)
            local.scope_exclusive = False


def native_lock_holders(path):
    """Inspect the exact native lock; incomplete visibility is an error."""
    inspector = shutil.which("lsof")
    if inspector:
        result = subprocess.run([inspector, "-nP", "-F", "p", "--", str(path)],
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30,
                                env=git_environment())
        if result.stderr or result.returncode not in (0, 1):
            raise OSError("incomplete lsof inspection")
        rows = result.stdout.decode("ascii").splitlines()
        if any(not row.startswith("f") and (not row.startswith("p") or not row[1:].isdigit()) for row in rows):
            raise OSError("unrecognized lsof inspection")
        holders = [row[1:] for row in rows if row.startswith("p")]
        if result.returncode == 0 and not holders or result.returncode == 1 and rows:
            raise OSError("incomplete lsof result")
        return holders
    if not sys.platform.startswith("linux"):
        raise OSError("holder inspection unavailable")
    target = path.stat()
    holders = []
    for process in Path("/proc").iterdir():
        if not process.name.isdigit():
            continue
        try:
            for descriptor in (process / "fd").iterdir():
                try:
                    actual = descriptor.stat()
                    if (actual.st_dev, actual.st_ino) == (target.st_dev, target.st_ino):
                        holders.append(process.name)
                except FileNotFoundError:
                    pass
        except FileNotFoundError:
            pass
    return holders


def native_lock_candidates(path, metadata, branch, error):
    candidates = [metadata / "index.lock", metadata / "HEAD.lock"]
    if branch.startswith("refs/heads/"):
        candidates.append(common(path) / (branch + ".lock"))
    return [lock for lock in candidates if str(lock) in str(error) and os.path.lexists(lock)]


def clear_native_locks(source, path, locks):
    identity(source, path)
    cleared = []
    for lock in locks:
        before = lock.lstat()
        evidence = dict(event="worktree_native_lock", path=str(lock), size=before.st_size,
                        age_seconds=time.time() - before.st_mtime)
        try:
            if not stat.S_ISREG(before.st_mode):
                raise OSError("nonregular native lock")
            holders = native_lock_holders(lock)
        except (OSError, ValueError, subprocess.SubprocessError) as error:
            observation = dict(evidence, status="unverifiable")
            print(json.dumps(observation), file=sys.stderr, flush=True)
            raise Refused("native_lock_unverifiable:" + str(lock), cleared + [observation]) from error
        if holders:
            observation = dict(evidence, status="held", holders=holders)
            print(json.dumps(observation), file=sys.stderr, flush=True)
            raise Refused("native_lock_held:" + str(lock), cleared + [observation])
        try:
            after = lock.lstat()
        except FileNotFoundError:
            after = None
        fingerprint = lambda item: (item.st_dev, item.st_ino, item.st_size, item.st_mtime_ns)
        if after is None or fingerprint(before) != fingerprint(after):
            observation = dict(evidence, status="changed")
            print(json.dumps(observation), file=sys.stderr, flush=True)
            raise Refused("native_lock_changed:" + str(lock), cleared + [observation])
        lock.unlink()
        cleared.append(dict(evidence, status="native_lock_cleared"))
        print(json.dumps(cleared[-1]), file=sys.stderr, flush=True)
    return cleared


def read_input(source, file):
    with ExitStack() as stack:
        target = Path(file).resolve()
        tree_scope(stack, source, target.parent)
        path_scopes(stack, source, target.parent, reads=(target.name,))
        return target.read_bytes()


def with_command(options):
    if not options.argv:
        raise Refused("missing_command")
    with ExitStack() as stack:
        path = tree_scope(stack, options.source, options.path, options.exclusive)
        identity(options.source, path)
        path_scopes(stack, options.source, path, options.read, options.write)
        own_branch = git_scope(stack, options.source, path) if options.git else None
        for reference in sorted(set(options.ref) - {own_branch}):
            git(options.source, "check-ref-format", reference)
            acquire(stack, options.source, "ref:" + reference, True)
        for operation in sorted(set(options.operation)):
            acquire(stack, options.source, "operation:" + operation, True)
        # exec transfers descriptors to the actual job: wrapper exit is not a release
        # while a descendant still owns a copy of an open file description.
        os.environ["WORKTREE_SCOPE_FDS"] = ",".join(map(str, scope_fds()))
        os.chdir(path)
        os.execvpe(options.argv[0], options.argv, git_environment())


def reuse(options, allow_recovered_base=False):
    with ExitStack() as stack:
        if options.path.is_symlink():
            raise Refused("linked_tree")
        path = tree_scope(stack, options.source, options.path)
        item, _ = identity(options.source, path)
        git_scope(stack, options.source, path)
        path_scopes(stack, options.source, path, reads=("lean-toolchain", "lake-manifest.json"))
        if "locked" in item:
            raise Refused("intentional_or_initialization_lock")
        if (path / ".lake").is_symlink():
            raise Refused("linked_cache")
        if item.get("branch") != "refs/heads/" + options.branch:
            raise Refused("incompatible_branch")
        base = value(options.source, "rev-parse", "--verify", options.base + "^{commit}")
        pin_revision = base
        if git(path, "merge-base", "--is-ancestor", base, "HEAD", check=False).returncode:
            if not allow_recovered_base:
                raise Refused("incompatible_base")
            from worktree_publication import creation_witness
            try:
                token, creation = creation_witness(options.source, item["branch"])
            except Refused as error:
                raise Refused("incompatible_base") from error
            recovered = (creation + "\0worktree-recovered:" + token.removeprefix("worktree-init:")).encode("ascii")
            if recovered not in git(path, "reflog", "show", "--format=%H%x00%gs", "HEAD").stdout.splitlines():
                raise Refused("incompatible_base")
            if git(path, "merge-base", "--is-ancestor", creation, base, check=False).returncode:
                raise Refused("incompatible_base")
            pin_revision = creation
        # Toolchain/cache ownership is still enforced by the canonical Lean doors.
        # Reuse never materializes, repairs or replaces a cache.
        for pin in ("lean-toolchain", "lake-manifest.json"):
            expected = git(options.source, "show", pin_revision + ":" + pin).stdout
            if (path / pin).read_bytes() != expected:
                raise Refused("incompatible_pin:" + pin)
        return dict(event="worktree_init", status="reused", path=str(path),
                    branch=options.branch, base_revision=base)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=Path.cwd())
    commands = parser.add_subparsers(dest="action", required=True)
    command = commands.add_parser("with")
    command.add_argument("--path", type=Path, default=Path.cwd())
    command.add_argument("--read", action="append", default=[])
    command.add_argument("--write", action="append", default=[])
    command.add_argument("--git", action="store_true")
    command.add_argument("--ref", action="append", default=[])
    command.add_argument("--operation", action="append", default=[])
    command.add_argument("--exclusive", action="store_true")
    command.add_argument("argv", nargs=argparse.REMAINDER)
    joined = commands.add_parser("reuse")
    joined.add_argument("--path", type=Path, required=True)
    joined.add_argument("--branch", required=True)
    joined.add_argument("--base", required=True)
    returned = commands.add_parser("return")
    returned.add_argument("--path", type=Path, default=Path.cwd())
    returned.add_argument("--pr", type=int)
    returned.add_argument("--writers-joined", action="store_true")
    claimed = commands.add_parser("claim")
    claimed.add_argument("--path", type=Path)
    claimed.add_argument("--branch", required=True)
    claimed.add_argument("--base", required=True)
    claimed.add_argument("--skip-restore", action="store_true")
    pool = commands.add_parser("pool")
    pool.add_argument("--dev", required=True)
    pool.add_argument("--force", action="store_true")
    recovery = commands.add_parser("recover-init")
    recovery.add_argument("--path", type=Path, required=True)
    recovery.add_argument("--branch", required=True)
    recovery.add_argument("--base", required=True)
    recovery.add_argument("--expected-token")
    recovery.add_argument("--skip-restore", action="store_true")
    removal = commands.add_parser("remove")
    removal.add_argument("--names", default="")
    removal.add_argument("--path", action="append", type=Path, default=[])
    removal.add_argument("--force", action="store_true")
    removal.add_argument("--preview", action="store_true")
    removal.add_argument("--expected", action="append", default=[])
    pending = commands.add_parser("removal-pending")
    pending.add_argument("--path", type=Path, required=True)
    qualification = commands.add_parser("qualify")
    qualification.add_argument("--path", action="append", type=Path, required=True)
    qualification.add_argument("--stream", action="store_true")
    qualification.add_argument("--budget-seconds", type=float)
    for action in ("prepare-mirror", "validate-mirror"):
        mirror = commands.add_parser(action)
        mirror.add_argument("--base", required=True)
        mirror.add_argument("--merge", required=True)
        mirror.add_argument("--message", required=True)
        if action == "prepare-mirror":
            mirror.add_argument("--path", type=Path, required=True)
            mirror.add_argument("--branch", required=True)
            mirror.add_argument("--remote", default="origin")
        else:
            mirror.add_argument("--commit", required=True)
    for action in ("checkpoint", "publish", "finalize"):
        publication = commands.add_parser(action)
        publication.add_argument("--path", type=Path, default=Path.cwd())
        publication.add_argument("--message-file")
        publication.add_argument("--remote", default="origin")
        publication.add_argument("--branch")
        publication.add_argument("--commit", default="HEAD")
        publication.add_argument("--writers-joined", action="store_true")
    options = parser.parse_args(argv)
    try:
        if options.action == "with":
            if options.argv[:1] == ["--"]:
                options.argv.pop(0)
            with_command(options)
        elif options.action == "reuse":
            print(json.dumps(reuse(options)), flush=True)
        elif options.action in ("return", "claim", "pool"):
            from worktree_pool import return_tree, claim, sweep
            result = (return_tree(options) if options.action == "return" else claim(options)
                      if options.action == "claim" else sweep(options.source, options.dev, options.force))
            print(json.dumps(result), flush=True)
            return 74 if result.get("pool", result).get("status") == "failed" else 0
        elif options.action == "recover-init":
            from worktree_publication import recover_initialization
            print(json.dumps(recover_initialization(options)), flush=True)
        elif options.action == "qualify":
            from worktree_preservation import qualify_batch
            def emit(row):
                print(json.dumps(dict(event="worktree_qualification_item", **row)), flush=True)
            def emit_started(path):
                print(json.dumps(dict(event="worktree_qualification_started", path=str(path))), flush=True)
            result = qualify_batch(options, emit if options.stream else None,
                                   emit_started if options.stream else None)
            if options.stream:
                result = dict(event=result["event"], status=result["status"], item_count=len(result["items"]))
            print(json.dumps(result), flush=True)
            return 74 if result["status"] == "failed" else 0
        elif options.action == "removal-pending":
            from worktree_preservation import removal_pending
            print(json.dumps(removal_pending(options)), flush=True)
        elif options.action == "remove":
            from worktree_preservation import remove
            result = remove(options)
            print(json.dumps(result), flush=True)
            if result["status"] == "refused":
                return 68 if all(row.get("reason", "").startswith("locked_") for row in result["items"]) else 73
            return 74 if result["status"] == "failed" else 0
        elif options.action == "prepare-mirror":
            from worktree_publication import prepare_mirror
            print(json.dumps(prepare_mirror(options)), flush=True)
        elif options.action == "validate-mirror":
            from worktree_publication import validate_mirror
            print(json.dumps(validate_mirror(options.source, options.commit, options.base,
                                            options.merge, options.message)), flush=True)
        else:
            from worktree_publication import checkpoint, publish, finalize
            print(json.dumps(dict(checkpoint=checkpoint, publish=publish, finalize=finalize)[options.action](options)), flush=True)
        return 0
    except Exception as error:
        # Only remove/qualify use the qualification failure boundary. Other
        # commands retain their existing refusal and exception contracts.
        if options.action in ("remove", "qualify") and (
                isinstance(error, GitFailure) or not isinstance(error, Refused)):
            from worktree_preservation import qualification_failure
            print("WORKTREE_FAILED " + qualification_failure(error), file=sys.stderr, flush=True)
            return 74
        if not isinstance(error, (Refused, OSError, ValueError, subprocess.SubprocessError)):
            raise
        if options.action == "checkpoint" and getattr(error, "native_locks", []):
            print(json.dumps(dict(event="worktree_checkpoint", status="failed", error=str(error),
                                  native_locks=error.native_locks)), flush=True)
        print("WORKTREE_RETAINED " + str(error), file=sys.stderr, flush=True)
        return 68 if options.action == "remove" and str(error).startswith("locked_") else 73


if __name__ == "__main__":
    sys.exit(main())
