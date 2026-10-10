#!/usr/bin/env python3
"""Cooperative worktree scopes. Locks are OS descriptors, never custody records.

Participants must enter before using a tree, declare overlapping reads/writes,
and preserve inherited descriptors in descendants that continue using it.
Programs that close inherited descriptors must enter again before accessing it.
"""

import argparse
from contextlib import ExitStack
import fcntl
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from urllib.parse import unquote, urlsplit

if __name__ == "__main__":
    sys.modules["worktree_protocol"] = sys.modules[__name__]

OPEN_SCOPES = []


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
    pass


def git_environment(overrides=None):
    # Ambient location/index/object overrides must never redirect canonical
    # inspection. Keep transport and author identity settings; owned private
    # indexes are supplied explicitly by the checkpoint operation.
    permitted = {"GIT_SSH", "GIT_SSH_COMMAND", "GIT_SSH_VARIANT", "GIT_ASKPASS",
                 "GIT_TERMINAL_PROMPT", "GIT_AUTHOR_NAME", "GIT_AUTHOR_EMAIL",
                 "GIT_AUTHOR_DATE", "GIT_COMMITTER_NAME", "GIT_COMMITTER_EMAIL",
                 "GIT_COMMITTER_DATE"}
    environment = {key: val for key, val in os.environ.items()
                   if not key.startswith("GIT_") or key in permitted}
    environment.update(overrides or {})
    return environment


def git(root, *args, env=None, input=None, check=True, timeout=300):
    result = subprocess.run(["git", "-C", str(root), *map(str, args)], input=input,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            env=git_environment(env), timeout=timeout, pass_fds=scope_fds())
    if check and result.returncode:
        raise Refused(result.stderr.decode(errors="replace").strip() or "git failed")
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


def identity(source, path):
    path = Path(path).absolute()
    if path.is_symlink() or not path.is_dir():
        raise Refused("missing_or_linked_tree")
    path = path.resolve()
    match = [r for r in inventory(source) if Path(r["worktree"]).resolve() == path]
    if len(match) != 1 or common(path) != common(source):
        raise Refused("repository_identity")
    if Path(value(path, "rev-parse", "--show-toplevel")).resolve() != path:
        raise Refused("tree_identity")
    metadata = Path(value(path, "rev-parse", "--absolute-git-dir")).resolve()
    if metadata != common(source):
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
    branch = os.fsdecode(result.stdout).strip() if result.returncode == 0 else "HEAD"
    acquire(stack, source, "ref:" + (branch if branch != "HEAD" else metadata + ":HEAD"), True)
    acquire(stack, source, "index:" + metadata, True)
    return branch


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


def reuse(options):
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
        if git(path, "merge-base", "--is-ancestor", base, "HEAD", check=False).returncode:
            raise Refused("incompatible_base")
        # Toolchain/cache ownership is still enforced by the canonical Lean doors.
        # Reuse never materializes, repairs or replaces a cache.
        for pin in ("lean-toolchain", "lake-manifest.json"):
            expected = git(options.source, "show", base + ":" + pin).stdout
            if (path / pin).read_bytes() != expected:
                raise Refused("incompatible_pin:" + pin)
        print(json.dumps(dict(event="worktree_init", status="reused", path=str(path),
                              branch=options.branch, base_revision=base)), flush=True)


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
    removal = commands.add_parser("remove")
    removal.add_argument("--names", default="")
    removal.add_argument("--path", action="append", type=Path, default=[])
    removal.add_argument("--force", action="store_true")
    removal.add_argument("--preview", action="store_true")
    removal.add_argument("--expected", action="append", default=[])
    retirement = commands.add_parser("retire-branch")
    retirement.add_argument("--branch", required=True)
    retirement.add_argument("--commit", required=True)
    retirement.add_argument("--preview", action="store_true")
    retirement.add_argument("--expected-reflog-sha256")
    snapshot = commands.add_parser("remove-snapshot")
    snapshot.add_argument("--path", type=Path, required=True)
    snapshot.add_argument("--base", required=True)
    snapshot.add_argument("--preview", action="store_true")
    mirror = commands.add_parser("prepare-mirror")
    mirror.add_argument("--path", type=Path, required=True)
    mirror.add_argument("--branch", required=True)
    mirror.add_argument("--base", required=True)
    mirror.add_argument("--merge", required=True)
    mirror.add_argument("--message", required=True)
    mirror.add_argument("--remote", default="origin")
    for action in ("checkpoint", "publish", "finalize"):
        publication = commands.add_parser(action)
        publication.add_argument("--path", type=Path, default=Path.cwd())
        publication.add_argument("--write", action="append", default=[])
        publication.add_argument("--read", action="append", default=[])
        publication.add_argument("--message-file")
        publication.add_argument("--paths-from", type=Path)
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
            reuse(options)
        elif options.action == "remove":
            from worktree_preservation import remove
            result = remove(options)
            print(json.dumps(result), flush=True)
            return 74 if result["status"] == "failed" else 0
        elif options.action in ("retire-branch", "remove-snapshot"):
            from worktree_preservation import retire_branch, remove_snapshot
            result = (retire_branch if options.action == "retire-branch" else remove_snapshot)(options)
            print(json.dumps(result), flush=True)
            if result["status"] == "partial_or_indeterminate":
                return 74
        elif options.action == "prepare-mirror":
            from worktree_publication import prepare_mirror
            print(json.dumps(prepare_mirror(options)), flush=True)
        else:
            from worktree_publication import checkpoint, publish, finalize
            if options.paths_from:
                options.write.extend(os.fsdecode(name) for name in read_input(options.source, options.paths_from).split(b"\0") if name)
            print(json.dumps(dict(checkpoint=checkpoint, publish=publish, finalize=finalize)[options.action](options)), flush=True)
        return 0
    except (Refused, OSError, ValueError, subprocess.SubprocessError) as error:
        print("WORKTREE_RETAINED " + str(error), file=sys.stderr, flush=True)
        return 68 if options.action == "remove" and str(error).startswith("locked_") else 73


if __name__ == "__main__":
    sys.exit(main())
