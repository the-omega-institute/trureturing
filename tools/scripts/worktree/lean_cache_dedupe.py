"""Re-share worktree Lake artifacts that are byte-identical to the donor checkout.

A linked worktree starts as an APFS clone of the donor `.lake`, but the sharing decays:
the worktree rebuilds changed modules, and every donor rebuild leaves older worktrees
holding the previous generation alone. This pass restores the incremental footprint.
Each regular file under the worktree `.lake` whose donor counterpart has identical bytes
is replaced by a clone of the donor file, keeping the worktree mode and timestamps, so
only real differences stay private.

After a build, `--since` and `--build-only` limit the pass to `.lake/build` files written by
that build; `--all` (run after the donor is warmed) covers every file of every linked worktree.
Locking follows the canonical cache guards: the target `.lake` exclusively (the writer
guard every canonical Lake build holds) and the donor `.lake` shared. A busy guard skips
that tree. Replacement re-checks the target stat identity right before the atomic rename.
Only macOS clonefile(2) is supported; other platforms report `unsupported` and exit 0.
"""
from __future__ import annotations

import argparse
import ctypes
import ctypes.util
import errno
import fcntl
import hashlib
import json
import os
import pathlib
import stat
import struct
import subprocess
import sys

RECEIPT = "LEAN_CACHE_DEDUPE"
MIN_BYTES = 16 * 1024
CHUNK = 8 * 1024 * 1024
F_LOG2PHYS_EXT = 65
CLONE_NOFOLLOW = 1


def guard_path(lake: pathlib.Path) -> pathlib.Path:
    # Mirrors LeanCacheGuard: ~/.cache/stratalint-lean-cache-guards/<sha256(physical .lake)>.lock
    address = hashlib.sha256(os.path.realpath(lake).encode("utf-8")).hexdigest()
    return pathlib.Path.home() / ".cache" / "stratalint-lean-cache-guards" / f"{address}.lock"


class Guard:
    def __init__(self, lake: pathlib.Path, exclusive: bool):
        path = guard_path(lake)
        path.parent.mkdir(parents=True, exist_ok=True)
        self.fd = os.open(path, os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(self.fd, (fcntl.LOCK_EX if exclusive else fcntl.LOCK_SH) | fcntl.LOCK_NB)
        except BlockingIOError:
            os.close(self.fd)
            self.fd = -1

    @property
    def held(self) -> bool:
        return self.fd >= 0

    def __enter__(self) -> "Guard":
        return self

    def __exit__(self, *_: object) -> None:
        if self.fd >= 0:
            fcntl.flock(self.fd, fcntl.LOCK_UN)
            os.close(self.fd)


def first_extent(path: str, size: int) -> int | None:
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        out = fcntl.fcntl(fd, F_LOG2PHYS_EXT, struct.pack("=Iqq", 0, size, 0))
        return struct.unpack("=Iqq", out)[2]
    except OSError:
        return None
    finally:
        os.close(fd)


def same_bytes(left: str, right: str) -> bool:
    with open(left, "rb") as a, open(right, "rb") as b:
        while True:
            x, y = a.read(CHUNK), b.read(CHUNK)
            if x != y:
                return False
            if not x:
                return True


def read_small(path: str) -> bytes | None:
    try:
        with open(path, "rb") as handle:
            return handle.read(4096)
    except OSError:
        return None


def sidecar_differs(target: str, donor: str) -> bool:
    # Lake writes a content hash next to each artifact; different hashes mean different bytes.
    mine, theirs = read_small(target + ".hash"), read_small(donor + ".hash")
    return mine is not None and theirs is not None and mine != theirs


class Cloner:
    def __init__(self) -> None:
        libc = ctypes.CDLL(ctypes.util.find_library("c"), use_errno=True)
        self.clonefile = libc.clonefile
        self.clonefile.argtypes = [ctypes.c_char_p, ctypes.c_char_p, ctypes.c_uint32]
        self.clonefile.restype = ctypes.c_int

    def clone(self, source: str, destination: str) -> None:
        if self.clonefile(os.fsencode(source), os.fsencode(destination), CLONE_NOFOLLOW) != 0:
            code = ctypes.get_errno()
            raise OSError(code, os.strerror(code), destination)


def identity(st: os.stat_result) -> tuple[int, int, int, int, int]:
    return (st.st_dev, st.st_ino, st.st_size, st.st_mtime_ns, st.st_ctime_ns)


def dedupe_tree(target_lake: pathlib.Path, donor_lake: pathlib.Path, cloner: Cloner,
                since: int | None = None) -> dict[str, int]:
    counts = {"files_relinked": 0, "bytes_relinked": 0, "files_already_shared": 0,
              "files_differ": 0, "files_raced": 0, "errors": 0}
    for directory, subdirectories, files in os.walk(target_lake):
        subdirectories[:] = [name for name in subdirectories if name != ".git"]
        relative = os.path.relpath(directory, target_lake)
        donor_directory = os.path.normpath(os.path.join(donor_lake, relative))
        if not os.path.isdir(donor_directory):
            subdirectories[:] = []
            continue
        for name in files:
            if name.startswith(".lean-cache-dedupe-"):
                continue
            target = os.path.join(directory, name)
            donor = os.path.join(donor_directory, name)
            try:
                before = os.lstat(target)
                if not stat.S_ISREG(before.st_mode) or before.st_nlink != 1 or before.st_size < MIN_BYTES:
                    continue
                if since is not None and before.st_mtime < since:
                    continue
                donor_stat = os.lstat(donor)
            except OSError:
                continue
            if (not stat.S_ISREG(donor_stat.st_mode) or before.st_size != donor_stat.st_size
                    or before.st_dev != donor_stat.st_dev):
                continue
            try:
                shared = first_extent(target, before.st_size)
                if shared is not None and shared == first_extent(donor, donor_stat.st_size):
                    counts["files_already_shared"] += 1
                    continue
                if sidecar_differs(target, donor) or not same_bytes(target, donor):
                    counts["files_differ"] += 1
                    continue
                staging = os.path.join(directory, f".lean-cache-dedupe-{os.getpid()}-{name}")
                cloner.clone(donor, staging)
                try:
                    os.chmod(staging, before.st_mode & 0o7777)
                    os.utime(staging, ns=(before.st_atime_ns, before.st_mtime_ns))
                    if identity(os.lstat(target)) != identity(before):
                        counts["files_raced"] += 1
                        continue
                    os.rename(staging, target)
                    staging = ""
                finally:
                    if staging:
                        try:
                            os.unlink(staging)
                        except FileNotFoundError:
                            pass
                counts["files_relinked"] += 1
                counts["bytes_relinked"] += before.st_size
            except OSError as error:
                if error.errno in (errno.ENOSPC, errno.EDQUOT):
                    raise
                counts["errors"] += 1
    return counts


def git(root: pathlib.Path, *arguments: str) -> str:
    return subprocess.run(["git", "-C", str(root), *arguments], check=True,
                          capture_output=True, text=True).stdout


def main_checkout(root: pathlib.Path) -> pathlib.Path:
    common = pathlib.Path(git(root, "rev-parse", "--path-format=absolute", "--git-common-dir").strip())
    return common.parent


def linked_worktrees(root: pathlib.Path) -> list[pathlib.Path]:
    entries = [line[len("worktree "):] for line in git(root, "worktree", "list", "--porcelain").splitlines()
               if line.startswith("worktree ")]
    return [pathlib.Path(entry) for entry in entries[1:]]


def receipt(payload: dict[str, object]) -> None:
    print(f"{RECEIPT} {json.dumps(payload, separators=(',', ':'))}", flush=True)


def run_one(target: pathlib.Path, donor: pathlib.Path, cloner: Cloner | None,
            since: int | None = None, build_only: bool = False) -> dict[str, object]:
    base: dict[str, object] = {"root": str(target), "donor": str(donor)}
    target_lake, donor_lake = target / ".lake", donor / ".lake"
    if cloner is None:
        return {**base, "status": "unsupported", "reason": "clonefile(2) is only available on macOS"}
    if os.path.realpath(target) == os.path.realpath(donor):
        return {**base, "status": "skipped", "reason": "target is the donor"}
    for lake, role in ((target_lake, "target"), (donor_lake, "donor")):
        if not lake.is_dir() or lake.is_symlink():
            return {**base, "status": "skipped", "reason": f"{role} .lake is absent"}
    with Guard(target_lake, exclusive=True) as writer, Guard(donor_lake, exclusive=False) as reader:
        if not writer.held:
            return {**base, "status": "skipped", "reason": "target cache writer guard is busy"}
        if not reader.held:
            return {**base, "status": "skipped", "reason": "donor cache guard is busy"}
        subtree = pathlib.Path("build") if build_only else pathlib.Path()
        counts = dedupe_tree(target_lake / subtree, donor_lake / subtree, cloner, since)
    return {**base, "status": "completed", "reason": None, **counts}


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--root", default=".", help="worktree to re-share (default: current checkout)")
    parser.add_argument("--donor", help="donor checkout (default: the main checkout)")
    parser.add_argument("--all", action="store_true", help="re-share every linked worktree of the repository")
    parser.add_argument("--since", type=int, help="only consider files modified at or after this epoch second")
    parser.add_argument("--build-only", action="store_true",
                        help="only consider .lake/build (pinned dependency packages are left to --all)")
    options = parser.parse_args(argv)

    root = pathlib.Path(git(pathlib.Path(options.root), "rev-parse", "--show-toplevel").strip())
    donor = pathlib.Path(options.donor).resolve() if options.donor else main_checkout(root)
    cloner = Cloner() if sys.platform == "darwin" else None
    targets = linked_worktrees(root) if options.all else [root]
    exit_code = 0
    for target in targets:
        try:
            result = run_one(target, donor, cloner, options.since, options.build_only)
        except OSError as error:
            result = {"root": str(target), "donor": str(donor), "status": "failed", "reason": str(error)}
            exit_code = 1
        receipt(result)
    return exit_code


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
