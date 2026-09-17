"""Regular-file inventories shared by optional cache transports and producers."""
import hashlib
import os
import shutil
import pathlib
import re
import sys
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction

_UNSPECIFIED = object()


class CacheMaterialDifference(ValueError):
    """A fixed mismatch category and relative member, without material bytes."""
    def __init__(self, message, reason, path=None):
        super().__init__(message)
        self.reason, self.path = reason, path


def _cgroup_cpu_limits():
    """Read applicable Linux CPU quotas, including mounted ancestors."""
    memberships = []
    for line in pathlib.Path("/proc/self/cgroup").read_text().splitlines():
        hierarchy, controllers, member = line.split(":", 2)
        if hierarchy == "0" and not controllers:
            memberships.append(("cgroup2", member))
        elif "cpu" in controllers.split(","):
            memberships.append(("cgroup", member))
    if not memberships:
        return []
    mounts = []
    decode = lambda value: re.sub(r"\\([0-7]{3})", lambda match: chr(int(match[1], 8)), value)
    for line in pathlib.Path("/proc/self/mountinfo").read_text().splitlines():
        before, separator, after = line.partition(" - ")
        fields, options = before.split(), after.split()
        if separator and len(fields) >= 5 and len(options) >= 3:
            if options[0] == "cgroup2" or (options[0] == "cgroup" and "cpu" in options[2].split(",")):
                mounts.append((options[0], pathlib.PurePosixPath(decode(fields[3])),
                               pathlib.Path(decode(fields[4]))))
    limits = []
    for kind, name in memberships:
        member = pathlib.PurePosixPath(name)
        applicable = [(root, mount) for mount_kind, root, mount in mounts
                      if mount_kind == kind and member.is_relative_to(root)]
        if not member.is_absolute() or ".." in member.parts or not applicable:
            raise ValueError("cache hashing CPU capacity: unresolved cgroup membership")
        for root, mount in applicable:
            if not mount.is_absolute() or ".." in mount.parts:
                raise ValueError("cache hashing CPU capacity: invalid cgroup mount")
            directory = mount / member.relative_to(root)
            while True:
                try:
                    value = (directory / ("cpu.max" if kind == "cgroup2" else "cpu.cfs_quota_us")).read_text()
                except FileNotFoundError:
                    # This controller may be disabled here; ancestors still apply.
                    if kind == "cgroup":
                        try:
                            (directory / "cpu.cfs_period_us").read_text()
                        except FileNotFoundError:
                            pass
                        else:
                            raise ValueError("cache hashing CPU capacity: incomplete cgroup quota")
                else:
                    if kind == "cgroup2":
                        quota, period = value.split()
                    else:
                        quota = value.strip()
                        period = (directory / "cpu.cfs_period_us").read_text().strip()
                    period = int(period)
                    if period <= 0:
                        raise ValueError("cache hashing CPU capacity: invalid cgroup period")
                    if quota != ("max" if kind == "cgroup2" else "-1"):
                        quota = int(quota)
                        if quota <= 0:
                            raise ValueError("cache hashing CPU capacity: invalid cgroup quota")
                        limits.append(Fraction(quota, period))
                if directory == mount:
                    break
                directory = directory.parent
    return limits


def hash_workers(file_count):
    """CPU-derived concurrency; each sequential worker uses at most one vCPU.

    C_cpu = min(online, affinity, applicable cgroup quotas), R_cpu = 0,
    r_cpu = 1 vCPU (one executing thread). N = floor(C_cpu), limited only by
    the declared number of files. Missing/insufficient capacity is an error,
    never max(1, N). This is not a memory-capacity or peak-memory claim: each
    worker keeps the existing streaming hash, and no memory/load observation
    controls its concurrency. No ownership or cache-material selection occurs.
    """
    online = os.cpu_count()
    if type(online) is not int or online < 1 or type(file_count) is not int or file_count < 1:
        raise ValueError("cache hashing CPU capacity is unavailable")
    limits = [Fraction(online)]
    if hasattr(os, "sched_getaffinity"):
        limits.append(Fraction(len(os.sched_getaffinity(0))))
    if sys.platform == "linux":
        limits.extend(_cgroup_cpu_limits())
    workers = int(min(limits))
    if workers < 1:
        raise ValueError("cache hashing CPU capacity is insufficient")
    return min(workers, file_count)


def sha(path):
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def copy_hash(path, destination):
    """Hash exactly the bytes copied to a new, independently owned file."""
    destination.parent.mkdir(parents=True, exist_ok=True)
    value = hashlib.sha256()
    with path.open("rb") as source, destination.open("xb") as target:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            target.write(block)
            value.update(block)
    shutil.copystat(path, destination)
    return value.hexdigest(), destination.stat().st_mode & 0o777


def snapshot_files(directory, destination, *, materialize_links=False):
    """Copy and inventory one registered layer directory in a single read."""
    destination.mkdir()
    result, directories = [], [(directory, destination)]
    for path in sorted(directory.rglob("*")):
        relative = path.relative_to(directory)
        target = destination / relative
        source = path
        if path.is_symlink():
            if not materialize_links:
                raise ValueError(f"cache has a symlink: {relative.as_posix()}")
            try:
                source = path.resolve(strict=True)
                if (path.readlink().is_absolute() or not source.is_relative_to(directory.resolve())
                        or not source.is_file()):
                    raise ValueError("link must resolve to an internal regular file")
            except (OSError, RuntimeError, ValueError) as error:
                raise ValueError(f"cache link {relative.as_posix()}: {error}") from error
        elif path.is_dir():
            target.mkdir(parents=True, exist_ok=True)
            directories.append((path, target))
            continue
        if not source.is_file():
            raise ValueError(f"cache material is not a regular file: {relative.as_posix()}")
        digest, mode = copy_hash(source, target)
        result.append({"path": relative.as_posix(), "sha256": digest, "mode": mode})
    if not result:
        raise ValueError("cache has no files")
    for source, target in reversed(directories):
        shutil.copystat(source, target)
    return result


def validate_manifest(expected):
    """Validate declared transport rows without reading their material."""
    if not isinstance(expected, list) or not expected:
        raise ValueError("cache has no registered material")
    seen = set()
    for item in expected:
        if not isinstance(item, dict) or set(item) != {"path", "sha256", "mode"}:
            raise ValueError("invalid cache material row")
        name = item["path"]
        if (not isinstance(name, str) or not name or "\\" in name or ":" in name
                or name.startswith("/") or any(part in ("", ".", "..") for part in name.split("/"))
                or name in seen or not isinstance(item["sha256"], str)
                or not re.fullmatch(r"[0-9a-f]{64}", item["sha256"])
                or type(item["mode"]) is not int or not 0 <= item["mode"] <= 0o777):
            raise ValueError("invalid or duplicate cache material identity")
        seen.add(name)


def _verified_file(directory, item, copy_to):
    name = item["path"]
    path = directory
    for part in pathlib.PurePosixPath(name).parts:
        path /= part
        if path.is_symlink():
            raise ValueError(f"cache has a symlink: {name}")
    if not path.is_file():
        raise ValueError(f"cache material is not a regular file: {name}")
    if copy_to is None:
        digest, mode = sha(path), path.stat().st_mode & 0o777
    else:
        digest, mode = copy_hash(path, copy_to / name)
    actual = {"path": name, "sha256": digest, "mode": mode}
    if actual != item:
        raise CacheMaterialDifference(f"cache material integrity mismatch: {name}",
            "mode-changed" if mode != item["mode"] else "content-changed", name)
    return actual


def files(directory, *, expected=_UNSPECIFIED, copy_to=None, parallel=False):
    if parallel and (expected is _UNSPECIFIED or copy_to is not None):
        raise ValueError("parallel validation requires declared read-only material")
    if copy_to is not None and expected is _UNSPECIFIED:
        raise ValueError("copy requires registered cache material")
    if expected is not _UNSPECIFIED:
        validate_manifest(expected)
        workers = hash_workers(len(expected)) if parallel else 1

        def verify(batch):
            return [_verified_file(directory, item, copy_to) for item in batch]

        if workers == 1:
            result = verify(expected)
        else:
            # Bound queued work to N batches; input order determines failures.
            # Joining before returning/raising keeps rollback free of readers.
            size = (len(expected) + workers - 1) // workers
            batches = [expected[index:index + size] for index in range(0, len(expected), size)]
            try:
                with ThreadPoolExecutor(max_workers=workers) as executor:
                    result = [item for batch in executor.map(verify, batches) for item in batch]
            except RuntimeError as error:
                raise ValueError("cache material parallel validation failed: " + str(error)) from error
        return sorted(result, key=lambda item: item["path"])
    result = []
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            relative = path.relative_to(directory).as_posix()
            raise ValueError(f"cache has a symlink: {relative}")
        if path.is_file():
            result.append({"path": path.relative_to(directory).as_posix(), "sha256": sha(path), "mode": path.stat().st_mode & 0o777})
    if not result:
        raise ValueError("cache has no files")
    return result
