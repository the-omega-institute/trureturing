"""Regular-file inventories shared by optional cache transports and producers."""
import hashlib
import shutil
import pathlib
import re

_UNSPECIFIED = object()


class CacheMaterialDifference(ValueError):
    """A fixed mismatch category and relative member, without material bytes."""
    def __init__(self, message, reason, path=None):
        super().__init__(message)
        self.reason, self.path = reason, path


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
    path = directory / name
    parent = directory
    for part in pathlib.PurePosixPath(name).parts[:-1]:
        parent /= part
        if parent.is_symlink():
            raise ValueError(f"cache has a symlink: {name}")
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


def files(directory, *, expected=_UNSPECIFIED, copy_to=None):
    if copy_to is not None and expected is _UNSPECIFIED:
        raise ValueError("copy requires registered cache material")
    if expected is not _UNSPECIFIED:
        validate_manifest(expected)
        return sorted((_verified_file(directory, item, copy_to) for item in expected),
                      key=lambda item: item["path"])
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
