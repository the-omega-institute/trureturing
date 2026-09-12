"""Regular-file inventories shared by optional cache transports and producers."""
import hashlib
import shutil
import pathlib
import re

_UNSPECIFIED = object()


def sha(path):
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def files(directory, *, materialize_links=False, expected=_UNSPECIFIED):
    if expected is not _UNSPECIFIED:
        if not isinstance(expected, list) or not expected:
            raise ValueError("cache has no registered material")
        result, seen = [], set()
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
            path = directory
            for part in pathlib.PurePosixPath(name).parts:
                path /= part
                if path.is_symlink():
                    raise ValueError(f"cache has a symlink: {name}")
            actual = {"path": name, "sha256": sha(path), "mode": path.stat().st_mode & 0o777}
            if actual != item:
                raise ValueError(f"cache material integrity mismatch: {name}")
            result.append(actual)
        return sorted(result, key=lambda item: item["path"])
    result = []
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            relative = path.relative_to(directory).as_posix()
            if not materialize_links:
                raise ValueError(f"cache has a symlink: {relative}")
            # Only the private dependency snapshot may turn internal file links
            # into ordinary, hashed copies. Restores still reject raw links.
            try:
                target = path.resolve(strict=True)
                if not target.is_relative_to(directory.resolve()) or not target.is_file():
                    raise ValueError("link must resolve to an internal regular file")
                path.unlink()
                shutil.copy2(target, path)
            except (OSError, RuntimeError, ValueError) as error:
                raise ValueError(f"cache link {relative}: {error}") from error
        if path.is_file():
            result.append({"path": path.relative_to(directory).as_posix(), "sha256": sha(path), "mode": path.stat().st_mode & 0o777})
    if not result:
        raise ValueError("cache has no files")
    return result
