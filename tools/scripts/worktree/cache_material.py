"""Regular-file inventories shared by optional cache transports and producers."""
import hashlib
import shutil


def sha(path):
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def files(directory, *, materialize_links=False):
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
