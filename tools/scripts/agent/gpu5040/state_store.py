"""External paths, local exclusion, and fsync-backed atomic publication (no Torch)."""

import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path


def utc_now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, allow_nan=False) + "\n").encode("utf-8")


def hash_json(value):
    return hashlib.sha256(json_bytes(value)).hexdigest()


def file_hash(path):
    digest = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tensor_digest(matrices, initial):
    digest = hashlib.sha256()
    for tensor in (matrices, initial):
        tensor = tensor.detach().cpu().contiguous()
        digest.update(str(tensor.dtype).encode("ascii"))
        digest.update(str(tuple(tensor.shape)).encode("ascii"))
        digest.update(tensor.numpy().tobytes())
    return digest.hexdigest()


def external_path(text):
    path = Path(text).expanduser().resolve()
    source = Path(__file__).resolve().parent
    if path == source or source in path.parents:
        raise ValueError("runtime files must be external to the source directory")
    if any((parent / ".git").exists() for parent in (path, *path.parents)):
        raise ValueError("runtime files must be external to repository trees")
    return path


def shared_root():
    base = Path(os.environ.get("XDG_STATE_HOME", str(Path.home() / ".local" / "state")))
    return external_path(os.environ.get("GPU5040_SHARED_ROOT", str(base / "gpu5040")))


def default_state():
    return shared_root() / "state"


def default_history():
    return shared_root() / "history.sqlite3"


def sync_directory(path):
    descriptor = os.open(path, os.O_RDONLY)
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def sync_file(path):
    with open(path, "rb") as stream:
        os.fsync(stream.fileno())
    sync_directory(Path(path).parent)


def atomic_write(path, writer):
    path = Path(path)
    temporary = path.with_name(path.name + ".tmp")
    descriptor = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW, 0o600)
    with os.fdopen(descriptor, "wb") as stream:
        writer(stream)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)
    sync_directory(path.parent)


def atomic_json(path, value):
    data = json_bytes(value)
    atomic_write(path, lambda stream: stream.write(data))


class StateLocks:
    """Always acquire the canonical state lock, then the per-user GPU/verifier lock.

    All source copies and all registries use the same shared lock. Never unlink a
    lock file: removing its inode would let a second owner acquire another inode.
    """

    def __init__(self, directory):
        self.paths = [external_path(directory) / ".state.lock", shared_root() / "gpu-verifier.lock"]
        self.streams = []

    def __enter__(self):
        try:
            for path in self.paths:
                path.parent.mkdir(parents=True, exist_ok=True)
                stream = open(path, "a+b")
                self.streams.append(stream)
                fcntl.flock(stream, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            self.__exit__()
            raise ValueError("another worker or verifier holds lock: " + str(path)) from None
        except BaseException:
            self.__exit__()
            raise
        return self

    def __exit__(self, *args):
        while self.streams:
            self.streams.pop().close()
