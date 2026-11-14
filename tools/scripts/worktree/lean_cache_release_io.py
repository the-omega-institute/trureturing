"""Cooperative bounded Release I/O; the caller owns staging and rollback."""

import contextlib
import hashlib
import time


class OperationBudget:
    """A computation deadline whose clock can exclude an owned asset transfer."""
    def __init__(self, deadline):
        self.deadline = deadline

    @contextlib.contextmanager
    def pause(self):
        started = time.monotonic()
        try:
            yield
        finally:
            self.deadline += time.monotonic() - started


def remaining(deadline):
    if deadline is None:
        return float("inf")
    if isinstance(deadline, OperationBudget):
        deadline = deadline.deadline
    seconds = deadline - time.monotonic()
    if seconds <= 0:
        raise TimeoutError("Release operation deadline exhausted")
    return seconds


class MultipartArchiveOutput:
    """Stage one gzip stream without retaining a second copy of its parts."""
    def __init__(self, stage, name, chunk_bytes, deadline):
        if chunk_bytes <= 0:
            raise ValueError("archive part size must be positive")
        self.stage, self.name = stage, name
        self.chunk_bytes, self.deadline = chunk_bytes, deadline
        self.output = None
        self.failure = None
        self.parts = []
        self.archive_bytes = self.part_bytes = 0
        self.archive_hash, self.part_hash = hashlib.sha256(), hashlib.sha256()

    def __enter__(self):
        self._open_part()
        return self

    def _open_part(self):
        remaining(self.deadline)
        if len(self.parts) == 100:
            raise ValueError("archive must fit in 1 to 100 parts")
        self.path = self.stage / f"{self.name}.part-{len(self.parts):02d}"
        self.output = self.path.open("wb")
        self.part_bytes, self.part_hash = 0, hashlib.sha256()

    def _close_part(self):
        output, self.output = self.output, None
        try:
            remaining(self.deadline)
            output.flush()
        finally:
            output.close()
        remaining(self.deadline)
        self.parts.append({"name": self.path.name, "sha256": self.part_hash.hexdigest(), "bytes": self.part_bytes})

    def tell(self):
        return self.archive_bytes

    def write(self, block):
        if self.failure is not None:
            raise self.failure
        try:
            remaining(self.deadline)
            return self._write(block)
        except BaseException as error:
            self.failure = error
            raise

    def _write(self, block):
        view = memoryview(block)
        transferred = 0
        while transferred < len(view):
            remaining(self.deadline)
            if self.part_bytes == self.chunk_bytes:
                self._close_part()
                self._open_part()
            piece = view[transferred:transferred + min(self.chunk_bytes - self.part_bytes, 1024 * 1024)]
            count = self.output.write(piece)
            if not isinstance(count, int) or not 0 < count <= len(piece):
                raise OSError("archive output made no valid write progress")
            self.archive_hash.update(piece[:count])
            self.part_hash.update(piece[:count])
            self.archive_bytes += count
            self.part_bytes += count
            transferred += count
            remaining(self.deadline)
        return transferred

    def __exit__(self, error_type, error, traceback):
        if error_type is not None:
            if self.output is not None:
                self.output.close()
            return
        self._close_part()
        if not self.archive_bytes:
            raise ValueError("archive must fit in 1 to 100 parts")
        if len(self.parts) == 1:
            self.path.rename(self.stage / self.name)
            self.parts[0]["name"] = self.name
        remaining(self.deadline)

    def metadata(self):
        remaining(self.deadline)
        return {"archive_sha256": self.archive_hash.hexdigest(), "archive_bytes": self.archive_bytes,
                "parts": self.parts}


def archive_sha(path, deadline):
    value = hashlib.sha256()
    with path.open("rb") as source:
        while True:
            remaining(deadline)
            block = source.read(1024 * 1024)
            if not block:
                return value.hexdigest()
            value.update(block)
            remaining(deadline)


def copy_chunks(source, target, deadline):
    transferred = 0
    while True:
        remaining(deadline)
        block = source.read(1024 * 1024)
        if not block:
            return transferred
        target.write(block)
        transferred += len(block)
        remaining(deadline)


class ArchiveInput:
    """Check compressed reads, including gzip seeks used during tar scanning."""
    def __init__(self, source, deadline):
        self.source, self.deadline = source, deadline

    def __getattr__(self, name):
        return getattr(self.source, name)

    def read(self, size=-1):
        remaining(self.deadline)
        block = self.source.read(size)
        remaining(self.deadline)
        return block


def extract_members(archive, destination, members, deadline):
    directories = []
    for member in members:
        remaining(deadline)
        target = destination / member.name
        if member.isdir():
            target.mkdir(parents=True, exist_ok=True)
            directories.append((member, target))
            continue
        source = archive.extractfile(member)
        if source is None:
            raise ValueError("archive member has no file content: " + member.name)
        target.parent.mkdir(parents=True, exist_ok=True)
        with source, target.open("wb") as output:
            copy_chunks(source, output, deadline)
        archive.chown(member, target, numeric_owner=False)
        archive.chmod(member, target)
        archive.utime(member, target)
        remaining(deadline)
    # Match extractall: apply directory metadata after creating descendants.
    for member, target in sorted(directories, key=lambda item: item[0].name, reverse=True):
        remaining(deadline)
        archive.chown(member, target, numeric_owner=False)
        archive.utime(member, target)
        archive.chmod(member, target)
