"""Cooperative bounded Release I/O; the caller owns staging and rollback."""

import hashlib
import time


def remaining(deadline):
    seconds = deadline - time.monotonic()
    if seconds <= 0:
        raise TimeoutError("Release operation deadline exhausted")
    return seconds


class ArchiveOutput:
    """Check the publication budget at each bounded tar/gzip output write."""
    def __init__(self, output, deadline):
        self.output, self.deadline = output, deadline

    def __getattr__(self, name):
        return getattr(self.output, name)

    def write(self, block):
        remaining(self.deadline)
        count = self.output.write(block)
        remaining(self.deadline)
        return count


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
