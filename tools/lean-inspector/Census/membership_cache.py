"""Reuse the pure membership decision stream only for byte-identical inputs."""

import hashlib
import pathlib
import shutil
import subprocess
import sys

from incremental import atomic_json
from streaming import digest


def file_digest(path):
    hashed = hashlib.sha256()
    with pathlib.Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            hashed.update(block)
    return "sha256:" + hashed.hexdigest()


def reuse(index, request, reader, cache, destination, compute):
    address = digest([file_digest(index), file_digest(request), reader])
    folder = cache / address[7:]
    rows = pathlib.Path(str(destination) + ".rows.jsonl")
    cached = [folder / "metadata.json", folder / "rows.jsonl"]
    hit = all(path.is_file() for path in cached) and (folder / "complete.json").is_file()
    if hit:
        import json
        expected = json.loads((folder / "complete.json").read_bytes())
        if expected != [file_digest(path) for path in cached]:
            raise ValueError("IE-C044 membership cache result digest mismatch")
        for source, target in zip(cached, [destination, rows]):
            shutil.copyfile(source, target)
    else:
        compute(destination)
        folder.mkdir(parents=True, exist_ok=True)
        for source, target in zip([destination, rows], cached):
            shutil.copyfile(source, target)
        # The completion record is published last; partial writes cannot hit.
        atomic_json(folder / "complete.json", [file_digest(path) for path in cached])
    return {"hit": hit, "receipt": {"cache_key": address,
            "result_digests": [file_digest(destination), file_digest(rows)]}}


if __name__ == "__main__":
    repository, directory, binary = map(pathlib.Path, sys.argv[1:])
    destination = directory / "membership.json"
    def compute(path):
        subprocess.run([str(binary), str(directory / "index.jsonl"),
                        str(directory / "membership-request.json"), str(path)], check=True)
    result = reuse(directory / "index.jsonl", directory / "membership-request.json",
        binary.parent.name, repository / ".lake/build/census/membership", destination, compute)
    atomic_json(directory / "membership-cache.json", result)
