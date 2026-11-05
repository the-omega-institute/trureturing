#!/usr/bin/env python3
"""Reuse test snapshots by data inputs, explicit formats and output integrity."""
import argparse
import hashlib
import json
import pathlib
import subprocess
import time

VERSION = "snapshot-cache-v2/discrtree-pickle-v5/membership-alpha-syntax-v5-qualified-parts-memo-2000000"


class ContentHashes:
    """Share hashing of common Mathlib inputs across one sequential fixture suite."""
    def __init__(self):
        self.values = {}

    def digest(self, path):
        path = pathlib.Path(path).resolve()
        try:
            stat = path.stat()
        except FileNotFoundError:
            return None
        stamp = (stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns)
        previous = self.values.get(path)
        if previous is not None and previous[0] == stamp:
            return previous[1]
        digest = hashlib.sha256()
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
        after = path.stat()
        if stamp != (after.st_dev, after.st_ino, after.st_size,
                     after.st_mtime_ns, after.st_ctime_ns):
            raise RuntimeError(f"snapshot input changed while hashing: {path}")
        value = digest.hexdigest()
        self.values[path] = (stamp, value)
        return value

    def inventory(self, paths):
        return {str(pathlib.Path(path).resolve()): self.digest(path) for path in paths}


def read_json(path):
    return json.loads(pathlib.Path(path).read_text())


def outputs(directory, basis):
    header = read_json(directory / "header.json")
    member = read_json(directory / "membership-header.json")
    if not (header["scope"] == "test" and header["basis"] == basis
            and header["complete"] and not header["missing"]
            and member["complete"] and not member["missing"]
            and member["inputs"] == header["inputs"]):
        raise ValueError("test snapshot is incomplete or has a different population")
    files = [directory / name for name in (
        "header.json", "membership-header.json", "input-files.json", "import-partitions.json")]
    for storage in (header["storage"], member["storage"]):
        files.extend(path for path in (directory / storage).rglob("*")
                     if path.is_file() and path.suffix in (".pickle", ".json"))
    return sorted(set(files))


def ensure_snapshot(directory, basis, roots, producer, produce, hashes):
    directory = pathlib.Path(directory)
    configuration = {"version": VERSION, "basis": basis, "roots": roots}
    cache_path = directory / "cache-sha256.json"
    try:
        old = read_json(cache_path)
        inputs = read_json(directory / "input-files.json")
        if (old["configuration"] == configuration
                and old["inputs"] == hashes.inventory(inputs)
                and old["outputs"] == hashes.inventory(outputs(directory, basis))):
            return "reused"
    except (OSError, ValueError, KeyError, TypeError):
        pass
    if not pathlib.Path(producer).is_file():
        raise ValueError("snapshot producer is not built")
    produce()
    checked_outputs = outputs(directory, basis)
    record = {"configuration": configuration,
              "inputs": hashes.inventory(read_json(directory / "input-files.json")),
              "outputs": hashes.inventory(checked_outputs)}
    temporary = cache_path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(record, sort_keys=True) + "\n")
    temporary.replace(cache_path)
    return "generated"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--snapshot", nargs="+", action="append", required=True,
                        metavar="BASIS_OR_MODULE")
    args = parser.parse_args()
    if any(len(spec) < 2 for spec in args.snapshot):
        parser.error("each --snapshot needs a basis and at least one module")
    producer = pathlib.Path(".lake/build/lean-inspector/reg/bin/searchReductionIndex")
    hashes = ContentHashes()
    for basis, *roots in args.snapshot:
        directory = pathlib.Path("build/lean-inspector/search-reduction-test-index") / basis
        started = time.monotonic()

        def produce():
            subprocess.run(["make", "search-reduction-index-run", f"INDEX_BASIS={basis}",
                            f"INDEX_DIR={directory}", f"INDEX_MODULES={' '.join(roots)}"],
                           check=True)

        status = ensure_snapshot(directory, basis, roots, producer, produce, hashes)
        print(f"SEARCH_REDUCTION_INDEX_TIMING basis={basis} "
              f"seconds={time.monotonic() - started:.3f} status={status}", flush=True)


if __name__ == "__main__":
    main()
