#!/usr/bin/env python3
"""Hash raw input bytes and inventory artifacts; interpret no Lean declarations."""
import hashlib
import json
import os
import subprocess
import sys
import time
from pathlib import Path


def digest(path):
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(8 * 1024 * 1024), b""):
            result.update(block)
    return result.hexdigest()


def main():
    if len(sys.argv) != 3 or not all(sys.argv[1:]):
        raise SystemExit("index-domain requires SEARCH_REDUCTION_INDEX and DOMAIN_DIR")
    index, destination = map(Path, sys.argv[1:])
    started = time.time_ns()
    commands = [
        ["make", "lean", "LEAN_TARGETS=LeanInformationAuditRegAnalysis.SearchReduction.Commands"],
        ["make", "search-reduction-run",
         "REQUESTS=tools/lean-inspector/LeanInformationAuditRegAnalysis/SearchReduction/IndexDomain.lean"],
    ]
    for command in commands:
        exit_code = subprocess.run(command, check=False).returncode
        if exit_code:
            break
    summary_path = destination / "compiled-summary.json"
    if not summary_path.is_file() or summary_path.stat().st_mtime_ns < started:
        return exit_code or 1
    files = json.loads((index / "input-files.json").read_text())
    inventory = destination / "inputs.jsonl"
    temporary = inventory.with_suffix(".jsonl.tmp")
    present = 0
    with temporary.open("w") as stream:
        for ordinal, name in enumerate(files):
            path = Path(name)
            exists = path.is_file()
            row = {"ordinal": ordinal, "path": name, "exists": exists,
                   "bytes": path.stat().st_size if exists else None,
                   "sha256": digest(path) if exists else None}
            present += int(exists)
            stream.write(json.dumps(row, separators=(",", ":")) + "\n")
    os.replace(temporary, inventory)
    summary = json.loads(summary_path.read_text())
    artifacts = ["inputs.jsonl", "declarations.jsonl", "compiled-summary.json"]
    result = {"compiled": summary, "compiled_command_exit": exit_code,
              "input_paths": len(files), "present_files": present,
              "absent_files": len(files) - present,
              "artifacts": {name: {"sha256": digest(destination / name),
                                    "bytes": (destination / name).stat().st_size}
                            for name in artifacts}}
    temporary = destination / "domain.json.tmp"
    temporary.write_text(json.dumps(result, indent=2) + "\n")
    os.replace(temporary, destination / "domain.json")
    print(json.dumps({"INDEX_DOMAIN_BYTES": result}))
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
