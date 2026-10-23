#!/usr/bin/env python3
"""Filter transient candidate rows against current source-owned default dispatch."""
import pathlib
import re
import subprocess
import sys


def eligible_atoms(repo, atom_ids):
    repo = pathlib.Path(repo).resolve()
    cli = repo / "tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll"
    if not cli.is_file():
        raise RuntimeError("build the current CLI with make -C tools dotnet before selection")
    ids = list(dict.fromkeys(atom_ids))
    if any(re.fullmatch(r"[0-9a-f]{64}", atom) is None for atom in ids):
        raise ValueError("candidate atom ID is not canonical")
    eligible = set()
    for start in range(0, len(ids), 200):
        batch = ids[start:start + 200]
        args = ["dotnet", str(cli), "search-atoms", "--selection", "default-dispatch",
                "--limit", str(len(batch))]
        for atom in batch:
            args.extend(["--atom-id", atom])
        result = subprocess.run(args, cwd=repo, capture_output=True, text=True, check=False)
        if result.returncode:
            raise RuntimeError(result.stderr.strip() or "default dispatch query failed")
        for line in result.stdout.splitlines():
            match = re.fullmatch(r"ATOM source_id=\S+ atom_id=([0-9a-f]{64}) state=\S+ path=\S+", line)
            if not match or match[1] not in batch:
                raise RuntimeError("unexpected default dispatch query output")
            eligible.add(match[1])
    return eligible


def main():
    if len(sys.argv) != 2:
        raise ValueError("usage: default_dispatch_filter.py REPO < atom-and-title.tsv")
    rows = sys.stdin.read().splitlines()
    eligible = eligible_atoms(sys.argv[1], [row.split("\t", 1)[0] for row in rows])
    for row in rows:
        if row.split("\t", 1)[0] in eligible:
            print(row)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"DEFAULT_DISPATCH_INVALID {error}", file=sys.stderr)
        sys.exit(2)
