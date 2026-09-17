"""Resolved mathlib seed partitions and binary platform isolation."""
from __future__ import annotations

import argparse
import json
import pathlib
import platform
import re
import sys


def resolved_mathlib(root: pathlib.Path) -> str:
    return manifest_mathlib(json.loads((root / "lake-manifest.json").read_text(encoding="utf-8")))


def manifest_mathlib(manifest: object) -> str:
    packages = manifest.get("packages") if isinstance(manifest, dict) else None
    if not isinstance(packages, list) or any(not isinstance(item, dict) for item in packages):
        raise ValueError("manifest packages must be an array of objects")
    mathlib = [item for item in packages if item.get("name") == "mathlib"]
    revision = mathlib[0].get("rev") if len(mathlib) == 1 else None
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("manifest requires exactly one mathlib package with a resolved 40-hex revision")
    return revision


def binary_platform() -> tuple[str, str]:
    return normalized_platform(platform.system(), platform.machine())


def normalized_platform(system: str, machine: str) -> tuple[str, str]:
    system, machine = system.lower(), machine.lower()
    return system, {"aarch64": "arm64", "x86_64": "x64", "amd64": "x64"}.get(machine, machine)


def partition_path(root: pathlib.Path) -> str:
    system, machine = binary_platform()
    return f"{resolved_mathlib(root)}/{system}-{machine}"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["partition", "partition-path"])
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    args = parser.parse_args()
    try:
        if args.command == "partition":
            print(resolved_mathlib(args.repository))
        elif args.command == "partition-path":
            print(partition_path(args.repository))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"lean-cache-input: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
