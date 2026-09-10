"""Lean seed partitions and internal semantic inputs; no network operations."""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import platform
import re
import sys


def resolved_mathlib(root: pathlib.Path) -> str:
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    packages = manifest.get("packages") if isinstance(manifest, dict) else None
    if not isinstance(packages, list) or any(not isinstance(item, dict) for item in packages):
        raise ValueError("manifest packages must be an array of objects")
    mathlib = [item for item in packages if item.get("name") == "mathlib"]
    revision = mathlib[0].get("rev") if len(mathlib) == 1 else None
    if not isinstance(revision, str) or not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise ValueError("manifest requires exactly one mathlib package with a resolved 40-hex revision")
    return revision


def binary_platform() -> tuple[str, str]:
    system = platform.system().lower()
    machine = platform.machine().lower()
    return system, {"aarch64": "arm64", "x86_64": "x64", "amd64": "x64"}.get(machine, machine)


def partition_path(root: pathlib.Path) -> str:
    system, machine = binary_platform()
    return f"{resolved_mathlib(root)}/{system}-{machine}"


def semantic_config(root: pathlib.Path) -> dict:
    # TOML metadata (name/version/keywords/defaultTargets and requested refs) is
    # excluded. Lake remains responsible for trace validation and target choice.
    import tomllib
    resolved_mathlib(root)
    manifest = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
    dependencies = sorted(
        [{key: item[key] for key in ("name", "rev", "dir") if key in item}
         for item in manifest["packages"]], key=lambda item: item["name"])
    options = ("leanOptions", "moreLeanArgs", "weakLeanArgs", "plugins", "dynlibs")
    lakefile = root / "lakefile.toml"
    if lakefile.is_file():
        with lakefile.open("rb") as source:
            config = tomllib.load(source)
        lean = {key: config[key] for key in options if key in config}
        lean["libraries"] = [
            {key: library[key] for key in ("name", "srcDir", "roots", "globs", *options) if key in library}
            for library in config.get("lean_lib", [])]
    elif (root / "lakefile.lean").is_file():
        # Executable Lake configuration has no metadata/option field boundary.
        lean = {"lakefile_program": hashlib.sha256((root / "lakefile.lean").read_bytes()).hexdigest()}
    else:
        raise ValueError("repository has no lakefile")
    return {"schema": "lean-semantic-config-v1", "packages": dependencies,
            "toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
            "lean": lean}


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=["partition", "partition-path", "config", "dependency-address"])
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    args = parser.parse_args()
    try:
        if args.command == "partition":
            print(resolved_mathlib(args.repository))
        elif args.command == "partition-path":
            print(partition_path(args.repository))
        elif args.command == "dependency-address":
            # Default dev ci.yml transition only: a 64-hex rendering of the same
            # partition. Remove after ci-push/ci-pr success and required-set migration.
            print(hashlib.sha256(partition_path(args.repository).encode("utf-8")).hexdigest())
        else:
            print(json.dumps(semantic_config(args.repository), sort_keys=True, separators=(",", ":")))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"lean-cache-input: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
