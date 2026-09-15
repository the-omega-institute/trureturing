"""Select the pinned tools and hash only explicitly registered runtime material."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "scripts/report"))
from producer_paths import load_scope, runtime_registration


def file_sha(path: pathlib.Path) -> str:
    value = hashlib.sha256()
    with path.open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            value.update(block)
    return value.hexdigest()


def declared_lean_material(toolchain: pathlib.Path, patterns: list[str]) -> dict:
    programs = {}
    owners = {}
    for pattern in patterns:
        # Only registered filename globs expand; imports and neighboring files
        # cannot introduce additional material into the identity.
        matches = sorted(toolchain.glob(pattern))
        if not matches:
            raise ValueError(f"required runtime.lean material is absent: {pattern} under {toolchain}")
        for path in matches:
            resolved = path.resolve()
            if not resolved.is_relative_to(toolchain) or not resolved.is_file():
                raise ValueError(f"invalid runtime.lean material: {pattern} resolved to {path}")
            if resolved in owners:
                raise ValueError(f"conflicting runtime.lean material: {path.relative_to(toolchain)} declared by {owners[resolved]} and {pattern}")
            owners[resolved] = pattern
            programs["lean:" + path.relative_to(toolchain).as_posix()] = file_sha(resolved)
    return programs


def registration(root: pathlib.Path) -> dict:
    _, manifest = load_scope(root, "lean-report")
    return runtime_registration(manifest)


def select_binaries(root: pathlib.Path, lake: str = "", lean: str = "") -> tuple[str, str]:
    lake = lake or os.environ.get("LAKE_BIN", "")
    lean = lean or os.environ.get("LEAN_BIN", "")
    if lake or lean:
        if not lake or not lean:
            raise ValueError("custom LAKE_BIN requires an explicit paired LEAN_BIN (and conversely)")
    else:
        pin = (root / "lean-toolchain").read_text().strip()
        if not pin or any(char.isspace() for char in pin):
            raise ValueError("lean-toolchain must name one pinned selector")
        elan = shutil.which("elan")
        if not elan:
            raise ValueError("elan is required to resolve the pinned Lean and Lake executables")
        environment = dict(os.environ, ELAN_TOOLCHAIN=pin)
        lake, lean = (subprocess.run([elan, "which", command], cwd=root, env=environment,
            check=True, capture_output=True, text=True).stdout.strip() for command in ("lake", "lean"))
    for name, value in (("LAKE_BIN", lake), ("LEAN_BIN", lean)):
        if not pathlib.Path(value).is_absolute() or not os.access(value, os.X_OK):
            raise ValueError(f"{name} must be an absolute executable: {value!r}")
    return lake, lean


def runtime_hash(root: pathlib.Path, lean: str) -> str:
    runtime = registration(root)
    # Direct Lean lookup does not initialize a Lake project or provision .lake.
    prefix = subprocess.run([lean, "--print-prefix"], cwd=root,
        check=True, capture_output=True, text=True).stdout.strip()
    if not prefix or not pathlib.Path(prefix).is_absolute():
        raise ValueError(f"invalid declared Lean installation prefix: {prefix!r}")
    programs = declared_lean_material(pathlib.Path(prefix).resolve(), runtime["lean"])
    for material in runtime["python"]:
        executable = pathlib.Path(sys.executable).resolve()
        if not executable.is_file():
            raise ValueError(f"required runtime.python {material} is absent: {executable}")
        programs["python:" + material] = file_sha(executable)
    identity = {"schema": "lean-report-runtime-v2", "programs": programs}
    return hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=pathlib.Path, required=True)
    parser.add_argument("--lean")
    parser.add_argument("--select", action="store_true")
    parser.add_argument("--validate-only", action="store_true")
    args = parser.parse_args()
    try:
        root = args.repository.resolve()
        registration(root)
        if args.validate_only:
            return 0
        if args.select:
            lake, lean = select_binaries(root)
            print(json.dumps({"lake": lake, "lean": lean}))
        else:
            if not args.lean:
                raise ValueError("--lean is required")
            print(runtime_hash(root, args.lean))
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f"lean-report-runtime: Meta/ReportProducers/lean-report.json: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
