"""Hash only runtime material explicitly registered by the report producer."""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
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
        # Only the registered filename glob expands; imports and neighboring files
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


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repository", type=pathlib.Path, required=True)
    parser.add_argument("--lake", required=True)
    args = parser.parse_args()
    try:
        _, manifest = load_scope(args.repository.resolve(), "lean-report")
        runtime = runtime_registration(manifest)
        # Resolve the installation actually selected by Lake; this does not select
        # dependencies. The manifest alone selects material within this root.
        prefix = subprocess.run([args.lake, "env", "lean", "--print-prefix"],
            cwd=args.repository, check=True, capture_output=True, text=True).stdout.strip()
        if not prefix or not pathlib.Path(prefix).is_absolute():
            raise ValueError(f"invalid declared Lean installation prefix: {prefix!r}")
        programs = declared_lean_material(pathlib.Path(prefix).resolve(), runtime["lean"])
        for material in runtime["python"]:
            executable = pathlib.Path(sys.executable).resolve()
            if not executable.is_file():
                raise ValueError(f"required runtime.python {material} is absent: {executable}")
            programs["python:" + material] = file_sha(executable)
        identity = {"schema": "lean-report-runtime-v2", "programs": programs}
        print(hashlib.sha256(json.dumps(identity, sort_keys=True, separators=(",", ":")).encode()).hexdigest())
        return 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.CalledProcessError) as error:
        print(f"lean-report-runtime: Meta/ReportProducers/lean-report.json: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
