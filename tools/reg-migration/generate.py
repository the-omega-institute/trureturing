#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

if __package__ in {None, ""}:
    import importlib.util

    package_dir = Path(__file__).resolve().parent
    spec = importlib.util.spec_from_file_location(
        "reg_migration", package_dir / "__init__.py", submodule_search_locations=[str(package_dir)])
    assert spec and spec.loader
    package = importlib.util.module_from_spec(spec)
    sys.modules["reg_migration"] = package
    spec.loader.exec_module(package)
    from reg_migration.generator import Generator, GeneratorFailure
else:
    from .generator import Generator, GeneratorFailure


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Plan and render contracts from compiled raw inputs and Lean parser spans")
    sub = parser.add_subparsers(dest="command", required=True)
    plan = sub.add_parser("plan")
    plan.add_argument("--repo", type=Path, required=True)
    plan.add_argument("--inputs", type=Path, required=True)
    plan.add_argument("--syntax", type=Path, help="Lean parser output (or embed files in --inputs)")
    plan.add_argument("--mapping", type=Path, required=True)
    plan.add_argument("--output", type=Path, required=True)
    plan.add_argument("--input-sha256")
    plan.add_argument("--apply", type=Path, help="write to an explicit target tree after validation")
    args = parser.parse_args(argv)
    generator = Generator(args.repo, args.inputs, args.mapping, args.syntax)
    result = generator.plan(args.input_sha256)
    summary = {"audit": result.audit, "failures": [failure.as_dict() for failure in result.failures]}
    print(json.dumps(summary, sort_keys=True, ensure_ascii=False))
    if result.failures:
        return 1
    try:
        generator.write(result, args.output / "rendered", args.apply)
    except (GeneratorFailure, OSError) as error:
        print(json.dumps({"failures": [{"code": "write_preflight_failed", "detail": str(error)}]}, sort_keys=True))
        return 1
    args.output.mkdir(parents=True, exist_ok=True)
    path = args.output / "audit.json"
    data = (json.dumps(summary, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")
    if not path.exists() or path.read_bytes() != data:
        temporary = path.with_name(path.name + ".tmp")
        temporary.write_bytes(data)
        temporary.replace(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
