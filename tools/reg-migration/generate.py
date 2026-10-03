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
        "reg_migration", package_dir / "__init__.py",
        submodule_search_locations=[str(package_dir)])
    assert spec and spec.loader
    package = importlib.util.module_from_spec(spec)
    sys.modules["reg_migration"] = package
    spec.loader.exec_module(package)
    from reg_migration.generator import Generator  # type: ignore
else:
    from .generator import Generator


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Plan/render fixed registration declarations")
    sub = parser.add_subparsers(dest="command", required=True)
    plan = sub.add_parser("plan")
    plan.add_argument("--repo", type=Path, required=True)
    plan.add_argument("--report", type=Path, required=True)
    plan.add_argument("--mapping", type=Path, required=True)
    plan.add_argument("--inputs", type=Path)
    plan.add_argument("--root-inventory", type=Path)
    plan.add_argument("--output", type=Path, required=True)
    plan.add_argument("--input-sha256")
    plan.add_argument("--apply", type=Path, help="write to an explicit target tree after validation")
    args = parser.parse_args(argv)
    generator = Generator(args.repo, args.report, args.mapping, args.inputs, args.root_inventory)
    result = generator.plan(args.input_sha256)
    args.output.mkdir(parents=True, exist_ok=True)
    summary = {"audit": result.audit, "failures": [failure.as_dict() for failure in result.failures]}
    (args.output / "audit.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, sort_keys=True))
    if result.failures:
        return 1
    generator.write(result, args.output / "rendered", args.apply)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
