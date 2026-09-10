"""Actions snapshots are optional, integrity-checked inputs to normal producers."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import sys
import tempfile

from lean_cache import actions_keys, binary_platform
from lean_cache_release import cache_guard, sha

LAYERS = ("dependency", "project", "report")
ALL_LAYERS = (*LAYERS, "judge")


def output(values, destination="GITHUB_OUTPUT"):
    text = "".join(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n" for key, value in values.items())
    if os.environ.get(destination):
        try:
            with open(os.environ[destination], "a", encoding="utf-8") as stream:
                stream.write(text)
        except OSError as error:
            receipt("all", "output-unavailable", reason=str(error))
    print(text, end="")


def receipt(layer, status, **fields):
    print("LEAN_ACTIONS_CACHE " + json.dumps({"layer": layer, "status": status, **fields}, sort_keys=True))


def files(directory):
    result = []
    for path in sorted(directory.rglob("*")):
        if path.is_symlink():
            raise ValueError("cache has a symlink")
        if path.is_file():
            result.append({"path": path.relative_to(directory).as_posix(), "sha256": sha(path), "mode": path.stat().st_mode & 0o777})
    if not result:
        raise ValueError("cache has no files")
    return result


def snapshot(root, keys, layers=LAYERS):
    for layer in layers:
        ready = False
        try:
            if not keys["judge_save_allowed" if layer == "judge" else "save_allowed"]:
                receipt(layer, "save-disabled")
                continue
            spec = keys[layer]
            target = root / spec["path"]
            target.parent.mkdir(parents=True, exist_ok=True)
            with tempfile.TemporaryDirectory(prefix=".snapshot-", dir=target.parent) as temporary:
                staged = pathlib.Path(temporary)
                with cache_guard(root, shared=True):
                    if layer == "judge":
                        sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "report"))
                        from dotnet_producer import stage_seed
                        stage_seed(root, staged / "data")
                    else:
                        shutil.copytree(root / spec["target"], staged / "data", symlinks=True)
                manifest = {"schema": "lean-actions-seed-v1", "partition": keys["partition"], "layer": layer,
                            "key": spec["key"], "files": files(staged / "data")}
                (staged / "manifest.json").write_text(json.dumps(manifest, sort_keys=True) + "\n")
                if target.exists():
                    shutil.rmtree(target)
                staged.rename(target)
                ready = True
                receipt(layer, "snapshot", key=spec["key"])
        except (OSError, ValueError, TypeError) as error:
            receipt(layer, "save-failed", reason=str(error))
        finally:
            output({layer + "_ready": ready})


def restore(root, keys, matched, layers=LAYERS):
    project_seeded = False
    for layer in layers:
        try:
            spec, key = keys[layer], matched[layer]
            if not key:
                receipt(layer, "miss", reason="Actions supplied no cache")
                continue
            if not re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", key):
                raise ValueError("Actions seed is outside the selected partition")
            cached = root / spec["path"]
            manifest = json.loads((cached / "manifest.json").read_text())
            if (not isinstance(manifest, dict) or manifest.get("schema") != "lean-actions-seed-v1" or manifest.get("partition") != keys["partition"]
                    or manifest.get("layer") != layer or manifest.get("key") != key
                    or manifest.get("files") != files(cached / "data")):
                raise ValueError("Actions seed identity or material integrity mismatch")
            if layer == "report":
                sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "lean-inspector"))
                from report_cache import seed_valid
                reports = list((cached / "data" / keys["partition"]).glob("*/raw-lean-report.json"))
                if not reports or not any(seed_valid(report, keys["partition"]) for report in reports):
                    raise ValueError("Actions report cache has no valid complete seed")
            target = root / spec["target"]
            with cache_guard(root):
                target.parent.mkdir(parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(prefix=".actions-", dir=target.parent) as temporary:
                    staged = pathlib.Path(temporary) / "data"
                    shutil.copytree(cached / "data", staged)
                    if target.exists():
                        shutil.rmtree(target)
                    staged.rename(target)
            project_seeded |= layer == "project"
            receipt(layer, "restored", key=key, partition=keys["partition"])
        except (OSError, ValueError, TypeError, KeyError) as error:
            receipt(layer, "miss", reason=str(error))
    # Release supplies the project layer. Dependency-only and report-only hits
    # must not suppress a missing project layer's same-partition fallback.
    if "project" in layers:
        output({"STRATALINT_ACTIONS_CACHE_SEEDED": "1" if project_seeded else "0"}, "GITHUB_ENV")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("keys", "restore", "snapshot"))
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    parser.add_argument("--layers", choices=ALL_LAYERS, nargs="+", default=LAYERS)
    for layer in ALL_LAYERS:
        parser.add_argument("--" + layer + "-key", default="")
    args = parser.parse_args()
    try:
        keys = actions_keys(args.repository)
        if args.command == "keys":
            values = {}
            for layer in args.layers:
                values.update({layer + "_" + key: value for key, value in keys[layer].items()})
            system, arch = binary_platform()
            toolchain = hashlib.sha256((args.repository / "lean-toolchain").read_bytes()).hexdigest()
            values["elan_key"] = f"elan-v1-{system}-{arch}-{toolchain}"
            output(values)
        elif args.command == "restore":
            restore(args.repository, keys, {layer: getattr(args, layer + "_key") for layer in args.layers}, args.layers)
        else:
            snapshot(args.repository, keys, args.layers)
        return 0
    except (OSError, ValueError, TypeError, KeyError) as error:
        receipt("all", "unavailable", reason=str(error))
        if args.command == "restore" and "project" in args.layers:
            output({"STRATALINT_ACTIONS_CACHE_SEEDED": "0"}, "GITHUB_ENV")
        return 0


if __name__ == "__main__":
    raise SystemExit(main())
