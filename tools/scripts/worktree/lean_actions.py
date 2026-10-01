"""Transport the independent Lean dependency and project cache layers."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import tempfile

from cache_material import sha
from lean_cache import binary_platform, partition_path, resolved_mathlib

LAYERS = ("dependency", "project")


class CachePathRegistrationError(ValueError):
    pass


def native_archive_paths(root: pathlib.Path, layers):
    selected = set(layers) & set(LAYERS)
    if not selected:
        return {}
    manifest = "Meta/ci-cache-paths.json"

    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError("duplicate field: " + key)
            result[key] = value
        return result

    try:
        import tomllib
        filemap = tomllib.loads((root / "Meta/FILEMAP.toml").read_text())
        rows = [row for row in filemap.get("files", []) if row.get("pattern") == manifest]
        if len(rows) != 1:
            raise ValueError("manifest must have one literal FILEMAP entry")
        registration = json.loads((root / manifest).read_text(), object_pairs_hook=unique_object)
        if (not isinstance(registration, dict) or set(registration) != {"schema_version", "layers"}
                or registration["schema_version"] != 1 or not isinstance(registration["layers"], dict)
                or not set(registration["layers"]).issubset(LAYERS)):
            raise ValueError("invalid schema or layer")
        roots = {"dependency": ".lake/packages", "project": ".lake/build"}
        result = {}
        for layer in sorted(selected):
            paths = registration["layers"].get(layer)
            if not isinstance(paths, list) or not paths:
                raise ValueError("missing paths for " + layer)
            for path in paths:
                if (not isinstance(path, str) or not re.fullmatch(r"[A-Za-z0-9_./*\-]+", path)
                        or any(part in ("", ".", "..") for part in path.split("/"))
                        or not (path == roots[layer] or path.startswith(roots[layer] + "/"))):
                    raise ValueError("invalid path for " + layer + ": " + repr(path))
            if len(set(paths)) != len(paths):
                raise ValueError("duplicate paths for " + layer)
            result[layer] = sorted(paths)
        return result
    except (OSError, ValueError, TypeError, AttributeError) as error:
        raise CachePathRegistrationError(f"cache path registration {manifest}: {error}") from error


def output_archive_paths(layer, paths):
    key = layer + "_archive_path"
    value = "\n".join(paths)
    delimiter = "STRATALINT_" + hashlib.sha256(value.encode()).hexdigest()
    if os.environ.get("GITHUB_OUTPUT"):
        with open(os.environ["GITHUB_OUTPUT"], "a", encoding="utf-8") as stream:
            stream.write(f"{key}<<{delimiter}\n{value}\n{delimiter}\n")
    print(key + "=" + json.dumps(paths, separators=(",", ":")))


def actions_keys(root: pathlib.Path) -> dict:
    revision = resolved_mathlib(root)
    system, machine = binary_platform()
    run = os.environ.get("GITHUB_RUN_ID", "")
    attempt = os.environ.get("GITHUB_RUN_ATTEMPT", "")
    if not re.fullmatch(r"[0-9]+", run) or not re.fullmatch(r"[0-9]+", attempt):
        raise ValueError("snapshot keys require GITHUB_RUN_ID and GITHUB_RUN_ATTEMPT")
    event, ref = os.environ.get("GITHUB_EVENT_NAME"), os.environ.get("GITHUB_REF", "")
    push_writer = event == "push" and (ref == "refs/heads/dev" or ref.startswith("refs/heads/integration-"))
    pr_writer = event == "pull_request" and re.fullmatch(r"refs/pull/[1-9][0-9]*/merge", ref) is not None
    writer_allowed = (push_writer or pr_writer) and os.environ.get("STRATALINT_CACHE_WRITES") == "true"
    result = {
        "mathlib_revision": revision, "os": system, "arch": machine,
        "partition": partition_path(root),
        "save_allowed": writer_allowed and os.environ.get("STRATALINT_CHECK_SUCCEEDED") == "true",
        "release_prefix": f"lean-cache-v2-{revision}-{system}-{machine}-",
    }
    for layer in LAYERS:
        prefix = f"lean-{layer}-v4-{revision}-{system}-{machine}-"
        result[layer] = {
            "restore_prefix": prefix, "key": f"{prefix}{run}-{attempt}",
            "path": ".lake/packages" if layer == "dependency" else ".lake/build",
        }
    return result


def output(values, destination="GITHUB_OUTPUT"):
    text = "".join(f"{key}={str(value).lower() if isinstance(value, bool) else value}\n" for key, value in values.items())
    if os.environ.get(destination):
        with open(os.environ[destination], "a", encoding="utf-8") as stream:
            stream.write(text)
    print(text, end="")


def receipt(layer, status, **fields):
    print("LEAN_ACTIONS_CACHE " + json.dumps({"layer": layer, "status": status, **fields}, sort_keys=True), flush=True)


def dependency_inputs(root: pathlib.Path):
    inputs = {}
    for relative in ("lake-manifest.json", "lean-toolchain", "lakefile.toml"):
        path = root / relative
        if path.is_symlink() or not path.is_file():
            raise ValueError("dependency save input is unavailable: " + relative)
        inputs[relative] = sha(path)
    optional = root / "lakefile.lean"
    if optional.exists():
        if optional.is_symlink() or not optional.is_file():
            raise ValueError("dependency save input is unavailable: lakefile.lean")
        inputs["lakefile.lean"] = sha(optional)
    declaration = json.loads((root / "lean-report-inputs.json").read_text())
    names = declaration["report_execution"]["environment"]
    if (not isinstance(names, list) or any(not isinstance(name, str) or not name for name in names)
            or len(set(names)) != len(names)):
        raise ValueError("dependency save environment registration is invalid")
    value = {"files": inputs, "environment": {name: os.environ.get(name) for name in names}}
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def dependency_restored_record(root):
    return root / "build/lean-cache/dependency-restored.json"


def write_small_record(path: pathlib.Path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, name = tempfile.mkstemp(prefix=".actions-inputs-", dir=path.parent)
    temporary = pathlib.Path(name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            json.dump(value, stream)
            stream.write("\n")
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def stamp_restored_dependency(root, keys):
    write_small_record(root / ".lake/.stratalint-lean-cache-stamp.json", {
        "schema": "stratalint-lean-cache-v2", "mathlib_revision": keys["mathlib_revision"],
        "os": keys["os"], "arch": keys["arch"]})


def restore_native(root, keys, layer, key, outcome):
    spec = keys[layer]
    record = dependency_restored_record(root)
    if layer == "dependency":
        record.unlink(missing_ok=True)
    if outcome in ("", "skipped"):
        receipt(layer, "miss", reason="Actions supplied no cache")
        return False
    target = root / spec["path"]
    try:
        if outcome != "success" or not key:
            raise ValueError("Actions restore did not succeed or supplied no matched cache")
        if not re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", key):
            raise ValueError("Actions seed is outside the selected partition")
        if target.is_symlink() or not target.is_dir():
            raise ValueError("native Actions cache directory is unavailable")
        if layer == "dependency":
            stamp_restored_dependency(root, keys)
            try:
                previous = json.loads((target / ".stratalint-actions-inputs.json").read_text())
                digest = previous["inputs_sha256"]
                if isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest):
                    write_small_record(record, {"snapshot_key": spec["key"], "matched_key": key, "inputs_sha256": digest})
            except (OSError, ValueError, TypeError, KeyError):
                pass
        receipt(layer, "restored", key=key, partition=keys["partition"], transport="actions-native")
        return True
    except (OSError, ValueError, TypeError) as error:
        if target.is_symlink() or target.is_file():
            target.unlink()
        elif target.exists():
            shutil.rmtree(target)
        receipt(layer, "miss", reason=str(error))
        return False


def restore(root, keys, matched, layers=LAYERS, *, outcomes=None):
    seeded = False
    for layer in layers:
        accepted = restore_native(root, keys, layer, matched.get(layer, ""), (outcomes or {}).get(layer, "success"))
        seeded |= layer == "project" and accepted
    if "project" in layers:
        output({"STRATALINT_ACTIONS_CACHE_SEEDED": "1" if seeded else "0"}, "GITHUB_ENV")


def snapshot(root, keys, layers=LAYERS):
    for layer in layers:
        if layer not in LAYERS:
            continue
        ready = False
        try:
            if not keys["save_allowed"]:
                receipt(layer, "save-disabled")
                output({layer + "_ready": False})
                continue
            target = root / keys[layer]["path"]
            if target.is_symlink() or not target.is_dir():
                raise ValueError("native cache directory is unavailable: " + keys[layer]["path"])
            if layer == "dependency":
                fingerprint = dependency_inputs(root)
                try:
                    restored = json.loads(dependency_restored_record(root).read_text())
                    spec = keys[layer]
                    if (restored.get("snapshot_key") == spec["key"]
                            and re.fullmatch(re.escape(spec["restore_prefix"]) + r"[0-9]+-[0-9]+", restored.get("matched_key", ""))
                            and restored.get("inputs_sha256") == fingerprint):
                        receipt(layer, "save-disabled", reason="retained-restored-dependency")
                        output({layer + "_ready": False})
                        continue
                except (OSError, ValueError, TypeError, AttributeError):
                    pass
                write_small_record(target / ".stratalint-actions-inputs.json", {"inputs_sha256": fingerprint})
            ready = True
            receipt(layer, "snapshot", key=keys[layer]["key"])
        except (OSError, ValueError, TypeError) as error:
            receipt(layer, "save-failed", reason=str(error))
        output({layer + "_ready": ready})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("command", choices=("keys", "restore", "snapshot"))
    parser.add_argument("--repository", required=True, type=pathlib.Path)
    parser.add_argument("--layers", choices=LAYERS, nargs="+")
    for layer in LAYERS:
        parser.add_argument("--" + layer + "-key", default="")
        parser.add_argument("--" + layer + "-outcome", default="", choices=("", "success", "failure", "cancelled", "skipped"))
    args = parser.parse_args()
    args.layers = list(LAYERS) if args.layers is None else args.layers
    try:
        root = args.repository.resolve()
        keys = actions_keys(root)
        if args.command == "keys":
            archive_paths = native_archive_paths(root, args.layers)
            values = {key: keys[key] for key in ("mathlib_revision", "os", "arch", "partition", "save_allowed", "release_prefix")}
            system, arch = binary_platform()
            values["elan_key"] = f"elan-v1-{system}-{arch}-{hashlib.sha256((root / 'lean-toolchain').read_bytes()).hexdigest()}"
            for layer in args.layers:
                values.update({layer + "_" + key: value for key, value in keys[layer].items()})
            output(values)
            for layer, paths in archive_paths.items():
                output_archive_paths(layer, paths)
        elif args.command == "restore":
            restore(root, keys, {layer: getattr(args, layer + "_key") for layer in args.layers}, args.layers,
                    outcomes={layer: getattr(args, layer + "_outcome") for layer in args.layers})
        else:
            snapshot(root, keys, args.layers)
        return 0
    except (OSError, ValueError, TypeError, KeyError, CachePathRegistrationError) as error:
        print("CI_INPUT_FAILED " + str(error), file=os.sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
