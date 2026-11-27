"""Reuse successful Omega checks on identical compiled inputs from a trusted run."""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import platform
import tempfile

SCHEMA = "omega-audit-result-v1"
ROOT = Path(__file__).resolve().parents[2]
RULES = ("lean-toolchain", "lakefile.toml", "lake-manifest.json", "Reg/lakefile.toml",
         "Reg/lake-manifest.json", "src/OmegaChecks/check.py", "src/OmegaChecks/scope.py",
         "src/OmegaChecks/strict_lake.py", "src/OmegaChecks/portable.py", "src/OmegaChecks/audit_cache.py")
KINDS = {"strict-kernel", "common-interface", "official-interface"}


def encoded(value):
    return json.dumps(value, separators=(",", ":"), sort_keys=True).encode()


def atomic_write(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=path.parent) as temp:
        staged = Path(temp) / "result"
        staged.write_bytes(data)
        staged.replace(path)


def stamp(st):
    return [st.st_dev, st.st_ino, st.st_size, st.st_ctime_ns, st.st_mtime_ns]


def inputs(manifest):
    named = [(name, Path(path)) for name, path in manifest["files"]]
    named.extend((name, ROOT / name) for name in RULES)
    for sources in ("OmegaChecks", "OmegaBuild"):
        for source in (ROOT / "src" / sources).rglob("*.lean"):
            named.append((str(source.relative_to(ROOT)), source))
    if manifest["kind"] not in KINDS or not named or len({name for name, _ in named}) != len(named):
        raise ValueError("unknown check or duplicate audit input")
    return sorted(named)


def lookup(directory, path, manifest):
    named = inputs(manifest)
    dependencies = []
    stamps = []
    for name, file in named:
        with file.open("rb") as stream:
            initial = stamp(os.fstat(stream.fileno()))
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
            if initial != stamp(os.fstat(stream.fileno())):
                raise ValueError(f"audit input changed while hashing: {name}")
        stamps.append(initial)
        dependencies.append((name, digest))
    identity = [SCHEMA, manifest["kind"], manifest["arguments"], bool(manifest["report"]),
                platform.system(), platform.machine(), dependencies]
    key = hashlib.sha256(encoded(identity)).hexdigest()
    atomic_write(path.with_suffix(".lookup"), encoded([key, stamps]))
    record_path = directory / "restored" / (key + ".json")
    if not record_path.is_file():
        print(f"Omega audit miss {manifest['kind']} {key}", flush=True)
        return False
    record = json.loads(record_path.read_bytes())
    if (not isinstance(record, dict) or set(record) != {"schema", "key", "kind", "report", "report_sha256"}
            or (record["schema"], record["key"], record["kind"]) != (SCHEMA, key, manifest["kind"])):
        raise ValueError("invalid Omega audit record")
    if manifest["report"]:
        raw = base64.b64decode(record["report"], validate=True)
        if hashlib.sha256(raw).hexdigest() != record["report_sha256"]:
            raise ValueError("invalid cached axiom report digest")
        atomic_write(Path(manifest["report"]), raw)
    elif record["report"] is not None or record["report_sha256"] is not None:
        raise ValueError("unexpected cached axiom report")
    print(f"Omega audit hit {manifest['kind']} {key}", flush=True)
    return True


def store(directory, path, manifest):
    key, before = json.loads(path.with_suffix(".lookup").read_bytes())
    if before != [stamp(file.stat()) for _, file in inputs(manifest)]:
        raise ValueError("audit inputs changed during verification")
    raw = Path(manifest["report"]).read_bytes() if manifest["report"] else None
    record = {"schema": SCHEMA, "key": key, "kind": manifest["kind"],
              "report": base64.b64encode(raw).decode() if raw is not None else None,
              "report_sha256": hashlib.sha256(raw).hexdigest() if raw is not None else None}
    atomic_write(directory / "produced" / (key + ".json"), encoded(record))
    print(f"Omega audit recorded {manifest['kind']} {key}", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("lookup", "store"))
    parser.add_argument("manifest", type=Path)
    args = parser.parse_args()
    try:
        cache = Path(os.environ["OMEGA_AUDIT_CACHE"])
        manifest = json.loads(args.manifest.read_bytes())
        if args.operation == "store":
            store(cache, args.manifest, manifest)
        elif not lookup(cache, args.manifest, manifest):
            raise SystemExit(1)
    except (OSError, KeyError, TypeError, ValueError) as error:
        print(f"Omega audit cache unavailable: {error}", flush=True)
        raise SystemExit(1)
