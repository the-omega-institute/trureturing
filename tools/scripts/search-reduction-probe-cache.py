#!/usr/bin/env python3
"""Authenticated probe reuse; Lean rechecks certificates and the classifier.

The stat memo only avoids rehashing unchanged files on this local filesystem.
Its entries and probe records are authenticated by a separate per-user key.
The cache is an optimization, never an alternative verdict producer.
"""
import hashlib
import hmac
import json
import os
from pathlib import Path
import secrets
import subprocess
import sys
import tempfile
import time


VERSION = "probe-cache-v2"


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def digest(path):
    result = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            result.update(chunk)
    return result.hexdigest()


def sign(value, key):
    return hmac.new(key, canonical(value), hashlib.sha256).hexdigest()


def read_signed(path, key):
    value = json.loads(path.read_bytes())
    if set(value) != {"data", "mac"} or not hmac.compare_digest(
            value["mac"], sign(value["data"], key)):
        raise ValueError("authentication failed")
    return value["data"]


def write_signed(path, value, key):
    temporary = path.with_name(path.name + ".tmp-" + secrets.token_hex(8))
    temporary.write_bytes(canonical({"data": value, "mac": sign(value, key)}))
    temporary.replace(path)


def auth_key():
    # Separate from the cache record directory, including for caller-owned caches.
    directory = Path.home() / ".cache/trureturing/search-reduction"
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    path = directory / "probe-auth-key"
    try:
        with path.open("xb") as stream:
            os.chmod(path, 0o600)
            stream.write(secrets.token_bytes(32))
    except FileExistsError:
        pass
    key = path.read_bytes()
    if len(key) != 32 or path.stat().st_mode & 0o077:
        raise ValueError("invalid probe authentication key")
    return key


def files_under(path):
    if path.is_file():
        yield path
    elif path.is_dir():
        for directory, names, files in os.walk(path):
            names.sort()
            for name in sorted(files):
                candidate = Path(directory) / name
                if candidate.is_file():
                    yield candidate


def tree_fingerprint(path, memo, updated):
    result = hashlib.sha256()
    result.update(str(path.absolute()).encode())
    result.update(b"directory" if path.is_dir() else b"file")
    for candidate in files_under(path):
        stat = candidate.stat()
        stamp = [stat.st_dev, stat.st_ino, stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns]
        name = str(candidate.absolute())
        prior = memo.get(name)
        checksum = prior[1] if prior and prior[0] == stamp else digest(candidate)
        updated[name] = [stamp, checksum]
        result.update(canonical([str(candidate.relative_to(path)) if candidate != path else "", checksum]))
    if not path.exists():
        result.update(b"missing")
    return result.hexdigest()


def input_identity(request, root, key):
    memo_path = root / "fingerprints.json"
    try:
        memo = read_signed(memo_path, key)
    except (OSError, ValueError, TypeError, KeyError):
        memo = {}
    updated = {}
    # Hash source and the actual compiled judge/dependency closure. The research
    # library and production index are fingerprinted in their entirety.
    inputs = [Path(request), Path("Makefile"), Path("lean-toolchain"), Path("lake-manifest.json"),
              Path("tools/lean-inspector-reg/lakefile.lean"),
              Path("tools/lean-inspector"),
              Path("tools/lean-inspector-interface"), Path("Reg"),
              Path(".lake/build/lean-inspector/reg/lib"),
              Path(".lake/build/lean-inspector/interface/lib"),
              Path(".lake/build/lean-inspector/producer/lib"),
              Path(".lake/build/reg/lib/lean"),
              Path(".lake/packages/mathlib/lake-manifest.json"),
              Path(".lake/packages/mathlib/Mathlib.lean"),
              Path("tools/scripts/search-reduction-runner.sh"), Path(__file__)]
    for variable in ["SEARCH_REDUCTION_INDEX", "SEARCH_REDUCTION_SOURCE_LIBRARY"]:
        if os.environ.get(variable):
            inputs.append(Path(os.environ[variable]))
    if not os.environ.get("SEARCH_REDUCTION_INDEX"):
        inputs += [Path("build/lean-inspector/lookup-index"),
                   Path("build/lean-inspector/search-reduction-test-index")]
    fingerprint = [(str(path), tree_fingerprint(path, memo, updated)) for path in inputs]
    write_signed(memo_path, updated, key)
    # Profiling/telemetry paths do not change mathematical inputs. Unknown
    # SEARCH_REDUCTION options are conservative cache invalidators.
    operational = {"SEARCH_REDUCTION_REQUESTS", "SEARCH_REDUCTION_PROFILE",
                   "SEARCH_REDUCTION_TELEMETRY", "SEARCH_REDUCTION_WORKERS",
                   "SEARCH_REDUCTION_RESUME", "SEARCH_REDUCTION_QUERY_CACHE",
                   "SEARCH_REDUCTION_PROBE_CACHE", "SEARCH_REDUCTION_PROBE_READ",
                   "SEARCH_REDUCTION_PROBE_WRITE", "SEARCH_REDUCTION_PROBE_ID"}
    environment = {k: v for k, v in os.environ.items()
                   if k.startswith("SEARCH_REDUCTION_") and k not in operational}
    return hashlib.sha256(canonical([VERSION, fingerprint, environment,
                                    os.environ.get("LEAN_PATH"),
                                    os.environ.get("LEAN_SYSROOT")])).hexdigest()


def record_files(directory):
    return {str(path.relative_to(directory)): digest(path)
            for path in files_under(directory)
            if path.name != "manifest.json"}


def valid_record(directory, identity, key):
    manifest = read_signed(directory / "manifest.json", key)
    if manifest["identity"] != identity:
        raise ValueError("input identity mismatch")
    actual = record_files(directory)
    if not actual or actual != manifest["files"]:
        raise ValueError("record bytes changed")
    if not any(name.endswith(".pickle") for name in actual):
        raise ValueError("no typed probe record")


def emit(message):
    print(message, flush=True)


def run(command):
    request = os.environ["SEARCH_REDUCTION_REQUESTS"]
    if os.environ.get("SEARCH_REDUCTION_PROBE_CACHE") == "0":
        return subprocess.call(command)
    root = Path(os.environ.get("SEARCH_REDUCTION_PROBE_CACHE",
                              "build/lean-inspector/search-reduction-probe-cache"))
    root.mkdir(parents=True, exist_ok=True)
    key = auth_key()
    started = time.monotonic()
    identity = input_identity(request, root, key)
    emit(f"PROBE_CACHE_INPUT identity={identity} seconds={time.monotonic()-started:.6f}")
    directory = root / identity
    env = dict(os.environ)
    env.pop("SEARCH_REDUCTION_PROBE_READ", None)
    env.pop("SEARCH_REDUCTION_PROBE_WRITE", None)
    env["SEARCH_REDUCTION_PROBE_ID"] = identity
    # Candidate checkpoints and local query answers also inherit the full
    # semantic identity when the whole probe has to follow the cold path.
    env["SEARCH_REDUCTION_RESUME_INPUTS"] = identity
    if directory.exists():
        try:
            valid_record(directory, identity, key)
        except (OSError, ValueError, TypeError, KeyError) as error:
            emit(f"PROBE_CACHE_REJECTED reason={error}")
        else:
            env["SEARCH_REDUCTION_PROBE_READ"] = str(directory.absolute())
            result = subprocess.call(command, env=env)
            if result == 0:
                return 0
            if result == 75:
                return result
            emit(f"PROBE_CACHE_REJECTED kernel_exit={result}; recomputing cold")
            env.pop("SEARCH_REDUCTION_PROBE_READ", None)
    stage = Path(tempfile.mkdtemp(prefix="pending-", dir=root))
    env["SEARCH_REDUCTION_PROBE_WRITE"] = str(stage.absolute())
    result = subprocess.call(command, env=env)
    if result != 0:
        return result
    files = record_files(stage)
    if any(name.endswith(".pickle") for name in files):
        # Refuse to cache a result if any input changed during the computation.
        if input_identity(request, root, key) != identity:
            emit("PROBE_CACHE_NOT_STORED reason=inputs_changed_during_run")
            return 0
        write_signed(stage / "manifest.json", {"identity": identity, "files": files}, key)
        if directory.exists():
            directory.rename(root / (identity + ".rejected-" + secrets.token_hex(8)))
        stage.rename(directory)
        emit(f"PROBE_CACHE_STORED identity={identity} files={len(files)}")
    return 0


if __name__ == "__main__":
    if len(sys.argv) < 2:
        raise SystemExit("expected a Lean command")
    raise SystemExit(run(sys.argv[1:]))
