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
import stat
import subprocess
import sys
import tempfile
import time


VERSION = "probe-cache-v9"
# Explicit procedure identity, checked against Lean's configuration by tests.
R_VERSION = "R_lookup/v19/obvious-v1/lazy-interval/scope-B_T/primary-index-only/candidate-200000/preparation-8000000/G-340000000/memo-target-basis-R-v3/N-memo-2000000/checkpoint-v6/views-kappa/isolation-independent-units/analytic-cut-k2/200000"


def wall_phase(label):
    """Outer-process timing, kept separate from Lean's monotonic clock."""
    path = os.environ.get("SEARCH_REDUCTION_PROFILE")
    if path:
        # Python 3.9 on Darwin gives monotonic_ns a process-local epoch.
        # CLOCK_UPTIME_RAW also matches Lean's mach_absolute_time clock.
        clock = time.CLOCK_UPTIME_RAW if sys.platform == "darwin" else time.CLOCK_MONOTONIC
        with open(path, "a") as stream:
            stream.write(f"WALL {time.clock_gettime_ns(clock)} {label}\n")


def native_run(command):
    wall_phase("native/environment-start")
    native_env = json.loads(subprocess.check_output([
        "lake", "-d", "tools/lean-inspector-reg", "env", "python3", "-c",
        "import json, os; print(json.dumps(dict(os.environ)))"], text=True))
    wall_phase("native/environment-end")
    os.execvpe(command[0], command, native_env)


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


def fingerprint_inventory(path, root_stat):
    """Read each file's full change stamp once, without a second is_file stat."""
    if stat.S_ISREG(root_stat.st_mode):
        yield path, root_stat
    elif stat.S_ISDIR(root_stat.st_mode):
        for directory, names, files in os.walk(path):
            names.sort()
            for name in sorted(files):
                candidate = os.path.join(directory, name)
                info = os.stat(candidate)
                if stat.S_ISREG(info.st_mode):
                    yield candidate, info


def tree_fingerprint(path, memo, updated, counts=None, *, tree_memo=None,
                     trees=None, file_only=False):
    base = os.path.abspath(path)
    result = hashlib.sha256()
    result.update(base.encode())
    try:
        root_stat = os.stat(base)
    except FileNotFoundError:
        result.update(b"filemissing")
        return result.hexdigest()
    if file_only and stat.S_ISDIR(root_stat.st_mode):
        raise ValueError("invalid mathematical input file")
    result.update(b"directory" if stat.S_ISDIR(root_stat.st_mode) else b"file")
    members = []
    checksums = []
    unchanged = True
    for name, info in fingerprint_inventory(base, root_stat):
        stamp = [info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns]
        prior = memo.get(name)
        reused = prior and prior[0] == stamp
        checksum = prior[1] if reused else digest(name)
        unchanged = unchanged and bool(reused)
        if counts is not None:
            counts["checked"] += 1
            counts["hashed"] += not bool(reused)
        updated[name] = [stamp, checksum]
        members.append(name)
        checksums.append(checksum)
    # The signed aggregate saves per-member JSON encoding and hash updates,
    # after the full current population and every change stamp are checked.
    prior_tree = (tree_memo or {}).get(base)
    if (unchanged and prior_tree and prior_tree["members"] == members
            and prior_tree.get("checksums") == checksums):
        checksum = prior_tree["digest"]
    else:
        for name in members:
            checksum = updated[name][1]
            result.update(canonical([name[len(base) + 1:] if name != base else "", checksum]))
        checksum = result.hexdigest()
    if trees is not None:
        trees[base] = {"members": members, "checksums": checksums, "digest": checksum}
    return checksum


def input_identity(request, root, key):
    wall_phase("fingerprint/memo-read-start")
    memo_path = root / "fingerprints.json"
    try:
        memo = read_signed(memo_path, key)
    except (OSError, ValueError, TypeError, KeyError):
        memo = {}
    tree_path = root / "fingerprint-trees.json"
    try:
        tree_memo = read_signed(tree_path, key)
    except (OSError, ValueError, TypeError, KeyError):
        tree_memo = {}
    wall_phase("fingerprint/memo-read-end")
    updated = {}
    trees = {}
    # These are request/data populations and explicit dependency pins. Judge
    # source, build configuration and compiled programs are not reuse inputs.
    # Lean additionally compares current target declarations and their complete
    # mathematical dependency closure before accepting a typed probe record.
    inputs = [Path(request), Path("lean-toolchain"), Path("lake-manifest.json"),
              Path("D5"), Path("Golden/Frozen/state"),
              Path(".lake/packages/mathlib/lake-manifest.json"),
              Path(".lake/packages/mathlib/Mathlib.lean")]
    for variable in ["SEARCH_REDUCTION_INDEX", "SEARCH_REDUCTION_SOURCE_LIBRARY"]:
        if os.environ.get(variable):
            inputs.append(Path(os.environ[variable]))
    if not os.environ.get("SEARCH_REDUCTION_INDEX"):
        inputs += [Path("build/lean-inspector/lookup-index"),
                   Path("build/lean-inspector/search-reduction-test-index")]
    fingerprint = []
    counts = {"checked": 0, "hashed": 0}
    for path in inputs:
        wall_phase(f"fingerprint/tree-start path={path}")
        fingerprint.append((str(path), tree_fingerprint(
            path, memo, updated, counts, tree_memo=tree_memo, trees=trees)))
        wall_phase(f"fingerprint/tree-end path={path}")
    if updated != memo:
        wall_phase("fingerprint/memo-write-start")
        write_signed(memo_path, updated, key)
        wall_phase("fingerprint/memo-write-end")
    if trees != tree_memo:
        write_signed(tree_path, trees, key)
    wall_phase(f"fingerprint/inventory checked={counts['checked']} hashed={counts['hashed']} memo_changed={updated != memo}")
    # Profiling/telemetry paths do not change mathematical inputs. Unknown
    # SEARCH_REDUCTION options are conservative cache invalidators.
    operational = {"SEARCH_REDUCTION_REQUESTS", "SEARCH_REDUCTION_PROFILE",
                   "SEARCH_REDUCTION_TELEMETRY", "SEARCH_REDUCTION_WORKERS",
                   "SEARCH_REDUCTION_RESUME", "SEARCH_REDUCTION_QUERY_CACHE",
                   "SEARCH_REDUCTION_PROBE_CACHE", "SEARCH_REDUCTION_PROBE_READ",
                   "SEARCH_REDUCTION_PROBE_WRITE", "SEARCH_REDUCTION_PROBE_ID",
                   "SEARCH_REDUCTION_PROBE_PLANNED"}
    environment = {k: v for k, v in os.environ.items()
                   if k.startswith("SEARCH_REDUCTION_") and k not in operational}
    return hashlib.sha256(canonical([VERSION, R_VERSION, fingerprint, environment,
                                    os.environ.get("LEAN_PATH"),
                                    os.environ.get("LEAN_SYSROOT")])).hexdigest()


def record_files(directory):
    return {str(path.relative_to(directory)): digest(path)
            for path in files_under(directory)
            if path.name != "manifest.json"}


def source_data_fingerprints(paths, root, key):
    """Hash only Lean-selected mathematical input files, with a signed stat memo."""
    memo_path = root / "source-data-fingerprints.json"
    try:
        memo = read_signed(memo_path, key)
        if not isinstance(memo, dict):
            raise ValueError("invalid data fingerprint memo")
    except (OSError, ValueError, TypeError, KeyError):
        memo = {}
    updated = {}
    fingerprints = {}
    for name in paths:
        path = Path(name)
        if not path.is_absolute():
            raise ValueError("invalid mathematical input file")
        fingerprints[name] = tree_fingerprint(path, memo, updated, file_only=True)
    if updated != memo:
        write_signed(memo_path, updated, key)
    return fingerprints


def validate_source_data(directory, key):
    expected = read_signed(directory / "source-data.json", key)
    if not isinstance(expected, dict):
        raise ValueError("invalid mathematical input inventory")
    actual = source_data_fingerprints(expected, directory.parent, key)
    if actual != expected:
        raise ValueError("mathematical input data changed")


def snapshot_source_data(directory):
    """Called before cold R computation; records carry no verdict information."""
    directory = Path(directory)
    key = auth_key()
    path = directory / "source-data.json"
    if path.exists():
        validate_source_data(directory, key)
    paths = json.loads((directory / "source-input-files.json").read_text())
    if not isinstance(paths, list) or not all(isinstance(p, str) for p in paths):
        raise ValueError("invalid mathematical input paths")
    write_signed(path, source_data_fingerprints(paths, directory.parent, key), key)


def valid_record(directory, identity, key):
    manifest = read_signed(directory / "manifest.json", key)
    if manifest["identity"] != identity:
        raise ValueError("input identity mismatch")
    actual = record_files(directory)
    if not actual or actual != manifest["files"]:
        raise ValueError("record bytes changed")
    if not any(name.endswith(".pickle") for name in actual):
        raise ValueError("no typed probe record")
    wall_phase("cache/source-data-start")
    validate_source_data(directory, key)
    wall_phase("cache/source-data-end")


def emit(message):
    print(message, flush=True)


def replay_command(command, directory):
    """Replay a complete single-probe request through its authenticated Lean entry.

    The original request must have completed successfully before the runner
    signs the directory. Multi-probe or incomplete records keep the original
    wrapper, so a partial cache cannot omit a probe. The entry invokes the same
    live Lean kernel, leakage audit and GraphReading publication path.
    """
    entries = sorted(directory.glob("entry-*.lean"))
    plan = directory / "entry-plan"
    if (not plan.is_file() or plan.read_bytes() != b"probe\n"
            or len(entries) != 1 or len(list(directory.glob("*.pickle"))) != 1
            or not entries[0].with_suffix(".olean").is_file()
            or not command or command[-1] != os.environ.get("SEARCH_REDUCTION_REQUESTS")):
        return command
    return command[:-1] + [str(entries[0].absolute())]


def run(command):
    wall_phase("cache/runner-start")
    request = os.environ["SEARCH_REDUCTION_REQUESTS"]
    if os.environ.get("SEARCH_REDUCTION_PROBE_CACHE") == "0":
        return subprocess.call(command)
    root = Path(os.environ.get("SEARCH_REDUCTION_PROBE_CACHE",
                              "build/lean-inspector/search-reduction-probe-cache"))
    root.mkdir(parents=True, exist_ok=True)
    key = auth_key()
    started = time.monotonic()
    wall_phase("cache/fingerprint-start")
    identity = input_identity(request, root, key)
    wall_phase("cache/fingerprint-end")
    emit(f"PROBE_CACHE_INPUT identity={identity} seconds={time.monotonic()-started:.6f}")
    directory = root / identity
    env = dict(os.environ)
    env.pop("SEARCH_REDUCTION_PROBE_READ", None)
    env.pop("SEARCH_REDUCTION_PROBE_WRITE", None)
    env.pop("SEARCH_REDUCTION_PROBE_PLANNED", None)
    env["SEARCH_REDUCTION_PROBE_ID"] = identity
    # Candidate checkpoints and local query answers also inherit the full
    # semantic identity when the whole probe has to follow the cold path.
    env["SEARCH_REDUCTION_RESUME_INPUTS"] = identity
    if directory.exists():
        wall_phase("cache/authentication-start")
        try:
            valid_record(directory, identity, key)
        except (OSError, ValueError, TypeError, KeyError) as error:
            emit(f"PROBE_CACHE_REJECTED reason={error}")
        else:
            wall_phase("cache/authentication-end")
            env["SEARCH_REDUCTION_PROBE_READ"] = str(directory.absolute())
            hot_command = replay_command(command, directory)
            if hot_command != command:
                emit("PROBE_CACHE_ENTRY selected=authenticated request_elaboration=reused")
            hot_env = dict(env)
            # The authenticated entry imports its checked dependency module.
            # Only this hot subprocess sees the record directory on Lean's path.
            hot_env["LEAN_PATH"] = str(directory.absolute()) + os.pathsep + env.get("LEAN_PATH", "")
            wall_phase("lean/hot-start")
            result = subprocess.call(hot_command, env=hot_env)
            wall_phase("lean/hot-end")
            if result == 0:
                return 0
            if result == 75:
                return result
            emit(f"PROBE_CACHE_REJECTED kernel_exit={result}; recomputing cold")
            env.pop("SEARCH_REDUCTION_PROBE_READ", None)
    stage = Path(tempfile.mkdtemp(prefix="pending-", dir=root))
    env["SEARCH_REDUCTION_PROBE_WRITE"] = str(stage.absolute())
    wall_phase("lean/cold-start")
    result = subprocess.call(command, env=env)
    wall_phase("lean/cold-end")
    if result != 0:
        return result
    files = record_files(stage)
    if any(name.endswith(".pickle") for name in files):
        # Refuse to cache a result if any input changed during the computation.
        if input_identity(request, root, key) != identity:
            emit("PROBE_CACHE_NOT_STORED reason=inputs_changed_during_run")
            return 0
        try:
            validate_source_data(stage, key)
        except (OSError, ValueError, TypeError, KeyError) as error:
            emit(f"PROBE_CACHE_NOT_STORED reason={error}")
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
    if sys.argv[1] == "--native":
        native_run(sys.argv[2:])
    if sys.argv[1] == "--snapshot-source-data":
        snapshot_source_data(sys.argv[2])
        raise SystemExit(0)
    raise SystemExit(run(sys.argv[1:]))
