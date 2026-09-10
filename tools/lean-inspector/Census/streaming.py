"""Olean census domain, graph scopes, membership, and canonical read receipts.

The J3 grouping below defines query semantics, not execution batches. All roots
share one stream and one candidate Environment. Dependency packages may omit
evidence enumeration only if their header closure has no edge into the project
domain that defines the evidence types and extensions.
"""

from __future__ import annotations

import hashlib
import json
import pathlib
import subprocess


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode() + b"\n"


def digest(value):
    return "sha256:" + hashlib.sha256(canonical(value)).hexdigest()


def freshness(step):
    # Source freshness belongs exclusively to Lake, including all incremental failures.
    return step(["make", "lean"], "lake_freshness")


def check_domain(expected, actual):
    missing = sorted(set(expected) - set(actual))
    if missing:
        raise ValueError(f"IE-C044 olean domain missing={missing}")


def tracked_domain(repository):
    """Enumerate FROM tracked sources in Lake's default lean_lib globs.

    Cached modules outside this domain are never opened, statted or hashed.
    Opt-in analysis libraries are outside the default inspector build/domain.
    Dependency packages cannot import this downstream project: the package DAG
    is the evidence-free boundary, not a list of upstream module names.
    """
    repository = pathlib.Path(repository)
    tracked = subprocess.check_output(["git", "ls-files", "-z", "--", "*.lean"], cwd=repository)
    paths = [pathlib.PurePosixPath(p.decode()) for p in tracked.split(b"\0") if p]
    config = json.loads(subprocess.check_output([
        "lake", "env", "lean", "--run", "tools/lean-inspector/Census/config.lean", "lakefile.toml"],
        cwd=repository, text=True))
    domain = {}
    for library in config["lean_lib"]:
        if library["name"] not in config["defaultTargets"]:
            continue
        source_root = pathlib.PurePosixPath(library.get("srcDir", "."))
        for path in paths:
            if not path.is_relative_to(source_root):
                continue
            if path.parts[0] != "D5" and str(source_root) != "tools/lean-inspector":
                continue
            module = ".".join(path.relative_to(source_root).with_suffix("").parts)
            for glob in library.get("globs", library.get("roots", [library["name"]])):
                prefix = glob[:-2] if glob.endswith((".+", ".*")) else glob
                if (module == glob or glob.endswith(".*") and module == prefix
                        or glob.endswith((".+", ".*")) and module.startswith(prefix + ".")):
                    domain[module] = str(path)
    return dict(sorted(domain.items()))


def enumerate_oleans(repository, domain):
    inputs, manifest = [], []
    for module in sorted(domain):
        base = pathlib.Path(repository) / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        if not base.is_file():
            raise ValueError(f"IE-C044 missing olean for tracked module: {module}")
        paths = [str(base)]
        inputs.append((module, "base", str(base)))
        for part in ("server", "private"):
            path = pathlib.Path(str(base) + "." + part)
            if path.is_file():
                if part == "private" and len(paths) != 2:
                    raise ValueError(f"IE-C044 missing server part: {module}")
                paths.append(str(path))
                inputs.append((module, part, str(path)))
        manifest.append([module, paths])
    return manifest, inputs


def closure(graph, roots):
    visited, pending = set(), list(roots)
    while pending:
        module = pending.pop()
        if module in visited:
            continue
        if module not in graph:
            raise ValueError(f"IE-C044 missing import header: {module}")
        visited.add(module)
        pending.extend(graph[module])
    return sorted(visited)


def root_definitions(modules, keys, evidence):
    names = {}
    for owner, name, _ in keys:
        names.setdefault(name, set()).add(owner)
    isolated = {owner for owners in names.values() if len(owners) > 1 for owner in owners} & set(modules)
    groups = {}
    for module in sorted(set(modules) - isolated):
        groups.setdefault(".".join(module.split(".")[:3]), []).append(module)
    # 32 and the root spelling are the existing J3 scope definition. Changing
    # them changes the query; they are deliberately not resource tuning flags.
    roots = [(f"{group}.{start // 32:04d}", members[start:start + 32])
             for group, members in sorted(groups.items()) for start in range(0, len(members), 32)]
    roots = sorted(roots + [(module, [module]) for module in isolated])
    definitions, assignment = [], {}
    for number, (_, members) in enumerate(roots):
        root = f"CensusQueryRun.Group{number // 20:04d}.Part{number:05d}"
        definitions.append([root, sorted(set(members) | set(evidence)
                                         | {"LeanInformationAudit.Census.Command"})])
        assignment.update((module, root) for module in members)
    return definitions, assignment


def root_scopes(modules, keys, evidence, graph):
    definitions, assignment = root_definitions(modules, keys, evidence)
    scopes = {root: sorted([root] + closure(graph, imports)) for root, imports in definitions}
    return scopes, assignment


def owner_error(owner, records):
    modules = {record["module"] for record in records}
    if len(modules) > 1:
        return "IE-C035 DuplicateAnalysisDisposition component=ownership_collision modules=" + ",".join(sorted(modules))
    if not records:
        return "IE-C034 MissingAnalysisDisposition component=owning_module_membership"
    if not any(record["module"] == owner and record["matches"] for record in records):
        return "IE-C036 AnalysisDispositionIdentityMismatch component=owning_module_membership"
    return None


def select_candidates(key, scope, registrations, named):
    hits = [entry for entry in registrations if entry["module"] in scope and entry["key"] == key]
    for entry in named:
        if entry["module"] not in scope or entry["head"] == "support":
            continue
        if entry["key"] is None:
            return hits, "IE-C036 AnalysisDispositionIdentityMismatch component=unclassifiable_named_key name=" + entry["name"]
        if entry["key"] == key:
            hits.append(entry)
    return hits, None


def file_stamp(path):
    stat = pathlib.Path(path).stat()
    return [stat.st_size, stat.st_mtime_ns, stat.st_ctime_ns, stat.st_dev, stat.st_ino]


def hash_inputs(inputs, stamps=None):
    result = []
    for module, part, path in sorted(inputs):
        before = file_stamp(path)
        if stamps is not None and stamps[path] != before:
            raise ValueError(f"IE-C044 olean changed during scan: {module}/{part}")
        with open(path, "rb") as source:
            hasher = hashlib.sha256()
            for block in iter(lambda: source.read(1024 * 1024), b""):
                hasher.update(block)
            hashed = hasher.hexdigest()
        if file_stamp(path) != before:
            raise ValueError(f"IE-C044 olean changed while hashing: {module}/{part}")
        result.append([module, part, before[0], "sha256:" + hashed])
    return result


def receipt_digest(inputs):
    return digest(inputs)


def replay(scan, expected):
    actual = scan()
    if canonical(actual) != canonical(expected):
        raise ValueError("IE-C044 receipt replay mismatch")
    return "match"
