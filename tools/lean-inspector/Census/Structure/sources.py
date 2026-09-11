"""Run-local, per-olean-part caches for detached structural summaries."""

import gzip
import hashlib
import json
import os
import pathlib
import subprocess
import time

from incremental import atomic_json
from phases import read, write
from streaming import digest, file_stamp


def file_digest(path):
    hashed = hashlib.sha256()
    with pathlib.Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            hashed.update(block)
    return "sha256:" + hashed.hexdigest()


def fingerprint(repository):
    paths = ["Census/structure.lean", "LeanInformationAudit/Census/StructureReader.lean",
             "Inspector.lean", "Census/Structure/sources.py"]
    return digest([(p, file_digest(repository / "tools/lean-inspector" / p)) for p in paths] +
                  [("toolchain", (repository / "lean-toolchain").read_text())])


def upstream_inputs(repository, directory, cache):
    """Resolve declaring modules from search-path provenance, never Name prefixes.

    Pinned upstream digests are memoized by complete filesystem identity. Project
    digests are supplied by the census hash pass and never reread here.
    """
    graph = dict(read(directory / "membership-request.json")["external_graph"])
    project = (repository / ".lake/build/lib/lean").resolve()
    search = [pathlib.Path(p).resolve() for p in os.environ["LEAN_PATH"].split(os.pathsep)
              if p and pathlib.Path(p).resolve() != project]
    prefix = pathlib.Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    search.append(prefix / "lib/lean")
    memo_path = cache / "upstream-files.json"
    memo = read(memo_path) if memo_path.is_file() else {}
    used, manifest, hashes, libraries = {}, [], [], {}
    hits = misses = 0
    for module in sorted(graph):
        relative = pathlib.Path(module.replace(".", "/") + ".olean")
        root = next((p for p in search if (p / relative).is_file()), None)
        if root is None:
            raise ValueError("missing_olean_part")
        # Core library directories are installed provenance, not a whitelist of
        # constant namespace strings. Other packages retain their package name.
        if root.is_relative_to(prefix):
            library = relative.parts[0].removesuffix(".olean")
        else:
            package = root.parts[root.parts.index("packages") + 1]
            library = "Mathlib" if package == "mathlib" else package
        libraries[module] = library
        base, paths = root / relative, []
        for part in ["base", "server", "private"]:
            path = base if part == "base" else pathlib.Path(str(base) + "." + part)
            if not path.is_file():
                continue
            if part == "private" and len(paths) != 2:
                raise ValueError("missing_olean_part")
            paths.append(str(path))
            stamp = file_stamp(path)
            previous = memo.get(str(path))
            if previous and previous["stamp"] == stamp:
                hashed = previous["digest"]
                hits += 1
            else:
                hashed = file_digest(path)
                if file_stamp(path) != stamp:
                    raise ValueError("dependency_unresolved")
                misses += 1
            used[str(path)] = {"stamp": stamp, "digest": hashed}
            hashes.append([module, part, stamp[0], hashed])
        manifest.append([module, paths])
    atomic_json(memo_path, used)
    return manifest, hashes, libraries, {"upstream_hash_hits": hits, "upstream_hash_misses": misses}


def part_plan(manifest, hashes, reader, cache, mode):
    hashed = {(m, p): [size, h] for m, p, size, h in hashes}
    result = {}
    for module, paths in manifest:
        layout = ["base", "server", "private"][:len(paths)]
        # Layout includes sibling part content: private overrides cannot reuse a
        # base-only interpretation after the module's part layout changes.
        binding = [(part, hashed[module, part]) for part in layout]
        parts = [(part, digest([hashed[module, part], binding, reader, mode, part])) for part in layout]
        result[module] = {"paths": paths, "parts": [(p, cache / (h[7:] + ".jsonl.gz")) for p, h in parts],
                          "address": digest(parts)}
    return result


def split_summaries(source, plan, store, libraries):
    """Cache and pack the cold reader stream together, without reopening parts."""
    target, temporary, destination = None, None, None
    current, imports = None, set()
    stats = dict(packed_declarations=0, value_walks=0, type_walks=0,
                 value_name_incidences=0, type_name_incidences=0, stream_packed_modules=0)

    def finish():
        if target:
            target.close()
            temporary.replace(destination)

    def finish_module():
        if current is not None:
            store.finish_module(current, digest([plan[current]["address"], libraries[current]]))
            store.db.commit()
    try:
        with source.open("rb") as stream:
            for line in stream:
                row = json.loads(line)
                if "module" in row:
                    finish()
                    if current != row["module"]:
                        finish_module()
                        current, imports = row["module"], set()
                        stats["stream_packed_modules"] += 1
                        store.remove_module(current)
                    imports.update(row["imports"])
                    store.module(current, imports, libraries[current])
                    destination = dict(plan[row["module"]]["parts"])[row["part"]]
                    temporary = destination.with_suffix(".tmp")
                    target = gzip.open(temporary, "wb", compresslevel=1)
                if target is None:
                    raise ValueError("dependency_unresolved")
                target.write(line)
                if "name" in row:
                    pack_declaration(store, current, row, libraries[current], stats)
        finish()
        finish_module()
    finally:
        if target:
            target.close()
    return stats


def pack_declaration(store, module, row, library, stats):
    stats["packed_declarations"] += 1
    name = row["name"]
    if library == "repository":
        store.declaration(module, name, row["kind"], row["value"], row["type"])
        stats["value_walks"] += row["value"] is not None
        stats["type_walks"] += 1
        stats["value_name_incidences"] += len(row["value"] or [])
        stats["type_name_incidences"] += len(row["type"])
    else:
        store.db.execute("INSERT OR REPLACE INTO decl VALUES (?,?,NULL,NULL,NULL,NULL)",
                         (module, name))


def pack(store, plans, libraries):
    prior = dict(store.db.execute("SELECT name,address FROM modules"))
    hits = misses = 0
    stats = dict(packed_declarations=0, value_walks=0, type_walks=0,
                 value_name_incidences=0, type_name_incidences=0)
    for module in sorted(set(prior) - set(plans)):
        store.remove_module(module)
    for module, plan in sorted(plans.items()):
        address = digest([plan["address"], libraries[module]])
        if prior.get(module) == address:
            hits += 1
            continue
        misses += 1
        store.remove_module(module)
        imports = set()
        for part, path in plan["parts"]:
            with gzip.open(path, "rt") as source:
                header = json.loads(next(source))
                if (header["module"], header["part"]) != (module, part):
                    raise ValueError("dependency_unresolved")
                imports.update(header["imports"])
                store.module(module, imports, libraries[module])
                for line in source:
                    pack_declaration(store, module, json.loads(line), libraries[module], stats)
        store.finish_module(module, address)
        store.db.commit()
    return dict(stats, pack_module_hits=hits, pack_module_misses=misses)


def synchronize(repository, directory, cache, store, measure, mark=lambda _: None):
    from native import build
    raw = cache / "raw"
    raw.mkdir(parents=True, exist_ok=True)
    reader = fingerprint(repository)
    started = time.monotonic()
    mark("structure_upstream_input_hashing")
    external, upstream_hashes, libraries, stats = upstream_inputs(repository, directory, cache)
    timings = {"upstream_input_hashing": time.monotonic() - started}
    project, project_hashes = read(directory / "manifest.json"), read(directory / "olean-hashes.json")
    libraries.update((module, "repository") for module, _ in project)
    plans = {}
    binary = None
    new_index = store.db.execute("SELECT 1 FROM decl LIMIT 1").fetchone() is None
    if new_index:
        # Bulk construction avoids random writes through a global Name index
        # for every upstream occurrence. Incremental updates retain the index.
        store.db.execute("DROP INDEX names")
    for mode, manifest, hashes in [("bodies", project, project_hashes), ("names", external, upstream_hashes)]:
        if any(not pathlib.Path(p).is_file() for _, paths in manifest for p in paths):
            raise ValueError("missing_olean_part")
        plan = part_plan(manifest, hashes, reader, raw, mode)
        missing = [[m, p["paths"]] for m, p in plan.items() if any(not f.is_file() for _, f in p["parts"])]
        stats[mode + "_part_hits"] = sum(f.is_file() for p in plan.values() for _, f in p["parts"])
        stats[mode + "_part_misses"] = sum(not f.is_file() for p in plan.values() for _, f in p["parts"])
        if missing:
            if binary is None:
                binary = build(repository, "structure.lean")
            path = directory / ("structure-" + mode + "-manifest.json")
            write(path, missing)
            output = directory / ("structure-" + mode + ".jsonl")
            measure([str(binary), str(path), str(output), mode], "structure_" + mode)
            started = time.monotonic()
            mark("structure_" + mode + "_cache_and_pack")
            for key, value in split_summaries(output, plan, store, libraries).items():
                stats[key] = stats.get(key, 0) + value
            timings[mode + "_cache_and_pack"] = time.monotonic() - started
        plans.update(plan)
    started = time.monotonic()
    mark("structure_raw_cache_restore")
    for key, value in pack(store, plans, libraries).items():
        stats[key] = stats.get(key, 0) + value
    timings["raw_cache_restore"] = time.monotonic() - started
    if new_index:
        mark("structure_name_index")
        started = time.monotonic()
        store.db.execute("CREATE INDEX names ON decl(name)")
        store.db.commit()
        timings["name_index"] = time.monotonic() - started
    for path, stamp in read(directory / "stamps.json").items():
        if file_stamp(path) != stamp:
            raise ValueError("dependency_unresolved")
    upstream_memo = read(cache / "upstream-files.json")
    for path, value in upstream_memo.items():
        if file_stamp(path) != value["stamp"]:
            raise ValueError("dependency_unresolved")
    inputs = {"olean_part_manifest_sha256": digest(project_hashes), "reader_fingerprint": reader,
              "upstream_olean_manifest_sha256": digest(upstream_hashes),
              "ownership_fingerprint": store.snapshot()}
    return inputs, stats, timings
