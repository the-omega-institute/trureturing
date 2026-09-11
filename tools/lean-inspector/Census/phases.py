"""Measured IO around the Lean streaming query; no evidence classification here."""

import argparse
import hashlib
import json
import os
import pathlib
import subprocess
import sqlite3
import functools

from streaming import canonical, digest, enumerate_oleans, file_stamp, hash_inputs, tracked_domain


def read(path):
    return json.loads(pathlib.Path(path).read_bytes())


def write(path, value):
    pathlib.Path(path).write_bytes(canonical(value))


def enumerate_domain(repository, directory):
    domain = tracked_domain(repository)
    manifest, inputs = enumerate_oleans(repository, domain)
    write(directory / "domain.json", domain)
    write(directory / "manifest.json", manifest)
    write(directory / "inputs.json", inputs)
    write(directory / "stamps.json", {path: file_stamp(path) for _, _, path in inputs})
    write(directory / "olean-hashes.json", hash_inputs(inputs, read(directory / "stamps.json")))


def upstream_header(path, memo, cache):
    """Memoize pinned upstream metadata by path and full filesystem identity.

    This does not shortcut hashing any tracked project olean. A size/mtime/
    ctime/device/inode change requires rereading the compiler metadata bytes.
    """
    from incremental import atomic_json
    before = file_stamp(path)
    previous = memo.get(str(path))
    if previous and previous["stamp"] == before:
        return previous["header"], True, False
    encoded = path.read_bytes()
    if file_stamp(path) != before:
        raise ValueError("IE-C044 upstream metadata changed during read: " + str(path))
    address = hashlib.sha256(encoded).hexdigest()
    cached = cache / (address + ".json")
    hit = cached.is_file()
    if hit:
        header = read(cached)
    else:
        data = json.loads(encoded)
        header = {"module": data["module"], "imports": sorted(set(e[0] for e in data["directImports"]))}
        atomic_json(cached, header)
    memo[str(path)] = {"stamp": before, "address": address, "header": header}
    return header, hit, True


def external_graph(directory):
    """Upstream packages cannot depend on this downstream package.

    Project edges come exclusively from the streamed olean headers. For scope
    display, upstream edges use the compiler's directImports in ilean metadata;
    these packages define none of the downstream evidence types/extensions.
    A missing header or an edge back into the tracked domain fails closed. No
    upstream or surplus project olean is opened or hashed by the census.
    """
    domain = read(directory / "domain.json")
    domain_names = set(domain)
    repository = pathlib.Path(__file__).resolve().parents[3]
    pending = set()
    for line in (directory / "index.jsonl").open():
        data = json.loads(line)
        pending.update(e["module"] for e in data["imports"] if e["module"] not in domain)
    project_build = (repository / ".lake/build/lib/lean").resolve()
    search = [pathlib.Path(p) for p in os.environ["LEAN_PATH"].split(os.pathsep)
              if p and pathlib.Path(p).resolve() != project_build]
    prefix = subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    search.append(pathlib.Path(prefix) / "lib/lean")
    result = {}
    from incremental import atomic_json
    cache = repository / ".lake/build/census/upstream"
    memo_path = cache / ("files-" + hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest() + ".json")
    memo = read(memo_path) if memo_path.is_file() else {}
    used_memo = {}
    hits = misses = rereads = 0
    while pending:
        module = pending.pop()
        if module in result:
            continue
        relative = pathlib.Path(module.replace(".", "/") + ".ilean")
        path = next((root / relative for root in search if (root / relative).is_file()), None)
        if path is None:
            raise ValueError("IE-C044 missing upstream compiler import metadata: " + module)
        header, hit, reread = upstream_header(path, memo, cache)
        used_memo[str(path)] = memo[str(path)]
        hits += hit
        misses += not hit
        rereads += reread
        if header["module"] != module:
            raise ValueError("IE-C044 mismatched compiler import metadata: " + module)
        imports = header["imports"]
        if domain_names.intersection(imports):
            raise ValueError("IE-C044 upstream evidence boundary violated: " + module)
        result[module] = imports
        pending.update(dependency for dependency in imports if dependency not in result)
    request = read(directory / "membership-request.json")
    request["external_graph"] = sorted(result.items())
    write(directory / "membership-request.json", request)
    atomic_json(memo_path, used_memo)
    write(directory / "upstream-cache.json", {"hits": hits, "misses": misses, "metadata_files_reread": rereads})


def hash_receipt(repository, directory):
    request = read(directory / "request.json")
    membership = read(directory / "membership.json")
    projection = read(directory / "projection.json")
    paths = subprocess.check_output(["git", "ls-files", "-z", "--", "tools/lean-inspector",
        "lean-toolchain", "lakefile.toml", "lake-manifest.json"], cwd=repository).split(b"\0")
    programs = [[p.decode(), "sha256:" + hashlib.sha256((repository / p.decode()).read_bytes()).hexdigest()]
                for p in paths if p and pathlib.Path(p.decode()).suffix in (".lean", ".py", ".toml", ".json", "")]
    graph = {"project_headers": membership["headers"], "upstream": membership["external_graph"]}
    validation = read(directory / "validation.json")["receipt"]
    stamps = read(directory / "stamps.json")
    for _, _, path in read(directory / "inputs.json"):
        if file_stamp(path) != stamps[path]:
            raise ValueError("IE-C044 olean changed after extraction")
    extraction = read(directory / "extraction.json")
    inputs = {"head": request["head"],
              "oleans": read(directory / "olean-hashes.json"),
              "import_graph": digest(graph), "programs": sorted(programs),
              "export_sha256": request["report_sha256"], "domain": read(directory / "domain.json"),
              "scopes": membership["scopes"], "module_names": membership["module_names"],
              "extraction": {k: extraction[k] for k in ["cache_keys", "source_digest", "frozen_names_digest"]},
              "membership": read(directory / "membership-cache.json")["receipt"],
              "expanded_rows_cache_key": expanded_rows_key(projection, membership),
              "rows": {"artifact": "rows.jsonl", "sha256": projection["rows_sha256"]},
              "candidate_validation": validation,
              "toolchain": (repository / "lean-toolchain").read_text().strip()}
    from streaming import receipt_digest
    receipt = {"inputs": inputs, "digest": receipt_digest(inputs),
               "counts_sha256": digest(projection), "rows_sha256": projection["rows_sha256"],
               "candidate_keys": membership["candidate_keys"]}
    write(directory / "receipt.json", receipt)


def name_json(name):
    value = ["anonymous"]
    for part in name.split("."):
        value = ["str", value, part]
    return value


def expanded_rows_key(projection, membership):
    from emission_cache import cache_key
    emitter = digest([(name, hashlib.sha256(pathlib.Path(__file__).with_name(name).read_bytes()).hexdigest())
                      for name in ["phases.py", "emission_cache.py", "streaming.py"]])
    return cache_key(projection["rows_sha256"], membership["module_names"], membership["scopes"], emitter)


def emit(directory):
    projection = read(directory / "projection.json")
    info = read(directory / "emission.json")
    counts = projection["counts"]
    complete = counts["accounted"] == info["requested_keys"]
    fields = dict(info, schema="lean-information-disposition-census", counts=counts,
                  status="complete" if complete else "partial", coverage_theorem_count=counts["accounted"],
                  certified_complete=complete and counts["certified"] == counts["accounted"])
    metadata = read(directory / "membership.json")
    from emission_cache import restore_rows, store_rows
    address = expanded_rows_key(projection, metadata)
    cache = pathlib.Path(__file__).resolve().parents[3] / ".lake/build/census/expanded-rows"
    header = canonical(fields)[:-2] + b',"rows":[\n'
    if restore_rows(cache, address, directory / "census.json", header):
        write(directory / "census.json.summary.json", fields)
        write(directory / "emission-cache.json", {"cache_key": address, "hit": True})
        return
    names = [name_json(m) for m in metadata["module_names"]]
    scope_files = {}
    folder = directory / "scopes"
    folder.mkdir()
    for number, (root, indices) in enumerate(metadata["scopes"]):
        path = folder / f"{number}.json"
        path.write_bytes(canonical({"modules": [names[i] for i in indices], "completed": True}).rstrip(b"\n"))
        scope_files[canonical(name_json(root))] = path
    del names, metadata

    @functools.lru_cache(maxsize=4)
    def scope_bytes(key):
        return scope_files[key].read_bytes()
    # Scope bytes are encoded once per semantic root, then copied to each row.
    # This retains the J2 row schema without constructing a repository-sized DOM.
    with (directory / "census.json").open("wb") as out:
        out.write(header)
        for number, line in enumerate((directory / "rows.jsonl").open("rb")):
            row = json.loads(line)
            if number:
                out.write(b",\n")
            encoded = canonical(row).rstrip(b"\n")
            if row["class"] == "observed":
                encoded = encoded.replace(b'"import_scope":null', b'"import_scope":' +
                    scope_bytes(canonical(row["payload"]["root"])) , 1)
            out.write(encoded)
        out.write(b"\n]}\n")
    write(directory / "census.json.summary.json", fields)
    stored = store_rows(cache, address, directory / "census.json", len(header))
    write(directory / "emission-cache.json", {"cache_key": address, "hit": False, "stored": stored})


def sort_rows(directory):
    """Disk sort with an 8 MiB page cache; each row is parsed once at a time."""
    database = directory / "rows.sqlite"
    with sqlite3.connect(database) as db:
        db.execute("PRAGMA cache_size=-8192")
        db.execute("PRAGMA temp_store=FILE")
        db.execute("CREATE TABLE rows (name TEXT, identity TEXT PRIMARY KEY, row BLOB)")
        try:
            for line in (directory / "projection.json.rows.jsonl").open():
                value = json.loads(line)
                row = value["row"]
                db.execute("INSERT INTO rows VALUES (?, ?, ?)",
                           (value["sort_name"], row["statement_id"], canonical(row)))
        except sqlite3.IntegrityError as error:
            raise ValueError("IE-C035 duplicate accounting row") from error
        expected = read(directory / "request.json")["keys"]
        if db.execute("SELECT count(*) FROM rows").fetchone()[0] != len(expected):
            raise ValueError("IE-C044 accounting row count differs from request")
        for _, _, identity in expected:
            if db.execute("SELECT 1 FROM rows WHERE identity=?", (identity,)).fetchone() is None:
                raise ValueError("IE-C044 missing accounting key")
        hashed = hashlib.sha256()
        with (directory / "rows.jsonl").open("wb") as out:
            for (row,) in db.execute("SELECT row FROM rows ORDER BY name, identity"):
                out.write(row)
                hashed.update(row)
    projection = read(directory / "projection.json")
    projection["rows_sha256"] = "sha256:" + hashed.hexdigest()
    write(directory / "projection.json", projection)
    database.unlink()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["enumerate", "graph", "hash", "emit", "sort", "native"])
    parser.add_argument("repository", type=pathlib.Path)
    parser.add_argument("directory", type=pathlib.Path)
    options = parser.parse_args()
    if options.phase == "enumerate":
        enumerate_domain(options.repository, options.directory)
    elif options.phase == "graph":
        external_graph(options.directory)
    elif options.phase == "hash":
        hash_receipt(options.repository, options.directory)
    elif options.phase == "sort":
        sort_rows(options.directory)
    elif options.phase == "native":
        from native import build
        write(options.directory / "runtime.json", {name: str(build(options.repository, name))
              for name in ["scan.lean", "membership.lean"]})
    else:
        emit(options.directory)
