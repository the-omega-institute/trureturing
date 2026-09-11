"""Stream detached olean records into the content-addressed extraction cache."""

import hashlib
import json
import pathlib
import subprocess
import sys

from incremental import extraction_plan, save_extraction
from streaming import canonical, digest, file_stamp

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent.parent))
from materials import declaration_statement_id


def detached_records(lines, source_path=None):
    record = None
    for line in lines:
        value = json.loads(line)
        if "owner" in value:
            if record is None or any(value[k] != record[k] for k in ["module", "part"]):
                raise ValueError("IE-C044 owner outside its module part")
            owner = value["owner"]
            record["owners"].append(owner)
        else:
            if record is not None:
                yield record
            record = value
    if record is not None:
        yield record


def decoded_name_key(text):
    """Decode the producer's byte-length-prefixed Name wire; never hash it here."""
    data, offset = text.encode("utf-8"), 0
    def consume(expected):
        nonlocal offset
        if data[offset:offset + len(expected)] != expected:
            raise ValueError("IE-C044 invalid producer Name key")
        offset += len(expected)
    def number(delimiter):
        nonlocal offset
        end = data.index(delimiter, offset)
        value = int(data[offset:end])
        offset = end + 1
        return value
    def parse():
        nonlocal offset
        consume(b"n")
        tag = data[offset:offset + 1]
        offset += 1
        if tag == b"0":
            return ["anonymous"]
        if tag not in (b"s", b"n"):
            raise ValueError("IE-C044 invalid producer Name constructor")
        consume(b"(")
        parent = parse()
        consume(b",")
        if tag == b"n":
            return ["num", parent, number(b")")]
        size = number(b":")
        value = data[offset:offset + size].decode("utf-8")
        offset += size
        consume(b")")
        return ["str", parent, value]
    result = parse()
    if offset != len(data):
        raise ValueError("IE-C044 trailing producer Name key")
    return result


def add_collision_identities(repository, index, manifest, request, source_path, env=None):
    occurrences = {}
    for line in index.open():
        row = json.loads(line)
        for owner in row["owners"]:
            occurrences.setdefault(canonical(owner["name"]), set()).add(row["module"])
    collisions = {name: modules for name, modules in occurrences.items() if len(modules) > 1}
    if not collisions:
        return
    modules = set().union(*collisions.values())
    selected = index.with_suffix(".identities-manifest.json")
    selected.write_bytes(canonical([entry for entry in manifest if entry[0] in modules]))
    # Use the sole encoder in Inspector.lean and the report's existing compactor.
    command = ["lean", "--run", str(repository / "tools/lean-inspector/Inspector.lean"),
               "--statement-identities", str(selected), str(request)]
    proc = subprocess.Popen(command, cwd=repository, env=env, stdout=subprocess.PIPE, text=True)
    identities = {}
    try:
        for line in proc.stdout:
            row = json.loads(line)
            name = canonical(decoded_name_key(row["name_key"]))
            if name in collisions:
                identities[row["module"], row["part"], name] = declaration_statement_id(
                    source_path(row["module"]), row["kind"], row["name_key"], row["statement_material"])
        if proc.wait():
            raise ValueError("IE-C044 standalone statement identity producer failed")
    finally:
        proc.stdout.close()
        if proc.poll() is None:
            proc.kill()
            proc.wait()
    temporary = index.with_suffix(".identified")
    with index.open() as source, temporary.open("wb") as out:
        for line in source:
            row = json.loads(line)
            for owner in row["owners"]:
                name = canonical(owner["name"])
                if name in collisions:
                    owner["statement_id"] = identities[row["module"], row["part"], name]
            out.write(canonical(row))
    temporary.replace(index)


def source_digest(repository):
    inspector = repository / "tools/lean-inspector"
    paths = [inspector / name for name in [
        "LeanInformationAudit/Census/Stream.lean", "LeanInformationAudit/Census/Ownership.lean",
        "LeanInformationAudit/RegistryTypes.lean", "LeanInformationAudit/NameWire.lean",
        "Inspector.lean", "Census/scan.lean",
        "Census/extraction.py", "materials.py"]]
    return digest([(str(p.relative_to(repository)), hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths])


def scan(repository, directory, binary, cache=None):
    def read(name):
        return json.loads((directory / name).read_bytes())
    manifest, hashes = read("manifest.json"), read("olean-hashes.json")
    request, domain = read("request.json"), read("domain.json")
    names = digest(sorted(set(row[1] for row in request["keys"])))
    plan = extraction_plan(manifest, hashes, cache or repository / ".lake/build/census/index",
                           source_digest(repository), names)
    missing = directory / "missing-manifest.json"
    missing.write_bytes(canonical(plan["misses"]))
    if plan["misses"]:
        proc = subprocess.Popen([str(binary), str(missing), str(directory / "request.json"), "-"],
                                cwd=repository, stdout=subprocess.PIPE, text=True)
        try:
            current, records = None, []
            for data in detached_records(proc.stdout, domain.__getitem__):
                module = data["module"]
                if current is not None and module != current:
                    save_extraction(plan, current, records)
                    records = []
                current = module
                records.append(data)
            if proc.wait():
                raise ValueError("IE-C044 olean extraction failed")
            if current is not None:
                save_extraction(plan, current, records)
        finally:
            proc.stdout.close()
            if proc.poll() is None:
                proc.kill()
                proc.wait()
    # Each module is decoded, copied to the read stream, then released. No
    # repository-sized array of constant records or extraction DOM is retained.
    used = []
    with (directory / "index.jsonl").open("wb") as out:
        for module, _ in manifest:
            path = plan["paths"][module]
            data = path.read_bytes()
            for record in json.loads(data):
                if record["module"] != module:
                    raise ValueError("IE-C044 extraction module binding mismatch")
                out.write(canonical(record))
            used.append([module, plan["digests"][module], digest(json.loads(data))])
    add_collision_identities(repository, directory / "index.jsonl", manifest,
                             directory / "request.json", domain.__getitem__)
    stamps = read("stamps.json")
    for _, _, path in read("inputs.json"):
        if file_stamp(path) != stamps[path]:
            raise ValueError("IE-C044 olean changed during extraction")
    result = {"hits": len(plan["hits"]), "misses": len(plan["misses"]),
              "reread_modules": [m for m, _ in plan["misses"]], "cache_keys": used,
              "source_digest": source_digest(repository), "frozen_names_digest": names}
    (directory / "extraction.json").write_bytes(canonical(result))
    return result


if __name__ == "__main__":
    scan(pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2]), sys.argv[3],
         pathlib.Path(sys.argv[4]) if len(sys.argv) == 5 else None)
