"""FILEMAP declarations and complete path planning for ci.py; never executes work."""
import hashlib
import json
import pathlib
import re
import subprocess
import tomllib

STAGES = ("build", "engineering", "current", "delta")
TOOLS = {"bash", "dotnet", "git", "lake", "make", "python3"}
CACHES = {"dependency", "project", "report", "judge", "elan"}
FILEMAP = "Meta/FILEMAP.toml"


def exact(value, keys, where):
    if not isinstance(value, dict) or set(value) != set(keys):
        raise ValueError(f"{where}: expected fields {sorted(keys)}")


def string(value, where):
    if not isinstance(value, str) or not value or value != value.strip():
        raise ValueError(f"{where}: expected canonical string")
    return value


def name(value, where):
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9.-]*", string(value, where)):
        raise ValueError(f"{where}: invalid name")
    return value


def names(value, where, allowed=None, empty=True):
    if not isinstance(value, list) or (not value and not empty):
        raise ValueError(f"{where}: expected array")
    for item in value:
        name(item, where)
        if allowed is not None and item not in allowed:
            raise ValueError(f"{where}: unknown resource/tool/cache {item}")
    if value != sorted(set(value)):
        raise ValueError(f"{where}: must be unique and ordinally sorted")
    return value


def path(value):
    # Preserve whitespace and Unicode, never normalize a different path into scope.
    if (not isinstance(value, str) or not value or value.startswith("/") or "\\" in value
            or any(p in ("", ".", "..") for p in value.split("/"))
            or any(c == "\0" or 0xD800 <= ord(c) <= 0xDFFF for c in value)):
        raise ValueError(f"invalid repository path: {value!r}")
    return value


def ordinal(value):
    return value.encode("utf-16-be")  # Match .NET StringComparer.Ordinal.


def glob(pattern):
    string(pattern, "pattern")
    path(pattern)
    if "?" in pattern or any(ord(c) < 32 or ord(c) > 126 for c in pattern):
        raise ValueError(f"unsafe FILEMAP pattern: {pattern}")
    result, i = [], 0
    while i < len(pattern):
        if pattern[i:i + 3] == "**/":
            result.append("(?:.*/)?")
            i += 3
        elif pattern[i:i + 2] == "**":
            result.append(".*")
            i += 2
        else:
            result.append("[^/]*" if pattern[i] == "*" else re.escape(pattern[i]))
            i += 1
    return re.compile("\\A" + "".join(result) + "\\Z")


def load_filemap(raw):
    if not raw or raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw or not raw.endswith(b"\n"):
        raise ValueError("FILEMAP must be strict UTF-8 without BOM/CR and end in LF")
    data = tomllib.loads(raw.decode("utf-8"))
    exact(data, {"schema_version", "resources", "residence_policy", "files"}, FILEMAP)
    if type(data["schema_version"]) is not int or data["schema_version"] != 3:
        raise ValueError("FILEMAP schema_version must be 3")
    residence = data["residence_policy"]
    exact(residence, {"case_id", "desired", "known_violation_count", "status"}, "residence_policy")
    name(residence["case_id"], "case_id")
    for key in ("desired", "status"):
        string(residence[key], key)
    count = residence["known_violation_count"]
    if type(count) is not int or not 0 <= count <= 2147483647:
        raise ValueError("invalid known_violation_count")
    resources = {}
    if not isinstance(data["resources"], list):
        raise ValueError("resources must be an array")
    for resource in data["resources"]:
        exact(resource, {"id", "stage", "owner", "prerequisites", "tools", "cache_layers", "materials"}, "resource")
        rid = name(resource["id"], "resource id")
        if rid in resources or resource["stage"] not in STAGES:
            raise ValueError(f"duplicate/conflicting resource or invalid stage: {rid}")
        path(string(resource["owner"], rid + ":owner"))
        names(resource["tools"], rid + ":tools", TOOLS)
        names(resource["cache_layers"], rid + ":cache_layers", CACHES)
        materials = resource["materials"]
        if not isinstance(materials, list):
            raise ValueError(f"{rid}: materials must be an array")
        for material in materials:
            path(material)
        if materials != sorted(set(materials), key=ordinal):
            raise ValueError(f"{rid}: materials must be unique and sorted")
        resources[rid] = resource
    if list(resources) != sorted(resources):
        raise ValueError("resource ids must be ordinally sorted")
    for rid, resource in resources.items():
        names(resource["prerequisites"], rid + ":prerequisites", resources)
        for dep in resource["prerequisites"]:
            if STAGES.index(resources[dep]["stage"]) > STAGES.index(resource["stage"]):
                raise ValueError(f"conflicting resource stage dependency: {rid} -> {dep}")
    closure(resources, resources)  # Reject even unselected broken declarations.
    entries = data["files"]
    if not isinstance(entries, list) or not entries:
        raise ValueError("files must be a nonempty array")
    artifact_ids, patterns = set(), []
    for entry in entries:
        if not isinstance(entry, dict):
            raise ValueError("file row must be a table")
        where = entry.get("pattern", "file row") if isinstance(entry, dict) else "file row"
        keys = {"pattern", "require", "kind", "admission_plane", "produced_by", "consumed_by",
                "verified_by", "artifact_id", "runtime_disposition"}
        generated = entry.get("kind") == "generated"
        local = entry.get("runtime_disposition") == "run-local"
        keyed = generated and entry.get("artifact_id") == "none" and "*" in str(where)
        artifact = generated and entry.get("artifact_id") != "none" and entry.get("runtime_disposition") == "committed-source"
        projection = (local and not keyed) or artifact
        if projection:
            keys |= {"mode", "history_requirement"}
        elif not local and "residence_violation" in entry:
            keys.add("residence_violation")
        exact(entry, keys, where)
        glob(entry["pattern"])
        patterns.append(entry["pattern"])
        names(entry["require"], where + ":require", resources)
        if entry["kind"] not in {"truth", "program", "data", "generated", "ledger"} or entry["admission_plane"] not in {"judge", "content"}:
            raise ValueError(f"{where}: invalid kind/admission_plane")
        for key in ("produced_by", "artifact_id"):
            name(entry[key], where + ":" + key)
        for key in ("consumed_by", "verified_by"):
            names(entry[key], where + ":" + key, empty=False)
        if "residence_violation" in entry and (entry["residence_violation"] is not True or entry["kind"] != "data"):
            raise ValueError(f"{where}: invalid residence_violation")
        if generated and (entry["produced_by"] == "none" or entry["produced_by"] not in entry["verified_by"]):
            raise ValueError(f"{where}: generated verifier must include its producer")
        if entry["runtime_disposition"] not in {"committed-source", "committed-ledger", "run-local"}:
            raise ValueError(f"{where}: invalid runtime_disposition")
        if (entry["kind"] == "ledger") != (entry["runtime_disposition"] == "committed-ledger"):
            raise ValueError(f"{where}: ledger disposition mismatch")
        if projection and (not generated or entry["artifact_id"] == "none" or not isinstance(entry["mode"], str)
                           or not re.fullmatch(r"[0-7]{6}", entry["mode"])
                           or entry["history_requirement"] != "not-required"):
            raise ValueError(f"{where}: invalid projection fields")
        if entry["artifact_id"] != "none":
            if entry["artifact_id"] in artifact_ids:
                raise ValueError(f"{where}: duplicate artifact_id")
            artifact_ids.add(entry["artifact_id"])
    if patterns != sorted(set(patterns)):
        raise ValueError("file patterns must be unique and ordinally sorted")
    return data


def closure(resources, roots):
    selected, visiting = set(), set()
    def visit(rid):
        if rid in visiting:
            raise ValueError(f"cyclic resource: {rid}")
        if rid not in resources:
            raise ValueError(f"unknown resource: {rid}")
        if rid not in selected:
            visiting.add(rid)
            for dep in resources[rid]["prerequisites"]:
                visit(dep)
            visiting.remove(rid)
            selected.add(rid)
    for rid in roots:
        visit(rid)
    return sorted(selected)


def oid(value):
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value) or value == "0" * 40:
        raise ValueError("expected immutable nonzero 40-hex object identity")
    return value


def git(root, *args):
    return subprocess.run(["git", "--no-replace-objects", *args], cwd=root, check=True, capture_output=True).stdout


def candidate(root, commit):
    oid(commit)
    if git(root, "cat-file", "-t", commit).strip() != b"commit":
        raise ValueError("candidate must be a commit")
    return {"commit": commit, "tree": oid(git(root, "rev-parse", commit + "^{tree}").decode().strip())}


def strict_json(file):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f"duplicate JSON field: {key}")
            result[key] = value
        return result
    def invalid(value):
        raise ValueError(f"invalid JSON constant: {value}")
    return json.loads(file.read_bytes().decode("utf-8"), object_pairs_hook=pairs, parse_constant=invalid)


def same_record(left, right):
    # Python equality aliases false/0 and true/1; JSON protocol fields do not.
    return json.dumps(left, sort_keys=True, ensure_ascii=True) == json.dumps(right, sort_keys=True, ensure_ascii=True)


def tree_entries(root, tree):
    result = {}
    for record in git(root, "ls-tree", "-rz", "--full-tree", tree).split(b"\0")[:-1]:
        meta, raw_path = record.split(b"\t", 1)
        mode, kind, blob = meta.decode("ascii").split(" ")
        result[raw_path.decode("utf-8")] = {"mode": mode, "oid": blob}
    return result


def endpoint(value):
    exact(value, {"path", "mode", "oid"}, "changed endpoint")
    path(value["path"])
    oid(value["oid"])
    if value["mode"] not in {"100644", "100755"}:
        raise ValueError(f"{value['path']}: invalid file mode {value['mode']}")
    return value


def change_paths(data):
    if data["complete"] is not True or type(data["change_count"]) is not int or not isinstance(data["changes"], list) or data["change_count"] != len(data["changes"]):
        raise ValueError("complete changed-path list and matching change_count required")
    selected = {}
    for record in data["changes"]:
        exact(record, {"status", "old", "new"}, "change")
        status, old, new = record["status"], record["old"], record["new"]
        if status not in {"A", "D", "M", "R"} or (old is None) != (status == "A") or (new is None) != (status == "D"):
            raise ValueError("invalid change status/endpoints")
        for value in (old, new):
            if value is not None:
                endpoint(value)
        if status == "M" and (old["path"] != new["path"] or old == new):
            raise ValueError("modified path must retain name and change blob or mode")
        if status == "R" and old["path"] == new["path"]:
            raise ValueError("rename requires both distinct endpoints")
        for p in {v["path"] for v in (old, new) if v is not None}:
            if p in selected:
                raise ValueError(f"duplicate changed path: {p}")
            selected[p] = record
    return selected


def pr_paths(root, commit, base, head):
    identity = candidate(root, commit)
    oid(base)
    oid(head)
    parents = git(root, "show", "-s", "--format=%P", commit).decode().strip().split()
    if parents != [base, head]:
        raise ValueError("PR candidate parents do not match fixed B and triggering head")
    # No base checkout/code: raw -z object diff includes mode-only changes and both
    # rename endpoints. Git owns rename recognition; the planner only unions paths.
    raw = git(root, "diff", "--raw", "-z", "--no-abbrev", "--no-ext-diff", "--no-textconv", "--find-renames", base, commit, "--")
    fields = raw.split(b"\0")
    if fields.pop() != b"":
        raise ValueError("unterminated NUL Git diff")
    changes, i = [], 0
    while i < len(fields):
        meta = fields[i].decode("ascii").split()
        i += 1
        if len(meta) != 5 or not meta[0].startswith(":"):
            raise ValueError("invalid raw Git diff metadata")
        old_mode, new_mode, old_oid, new_oid, status = meta
        old_mode = old_mode[1:]
        old_path = fields[i].decode("utf-8")
        i += 1
        new_path = old_path
        if status.startswith("R"):
            new_path = fields[i].decode("utf-8")
            i += 1
            status = "R"
        changes.append({"status": status,
                        "old": None if status == "A" else {"path": old_path, "mode": old_mode, "oid": old_oid},
                        "new": None if status == "D" else {"path": new_path, "mode": new_mode, "oid": new_oid}})
    data = {"schema_version": 1, "mode": "pr", "candidate": identity, "base": base, "head": head,
            "complete": True, "change_count": len(changes), "changes": changes}
    change_paths(data)
    return data


def make_plan(root, commit, changes_file):
    data = strict_json(changes_file)
    exact(data, {"schema_version", "mode", "candidate", "base", "head", "complete", "change_count", "changes"}, "changed scope")
    if type(data["schema_version"]) is not int or data["schema_version"] != 1 or data["mode"] not in {"current", "pr"}:
        raise ValueError("invalid changed scope version/mode")
    exact(data["candidate"], {"commit", "tree"}, "candidate")
    paths = change_paths(data)
    if data["candidate"] != candidate(root, commit):
        raise ValueError("changed scope candidate identity mismatch")
    if data["mode"] == "current":
        if data["base"] is not None or data["head"] is not None:
            raise ValueError("current scope must not contain base/head")
    else:
        actual = pr_paths(root, commit, data["base"], data["head"])
        key = lambda row: json.dumps(row, sort_keys=True, ensure_ascii=True)
        if sorted(map(key, actual["changes"])) != sorted(map(key, data["changes"])):
            raise ValueError("incomplete or mismatched PR changed-path list")
    tree = tree_entries(root, data["candidate"]["tree"])
    for record in data["changes"]:
        new, old = record["new"], record["old"]
        if new is not None and tree.get(new["path"]) != {k: new[k] for k in ("mode", "oid")}:
            raise ValueError(f"{new['path']}: endpoint does not match candidate")
        if record["status"] in {"D", "R"} and old["path"] in tree:
            raise ValueError(f"{old['path']}: removed endpoint still exists")
    raw = git(root, "show", commit + ":" + FILEMAP)
    manifest = load_filemap(raw)
    resources = {r["id"]: r for r in manifest["resources"]}
    entries = [(glob(e["pattern"]), e) for e in manifest["files"]]
    def match(p):
        matches = [e for g, e in entries if g.fullmatch(p)]
        if len(matches) != 1:
            raise ValueError(f"{p}: FILEMAP match count {len(matches)}; patterns={[e['pattern'] for e in matches]}")
        return matches[0]
    # Declaration references must be registered candidate files, never neighboring
    # files discovered by suffix, runtime, calls, or host state.
    for resource in resources.values():
        for p in [resource["owner"], *resource["materials"]]:
            path(p)
            if p not in tree or tree[p]["mode"] not in {"100644", "100755"}:
                raise ValueError(f"{resource['id']}: missing resource owner/material {p}")
            match(p)
    scope, required = [], set()
    for p in sorted(paths):
        entry = match(p)
        if entry["runtime_disposition"] == "run-local":
            raise ValueError(f"{p}: run-local path cannot be a committed change")
        required.update(entry["require"])
        scope.append({"path": p, "pattern": entry["pattern"], "require": entry["require"]})
    selected = closure(resources, required)
    active = [resources[r] for r in selected if data["mode"] == "pr" or resources[r]["stage"] != "delta"]
    union = lambda key: sorted({v for r in active for v in r[key]}, key=ordinal)
    stages = {stage: {"resources": [r["id"] for r in active if r["stage"] == stage],
                      "status": "not-applicable" if stage == "delta" and data["mode"] == "current" else
                      "required" if any(r["stage"] == stage for r in active) else "not-required"} for stage in STAGES}
    return {"schema_version": 1, "status": "planned", "mode": data["mode"], "candidate": data["candidate"],
            "base": data["base"], "head": data["head"], "filemap_sha256": hashlib.sha256(raw).hexdigest(),
            "scope_sha256": hashlib.sha256(json.dumps(data, sort_keys=True, ensure_ascii=True, separators=(",", ":")).encode()).hexdigest(),
            "paths": scope, "declared_require": sorted(required), "resources": selected,
            "selected_stages": [s for s in STAGES if stages[s]["status"] == "required"], "stages": stages,
            "tools": union("tools"), "cache_layers": union("cache_layers"), "materials": union("materials")}


def no_work(plan, stage=None):
    if stage is not None and plan["stages"][stage]["status"] != "not-required":
        raise ValueError(f"{stage}: nonempty or inapplicable stage cannot be not-required")
    if stage is None and plan["resources"]:
        raise ValueError("nonempty resource plan cannot be not-required")
    return {"schema_version": 1, "status": "not-required", "exit": 0, "stage": stage,
            "candidate": plan["candidate"], "mode": plan["mode"], "base": plan["base"], "head": plan["head"],
            "filemap_sha256": plan["filemap_sha256"], "scope_sha256": plan["scope_sha256"],
            "paths": plan["paths"], "resources": plan["resources"], "stages": plan["stages"],
            "executed": [], "artifacts": []}


def write(file, value):
    if file is None:
        raise ValueError("--output is required")
    file.parent.mkdir(parents=True, exist_ok=True)
    temporary = file.with_name(file.name + ".tmp")
    temporary.write_text(json.dumps(value, sort_keys=True, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    temporary.replace(file)


def command(args):
    if args.command == "pr-paths":
        value = pr_paths(args.repository, args.commit, args.base, args.head)
    else:
        if args.changes is None:
            raise ValueError("--changes complete manifest is required")
        value = make_plan(args.repository, args.commit, args.changes)
        if args.command != "plan":
            if args.plan is None or not same_record(strict_json(args.plan), value):
                raise ValueError("missing, failed, or mismatched plan")
            if args.command == "validate-plan":
                return value
            value = no_work(value, args.stage)
            if args.command == "validate-no-work":
                if args.result is None or not same_record(strict_json(args.result), value):
                    raise ValueError("malformed or mismatched no-resource result")
                return value
    write(args.output, value)
    return value
