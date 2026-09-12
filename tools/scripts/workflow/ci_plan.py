"""FILEMAP declarations and complete path planning for ci.py; never executes work."""
import hashlib
import base64
import functools
import json
import os
import pathlib
import re
import stat
import subprocess
import tomllib

STAGES = ("build", "engineering", "current", "delta")
TOOLS = {"bash", "dotnet", "git", "lake", "make", "python3"}
CACHES = {"dependency", "project", "report", "judge", "elan", "engineering", "current"}
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


ZERO_OID = "0" * 40


def event_oid(value, allow_zero=False):
    if not isinstance(value, str) or not re.fullmatch(r"[0-9a-f]{40}", value):
        raise ValueError("push event endpoint must be a 40-hex object identity")
    if value == ZERO_OID and not allow_zero:
        raise ValueError("push event endpoint must be nonzero")
    return value


def native_push():
    workflow_candidate = os.environ.get("CI_WORKFLOW_CANDIDATE_SHA", "")
    if workflow_candidate:
        oid(workflow_candidate)
    return os.environ.get("GITHUB_EVENT_NAME") == "push" and not workflow_candidate


def push_endpoints(before=None, after=None):
    """The event owns native endpoints; explicit local ranges have no event."""
    fixed = None
    if native_push():
        event_path = os.environ.get("GITHUB_EVENT_PATH")
        if not event_path:
            raise ValueError("native push requires the actual fixed event input")
        event = strict_json(pathlib.Path(event_path))
        if not isinstance(event, dict):
            raise ValueError("native push event must be an object")
        fixed = (event_oid(event.get("before"), allow_zero=True), event_oid(event.get("after")))
    # Supplied copies may agree with the event, but cannot replace it. Do not
    # combine a partial CLI pair with a partial environment pair.
    for p, h in ((before, after), (os.environ.get("CI_PUSH_BEFORE"), os.environ.get("CI_PUSH_AFTER"))):
        if not p and not h:
            continue
        pair = (event_oid(p, allow_zero=True), event_oid(h))
        if fixed is not None and pair != fixed:
            raise ValueError("push endpoints differ from the fixed event or explicit input")
        fixed = pair
    return fixed


def git(root, *args):
    # Missing objects are input failures, including in partial clones. Planning
    # must never turn an object read into an implicit fetch from a remote.
    return subprocess.run(["git", "--no-replace-objects", *args], cwd=root, check=True, capture_output=True,
                          env={**os.environ, "GIT_NO_LAZY_FETCH": "1", "GIT_OPTIONAL_LOCKS": "0"}).stdout


@functools.cache
def commit_tree(root, commit):
    # Share only immutable object reads within this one-shot planner process.
    # HEAD, status, index and working file bytes must always be read afresh.
    oid(commit)
    if git(root, "cat-file", "-t", commit).strip() != b"commit":
        raise ValueError("candidate must be a commit")
    return oid(git(root, "rev-parse", commit + "^{tree}").decode().strip())


def candidate(root, commit):
    return {"commit": commit, "tree": commit_tree(root, commit)}


@functools.cache
def committed_file(root, commit, file):
    return git(root, "show", oid(commit) + ":" + path(file))


def checked_head(root, expected=""):
    commit = oid(git(root, "rev-parse", "--verify", "HEAD").decode().strip())
    if expected and oid(expected) != commit:
        raise ValueError("stage checkout does not match fixed candidate")
    return commit


def strict_json(file):
    return strict_json_bytes(file.read_bytes())


def strict_json_bytes(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError(f"duplicate JSON field: {key}")
            result[key] = value
        return result
    def invalid(value):
        raise ValueError(f"invalid JSON constant: {value}")
    return json.loads(raw.decode("utf-8"), object_pairs_hook=pairs, parse_constant=invalid)


def same_record(left, right):
    # Python equality aliases false/0 and true/1; JSON protocol fields do not.
    return json.dumps(left, sort_keys=True, ensure_ascii=True) == json.dumps(right, sort_keys=True, ensure_ascii=True)


@functools.cache
def tree_bytes(root, tree):
    return git(root, "ls-tree", "-rz", "--full-tree", oid(tree))


def tree_entries(root, tree):
    # Each caller owns its mutable entries, including any dirty push overlay.
    result = {}
    for record in nul_fields(tree_bytes(root, tree)):
        meta, raw_path = record.split(b"\t", 1)
        mode, kind, blob = meta.decode("ascii").split(" ")
        result[path(raw_path.decode("utf-8"))] = {"mode": mode, "oid": oid(blob)}
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


def nul_fields(raw):
    if not raw:
        return []
    if not raw.endswith(b"\0"):
        raise ValueError("unterminated NUL Git input")
    return raw.split(b"\0")[:-1]


def diff_paths(root, base, commit):
    # No base checkout/code: raw -z object diff includes mode-only changes and both
    # rename endpoints. Git owns rename recognition; the planner only unions paths.
    raw = git(root, "diff", "--raw", "-z", "--no-abbrev", "--no-ext-diff", "--no-textconv", "--find-renames", base, commit, "--")
    fields = nul_fields(raw)
    changes, i = [], 0
    while i < len(fields):
        meta = fields[i].decode("ascii").split()
        i += 1
        if len(meta) != 5 or not meta[0].startswith(":") or i >= len(fields):
            raise ValueError("invalid raw Git diff metadata")
        old_mode, new_mode, old_oid, new_oid, status = meta
        old_mode = old_mode[1:]
        old_path = fields[i].decode("utf-8")
        i += 1
        new_path = old_path
        if status.startswith("R"):
            if not re.fullmatch(r"R[0-9]{1,3}", status) or int(status[1:]) > 100 or i >= len(fields):
                raise ValueError("invalid raw Git rename endpoints")
            new_path = fields[i].decode("utf-8")
            i += 1
            status = "R"
        changes.append({"status": status,
                        "old": None if status == "A" else {"path": old_path, "mode": old_mode, "oid": old_oid},
                        "new": None if status == "D" else {"path": new_path, "mode": new_mode, "oid": new_oid}})
    return changes


def blob_oid(raw):
    return hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + b"\0" + raw).hexdigest()


def worktree_entries(root):
    # Same effective input domain as the native ReadCurrent: indexed paths plus
    # nonignored untracked files, reading working bytes (never staged blob bytes).
    paths = set()
    for record in nul_fields(git(root, "ls-files", "--stage", "-z")):
        meta, raw_path = record.split(b"\t", 1)
        mode, _, stage = meta.decode("ascii").split()
        p = path(raw_path.decode("utf-8"))
        if stage != "0" or mode not in {"100644", "100755"}:
            raise ValueError(f"{p}: unresolved or non-regular index entry")
        paths.add(p)
    paths.update(path(p.decode("utf-8")) for p in nul_fields(git(root, "ls-files", "--others", "--exclude-standard", "-z")))
    entries = {}
    for p in sorted(paths):
        file = root / p
        try:
            mode = file.lstat().st_mode
        except FileNotFoundError:
            continue
        if not stat.S_ISREG(mode):
            raise ValueError(f"{p}: non-regular working-tree input")
        raw = file.read_bytes()
        entries[p] = {"mode": "100755" if mode & 0o111 else "100644",
                      "oid": blob_oid(raw)}
    return entries


def entry_changes(before, after):
    # Local renames are represented by their deletion/addition endpoints; no
    # second rename analyzer or selector. FILEMAP consumes both paths as usual.
    return [{"status": "A" if p not in before else "D" if p not in after else "M",
             "old": {"path": p, **before[p]} if p in before else None,
             "new": {"path": p, **after[p]} if p in after else None}
            for p in sorted(before.keys() | after.keys()) if before.get(p) != after.get(p)]


def local_paths(root, commit, before=None):
    identity = candidate(root, commit)
    effective = worktree_entries(root)
    worktree = entry_changes(tree_entries(root, identity["tree"]), effective)
    if before is None:
        # HEAD is not passing-check evidence. Without an explicit complete range,
        # select every current input, plus removed dirty endpoints for ownership.
        changes = entry_changes({}, effective) + [row for row in worktree if row["new"] is None]
    else:
        changes = entry_changes(tree_entries(root, commit_tree(root, oid(before))), effective)
    origin = {"kind": "local-current-input" if before is None else "local-range", "before": before, "after": commit,
              "worktree": worktree}
    data = {"schema_version": 1, "mode": "push", "candidate": {"commit": commit, "tree": None},
            "base": None, "head": None, "origin": origin,
            "complete": True, "change_count": len(changes), "changes": changes}
    change_paths(data)
    return data


def push_paths(root, commit, before, after):
    """Plan the complete immutable push range supplied by the event."""
    commit = checked_head(root, commit)
    before = event_oid(before, allow_zero=True)
    after = event_oid(after)
    if after != commit:
        raise ValueError("push event after does not match checked-out HEAD")
    identity = candidate(root, after)
    if before == ZERO_OID:
        # A zero-before push is an explicit initial registered-current-input
        # mode.  It is not an empty diff and does not depend on H's parents.
        changes = [{"status": "A", "old": None, "new": {"path": p, **entry}}
                   for p, entry in tree_entries(root, identity["tree"]).items()]
        kind = "initial-registered-current-input"
    else:
        try:
            available = git(root, "cat-file", "-t", before).strip() == b"commit"
        except subprocess.SubprocessError as error:
            raise ValueError(f"PUSH_BEFORE_UNAVAILABLE: event.before {before} is unavailable") from error
        if not available:
            raise ValueError(f"PUSH_BEFORE_UNAVAILABLE: event.before {before} is not an available commit")
        changes = diff_paths(root, before, after)
        kind = "event-range"
    origin = {"kind": kind, "before": before, "after": after}
    data = {"schema_version": 1, "mode": "push", "candidate": identity, "base": None, "head": None,
            "origin": origin, "complete": True, "change_count": len(changes), "changes": changes}
    if git(root, "status", "--porcelain=v1", "-z", "--untracked-files=all"):
        raise ValueError("push checkout is dirty; event range must be evaluated against checked-out HEAD")
    change_paths(data)
    return data


def pr_paths(root, commit, base, head):
    identity = candidate(root, commit)
    oid(base)
    oid(head)
    parents = git(root, "show", "-s", "--format=%P", commit).decode().strip().split()
    if parents != list(dict.fromkeys([base, head])):
        raise ValueError("PR candidate parents do not match fixed B and triggering head")
    changes = diff_paths(root, base, commit)
    data = {"schema_version": 1, "mode": "pr", "candidate": identity, "base": base, "head": head,
            "complete": True, "change_count": len(changes), "changes": changes}
    change_paths(data)
    return data


def make_plan(root, commit, changes_file):
    data = strict_json(changes_file)
    push = isinstance(data, dict) and data.get("mode") == "push"
    exact(data, {"schema_version", "mode", "candidate", "base", "head", "complete", "change_count", "changes"}
          | ({"origin"} if push else set()), "changed scope")
    if type(data["schema_version"]) is not int or data["schema_version"] != 1 or data["mode"] not in {"current", "push", "pr"}:
        raise ValueError("invalid changed scope version/mode")
    exact(data["candidate"], {"commit", "tree"}, "candidate")
    paths = change_paths(data)
    actual = None
    if native_push():
        if not push:
            raise ValueError("native push requires its validated event endpoint origin")
        actual = push_paths(root, checked_head(root, commit), *push_endpoints())
        if not same_record(data["origin"], actual["origin"]):
            raise ValueError("native push origin differs from the fixed event input")
    elif push:
        origin = data["origin"]
        if not isinstance(origin, dict):
            raise ValueError("push origin must be an object")
        if origin.get("kind") in {"local-current-input", "local-range"}:
            actual = local_paths(root, checked_head(root, commit), origin.get("before"))
        else:
            actual = push_paths(root, checked_head(root, commit), origin.get("before"), origin.get("after"))
    if data["candidate"] != (actual["candidate"] if push else candidate(root, commit)):
        raise ValueError("changed scope candidate identity mismatch")
    if data["mode"] != "pr":
        if data["base"] is not None or data["head"] is not None:
            raise ValueError("current scope must not contain base/head")
    if push or data["mode"] == "pr":
        actual = actual if push else pr_paths(root, commit, data["base"], data["head"])
        if push and not same_record(data["origin"], actual["origin"]):
            raise ValueError("push origin does not match candidate's actual immutable event endpoints")
        key = lambda row: json.dumps(row, sort_keys=True, ensure_ascii=True)
        if sorted(map(key, actual["changes"])) != sorted(map(key, data["changes"])):
            raise ValueError(f"incomplete or mismatched {'push' if push else 'PR'} changed-path list")
    local = push and actual["origin"].get("kind") in {"local-current-input", "local-range"}
    tree = tree_entries(root, candidate(root, commit)["tree"])
    if local:
        for record in actual["origin"]["worktree"]:
            if record["new"] is None:
                tree.pop(record["old"]["path"])
            else:
                new = record["new"]
                tree[new["path"]] = {k: new[k] for k in ("mode", "oid")}
    for record in data["changes"]:
        new, old = record["new"], record["old"]
        if new is not None and tree.get(new["path"]) != {k: new[k] for k in ("mode", "oid")}:
            raise ValueError(f"{new['path']}: endpoint does not match candidate")
        if record["status"] in {"D", "R"} and old["path"] in tree:
            raise ValueError(f"{old['path']}: removed endpoint still exists")
    def read(p):
        if p not in tree:
            raise ValueError(f"{p}: missing registered candidate input")
        raw = (root / p).read_bytes() if local else committed_file(root, commit, p)
        if local and blob_oid(raw) != tree[p]["oid"]:
            raise ValueError(f"{p}: registered input differs from local candidate")
        return raw
    raw = read(FILEMAP)
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
                      "status": "not-applicable" if stage == "delta" and data["mode"] != "pr" else
                      "required" if any(r["stage"] == stage for r in active) else "not-required"} for stage in STAGES}
    execution = execution_selection(read, active, resources)
    return {"schema_version": 1, "status": "planned", "mode": data["mode"], "candidate": data["candidate"],
            **({"origin": data["origin"]} if push else {}),
            "base": data["base"], "head": data["head"], "filemap_sha256": hashlib.sha256(raw).hexdigest(),
            "scope_sha256": hashlib.sha256(json.dumps(data, sort_keys=True, ensure_ascii=True, separators=(",", ":")).encode()).hexdigest(),
            "paths": scope, "declared_require": sorted(required), "resources": selected,
            "selected_stages": [s for s in STAGES if stages[s]["status"] == "required"], "stages": stages,
            "tools": union("tools"), "cache_layers": union("cache_layers"), "materials": union("materials"), "execution": execution}


def execution_selection(read, active, resources):
    registration = "Meta/ci-resources.json"
    if not active:
        return {"projects": [], "checks": [], "steps": []}
    if not any(registration in row["materials"] for row in active):
        raise ValueError("missing declared resource execution manifest: " + registration)
    declarations = {registration, "Meta/engineering-projects.json", "Meta/ci-checks.json"}
    if not declarations <= {p for row in active for p in row["materials"]}:
        raise ValueError("resource plan lacks declared execution inputs")
    manifest = strict_json_bytes(read(registration))
    exact(manifest, {"schema", "resources"}, registration)
    if manifest["schema"] != "ci-resource-execution-v1":
        raise ValueError("invalid resource execution schema")
    rows = {}
    for row in manifest["resources"]:
        exact(row, {"id", "projects", "checks", "steps"}, registration)
        if row["id"] in rows or row["id"] not in resources:
            raise ValueError("unknown or duplicate resource execution: " + row["id"])
        for key in ("projects", "checks", "steps"):
            if not isinstance(row[key], list) or row[key] != sorted(set(row[key])):
                raise ValueError("resource execution requires sorted unique " + key)
        rows[row["id"]] = row
    if set(rows) != set(resources):
        raise ValueError("missing resource execution registration")
    registry = strict_json_bytes(read("Meta/engineering-projects.json"))
    projects = {row["path"]: row for row in registry["projects"]}
    checks = {row["id"]: row for row in strict_json_bytes(read("Meta/ci-checks.json"))["checks"]}
    selected_projects, selected_checks, steps = set(), set(), set()
    for resource in active:
        row = rows[resource["id"]]
        selected_projects.update(row["projects"])
        selected_checks.update(row["checks"])
        if resource["stage"] == "current":
            steps.update(row["steps"])
    for check in list(selected_checks):
        if check not in checks:
            raise ValueError("unregistered selected check: " + check)
        if any(item["artifact"] == "VerifiedScribeEmissions" for item in checks[check]["report_inputs"]):
            if "scribe-describe" not in selected_checks or "scribe" not in steps:
                raise ValueError("selected check requires declared Scribe producer: " + check)
    for check in selected_checks:
        if any(project not in projects for project in checks[check]["program_projects"]):
            raise ValueError("unregistered check program input: " + check)
        if checks[check]["report_inputs"] and "lean-report" not in steps:
            raise ValueError("selected check requires lean-report: " + check)
    # References are the only project closure authority. The compiler verifies these inputs.
    visited, dependencies, visiting = set(), set(), set()
    def visit(project):
        if project not in projects:
            raise ValueError("unregistered requested build root: " + project)
        if project in visiting:
            raise ValueError("cyclic project registration: " + project)
        if project in visited:
            return
        visiting.add(project)
        for ref in projects[project]["references"]:
            dependencies.add(ref)
            visit(ref)
        visiting.remove(project)
        visited.add(project)
    for project in list(selected_projects):
        visit(project)
    if "lean-report" in steps:
        steps.discard("lean")  # The report producer enters the Lean incremental path.
    order = ["lean", "lean-report", "scribe", "filemap", "check-current"]
    if steps - set(order):
        raise ValueError("unknown current step registration")
    return {"projects": sorted(selected_projects - dependencies), "checks": sorted(selected_checks),
            "steps": [step for step in order if step in steps]}


def no_work(plan, stage=None):
    if stage is not None and plan["stages"][stage]["status"] != "not-required":
        raise ValueError(f"{stage}: nonempty or inapplicable stage cannot be not-required")
    if stage is None and plan["resources"]:
        raise ValueError("nonempty resource plan cannot be not-required")
    return {"schema_version": 1, "status": "not-required", "exit": 0, "stage": stage,
            **({"origin": plan["origin"]} if plan["mode"] == "push" else {}),
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


def validate_plan(root, commit, plan, changes):
    if plan is None or changes is None:
        raise ValueError("missing plan or complete changed-path input")
    value = make_plan(root, commit, changes)
    if not same_record(strict_json(plan), value):
        raise ValueError("missing, failed, or mismatched plan")
    local = {endpoint["path"]: endpoint for row in value.get("origin", {}).get("worktree", [])
             if (endpoint := row["new"]) is not None}
    for material in sorted({FILEMAP, *value["materials"]}):
        raw = (root / material).read_bytes()
        # make_plan checked the complete effective scope. Dirty declarations are
        # bound by its local endpoints; unchanged declarations still bind HEAD.
        matches = (blob_oid(raw) == local[material]["oid"] if material in local else
                   raw == committed_file(root, commit, material))
        if not matches:
            raise ValueError("resource plan declaration differs from candidate: " + material)
    return value


def stage_requirements(root, plan, stage):
    if stage not in STAGES or plan["stages"][stage]["status"] == "not-applicable":
        raise ValueError("stage is not applicable to this plan: " + str(stage))
    manifest = load_filemap((root / FILEMAP).read_bytes())
    selected = set(plan["stages"][stage]["resources"])
    rows = [row for row in manifest["resources"] if row["id"] in selected]
    union = lambda key: sorted({item for row in rows for item in row[key]})
    return {"required": bool(rows), "tools": union("tools"), "cache_layers": union("cache_layers"),
            "materials": union("materials")}


def validate_stage(root, stage, base):
    if stage not in STAGES:
        raise ValueError("invalid execution stage")
    if stage == "delta":
        oid(base)
        if git(root, "cat-file", "-t", base).strip() != b"commit":
            raise ValueError("delta base must be an available commit object")
    elif base:
        raise ValueError("only delta accepts a base")


def plan_pr(root, commit, base, head):
    changes, plan = root / "build/ci/changes.json", root / "build/ci/plan.json"
    write(changes, pr_paths(root, commit, base, head))
    write(plan, make_plan(root, commit, changes))
    validate_plan(root, commit, plan, changes)
    return {"candidate_sha": commit, "base_sha": base,
            "changes_b64": base64.b64encode(changes.read_bytes()).decode("ascii"),
            "plan_b64": base64.b64encode(plan.read_bytes()).decode("ascii")}


def plan_push(root, commit="", plan=None, changes=None, before=None, after=None):
    commit = checked_head(root, commit)
    changes = changes or root / "build/ci/changes.json"
    plan = plan or root / "build/ci/plan.json"
    endpoints = push_endpoints(before, after)
    if native_push():
        value = push_paths(root, commit, *endpoints)
    else:
        if endpoints is not None and endpoints[1] != commit:
            raise ValueError("explicit local range after must match checked-out HEAD")
        value = local_paths(root, commit, None if endpoints is None or endpoints[0] == ZERO_OID else endpoints[0])
    write(changes, value)
    value = make_plan(root, commit, changes)
    write(plan, value)
    validate_plan(root, commit, plan, changes)
    return {"candidate_sha": commit, "origin": value["origin"], "complete": True}


def command(args):
    if args.command == "pr-paths":
        value = pr_paths(args.repository, args.commit, args.base, args.head)
    else:
        if args.changes is None:
            raise ValueError("--changes complete manifest is required")
        value = make_plan(args.repository, args.commit, args.changes) if args.command == "plan" else validate_plan(
            args.repository, args.commit, args.plan, args.changes)
        if args.command != "plan":
            if args.command == "validate-plan":
                return value
            value = no_work(value, args.stage)
            if args.command == "validate-no-work":
                if args.result is None or not same_record(strict_json(args.result), value):
                    raise ValueError("malformed or mismatched no-resource result")
                return value
    write(args.output, value)
    return value
