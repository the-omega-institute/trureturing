#!/usr/bin/env python3
"""On-demand observations of a finite compiler declaration graph, never admission."""
from collections import deque
import argparse
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[4]
SCHEMA = "compiled-dependencies-v1"


class RequestError(ValueError):
    pass


def validate_request(query):
    if not isinstance(query, dict) or set(query) != {"revision", "domain", "targets"}:
        raise RequestError("REQUEST_FIELDS: revision, domain and targets are required")
    if not isinstance(query["revision"], str) or not re.fullmatch("[0-9a-f]{40}", query["revision"]):
        raise RequestError("REVISION: expected a full commit SHA")
    domain = query["domain"]
    if not isinstance(domain, dict) or set(domain) != {"modules", "complete"}:
        raise RequestError("DOMAIN: explicit modules and complete are required")
    if type(domain["complete"]) is not bool:
        raise RequestError("DOMAIN_COMPLETE: expected boolean")
    for key, names in [("MODULES", domain["modules"]), ("TARGETS", query["targets"])]:
        if not isinstance(names, list) or not names or any(not isinstance(n, str) for n in names):
            raise RequestError(key + ": expected a nonempty name list")
        if len(set(names)) != len(names):
            raise RequestError(key + ": duplicate name")
        for name in names:
            if not all(part and all(c.isalnum() or c in "_'" for c in part)
                       for part in name.split(".")):
                raise RequestError(key + ": invalid name")
    return query


def paths(graph, root):
    """Positive-length reachability; only domain vertices have outgoing edges."""
    found = {}
    pending = deque([(root, [root])])
    visited = {root}
    while pending:
        node, path = pending.popleft()
        for target in sorted(graph.get(node, [])):
            if target in visited:
                continue
            visited.add(target)
            found[target] = path + [target]
            pending.append((target, path + [target]))
    return found


def relations(graph, names):
    forward = {n: paths(graph, n) for n in names}
    reverse = {n: [] for n in names}
    direct_reverse = {n: [] for n in names}
    for source in names:
        for target in forward[source]:
            if target in reverse:
                reverse[target].append(source)
        for target in graph.get(source, []):
            if target in direct_reverse:
                direct_reverse[target].append(source)
    return {n: {"forward": {"direct": sorted(set(graph.get(n, []))),
                            "transitive": sorted(forward[n])},
                "reverse": {"direct": sorted(direct_reverse[n]),
                            "transitive": sorted(reverse[n])}}
            for n in names}, forward


def summarize(raw, query, acquisition):
    validate_request(query)
    gaps = []

    def gap(code, subject):
        gaps.append({"code": code, "subject": subject})

    if not query["domain"]["complete"]:
        gap("USER_DOMAIN_INCOMPLETE", "caller did not declare the module list complete")
    if not acquisition.get("complete", False):
        gap("ACQUISITION_INCOMPLETE", acquisition["status"])
    modules = {m["module"]: m for m in raw["modules"]}
    declarations = {}
    for name in query["domain"]["modules"]:
        module = modules.get(name)
        if module is None or module["status"] != "ok":
            gap("MISSING_MODULE", name)
            continue
        for row in module["declarations"]:
            if row["name"] in declarations:
                gap("DUPLICATE_DECLARATION", row["name"])
            declarations[row["name"]] = dict(row)
            if row["value"] is None and row["kind"] in ("definition", "theorem", "opaque"):
                gap("MISSING_REQUIRED_VALUE", row["name"])
    for target in query["targets"]:
        if target not in declarations:
            gap("UNKNOWN_DECLARATION", target)
    complete = not gaps
    names = sorted(declarations)
    graphs = {side: {n: declarations[n][side] or [] for n in names} for side in ("type", "value")}
    edges = {side: relations(graphs[side], names) for side in graphs}
    for name, row in declarations.items():
        for side in graphs:
            available = row[side] is not None
            row[side] = {"status": "observed" if available else "no_value",
                         "complete": complete,
                         "forward": edges[side][0][name]["forward"] if available else None,
                         "reverse": edges[side][0][name]["reverse"]}
    module_names = sorted(query["domain"]["modules"])
    import_graph = {n: modules.get(n, {}).get("imports", []) for n in module_names}
    imports, _ = relations(import_graph, module_names)
    queries = []
    for target in query["targets"]:
        row = declarations.get(target)
        users = [] if row is None else sorted(n for n in names
            if declarations[n]["module"] != row["module"] and
            not declarations[n]["private"] and not declarations[n]["internal"] and
            declarations[n]["kind"] in ("theorem", "definition", "opaque") and
            target in edges["value"][1][n])
        queries.append({"target": target, "status": "complete" if complete else "incomplete",
                        "external_value_users": users,
                        "external_value_user_count": len(users) if complete else None,
                        "value_paths": {n: edges["value"][1][n][target] for n in users}})
    boundary = sorted({target for graph in graphs.values() for targets in graph.values()
                       for target in targets if target not in declarations})
    return {"schema": SCHEMA, "revision": query["revision"], "domain": query["domain"],
            "complete": complete, "gaps": gaps, "acquisition": acquisition,
            "path_scope": "intermediate declarations in domain modules only",
            "semantics": {
                "direct": "one raw constant occurrence edge; imports are separate module edges",
                "transitive": "positive-length paths of the same edge kind, excluding self",
                "reverse": "sources in domain that reach this declaration or module",
                "type": "compiled type constants plus constructors for inductives",
                "value": "raw proof or definition expression constants, without reduction or dead-term removal",
                "external_users": "public non-internal theorem/definition/opaque declarations in other domain modules; private and generated intermediates remain in paths",
                "boundary": "out-of-domain constants are unexpanded terminals; no whole-repository claim",
                "not_a_judge": "not live-path, irreplaceability, escape-witness, research-value or admission evidence"},
            "boundary_constants": boundary,
            "declarations": [declarations[n] for n in names],
            "modules": [{"module": n, "status": modules.get(n, {}).get("status", "missing"),
                         "detail": modules.get(n, {}).get("detail"),
                         "complete": complete, "imports": imports[n]} for n in module_names],
            "queries": queries}


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def acquire(query, no_build):
    empty = {"modules": []}
    acquisition = {"status": "missing_artifacts", "complete": False}
    head = git("rev-parse", "HEAD")
    acquisition["head"] = head
    if head != query["revision"]:
        acquisition["status"] = "revision_mismatch"
        return empty, acquisition
    if not no_build:
        targets = ["leanInspector/dependencyReadout", *query["domain"]["modules"]]
        command = ["make", "--no-print-directory", "-C", str(ROOT), "lean",
                   "LEAN_TARGETS=" + " ".join(targets)]
        built = subprocess.run(command, stdout=sys.stderr, stderr=sys.stderr)
        acquisition["build_exit"] = built.returncode
        if built.returncode:
            acquisition["status"] = "build_failed"
            return empty, acquisition
    program = ROOT / ".lake/build/lean-inspector/producer/bin/dependencyReadout"
    stamp = ROOT / ".lake/.stratalint-lean-cache-stamp.json"
    if not program.is_file() or not stamp.is_file():
        return empty, acquisition
    with tempfile.TemporaryDirectory(prefix="compiled-dependencies-", dir=ROOT / ".lake") as temporary:
        directory = Path(temporary)
        source, destination = directory / "request.json", directory / "raw.json"
        source.write_text(json.dumps({"modules": query["domain"]["modules"]}))
        command = ["lake", "-d", "tools/lean-inspector-reg", "env", str(program),
                   str(source), str(destination)]
        if not no_build:
            command = ["/bin/bash", str(ROOT / "tools/scripts/worktree/lean-cache-run.sh"), *command]
        read = subprocess.run(command, cwd=ROOT, stdout=sys.stderr, stderr=sys.stderr)
        acquisition["reader_exit"] = read.returncode
        if read.returncode or not destination.is_file():
            acquisition["status"] = "reader_failed"
            return empty, acquisition
        raw = json.loads(destination.read_text())
    # A HEAD label alone does not identify modified mathematical/compiler inputs.
    changed = set(git("diff", "HEAD", "--name-only").splitlines())
    changed.update(git("ls-files", "--others", "--exclude-standard").splitlines())
    source_changes = sorted(p for p in changed if p.endswith(".lean") or
                            Path(p).name in ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain"))
    acquisition["modified_source_inputs"] = source_changes
    if git("rev-parse", "HEAD") != head:
        acquisition["status"] = "revision_changed"
    elif no_build:
        acquisition["status"] = "freshness_unverified"
    elif source_changes:
        acquisition["status"] = "source_revision_modified"
    else:
        acquisition.update(status="built", complete=True)
    return raw, acquisition


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true",
                        help="read available artifacts without ensuring freshness; never claims completeness")
    args = parser.parse_args()
    query = None
    try:
        query = validate_request(json.load(sys.stdin))
        raw, acquisition = acquire(query, args.no_build)
        result = summarize(raw, query, acquisition)
        print(json.dumps(result, ensure_ascii=False, sort_keys=True))
        return 0 if result["complete"] else 2
    except (RequestError, ValueError, OSError, subprocess.SubprocessError) as error:
        if query is not None:
            result = summarize({"modules": []}, query,
                               {"status": "runtime_unavailable", "complete": False,
                                "detail": str(error)})
        else:
            result = {"schema": SCHEMA, "complete": False,
                      "gaps": [{"code": "INVALID_REQUEST", "subject": str(error)}]}
        print(json.dumps(result, ensure_ascii=False, sort_keys=True))
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
