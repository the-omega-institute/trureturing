"""Plan bounded imports, reuse per-key assessments, and bind batch receipts."""

import hashlib
import json
import pathlib
import subprocess

from incremental import BATCH_KEY_BOUND, BATCH_MODULE_BOUND, atomic_json, candidate_batches, module_digests, validation_key
from streaming import canonical, closure, digest

COMMAND = "LeanInformationAudit.Census.Command"


def prepare(repository, directory, membership, request, *, bound=BATCH_MODULE_BOUND, cache=None):
    def read(name):
        return json.loads((directory / name).read_bytes())
    graph = dict(membership["external_graph"])
    for row in membership["headers"]:
        graph[row["module"]] = [e["module"] for e in row["imports"]]
    names = membership["module_names"]
    scopes = {root: [names[i] for i in indices] for root, indices in membership["scopes"]}
    hashes = module_digests(read("olean-hashes.json"))
    domain = read("domain.json")
    programs = subprocess.check_output(["git", "ls-files", "-z", "--", "tools/lean-inspector"], cwd=repository)
    sources = [repository / p.decode() for p in programs.split(b"\0") if p]
    query_digest = digest([(str(p.relative_to(repository)), hashlib.sha256(p.read_bytes()).hexdigest())
                          for p in sources if p.suffix in (".lean", ".py")])
    toolchain = digest([(repository / "lean-toolchain").read_text(),
                        (repository / "lake-manifest.json").read_text()])
    imports, addresses, source_hashes = {}, {}, {}
    cache = cache or repository / ".lake/build/census/validation"
    keys_by_id = {key[2]: key for key in membership["candidate_keys"]}

    def inputs_for(key):
        # Only one key's dependency digest lists are transient. Keeping those
        # lists for every candidate would duplicate graph-sized data per key.
        owner = key[0]
        root = membership["assignment"][owner]
        scope = set(scopes[root])
        evidence = sorted(scope.intersection(membership["evidence_modules"]) |
                          {e["module"] for e in membership["named"] if e["module"] in scope})
        imports[owner] = sorted({owner, COMMAND, *evidence})
        # Dependencies can change while an importing module's serialized bytes
        # stay equal. Bind the actual project closure, plus pinned upstreams.
        owner_inputs = [[m, hashes[m]] for m in closure(graph, [owner]) if m in hashes]
        evidence_inputs = [[m, hashes[m]] for m in closure(graph, evidence) if m in hashes]
        for module in evidence:
            if module in hashes and module not in source_hashes:
                source_hashes[module] = hashlib.sha256((repository / domain[module]).read_bytes()).hexdigest()
        source_inputs = [[m, source_hashes[m]] for m in evidence if m in hashes]
        input_scope = digest([root, scopes[root], source_inputs])
        return {"key": key, "owner_olean": hashes[owner], "owner_inputs": owner_inputs,
            "evidence_inputs": evidence_inputs, "toolchain": toolchain, "query_source": query_digest,
            "scope": input_scope, "source_inputs": source_inputs}

    hits, missing, entries, source_inputs = [], [], [], []
    for key in membership["candidate_keys"]:
        inputs = inputs_for(key)
        addresses[key[2]] = validation_key(key, digest(inputs["owner_inputs"]), inputs["evidence_inputs"],
                                         toolchain, query_digest, inputs["scope"])
        path = cache / (addresses[key[2]][7:] + ".json")
        if path.is_file():
            value = json.loads(path.read_bytes())
            if value["inputs"] != inputs or value["row"]["statement_id"] != key[2]:
                raise ValueError("IE-C044 validation cache input binding mismatch")
            hits.append(key)
            entries.append(value["row"])
            source_inputs.extend(value["source_inputs"])
        else:
            missing.append(key)
    # The receipt's logical batches cover every key, independent of cache warmth.
    planned = candidate_batches(membership["candidate_keys"], imports, graph, bound)
    return {"planned": planned, "execute": candidate_batches(missing, imports, graph, bound), "bound": bound,
            "key_bound": BATCH_KEY_BOUND,
            "hits": hits, "misses": missing, "entries": entries, "source_inputs": source_inputs,
            "addresses": addresses, "inputs_for": inputs_for, "keys_by_id": keys_by_id,
            "cache": cache, "scopes": scopes}


def run_batches(repository, directory, membership, request, plan, step, lean_binary):
    from report_stream import fields
    executions = []
    for number, batch in enumerate(plan["execute"]):
        folder = directory / "batches" / f"{number:04d}"
        folder.mkdir(parents=True)
        owners = {key[0] for key in batch["keys"]}
        wanted = {key[2] for key in batch["keys"]}
        selected, report = [], {}
        for field, node in fields(request["report"]):
            if field != "nodes":
                report[field] = node
                continue
            declarations = [d for d in node["declarations"] if d["statement_id"] in wanted]
            if declarations:
                selected.append(dict(node, declarations=declarations))
        report["nodes"] = selected
        report_path = folder / "report.json"
        atomic_json(report_path, report)
        batch_request = dict(request, keys=batch["keys"], report=str(report_path),
                             report_sha256="sha256:" + hashlib.sha256(report_path.read_bytes()).hexdigest())
        atomic_json(folder / "request.json", batch_request)
        roots = {membership["assignment"][owner] for owner in owners}
        batch_scope = set().union(*(set(plan["scopes"][root]) for root in roots))
        named = [entry for entry in membership["named"] if entry["module"] in batch_scope]
        atomic_json(folder / "index.json", {"candidate_keys": batch["keys"], "named": named,
            "assignment": {owner: membership["assignment"][owner] for owner in owners},
            "scopes": [[root, plan["scopes"][root]] for root in sorted(roots)],
            "batch_module_bound": plan["bound"], "batch_key_bound": plan["key_bound"]})
        output = folder / "candidates.json"
        driver = folder / "Candidates.lean"
        driver.write_text("".join("import " + module + "\n" for module in batch["imports"]) +
            "#census_validate " + json.dumps(str(folder / "request.json")) + " using " +
            json.dumps(str(folder / "index.json")) + " output " + json.dumps(str(output)) + "\n")
        step([lean_binary, "-DmaxRecDepth=100000", "-DmaxHeartbeats=0", str(driver)],
             f"candidate_environment_{number:04d}", design_limit_gb=4)
        value = json.loads(output.read_bytes())
        receipt = json.loads(pathlib.Path(str(output) + ".receipt.json").read_bytes())
        if (receipt["rows_sha256"] != "sha256:" + hashlib.sha256(output.read_bytes()).hexdigest()
                or receipt["head"] != request["head"]
                or receipt["report_sha256"] != batch_request["report_sha256"]
                or value["environment_modules"] > plan["bound"]
                or len(value["entries"]) > plan["key_bound"]):
            raise ValueError("IE-C044 candidate batch receipt mismatch or module bound exceeded")
        if sorted(row["statement_id"] for row in value["entries"]) != sorted(wanted):
            raise ValueError("IE-C044 candidate batch does not cover its requested keys")
        keyed_sources = dict(value["key_source_inputs"])
        if set(keyed_sources) != wanted:
            raise ValueError("IE-C044 candidate provenance does not cover its requested keys")
        for row in value["entries"]:
            identity = row["statement_id"]
            atomic_json(plan["cache"] / (plan["addresses"][identity][7:] + ".json"), {
                "inputs": plan["inputs_for"](plan["keys_by_id"][identity]),
                "row": row, "source_inputs": keyed_sources[identity]})
        plan["entries"].extend(value["entries"])
        plan["source_inputs"].extend(value["source_inputs"])
        executions.append({"keys": batch["keys"], "receipt": receipt})
    rows = sorted(plan["entries"], key=lambda row: row["statement_id"])
    sources = {canonical(source): source for source in plan["source_inputs"]}
    result = {"entries": rows, "source_inputs": [sources[k] for k in sorted(sources)]}
    atomic_json(directory / "candidates.json", result)
    record = {"hits": len(plan["hits"]), "misses": len(plan["misses"]),
              "revalidated_keys": plan["misses"], "executions": executions,
              "receipt": {"bound": plan["bound"], "key_bound": plan["key_bound"], "batches": plan["planned"],
                "cache_keys": sorted(plan["addresses"].items()),
                "result_sha256": digest(result)}}
    atomic_json(directory / "validation.json", record)
    return result, record
