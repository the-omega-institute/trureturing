"""Real olean ballast and real sequential Environment batch controls."""

import json
import pathlib
import shutil
import sys

from phases import read, write
from resources import run
from streaming import canonical, closure
from negative_fixtures import COMMAND, PREFIX, key, lean_env, truth_export_identity


def non_evidence(repository, directory, request=None):
    from native import build
    env = lean_env(repository)
    binary = build(repository, "scan.lean", env)
    folder = directory / "non-evidence"
    folder.mkdir(parents=True)
    generator = folder / "Generate.lean"
    generator.write_text('''import Lean
open Lean
def main (args : List String) : IO Unit := do
  let [path, amount] := args | throw <| IO.userError "path count"
  let mut constants : Array ConstantInfo := #[]
  for i in [:amount.toNat!] do
    constants := constants.push (.defnInfo {
      name := .num `Noise i, levelParams := [], type := mkConst ``Nat,
      value := mkNatLit i, hints := .abbrev, safety := .safe })
  let data : ModuleData := { (default : ModuleData) with
    constNames := constants.map (·.name), constants }
  saveModuleData path `Fixture.Noise data
''')
    # Both arms scan the same real domain. File size alone is not a proxy for
    # the reader's maximum active working set; measure the actual index peak.
    manifest = read(directory / "manifest.json")
    ballast = folder / "Noise.olean"
    measurements = []
    for count in [0, 50000]:
        label = f"constants-{count}"
        run([shutil.which("lean", path=env["PATH"]), "--run", str(generator), str(ballast), str(count)],
            folder, label + "-generate", cwd=repository, env=env, budget_gb=None)
        # Exercise the complete production index, including compact ownership
        # hashing in its parent process. Both arms use isolated cold caches.
        arm = folder / label
        arm.mkdir()
        from streaming import file_stamp, hash_inputs
        inputs = read(directory / "inputs.json") + [["Fixture.Noise", "base", str(ballast)]]
        write(arm / "manifest.json", manifest + [["Fixture.Noise", [str(ballast)]]])
        write(arm / "inputs.json", inputs)
        write(arm / "stamps.json", {path: file_stamp(path) for _, _, path in inputs})
        write(arm / "olean-hashes.json", read(directory / "olean-hashes.json") + hash_inputs(inputs[-1:]))
        write(arm / "domain.json", dict(read(directory / "domain.json"), **{"Fixture.Noise": "Fixture/Noise.lean"}))
        shutil.copyfile(request or directory / "request.json", arm / "request.json")
        measurement = run([sys.executable, str(repository / "tools/lean-inspector/Census/extraction.py"),
                           str(repository), str(arm), str(binary), str(arm / "cache")],
                          folder, label, cwd=repository, env=env, budget_gb=1)
        output = arm / "index.jsonl"
        for line in output.open():
            last = json.loads(line)
        assert last["named"] == [] and last["owners"] == [], "streamNonEvidenceConstantBound"
        measurements.append({"non_evidence_constants": count, "peak_rss_bytes": measurement["peak_rss_bytes"],
                             "wall_seconds": measurement["wall_seconds"], "index_bytes": output.stat().st_size})
    import filecmp
    assert filecmp.cmp(folder / "constants-0/index.jsonl", folder / "constants-50000/index.jsonl", shallow=False), "streamNonEvidenceConstantBound"
    result = {"name": "non_evidence_constants", "check": "streamNonEvidenceConstantBound", "status": "passed",
              "baseline_modules": len(manifest), "requested_keys": len(read(request or directory / "request.json")["keys"]),
              "measurements": measurements, "retained_bytes_identical": True,
              "peak_did_not_increase": measurements[1]["peak_rss_bytes"] <= measurements[0]["peak_rss_bytes"]}
    write(folder / "result.json", result)
    return result


def two_batches(repository, directory):
    from incremental import candidate_batches
    from validation import prepare, run_batches
    env = lean_env(repository)
    folder = directory / "two-batches"
    folder.mkdir()
    keys = [key("StatementLeft", "statement_shared", 31), key("StatementRight", "statement_shared", 32)]
    graph = dict(read(directory / "external.json"))
    headers = []
    for line in (directory / "index.jsonl").open():
        row = json.loads(line)
        graph[row["module"]] = [entry["module"] for entry in row["imports"]]
        headers.append({k: row[k] for k in ["module", "part", "imports"]})
    imports = {k[0]: [COMMAND, k[0]] for k in keys}
    bound = max(len(closure(graph, value)) for value in imports.values())
    batches = candidate_batches(keys, imports, graph, bound)
    assert len(batches) == 2, "streamTwoBatchBound"
    names = sorted(graph)
    indices = {name: i for i, name in enumerate(names)}
    metadata = {"candidate_keys": keys, "external_graph": sorted(graph.items()), "headers": headers,
                "module_names": names, "assignment": {k[0]: k[0] for k in keys},
                "scopes": [[k[0], sorted(indices[n] for n in closure(graph, imports[k[0]]))] for k in keys],
                "evidence_modules": [], "named": []}
    report = dict(truth_export_identity(repository, directory),
              source_commit="fixture-head", nodes=[
                  {"repo_path": k[0].replace(".", "/") + ".lean", "freeze_status": "frozen",
                   "declarations": [{"kind": "theorem", "declaration_name_key": k[1], "statement_id": k[2]}]}
                  for k in keys])
    write(folder / "report.json", report)
    for name in ["domain.json", "olean-hashes.json"]:
        shutil.copyfile(directory / name, folder / name)
    request = {"head": "fixture-head", "keys": keys, "report": str(folder / "report.json"), "report_sha256": "unused-parent"}
    plan = prepare(repository, folder, metadata, request, bound=bound, cache=folder / "cache")
    assert len(plan["execute"]) == 2, "streamTwoBatchBound"
    def step(command, label, **kwargs):
        return run(command, folder, label, cwd=repository, env=env, **kwargs)
    result, record = run_batches(repository, folder, metadata, request, plan, step,
                                shutil.which("lean", path=env["PATH"]))
    assert len(result["entries"]) == 2 and len(record["executions"]) == 2, "streamTwoBatchBound"
    assert all(e["receipt"]["environment_modules"] <= bound for e in record["executions"]), "streamTwoBatchBound"
    return {"name": "two_candidate_batches", "check": "streamTwoBatchBound", "status": "passed",
            "bound": bound, "count": 2, "environment_modules": [e["receipt"]["environment_modules"] for e in record["executions"]]}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description="Measure non-evidence ballast against a completed census run")
    parser.add_argument("--directory", required=True, type=pathlib.Path)
    parser.add_argument("--request", type=pathlib.Path)
    options = parser.parse_args()
    print(json.dumps(non_evidence(pathlib.Path(__file__).resolve().parents[3], options.directory, options.request)))
