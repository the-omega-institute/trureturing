"""Executed regressions for the PR #6660 blind-review findings."""

import copy
import json
import os
import pathlib
import shutil
import sys
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
from negative_fixtures import COMMAND, PREFIX, key, lean, lean_env, truth_export_identity
from phases import read, write
from resources import run
from streaming import canonical


def collision_setup(repository, directory, label):
    folder = directory / label
    folder.mkdir(parents=True)
    keys = []
    for line in (directory / "index.jsonl").open():
        row = json.loads(line)
        if row["module"] in [PREFIX + "StatementLeft", PREFIX + "StatementRight"]:
            for owner in row["owners"]:
                keys.append([row["module"], key("", "statement_shared")[1], owner["statement_id"]])
    assert len(keys) == 2
    evidence = "LeanInformationAudit.Tests.Census.Evidence"
    request = {"keys": keys, "roots": [[k[0], [k[0], COMMAND, evidence]] for k in keys],
               "assignment": {k[0]: k[0] for k in keys}, "discovery_roots": [COMMAND],
               "external_graph": read(directory / "external.json")}
    write(folder / "membership-request.json", request)
    lean(repository, folder, "membership.lean", [directory / "index.jsonl",
         folder / "membership-request.json", folder / "membership.json"], "membership", lean_env(repository))
    metadata = read(folder / "membership.json")
    assert metadata["candidate_keys"] == keys and not metadata["errors"], "realMembershipCollisionCandidates"
    report = dict(truth_export_identity(repository, directory), source_commit="fixture-head", nodes=[{
        "repo_path": k[0].replace(".", "/") + ".lean", "freeze_status": "frozen", "declarations": [{
            "kind": "theorem", "declaration_name_key": k[1], "statement_id": k[2]}]} for k in keys])
    write(folder / "report.json", report)
    request = {"head": "fixture-head", "keys": keys, "report": str(folder / "report.json"), "report_sha256": "parent"}
    return folder, metadata, request


def candidate_arm(repository, directory, folder, metadata, request, cache, before=None):
    from validation import prepare, run_batches
    for name in ["domain.json", "olean-hashes.json"]:
        shutil.copyfile(directory / name, folder / name)
    plan = prepare(repository, folder, metadata, request, cache=cache)
    if before:
        before(plan)
    env = lean_env(repository)
    def step(command, label, **kwargs):
        return run(command, folder, label, cwd=repository, env=env, **kwargs)
    result, receipt = run_batches(repository, folder, metadata, request, plan, step,
                                 shutil.which("lean", path=env["PATH"]))
    return result, receipt, plan


def colliding_owners(repository, directory):
    folder, metadata, request = collision_setup(repository, directory, "collision-default")
    def isolated(plan):
        assert plan["bound"] == 5600 and len(plan["planned"]) == 2, "candidateNameIsolation"
        for batch in plan["planned"]:
            assert len({key[0] for key in batch["keys"]}) == 1, "candidateNameIsolation"
    cold, receipt, plan = candidate_arm(repository, directory, folder, metadata, request, folder / "cache", isolated)
    assert len(receipt["executions"]) == 2 and len(cold["entries"]) == 2, "candidateNameIsolation"
    warm_folder = folder / "warm"
    warm_folder.mkdir()
    warm, replay, warm_plan = candidate_arm(repository, directory, warm_folder, metadata, request, folder / "cache", isolated)
    assert not replay["executions"] and len(warm_plan["hits"]) == 2, "candidateNameIsolation"
    assert sorted(cold["entries"], key=lambda e: e["statement_id"]) == sorted(warm["entries"], key=lambda e: e["statement_id"]), "candidateNameIsolation"
    result = {"name": "colliding_owners_default_bound_cold_warm", "check": "candidateNameIsolation", "status": "passed",
              "bound": plan["bound"], "real_membership": True, "cold_batches": 2, "warm_hits": 2,
              "environment_modules": [e["receipt"]["environment_modules"] for e in receipt["executions"]]}
    write(folder / "result.json", result)
    return result


def named_ballast(repository, directory):
    folder, metadata, request = collision_setup(repository, directory, "named-ballast")
    metadata["candidate_keys"] = metadata["candidate_keys"][:1]
    request["keys"] = request["keys"][:1]
    values, sizes = [], []
    for count in [0, 20000]:
        arm = folder / str(count)
        arm.mkdir()
        padded = copy.deepcopy(metadata)
        padded["named"].extend({"module": "Outside.Ballast", "name": ["num", ["anonymous"], i],
            "head": "LeanInformationAudit.BoundedTruncationFamily", "mode": "support"} for i in range(count))
        value, _, plan = candidate_arm(repository, directory, arm, padded, request, arm / "cache")
        index = read(arm / "batches/0000/index.json")
        scopes = set().union(*(set(scope) for _, scope in index["scopes"]))
        assert all(e["module"] in scopes for e in index["named"]), "batchScopedNamedEvidence"
        values.append(value["entries"])
        sizes.append(len(canonical(index["named"])))
    assert values[0] == values[1] and sizes[0] == sizes[1], "batchScopedNamedEvidence"
    result = {"name": "out_of_scope_named_evidence_ballast", "check": "batchScopedNamedEvidence", "status": "passed",
              "outside_entries": 20000, "serialized_named_bytes": sizes, "identical_rows": True}
    write(folder / "result.json", result)
    return result


def nested_scope(repository, directory):
    folder = directory / "nested-scope"
    folder.mkdir(parents=True)
    env = lean_env(repository)
    env["LEAN_PATH"] = str(folder) + os.pathsep + env["LEAN_PATH"]
    owner = '''import LeanInformationAudit.Census.Query
open Lean LeanInformationAudit DispositionCensus
open D5.S3.ConceptDynamics.InformationEscape
namespace ReviewScope
 theorem target : True := True.intro
 def family : BoundedTruncationFamily True where
   arena := fun _ => Arena.ofFintype Bool
   approximation := fun _ => True
   restrict := fun _ h => h
 theorem comparison : True → family.approximation 1 := fun h => h
 def disposition : AnalysisDisposition ⟨``target, "scope-identity"⟩ :=
   .boundedFiniteTruncation {
     truncationFamily := ``family
     bound := 1
     comparisonStatement := ``comparison
     certification := .transferred `ReviewScope.transfer }
end ReviewScope
'''
    donor = '''import ReviewOwner
namespace ReviewScope
 theorem transfer : family.approximation 1 → True := fun h => h
 theorem peer : True := True.intro
end ReviewScope
'''
    binary = shutil.which("lean", path=env["PATH"])
    for name, text in [("ReviewOwner", owner), ("ReviewDonor", donor)]:
        path = folder / (name + ".lean")
        path.write_text(text)
        run([binary, "-R", str(folder), "-o", str(folder / (name + ".olean")), str(path)], folder,
            name, cwd=repository, env=env, budget_gb=None)
    outputs = []
    for label, imports in [("combined", ["ReviewOwner", "ReviewDonor"]), ("split", ["ReviewOwner"])]:
        destination = folder / (label + ".json")
        driver = folder / (label + ".lean")
        driver.write_text("".join("import " + m + "\n" for m in imports) + '''
open Lean Meta Elab Command LeanInformationAudit
run_cmd liftTermElabM do
  let index ← CensusQuery.indexScope `ReviewOwner
  let mut verdict := "certified"
  try
    discard <| CensusQuery.assess index "fixture-head" ⟨`ReviewScope.target, "scope-identity"⟩
  catch error =>
    verdict ← error.toMessageData.toString
  IO.FS.writeFile ''' + json.dumps(str(destination)) + ''' (toJson verdict).compress
''')
        run([binary, "-R", str(folder), str(driver)], folder, label, cwd=repository, env=env)
        outputs.append(read(destination))
    # A separate key in the donor root is a positive scope-membership control.
    control = folder / "control.lean"
    control.write_text('''import ReviewDonor
open Lean Meta Elab Command LeanInformationAudit
run_cmd liftTermElabM do
  let index ← CensusQuery.indexScope `ReviewDonor
  let .certified (.boundedFiniteTruncation _) ←
    CensusQuery.assess index "fixture-head" ⟨`ReviewScope.target, "scope-identity"⟩
      | throwError "nestedEvidenceInsideScopeControl"
  let .certified (.boundedFiniteTruncation _) ← CensusQuery.assess index "fixture-head" ⟨`ReviewScope.peer, "peer"⟩
      | throwError "nestedEvidencePeerControl"
''')
    run([binary, "-R", str(folder), str(control)], folder, "inside-control", cwd=repository, env=env)
    assert all("transfer_theorem.root_membership" in verdict for verdict in outputs), "nestedEvidenceRootScope"
    assert outputs[0] == outputs[1], "nestedEvidenceRootScope"
    result = {"name": "cross_root_nested_transfer_same_verdict", "check": "nestedEvidenceRootScope", "status": "passed",
              "combined": outputs[0], "split": outputs[1], "inside_scope_control": True}
    write(folder / "result.json", result)
    return result


def receipt_controls(repository, directory):
    from receipt_fixtures import check_receipts
    return {"controls": check_receipts(repository, directory)}


def receipt_sensitivity(repository, directory):
    import receipt_fixtures
    # This is the reviewer's exact mutation: run the fresh scan, skip comparison.
    with patch.object(receipt_fixtures, "replay", side_effect=lambda scan, expected: (scan(), "match")[1]):
        try:
            receipt_fixtures.check_receipts(repository, directory)
        except AssertionError as error:
            assert "streamReceiptReplayMismatch" in str(error), str(error)
        else:
            raise AssertionError("streamReceiptReplayMismatch: fixture survived disabled comparison")
    return {"name": "receipt_negative_requires_replay_comparison", "check": "streamReceiptReplayMismatch", "status": "passed"}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=pathlib.Path, required=True)
    parser.add_argument("--case", required=True, choices=["colliding_owners", "named_ballast", "nested_scope", "receipt_sensitivity", "receipt_controls"])
    args = parser.parse_args()
    repository = pathlib.Path(__file__).resolve().parents[4]
    print(json.dumps(globals()[args.case](repository, args.directory)))
