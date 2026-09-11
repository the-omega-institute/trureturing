"""Real olean negatives for the streaming ownership and scope boundary."""

import json
import os
import pathlib
import shutil
import subprocess
import sys

from phases import enumerate_domain, external_graph, read, write
from resources import run
from streaming import enumerate_oleans, freshness

PREFIX = "LeanInformationAudit.Tests.Census.Query."
COMMAND = "LeanInformationAudit.Census.Command"


def name_key(text):
    result = "n0"
    for part in text.split("."):
        result = f"ns({result},{len(part.encode('utf-8'))}:{part})"
    return result


def key(module, declaration, number=0):
    return [PREFIX + module, name_key(PREFIX + declaration), "sha256:" + format(number, "064x")]


def lean_env(repository):
    env = json.loads(subprocess.check_output(["lake", "env", sys.executable, "-c",
        "import os,json;print(json.dumps(dict(os.environ)))"], cwd=repository))
    env["LEAN_NUM_THREADS"] = "1"
    env["LEAN_SRC_PATH"] = str(repository / "tools/lean-inspector") + os.pathsep + str(repository)
    return env


def lean(repository, directory, program, args, label, env):
    binary = shutil.which("lean", path=env["PATH"])
    if program in ("scan.lean", "membership.lean"):
        from native import build
        native = build(repository, program, env)
        result = run([str(native), *map(str, args)], directory, label, cwd=repository, env=env,
                     budget_gb=1 if program == "scan.lean" else 0.5)
        if program == "scan.lean":
            from extraction import detached_records
            path = pathlib.Path(args[2])
            temporary = path.with_suffix(".finished")
            with path.open() as source, temporary.open("wb") as out:
                from streaming import canonical
                for row in detached_records(source, lambda module: "tools/lean-inspector/" +
                        module.replace(".", "/") + ".lean"):
                    out.write(canonical(row))
            os.replace(temporary, path)
            from extraction import add_collision_identities
            add_collision_identities(repository, path, read(args[0]), pathlib.Path(args[1]),
                lambda module: "tools/lean-inspector/" + module.replace(".", "/") + ".lean", env)
        return result
    return run([binary, "-DmaxRecDepth=100000", "-DmaxHeartbeats=0", "--run",
                str(repository / "tools/lean-inspector/Census" / program), *map(str, args)],
               directory, label, cwd=repository, env=env)


def prepare(repository, directory):
    directory.mkdir(parents=True, exist_ok=True)
    env = lean_env(repository)
    enumerate_domain(repository, directory)
    keys = [key("StreamingTarget", "StreamingTarget.target"),
            key("DuplicateLeft", "shared", 1), key("DuplicateRight", "shared", 2),
            key("StatementLeft", "statement_shared", 3), key("StatementRight", "statement_shared", 4)]
    write(directory / "request.json", {"keys": keys})
    lean(repository, directory, "scan.lean", [directory / "manifest.json", directory / "request.json",
                                            directory / "index.jsonl"], "fixture_index", env)
    write(directory / "membership-request.json", {})
    # The same compiler metadata resolver used by the production pipeline.
    old = os.environ.copy()
    try:
        os.environ.update(env)
        external_graph(directory)
    finally:
        os.environ.clear()
        os.environ.update(old)
    write(directory / "external.json", read(directory / "membership-request.json")["external_graph"])


def membership_case(repository, directory, label, roots, keys, discovery=None):
    request = {"keys": keys, "roots": [["Fixture.Root", roots]],
        "assignment": {row[0]: "Fixture.Root" for row in keys},
        "discovery_roots": discovery if discovery is not None else [PREFIX + "StreamingTarget", COMMAND],
        "external_graph": read(directory / "external.json")}
    input_path, output_path = directory / (label + ".input.json"), directory / (label + ".json")
    write(input_path, request)
    lean(repository, directory, "membership.lean", [directory / "index.jsonl", input_path, output_path],
         label, lean_env(repository))
    result = read(output_path)
    result["rows"] = [json.loads(line) for line in pathlib.Path(str(output_path) + ".rows.jsonl").open()]
    result["scopes"] = [[root, [result["module_names"][i] for i in indices]] for root, indices in result["scopes"]]
    from incremental import BATCH_KEY_BOUND, BATCH_MODULE_BOUND
    result["batch_module_bound"] = BATCH_MODULE_BOUND
    result["batch_key_bound"] = BATCH_KEY_BOUND
    # This small fixture view also serves the independent candidate command.
    write(output_path, result)
    return result


def truth_export_identity(repository, directory):
    identity = directory / "identity.json"
    driver = directory / "Identity.lean"
    driver.write_text("import LeanInformationAudit.Census.Report\n" +
        "#eval IO.FS.writeFile " + json.dumps(str(identity)) +
        " LeanInformationAudit.DispositionCensus.truthExportIdentity.compress\n")
    run(["lake", "env", "lean", str(driver)], directory, "identity", cwd=repository, env=lean_env(repository))
    return read(identity)


def validate_control(repository, directory):
    import hashlib
    env = lean_env(repository)
    identity = truth_export_identity(repository, directory)
    target = key("StreamingTarget", "StreamingTarget.target")
    report = dict(identity, source_commit="fixture-head", nodes=[{
        "repo_path": target[0].replace(".", "/") + ".lean", "freeze_status": "frozen",
        "declarations": [{"kind": "theorem", "declaration_name_key": target[1], "statement_id": target[2]}]}])
    report_path = directory / "control-report.json"
    write(report_path, report)
    request = directory / "control-request.json"
    write(request, {"head": "fixture-head", "keys": [target], "report": str(report_path),
                    "report_sha256": "sha256:" + hashlib.sha256(report_path.read_bytes()).hexdigest()})
    output = directory / "control-candidate.json"
    driver = directory / "Control.lean"
    driver.write_text("import " + COMMAND + "\nimport " + PREFIX + "StreamingOutside\n" +
        "#census_validate " + json.dumps(str(request)) + " using " +
        json.dumps(str(directory / "inside_scope.json")) + " output " + json.dumps(str(output)) + "\n")
    run(["lake", "env", "lean", "-DmaxRecDepth=100000", "-DmaxHeartbeats=0", str(driver)],
        directory, "candidate_control", cwd=repository, env=env)
    rows = read(output)["entries"]
    assert len(rows) == 1 and rows[0]["class"] == "unreachable", "streamCandidateValidationControl"
    return {"name": "single_environment_candidate_control", "status": "passed", "certified": 1}


def check_case(repository, directory, case):
    target = key("StreamingTarget", "StreamingTarget.target")
    if case == "ownership_collision":
        keys = [key("DuplicateLeft", "shared", 1), key("DuplicateRight", "shared", 2)]
        result = membership_case(repository, directory, case, [row[0] for row in keys] + [COMMAND], keys)
        assert len(result["errors"]) == 2 and all("IE-C035" in e["error"] for e in result["errors"]), "streamOwnershipCollision"
        assert all(not row["payload"]["query_completed"] for row in result["rows"]), "streamOwnershipCollision"
    elif case == "statement_collision":
        keys = []
        for line in (directory / "index.jsonl").open():
            row = json.loads(line)
            if row["module"] in [PREFIX + "StatementLeft", PREFIX + "StatementRight"]:
                for owner in row["owners"]:
                    keys.append([row["module"], name_key(PREFIX + "statement_shared"), owner["statement_id"]])
        assert len(keys) == 2, "streamStatementCollisionPositive"
        result = membership_case(repository, directory, case, [k[0] for k in keys] + [COMMAND], keys)
        assert not result["errors"] and len(result["rows"]) == 2, "streamStatementCollisionPositive"
        assert all(c["resolved_by_statement"] for c in result["collisions"]), "streamStatementCollisionPositive"
        assert all(r["payload"]["query_completed"] for r in result["rows"]), "streamStatementCollisionPositive"
    elif case == "unclassifiable_named_key":
        result = membership_case(repository, directory, case, [PREFIX + "StreamingUnknown", COMMAND], [target])
        assert any("unclassifiable_named_key" in e["error"] for e in result["errors"]), "streamUnclassifiableNamedKey"
        assert not result["candidate_keys"] and not result["rows"][0]["payload"]["query_completed"], "streamUnclassifiableNamedKey"
    elif case == "out_of_scope":
        result = membership_case(repository, directory, case, [target[0], COMMAND], [target])
        assert not result["candidate_keys"] and not result["errors"], "streamOutOfScopeEvidence"
        assert result["rows"][0]["payload"]["query_completed"], "streamOutOfScopeEvidence"
        control = membership_case(repository, directory, "inside_scope", [PREFIX + "StreamingOutside", COMMAND], [target])
        assert control["candidate_keys"] == [target] and not control["errors"], "streamInsideScopeControl"
    elif case == "missing_olean":
        folder = directory / "missing"
        folder.mkdir(exist_ok=True)
        try:
            enumerate_oleans(folder, {"Fixture.Missing": "Fixture/Missing.lean"})
        except ValueError as error:
            assert "IE-C044 missing olean" in str(error), "streamMissingOlean"
        else:
            raise AssertionError("streamMissingOlean")
    elif case == "stale_olean":
        folder = directory / "stale"
        folder.mkdir(exist_ok=True)
        source, olean = folder / "Fresh.lean", folder / ".lake/build/lib/lean/Fresh.olean"
        env = lean_env(repository)
        (folder / "lean-toolchain").write_bytes((repository / "lean-toolchain").read_bytes())
        (folder / "lakefile.toml").write_text('name = "census_stale_fixture"\ndefaultTargets = ["Fresh"]\n[[lean_lib]]\nname = "Fresh"\n')
        (folder / "Makefile").write_text("lean:\n\tlake build\n")
        source.write_text("theorem fresh : True := True.intro\n")
        run(["make", "lean"], folder, "valid", cwd=folder, env=env, budget_gb=None)
        original = olean.read_bytes()
        source.write_text('def fresh : Nat := "edited without rebuilding"\n')
        try:
            freshness(lambda command, label: run(command, folder, label, cwd=folder, env=env, budget_gb=None))
        except RuntimeError:
            assert "error:" in (folder / "lake_freshness.log").read_text(), "streamFreshnessGate"
        else:
            raise AssertionError("streamFreshnessGate: stale olean accepted after edited source failed Lake")
        assert not olean.exists() or olean.read_bytes() == original, "streamFreshnessGate"
    else:
        raise ValueError(case)
    return {"name": case, "status": "passed"}


def check_manifest_negatives(repository, directory):
    # The old per-partition transport fixtures are retired with that transport.
    return [check_case(repository, directory, case) for case in
            ("stale_olean", "missing_olean", "ownership_collision", "statement_collision",
             "unclassifiable_named_key", "out_of_scope")]


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=pathlib.Path, required=True)
    parser.add_argument("--case", required=True)
    options = parser.parse_args()
    repository = pathlib.Path(__file__).resolve().parents[3]
    print(check_case(repository, options.directory, options.case))
