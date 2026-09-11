"""Manifest and row binding attacks through the actual data-only publisher."""

import copy
import json
import os
import pathlib
import re

from Certificate.emission import manifest_source, bucket_sources, string, write_module
from pipeline import frozen_keys
from resources import run


def reseal(rows_path, receipt_path, report_path):
    """Synthetic negative authorities; never used by publication itself."""
    import hashlib
    from streaming import canonical, digest
    receipt = json.loads(receipt_path.read_bytes())
    report = json.loads(report_path.read_bytes())
    report_sha = "sha256:" + hashlib.sha256(report_path.read_bytes()).hexdigest()
    row_sha = "sha256:" + hashlib.sha256(rows_path.read_bytes()).hexdigest()
    inputs = receipt["inputs"]
    inputs.update(head=report["source_commit"], export_sha256=report_sha)
    programs = dict(inputs["programs"])
    emitter = digest([(name, programs["tools/lean-inspector/Census/" + name][7:])
                      for name in ["phases.py", "emission_cache.py", "streaming.py"]])
    inputs["expanded_rows_cache_key"] = digest([row_sha, inputs["module_names"], inputs["scopes"], emitter])
    inputs["rows"] = {"artifact": "rows.jsonl", "sha256": row_sha}
    receipt.update(digest=digest(inputs), rows_sha256=row_sha)
    receipt_path.write_bytes(canonical(receipt))
    return receipt["digest"]


def prepare_publication(repository, directory):
    import argparse
    from negative_fixtures import name_key, truth_export_identity
    from pipeline import execute
    from Certificate.handoff import file_digest
    identity = truth_export_identity(repository, directory)
    source = "LeanInformationAudit.Tests.Census.Query.Observed"
    finite = "LeanInformationAudit.Tests.SealSuccess"
    report = dict(identity, source_commit="fixture-head", nodes=[])
    for module, declaration, number in [(source, source + ".independent", 1),
                                        (finite, finite + ".idTheorem", 0)]:
        report["nodes"].append({"repo_path": module.replace(".", "/") + ".lean",
            "freeze_status": "frozen", "declarations": [{"kind": "theorem",
            "declaration_name_key": name_key(declaration), "statement_id": "sha256:" + format(number, "064x")}]})
    report["nodes"].append({"repo_path": "LeanInformationAudit/Tests/Census/Evidence.lean",
                            "freeze_status": "frozen", "declarations": []})
    report_path = directory / "report.json"
    report_path.write_text(json.dumps(report) + "\n")
    root = directory / "first"
    assert execute(argparse.Namespace(output=str(root), fixture_truth_export=str(report_path),
        lean_report=str(repository / ".lake/build/stratalint/raw-lean-report.json"),
        prefix="LeanInformationAudit", replay_of=None, no_structure=False)) == 0
    assert (root / "publication.json").is_file(), "wholeStreamPipelinePublication"
    structure = json.loads((root / "census-structure.json").read_bytes())
    assert structure["census_sha256"] == file_digest(root / "census.json"), "publicationPreservesCensusBytes"
    assert len(structure["rows"]) == 2, "wholeStreamPipelineStructure"
    state = json.loads((root / "run.json").read_bytes())
    assert state["publication"]["census_json_unchanged_by_publication"], "publicationPreservesCensusBytes"
    original = json.loads((root / "census.json").read_bytes())
    published = json.loads((root / "publication.json").read_bytes())
    assert len(original["rows"]) == state["publication"]["accounted"], "wholeStreamPublicationHandoff"
    assert "rows" not in published, "publicationReadsCompactRows"
    assert published["query_receipt_digest"] == json.loads((root / "receipt.json").read_bytes())["digest"]
    assert published["certificate"]["axioms"] == ["propext"]
    probe = write_module(root, "Absent", "import Lean\nimport CensusRun.Root\nopen Lean Elab Command\n"
        "run_cmd do\n  if (<- getEnv).contains\n"
        "      `LeanInformationAudit.Tests.Census.Query.Observed.independent then\n"
        "    throwError \"observed theorem imported by publication\"\n")
    run(["lake", "env", "lean", str(probe)], directory / "first-absent", "process",
        cwd=repository, env=dict(os.environ, LEAN_PATH=str(root), LEAN_NUM_THREADS="1"))
    second = root / "publication-second.json"
    driver = (root / "CensusPublish/Root.lean").read_text()
    second_driver = write_module(root, "SecondPublication", driver.replace(
        string(str(root / "publication.json")), string(str(second))))
    expanded = root / "census.json"
    held = root / "census.held"
    expanded.rename(held)
    try:
        run(["lake", "env", "lean", str(second_driver)], directory / "second", "process",
            cwd=repository, env=dict(os.environ, LEAN_PATH=str(root), LEAN_NUM_THREADS="1"))
    finally:
        held.rename(expanded)
    assert second.read_bytes() == (root / "publication.json").read_bytes(), "artifact_determinism"
    run(["lake", "env", "lean", str(probe)], directory / "second-absent", "process",
        cwd=repository, env=dict(os.environ, LEAN_PATH=str(root), LEAN_NUM_THREADS="1"))
    partial = directory / "partial-certified"
    assert execute(argparse.Namespace(output=str(partial), fixture_truth_export=str(report_path),
        lean_report=str(repository / ".lake/build/stratalint/raw-lean-report.json"),
        prefix=finite, replay_of=None, no_structure=True)) == 2
    summary = json.loads((partial / "census.json.summary.json").read_bytes())
    assert summary["status"] == "partial" and summary["requested_keys"] == 2
    assert summary["counts"]["accounted"] == summary["counts"]["certified"] == 1
    assert summary["counts"]["observed"] == 0 and summary["certified_complete"] is False


def check_publication_negatives(repository, directory, only=None):
    root = directory / "first"
    source = root / "CensusRun/Root.lean"
    original = {"CensusRun.Root": source.read_text()}
    original.update({"CensusRun." + p.stem: p.read_text() for p in source.parent.glob("Range*.lean")})

    def change(bundle, module, transform):
        return dict(bundle, **{module: transform(bundle[module])})

    def root_change(transform):
        return change(original, "CensusRun.Root", transform)

    def bucket_change(transform, bundle=None):
        return change(original if bundle is None else bundle, "CensusRun.Range8_0", transform)
    driver = root / "CensusPublish/Root.lean"
    # These attacks supply edited reviewable sources. The production generate
    # mode emits its sources during the single guarded compact-row handoff.
    original_driver = driver.read_text().replace(" generate certificate ", " certificate ")
    response = root / "rows.jsonl"
    receipt_path = root / "receipt.json"
    receipt_bytes = receipt_path.read_bytes()
    pristine = response.read_bytes()
    data = {"rows": [json.loads(line) for line in pristine.splitlines()]}
    report_path = directory / "report.json"
    report_bytes = report_path.read_bytes()
    report = json.loads(report_bytes)
    digest = json.loads((root / "census.json.summary.json").read_text())["report_sha256"]
    observed_index = next(i for i, row in enumerate(data["rows"]) if row["class"] == "observed")
    env = dict(os.environ, LEAN_PATH=str(root), LEAN_NUM_THREADS="1")
    outcomes = []

    def rejected(label, expected, *, text=original, transport=None, driver_text=original_driver,
                 report_data=None):
        if only is not None and label not in only:
            return
        output = directory / (label + ".json")
        for module, contents in text.items():
            write_module(root, module, contents)
        driver.write_text(driver_text.replace(string(str(root / "publication.json")), string(str(output))))
        if transport is not None:
            from streaming import canonical
            response.write_bytes(b"".join(canonical(row) for row in transport["rows"]))
        if report_data is not None:
            report_path.write_text(json.dumps(report_data) + "\n")
        if label != "observedRelabelledCertified" and (transport is not None or report_data is not None):
            from Certificate.publication_fixtures import reseal
            new_digest = reseal(response, receipt_path, report_path)
            driver.write_text(re.sub(r'receipt_digest "[^"]+"',
                'receipt_digest ' + string(new_digest), driver.read_text()))
        try:
            run(["lake", "env", "lean", "-DmaxRecDepth=100000", "-DmaxHeartbeats=0",
                 "-R", str(root), str(driver)], directory / label, "process", cwd=repository, env=env)
        except RuntimeError:
            log = (directory / label / "process.log").read_text()
            assert expected in log, label + ": " + log
            assert not output.exists(), "rejected manifest produced an artifact"
            outcomes.append({"name": label, "diagnostic": expected, "status": "rejected"})
        else:
            raise AssertionError(label + " was accepted")
        finally:
            for module, contents in original.items():
                write_module(root, module, contents)
            driver.write_text(original_driver)
            response.write_bytes(pristine)
            receipt_path.write_bytes(receipt_bytes)
            report_path.write_bytes(report_bytes)

    def source_for(transport):
        rows = transport["rows"]
        return dict(bucket_sources(rows, frozen_keys(report)), **{"CensusRun.Root":
            manifest_source(rows, frozen_keys(report), report["source_commit"], digest, "CensusRun.Root")})

    rejected("manifestDetachedFromRows", "component=manifest_keys",
             text=root_change(lambda text: text.replace("keys := CensusRun.manifestKeys", "keys := []", 1)))
    deleted = copy.deepcopy(data)
    deleted["rows"].pop(observed_index)
    rejected("deletedManifestRow", "IE-C034", text=source_for(deleted), transport=deleted)
    duplicated = copy.deepcopy(data)
    other = copy.deepcopy(duplicated["rows"][observed_index])
    other["theorem_name"] = ["str", ["anonymous"], "DifferentName"]
    duplicated["rows"].append(other)
    rejected("duplicateIdDifferentName", "IE-C035", transport=duplicated)
    malformed_report = copy.deepcopy(report)
    next(node for node in malformed_report["nodes"] if node["declarations"])["declarations"][0][
        "statement_id"] = "sha256:" + "0" * 63
    rejected("publisherInventoryDuplicateBeforeMalformedReport", "IE-C035",
             transport=duplicated, report_data=malformed_report)
    wrong_nat = bucket_change(lambda text: re.sub(r"(CensusRun.Range8_0.manifestKeys.chunk0 : Nat := )(0x[0-9a-f]+)",
                       lambda m: m[1] + hex(int(m[2], 0) + 1), text, count=1), source_for(deleted))
    rejected("publisherNatBeforeMissingRow", "component=statement_id_nat",
             text=wrong_nat, transport=deleted)
    # Both 0 and 1 have valid distinct wire strings. Binding both to Nat 1 fails.
    rejected("sameNatDifferentWireRejected", "component=statement_id_nat",
             text=bucket_change(lambda text: re.sub(r"(CensusRun.Range8_0.manifestKeys.chunk0 : Nat := )(0x[0-9a-f]+)",
                         lambda m: m[1] + hex(int(m[2], 0) + 1), text, count=1)))
    rejected("edited-inventory-row", "component=statement_id_nat",
             text=bucket_change(lambda text: re.sub(r"(CensusRun.Range8_0.manifestKeys.chunk0 : Nat := )(0x[0-9a-f]+)",
                         lambda m: m[1] + hex(int(m[2], 0) + 99), text, count=1)))
    rejected("idPlacedInWrongBucket", "component=bucket_prefix",
             text=bucket_change(lambda text: re.sub(r"(CensusRun.Range8_0.manifestKeys.chunk0 : Nat := )(0x[0-9a-f]+)",
                         lambda m: m[1] + hex(int(m[2], 0) + 2 ** 248), text, count=1)))
    for label, wire in [
            ("uppercaseIdentity", "sha256:" + "A" * 64),
            ("shortIdentity", "sha256:" + "0" * 63),
            ("longIdentity", "sha256:" + "0" * 65),
            ("idAtOrAbove256Bits", "sha256:" + format(2 ** 256, "x")),
            ("missingPrefixIdentity", "0" * 64),
            ("signedIdentity", "sha256:+" + "0" * 63),
            ("whitespaceIdentity", "sha256:" + "0" * 64 + " ")]:
        malformed = copy.deepcopy(data)
        malformed["rows"][observed_index]["statement_id"] = wire
        rejected(label, "component=statement_id_format", transport=malformed)
    reflexive = root_change(lambda text: re.sub(
        r"(def CensusRun.reportKeys : List Nat := )[^\n]+", r"\1CensusRun.manifestKeys", text))
    rejected("reflexiveReportRejected", "component=report_keys_binding", text=reflexive)
    rejected("reflexiveReportNameRejected", "component=report_keys_binding", driver_text=original_driver.replace(
        "report_keys CensusRun.reportKeys", "report_keys CensusRun.manifestKeys"))
    rejected("wrongChunkArity", "component=report_keys_binding", text=bucket_change(lambda text: re.sub(
        r"decodeIds (\d+) CensusRun.Range8_0.reportKeys.chunk0",
        lambda m: f"decodeIds {int(m[1]) - 1} CensusRun.Range8_0.reportKeys.chunk0", text, count=1)))
    relabelled = copy.deepcopy(data)
    certified = next(row for row in data["rows"] if row["class"] != "observed")
    relabelled["rows"][observed_index]["class"] = certified["class"]
    relabelled["rows"][observed_index]["payload"] = certified["payload"]
    rejected("observedRelabelledCertified", "whole_stream_rows_binding", transport=relabelled)
    rejected("staleManifestHead", "component=head",
             text=root_change(lambda text: text.replace('headSha := "fixture-head"', 'headSha := "stale"', 1)))
    rejected("wrongManifestDigest", "component=report_sha256",
             text=root_change(lambda text: text.replace('reportSha256 := ' + string(digest), 'reportSha256 := "wrong"', 1)))
    artifact = json.loads((root / "census.json").read_text())
    assert any(row["statement_id"] == "sha256:" + "0" * 64 for row in artifact["rows"])
    outcomes.append({"name": "leadingZeroIdentity", "status": "preserved"})
    outcomes.append({"name": "noncomputableDataBound", "status": "accepted"})
    rejected("chunkMovedBetweenSides", "component=report_keys_binding", text=bucket_change(lambda text: re.sub(
        r"decodeIds (\d+) CensusRun.Range8_0.reportKeys.chunk0", r"decodeIds \1 CensusRun.Range8_0.manifestKeys.chunk0", text)))
    rejected("chunkDuplicatedBetweenSides", "component=report_keys_binding", text=bucket_change(lambda text: re.sub(
        r"decodeIds (\d+) CensusRun.Range8_0.reportKeys.chunk0",
        r"decodeIds \1 CensusRun.Range8_0.reportKeys.chunk0, decodeIds \1 CensusRun.Range8_0.manifestKeys.chunk0", text)))
    (directory / "negative-fixtures.json").write_text(json.dumps(outcomes, indent=2) + "\n")
    return outcomes
