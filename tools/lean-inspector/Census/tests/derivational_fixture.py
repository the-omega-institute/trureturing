"""Noninterference on two real pipeline runs of the synthetic publication fixture."""

import argparse

from pipeline import execute
from phases import read, write
from Structure.derivational import publish
from Structure.sources import file_digest


def check_noninterference(repository, directory):
    without = directory / "first"  # prepare_publication runs the existing pipeline.
    with_step = directory / "with-derivational"
    assert execute(argparse.Namespace(output=str(with_step),
        fixture_truth_export=str(directory / "report.json"),
        lean_report=str(repository / ".lake/build/stratalint/raw-lean-report.json"),
        prefix="LeanInformationAudit", replay_of=None, no_structure=False)) == 0
    artifacts = ["census.json", "rows.jsonl", "census.json.summary.json",
                 "census-structure.json", "publication.json", "receipt.json"]
    before = {name: file_digest(with_step / name) for name in artifacts}
    publish(with_step)
    hashes = {}
    for name in artifacts:
        with (without / name).open("rb") as left, (with_step / name).open("rb") as right:
            while True:
                block = left.read(65536)
                assert block == right.read(65536), "derivationalNoninterference:" + name
                if not block:
                    break
        hashes[name] = file_digest(with_step / name)
        assert hashes[name] == before[name], "derivationalNoninterference:" + name
    counts = read(without / "census.json.summary.json")["counts"]
    assert counts == read(with_step / "census.json.summary.json")["counts"]
    result = {"test": "synthetic_fixture_pipeline_with_and_without_derivational",
              "status": "passed", "sha256": hashes, "counts": counts}
    write(directory / "derivational-noninterference.json", result)
    return result
