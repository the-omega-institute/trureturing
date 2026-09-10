"""Kernel negatives at the bucket boundary and at the assembly join."""

import json
import os
import pathlib
import re
import subprocess

import sys

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from Certificate.emission import bucket_sources, manifest_source, write_module
from tests.test_buckets import authorities


def check_bucket_negatives(repository, directory):
    rows, keys = authorities([0, 1, 2 ** 254, 2 ** 255, 3 * 2 ** 254])
    original = bucket_sources(rows, keys, b=2)
    original["CensusRun.Root"] = manifest_source(rows, keys, "fixture-head", "digest", "CensusRun.Root", b=2)
    theorem = ("\npublic theorem CensusRun.accountingCertificate : CensusKeyManifest.Certificate "
        "CensusRun.manifestKeys 5 CensusRun.reportKeys := certificate_of_range CensusRun.facts\n")
    original["CensusRun.Root"] += theorem
    changed = dict(original)
    changed["CensusRun.Range2_1"] = re.sub(r"(: Nat := )0x[0-9a-f]+", r"\g<1>0x0", changed["CensusRun.Range2_1"])
    literal = dict(original)
    literal["CensusRun.Range2_1"] = re.sub(r"(reportKeys.chunk0 : Nat := )(0x[0-9a-f]+)",
        lambda m: m[1] + hex(int(m[2], 0) + 1), literal["CensusRun.Range2_1"])
    join = dict(original)
    join["CensusRun.Root"] = join["CensusRun.Root"].replace(
        "certificate_of_range CensusRun.facts", "(by decide +kernel)")
    missing = dict(original)
    missing["CensusRun.Root"] = missing["CensusRun.Root"].replace("public import CensusRun.Range1_0\n", "")
    cases = [("bucketJoinAccepted", original, True, None),
             ("wrongBucketRangeTheorem", changed, False, "CensusRun.Range2_1"),
             ("bucketLiteralEdited", literal, False, "CensusRun.Range2_1"),
             ("joinLemmaRemoved", join, False, "CensusRun.Root"),
             ("bucketMissingFromAssembly", missing, False, "CensusRun.Root")]
    outcomes = []
    for label, sources, accepted, failed_module in cases:
        output = directory / "bucket-negatives" / label
        for module, source in sources.items():
            write_module(output, module, source)
        command = ["lake", "env", "python3", str(repository / "tools/lean-inspector/Census/Certificate/buckets.py"),
            "--source", str(output / "CensusRun/Root.lean"), "--root", "CensusRun.Root", "--inputs", str(output),
            "--certificate-directory", str(repository / ".lake/build/lib/lean")]
        with (output / "process.log").open("w") as log:
            result = subprocess.run(command, cwd=repository, stdout=log, stderr=subprocess.STDOUT,
                                    env=dict(os.environ, LEAN_NUM_THREADS="1"))
        build = json.loads((output / "CensusRun/Root.build.json").read_text())
        assert (result.returncode == 0) == accepted, (label, (output / "process.log").read_text())
        if not accepted:
            failures = [item for item in build["processes"] if item["exit_code"]]
            assert len(failures) == 1 and failures[0]["module"] == failed_module, (label, failures)
        outcomes.append({"name": label, "status": "accepted" if accepted else "rejected",
                         "failed_module": failed_module, "exit_code": result.returncode})
    (directory / "bucket-negatives.json").write_text(json.dumps(outcomes, indent=2) + "\n")
    return outcomes


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=pathlib.Path)
    args = parser.parse_args()
    check_bucket_negatives(pathlib.Path(__file__).resolve().parents[4], args.output.resolve())
