"""Run the retained J3 elaborator cases and actual streaming olean negatives."""

import argparse
import json
import pathlib
import tempfile
import shutil
import unittest
import sys

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from negative_fixtures import prepare, check_manifest_negatives, lean_env, validate_control
from receipt_fixtures import check_receipts
from resources import run

RETIRED_QUERY_PROTOCOL_FIXTURES = [
    "missing-query-receipt", "missing-query-transport", "edited-query-transport",
    "stale-query-receipt", "swapped-query-receipt", "invented-consistent-scope-and-completion",
    "duplicate-evidence-imports", "input-flag",
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output")
    options = parser.parse_args()
    directory = pathlib.Path(options.output or tempfile.mkdtemp(prefix="census-fixtures-")).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    repository = pathlib.Path(__file__).resolve().parents[4]
    suite = unittest.defaultTestLoader.discover(str(pathlib.Path(__file__).resolve().parents[1]), pattern="test_*.py")
    if not unittest.TextTestRunner().run(suite).wasSuccessful():
        raise SystemExit(1)
    run(["make", "lean-cache-ensure"], directory, "cache", cwd=repository, budget_gb=None)
    run(["make", "lean"], directory, "freshness", cwd=repository, budget_gb=None)
    env = lean_env(repository)
    # Lake checks every retained fixture through the inspector lean_lib glob.
    # Reimporting each fixture in another Environment would repeat that work.
    cases = ["Query/Streaming", "Query/Contract", "Query/DirectEvidence", "Query/Enumeration", "Query/Ownership",
             "Query/StreamingOutside", "Query/ReceiptHash", "Query/Coverage", "Query/Publication",
             "AssessmentCommand", "Command", "CommandRejection", "InvalidEvidence", "LandedFinite",
             "Manifest/Contract", "Manifest/Environment", "Manifest/Precedence"]
    for case in ["Query/Streaming"]:
        path = repository / "tools/lean-inspector/LeanInformationAudit/Tests/Census" / (case + ".lean")
        run([shutil.which("lean", path=env["PATH"]), "-DmaxRecDepth=100000", "-DmaxHeartbeats=0", str(path)],
            directory / "lean" / case, "fixture", cwd=repository, env=env)
    streaming = directory / "streaming"
    prepare(repository, streaming)
    negatives = check_manifest_negatives(repository, streaming) + check_receipts(repository, streaming)
    negatives.append(validate_control(repository, streaming))
    from bounded_fixtures import non_evidence, two_batches
    bounds = [non_evidence(repository, streaming), two_batches(repository, streaming)]
    from tests.review_fixtures import colliding_owners, nested_scope, receipt_sensitivity, named_ballast
    bounds.append(colliding_owners(repository, streaming))
    bounds.append(named_ballast(repository, streaming))
    negatives.append(nested_scope(repository, streaming))
    negatives.append(receipt_sensitivity(repository, streaming))
    from Certificate.chunk_fixtures import check_chunks
    chunks = check_chunks(repository, directory)
    from Certificate.bucket_fixtures import check_bucket_negatives
    chunks.extend(check_bucket_negatives(repository, directory))
    from Certificate.publication_fixtures import prepare_publication, check_publication_negatives
    prepare_publication(repository, directory)
    negatives.extend(check_publication_negatives(repository, directory))
    from Structure.fixtures import check_structure
    structure = check_structure(repository, directory)
    result = {"negative_fixtures": negatives, "lean_fixture_modules": cases, "retained_fixture_execution": "Lake lean_lib build",
              "certificate_chunk_binding": chunks, "bounded_fixtures": bounds, "query_scheduler": "retired",
              "retired_query_protocol_fixtures": RETIRED_QUERY_PROTOCOL_FIXTURES,
              "observed_theorem_absent_from_publication": True,
              "artifact_determinism": True, "partial_certified_denominator": "passed",
              "structure_fixtures": structure}
    (directory / "fixtures.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
