"""Emit the independent data-only Lean manifest from two separate authorities."""

import argparse
import hashlib
import json
import pathlib
import resource
import sys
import time

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from Certificate.emission import write_manifest, string, write_module
from pipeline import frozen_keys
from Certificate.handoff import read as read_handoff
from streaming import canonical


def driver(directory, report_path, rows_path, receipt_path, prefix, head, report_sha,
           receipt_digest, generate):
    path = directory / "CensusRun/Root.lean"
    text = ("import LeanInformationAudit.Census.Publish\n"
            f"#disposition_census projection root CensusRun.Root source {string(str(path))} "
            f"report {string(str(report_path))}\n"
            f"  head {string(head)} report_sha256 {string(report_sha)}\n"
            f"  prefix {string(prefix)} manifest CensusRun.manifest report_keys CensusRun.reportKeys\n"
            f"  rows {string(str(rows_path))} receipt {string(str(receipt_path))} "
            f"receipt_digest {string(receipt_digest)} " + ("generate " if generate else "") +
            f"certificate CensusRun.accountingCertificate output {string(str(directory / 'publication.json'))}\n")
    write_module(directory, "CensusPublish.Root", text)
    return path


def prepare(directory, report_path, rows_path, receipt_path, prefix):
    """Prepare the driver; its guarded handoff will read rows and emit once."""
    receipt = json.loads(receipt_path.read_bytes())
    return driver(directory, report_path, rows_path, receipt_path, prefix,
                  receipt["inputs"]["head"], receipt["inputs"]["export_sha256"], receipt["digest"], True)


def emit(directory, report_path, rows_path, receipt_path, prefix, *, expected_digest=None, keys_output=None):
    directory.mkdir(parents=True, exist_ok=True)
    profile = {}

    def mark(label):
        (directory / "handoff.phase").write_text(label)
        return time.monotonic()

    started = mark("report_inventory")
    report_bytes = report_path.read_bytes()
    report = json.loads(report_bytes)
    head = report["source_commit"]
    report_sha = "sha256:" + hashlib.sha256(report_bytes).hexdigest()
    try:
        all_keys = frozen_keys(report)
    except ValueError as error:
        raise ValueError("IE-C044 report: " + str(error)) from error
    keys = [key for key in all_keys if key[0] == prefix or key[0].startswith(prefix + ".")]
    del report_bytes, report, all_keys
    profile["report_inventory_s"] = time.monotonic() - started
    started = mark("handoff_read")
    rows, receipt_digest = read_handoff(rows_path, receipt_path, report_sha, head, expected_digest)
    profile["handoff_read_s"] = time.monotonic() - started
    profile.update(rows=len(rows), artifact_bytes=rows_path.stat().st_size,
                   peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss *
                   (1 if sys.platform == "darwin" else 1024))
    started = mark("emission")
    path = write_manifest(directory, rows, keys, head, report_sha, "CensusRun.Root")
    if keys_output is not None:
        keys_output.write_bytes(canonical(rows))
    else:
        driver(directory, report_path, rows_path, receipt_path, prefix, head, report_sha, receipt_digest, False)
    profile["emission_s"] = time.monotonic() - started
    (directory / "handoff-profile.json").write_bytes(canonical(profile))
    return path


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", required=True, type=pathlib.Path)
    parser.add_argument("--report", required=True, type=pathlib.Path)
    parser.add_argument("--rows", required=True, type=pathlib.Path)
    parser.add_argument("--receipt", required=True, type=pathlib.Path)
    parser.add_argument("--prefix", required=True)
    parser.add_argument("--prepare", action="store_true")
    parser.add_argument("--digest")
    parser.add_argument("--keys-output", type=pathlib.Path)
    options = parser.parse_args()
    args = (options.directory, options.report, options.rows, options.receipt, options.prefix)
    if options.prepare:
        prepare(*args)
    else:
        emit(*args, expected_digest=options.digest, keys_output=options.keys_output)
