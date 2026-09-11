"""Consume the query lane's J2 rows and whole-stream receipt, without query replay."""

import argparse
import hashlib
import json
import pathlib

import sys

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from streaming import canonical, digest


def file_digest(path):
    hashed = hashlib.sha256()
    with pathlib.Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            hashed.update(block)
    return "sha256:" + hashed.hexdigest()


def name_json(text):
    result = ["anonymous"]
    for part in text.split("."):
        result = ["str", result, part]
    return result


def read(rows_path, receipt_path, report_sha, head, expected_digest=None):
    receipt = json.loads(pathlib.Path(receipt_path).read_bytes())
    inputs = receipt["inputs"]
    if receipt["digest"] != digest(inputs) or (expected_digest is not None and
                                              receipt["digest"] != expected_digest):
        raise ValueError("IE-C044 whole_stream_receipt_digest")
    if inputs["head"] != head or inputs["export_sha256"] != report_sha:
        raise ValueError("IE-C044 whole_stream_report_binding")
    scopes = {canonical(name_json(root)) for root, _ in inputs["scopes"]}
    keys = []
    hashed = hashlib.sha256()
    # sort_rows writes canonical(row), including its newline, into both the
    # artifact and rows_sha256. Frame first, decode once, hash those exact bytes.
    with pathlib.Path(rows_path).open("rb") as source:
        for line in source:
            try:
                row = json.loads(line)
            except ValueError as error:
                raise ValueError("IE-C044 whole_stream_json invalid compact row") from error
            payload = row["payload"]
            if payload.get("import_scope") is not None:
                raise ValueError("IE-C044 whole_stream_scope_binding noncompact row")
            if row["class"] == "observed" and canonical(payload["root"]) not in scopes:
                raise ValueError("IE-C044 whole_stream_scope_binding")
            keys.append({key: row[key] for key in ["theorem_name", "statement_id"]})
            hashed.update(line)
    rows_sha = "sha256:" + hashed.hexdigest()
    programs = dict(inputs["programs"])
    emitter = digest([(name, programs["tools/lean-inspector/Census/" + name][7:])
                      for name in ["phases.py", "emission_cache.py", "streaming.py"]])
    if (rows_sha != receipt["rows_sha256"] or
            inputs.get("rows") != {"artifact": "rows.jsonl", "sha256": rows_sha} or
            inputs["expanded_rows_cache_key"] !=
            digest([rows_sha, inputs["module_names"], inputs["scopes"], emitter])):
        raise ValueError("IE-C044 whole_stream_rows_binding")
    return keys, receipt["digest"]


def publish(output, certificate):
    """Publish the certificate and query receipt binding as a small sidecar."""
    output = pathlib.Path(output)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_bytes(canonical(certificate))
    temporary.replace(output)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rows", type=pathlib.Path)
    parser.add_argument("--receipt", type=pathlib.Path)
    parser.add_argument("--report-sha")
    parser.add_argument("--head")
    parser.add_argument("--digest")
    parser.add_argument("--output", required=True, type=pathlib.Path)
    parser.add_argument("--certificate", type=pathlib.Path)
    args = parser.parse_args()
    if args.certificate:
        publish(args.output, json.loads(args.certificate.read_bytes()))
    else:
        rows, _ = read(args.rows, args.receipt, args.report_sha, args.head, args.digest)
        args.output.write_bytes(canonical(rows))


if __name__ == "__main__":
    main()
