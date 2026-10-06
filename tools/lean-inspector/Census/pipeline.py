"""Project registration inventory from the complete production report.

This consumer preserves production verdicts and evidence. It performs no
registration assessment and produces no mathematical disposition certificate.
"""
import argparse
from collections import Counter
import json
import pathlib

from report_stream import fields


def inventory(report, prefix):
    rows, owners, seen = [], set(), set()
    modules = 0
    for field, value in fields(report, array_field="modules"):
        if field != "modules":
            continue
        modules += 1
        for record in value.get("information_templates", {}).get("records", []):
            key = record["key"]
            theorem = key["theorem"]
            if not (theorem == prefix or theorem.startswith(prefix + ".")):
                continue
            identity = json.dumps(key, sort_keys=True, separators=(",", ":"))
            if identity in seen:
                raise ValueError("duplicate production registration key: " + identity)
            seen.add(identity)
            owners.add(key["registration_module"])
            rows.append(record)
    rows.sort(key=lambda row: json.dumps(row["key"], sort_keys=True))
    return {"schema": "lean-registration-census", "modules": modules,
            "registration_modules": len(owners), "registrations": len(rows),
            "counts": dict(sorted(Counter(row["state"] for row in rows).items())),
            "records": rows}


def execute(options):
    result = inventory(options.lean_report, options.prefix)
    directory = pathlib.Path(options.output)
    directory.mkdir(parents=True, exist_ok=True)
    (directory / "census.json").write_text(json.dumps(result, ensure_ascii=False) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key != "records"}))
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True)
    parser.add_argument("--lean-report", default=".lake/build/stratalint/raw-lean-report.json")
    parser.add_argument("--prefix", default="D5")
    return execute(parser.parse_args())


if __name__ == "__main__":
    raise SystemExit(main())
