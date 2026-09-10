"""Publish support-positive candidates from an existing structural sidecar.

Report-only: no grammar check or semantic classification. Statement keys and
theorem names retain the census structured Lean Name representation. Only one
sidecar row plus the selected projections is resident; census.json is not read.
"""

import argparse
import pathlib
import sys

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from incremental import atomic_json
from report_stream import fields
from streaming import canonical, file_stamp
from Structure.sources import file_digest


def build_report(sidecar):
    """A deterministic projection of sidecar bytes, independent of its path."""
    before = file_stamp(sidecar)
    input_sha256 = file_digest(sidecar)
    candidates = []
    for field, row in fields(sidecar, array_field="rows"):
        if field != "rows":
            continue
        readings = row.get("readings")
        if readings is None:
            continue
        if readings["core_or_frozen_support"] is True:
            generated = row["generated_candidate"]
            if not isinstance(generated, bool):
                raise ValueError("generated_candidate must be a boolean")
            candidates.append({
                "key": {k: row[k] for k in ("theorem_name", "statement_id")},
                "module": row["owning_module"], "theorem_name": row["theorem_name"],
                "generated_candidate": generated,
                "direct_frozen_prerequisites": readings["direct_frozen_prerequisites"],
                "value_constant_count": readings["value_constant_count"],
                "structural_status": row["status"],
            })
    if file_stamp(sidecar) != before:
        raise ValueError("structural sidecar changed during candidate projection")
    candidates.sort(key=lambda c: (canonical(c["theorem_name"]),
                                   c["key"]["statement_id"], c["module"]))
    generated = sum(c["generated_candidate"] for c in candidates)
    return {"schema": "derivational-candidates", "input_sha256": input_sha256,
            "candidates": candidates, "summary": {
                "candidates": len(candidates), "generated": generated,
                "non_generated": len(candidates) - generated,
                "with_at_least_one_frozen_leaf": sum(bool(c["direct_frozen_prerequisites"])
                                                      for c in candidates)}}


def publish(directory):
    directory = pathlib.Path(directory)
    report = build_report(directory / "census-structure.json")
    output = directory / "derivational-candidates.json"
    atomic_json(output, report)
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=pathlib.Path, required=True,
                        help="existing census run directory; writes derivational-candidates.json")
    print(publish(parser.parse_args().directory))
