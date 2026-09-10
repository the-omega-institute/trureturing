"""Isolated RSS probe for one frozen root with a disk-backed large frontier."""

import gzip
import json
import pathlib
import resource
import sys
import tempfile

from streaming import canonical
from Structure.graph import analyse
from Structure.sidecar import publish


def probe(mebibytes):
    with tempfile.TemporaryDirectory() as scratch:
        directory = pathlib.Path(scratch)
        frontier = directory / "frontier.gz"
        key = ("Fixture", "ns(n0,4:root)", "id-root")
        count = 0
        with gzip.open(frontier, "wb", compresslevel=1) as out:
            size = 0
            while size < mebibytes * 1024 ** 2:
                row = {"declaration_name_key": "ns(n0,12:u" + format(count, "011d") + ")",
                       "library": "Upstream", "provenance": [
                           {"declaring_module": "Module" + str(count // 1000), "library": "Upstream"}]}
                encoded = canonical(row)
                out.write(encoded)
                size += len(encoded)
                count += 1

        class DiskFrontier:
            def set_frozen(self, _keys):
                pass

            def snapshot(self):
                return "one-root-many-modules"

            def read_key(self, *_args):
                return {"direct": [], "folded": [], "potential": [], "unbounded": False,
                        "reason": None, "value_constant_count": 1, "core_or_frozen_support": "undetermined",
                        "empty_core_support": False, "scope_resolved_direct_references": 0,
                        "ambiguous_direct_references": 0, "helper_visits": 1}, frontier, False

        rows = directory / "rows.jsonl"
        summary = analyse(DiskFrontier(), [key], rows, [], axioms={key[1:]: []})
        publish(directory, {"schema": "census-structure"}, rows)
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        return {"rss_bytes": rss * (1 if sys.platform == "darwin" else 1024),
                "frontier_bytes": size, "elements": count,
                "reported_elements": summary["frontier_incidences"],
                "artifact_bytes": (directory / "census-structure.json").stat().st_size}


if __name__ == "__main__":
    print(json.dumps(probe(int(sys.argv[1]))))
