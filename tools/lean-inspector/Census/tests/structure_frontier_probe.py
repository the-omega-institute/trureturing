"""One frozen root with a disk-backed large frontier.

The functional suite calls probe() without measuring RSS and checks streaming
IO progress. This original #6767 context adaptation separates machine memory
from the functional verdict; the production graph and publication are unchanged.

From Census/, run `python3 -m tests.structure_frontier_probe --compare-rss` for
the separate performance experiment: fresh processes, 1/128 MiB uncompressed
frontiers, and RSS growth strictly below 16 MiB. A numeric argument retains the
single-sample RSS entry point. Measurements describe this host and Python run,
not CI performance or a universal memory bound.
"""

import argparse
import gzip
import json
import pathlib
import resource
import subprocess
import sys
import tempfile

from streaming import canonical
from Structure.graph import analyse
from Structure.sidecar import publish


def probe(mebibytes, *, measure_rss=False):
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
        result = {"frontier_bytes": size, "elements": count,
                  "reported_elements": summary["frontier_incidences"],
                  "artifact_bytes": (directory / "census-structure.json").stat().st_size}
        if measure_rss:
            rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
            result["rss_bytes"] = rss * (1 if sys.platform == "darwin" else 1024)
        return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("mebibytes", type=int, nargs="?")
    mode.add_argument("--compare-rss", action="store_true")
    options = parser.parse_args()
    if options.compare_rss:
        results = [json.loads(subprocess.check_output(
            [sys.executable, "-m", "tests.structure_frontier_probe", str(size)],
            cwd=pathlib.Path(__file__).resolve().parents[1], text=True)) for size in [1, 128]]
        growth = results[1]["rss_bytes"] - results[0]["rss_bytes"]
        within_limit = growth < 16 * 1024 ** 2
        print(json.dumps({"samples": results, "rss_growth_bytes": growth,
                          "limit_bytes": 16 * 1024 ** 2, "within_limit": within_limit}), flush=True)
        raise SystemExit(0 if within_limit else 1)
    print(json.dumps(probe(options.mebibytes, measure_rss=True)))
