"""Isolated peak RSS for candidate count and single-row frontier scaling."""

import json
import pathlib
import resource
import sys
import tempfile

from Structure.derivational import publish
from streaming import canonical
from tests.test_derivational import row, statement


def probe(rows, frontier_mib, mode):
    with tempfile.TemporaryDirectory() as scratch:
        directory = pathlib.Path(scratch)
        with (directory / "census-structure.json").open("wb") as out:
            out.write(b'{"rows":[')
            for i in range(rows - 1, -1, -1):
                if i != rows - 1:
                    out.write(b",")
                value = row("same", format(i, "064x"), not frontier_mib or mode == "selected")
                if frontier_mib:
                    # Extend a real array without ever constructing its DOM.
                    field = "direct_frozen_prerequisites" if mode == "selected" else "frontier"
                    value["readings"].pop("direct_frozen_prerequisites")
                    prefix = json.dumps(value, separators=(",", ":")).encode()[:-2]
                    out.write(prefix + b',"' + field.encode() + b'":[\n')
                    element = canonical(statement("leaf", "id-leaf")).rstrip()
                    count = frontier_mib * 1024 ** 2 // (len(element) + 2)
                    for j in range(count):
                        out.write((b",\n" if j else b"") + element)
                    out.write(b"]}}")
                else:
                    out.write(canonical(value).rstrip())
            out.write(b"]}\n")
        output = publish(directory)
        # Read only the summary suffix; the probe never loads output candidates.
        rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        with output.open("rb") as source:
            source.seek(max(0, output.stat().st_size - 1024))
            suffix = source.read().split(b',"summary":', 1)[1].decode()
            summary, _ = json.JSONDecoder().raw_decode(suffix)
        return {"rows": rows, "frontier_mib": frontier_mib, "mode": mode,
                "rss_bytes": rss * (1 if sys.platform == "darwin" else 1024),
                "candidates": summary["candidates"], "artifact_bytes": output.stat().st_size}


if __name__ == "__main__":
    print(json.dumps(probe(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3])))
