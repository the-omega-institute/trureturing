"""Publish support-positive candidates from an existing structural sidecar.

Report-only: no grammar check or semantic classification. Statement keys and
theorem names retain the census structured Lean Name representation. Row count
and frontier size affect disk use only; memory holds one identity/scalar
projection, fixed IO buffers and a capped SQLite page cache.
"""

import argparse
import hashlib
import json
import pathlib
import shutil
import sqlite3
import sys
import tempfile

if __package__ in (None, ""):
    sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from streaming import canonical, file_stamp
from Structure.derivational_stream import BUFFER_BYTES, Reader, rows


def spool(reader, leaves, records, db):
    summary = dict(candidates=0, generated=0, non_generated=0, with_at_least_one_frozen_leaf=0)
    for row in rows(reader, leaves):
        readings = row.get("readings")
        if readings is None:
            continue
        if readings["core_or_frozen_support"] is True:
            generated = row["generated_candidate"]
            if not isinstance(generated, bool):
                raise ValueError("generated_candidate must be a boolean")
            candidate = {
                "key": {k: row[k] for k in ("theorem_name", "statement_id")},
                "module": row["owning_module"], "theorem_name": row["theorem_name"],
                "generated_candidate": generated,
                "value_constant_count": readings["value_constant_count"],
                "structural_status": row["status"],
            }
            start = records.tell()
            records.write(b'{"direct_frozen_prerequisites":')
            leaves.seek(0)
            shutil.copyfileobj(leaves, records, BUFFER_BYTES)
            records.write(b"," + canonical(candidate)[1:-1])
            db.execute("INSERT INTO candidates VALUES (?,?,?,?,?)",
                       (canonical(candidate["theorem_name"]), candidate["key"]["statement_id"],
                        candidate["module"], start, records.tell() - start))
            summary["candidates"] += 1
            summary["generated"] += generated
            summary["non_generated"] += not generated
            summary["with_at_least_one_frozen_leaf"] += readings["direct_frozen_prerequisites"]
    return summary


def publish(directory, *, receipt=None):
    """Atomically publish a disk-sorted projection, hashing input and output incrementally."""
    directory = pathlib.Path(directory)
    sidecar = directory / "census-structure.json"
    before = file_stamp(sidecar)
    output = directory / "derivational-candidates.json"
    with tempfile.TemporaryDirectory(prefix=".derivational-", dir=directory) as scratch:
        scratch = pathlib.Path(scratch)
        db = sqlite3.connect(scratch / "sort.sqlite")
        try:
            db.executescript("""
                PRAGMA cache_size=-2048;
                PRAGMA cache_spill=1;
                PRAGMA temp_store=FILE;
                PRAGMA mmap_size=0;
                CREATE TABLE candidates(name BLOB, identity TEXT, module TEXT, start INTEGER, size INTEGER);
                CREATE INDEX candidate_order ON candidates(name, identity, module);
            """)
            with sidecar.open("rb") as source, (scratch / "leaves").open("w+b") as leaves, \
                    (scratch / "records").open("w+b") as records:
                reader = Reader(source)
                summary = spool(reader, leaves, records, db)
                if file_stamp(sidecar) != before:
                    raise ValueError("structural sidecar changed during candidate projection")
                input_sha256 = "sha256:" + reader.sha256.hexdigest()
                db.commit()
                hashed = hashlib.sha256()
                temporary = scratch / "report.json"
                with temporary.open("wb") as out:
                    def write(block):
                        hashed.update(block)
                        out.write(block)
                    write(b'{"candidates":[')
                    for index, (start, size) in enumerate(db.execute(
                            "SELECT start,size FROM candidates ORDER BY name,identity,module,rowid")):
                        if index:
                            write(b",")
                        records.seek(start)
                        while size:
                            block = records.read(min(size, BUFFER_BYTES))
                            if not block:
                                raise ValueError("truncated candidate spool")
                            write(block)
                            size -= len(block)
                    write(b"]," + canonical({"schema": "derivational-candidates",
                          "input_sha256": input_sha256, "summary": summary})[1:])
                temporary.replace(output)
                if receipt is not None:
                    receipt.update(input_sha256=input_sha256, output_sha256="sha256:" + hashed.hexdigest(),
                                   summary=summary)
        finally:
            db.close()
    return output


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=pathlib.Path, required=True,
                        help="existing census run directory; writes derivational-candidates.json")
    receipt = {}
    print(publish(parser.parse_args().directory, receipt=receipt))
    print(json.dumps(receipt, sort_keys=True))
