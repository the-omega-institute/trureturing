# Completed actual-prime slab experiment

This dataset retains the completed `(2,3,q)` inquiry for `q = 23,29,31`
and paired exponents in `{0,...,15}^3`. Its 12,288 boxes contain 307,200
raw slots and 85,819 completed exact keys. Every retained eligible node
has a negative directed Arb enclosure at 128 bits. The declared ladder
was 128/256/512 bits; no node required a higher tier. These are numerical
experiment results. **C and Not C remain open.** No continuous-slab or
universal-prime conclusion, independent witness certification, or Lean
theorem follows from this dataset.

`experiment.json` retains the complete statement of C, the original R and
R_nodes hypotheses, exact domain and node definitions, source identities,
scoped prior-support exclusions, cumulative costs, measurement boundaries,
diagnostic keys and data-production provenance. Mathematical identity uses
the definition, sorted paired prime/exponent coordinates (including zero
exponents), and reduced positive rational `exp(M0), exp(M1)`. A producer ID
or a new invocation does not identify new mathematical work. Use the
retained keys to exclude completed units from any later proposed inquiry;
the scope is this experiment and the explicitly recorded prior supports,
not all research history.

Each `q*.rows.jsonl.xz.b64` file holds one prime support. RFC4648 base64 on
one unwrapped line with a final LF wraps an XZ stream (LZMA2 preset 6,
CRC64). The decoded JSON Lines start with a schema/column header. Later
lines are arrays `[table, original_rowid, ...column_values]`, first `boxes`
and then `nodes`, each in original rowid order. The original SQLite TEXT
cells remain exact strings, including their JSON formatting. Parse a
`document` cell separately to inspect its mathematical data. All rational
enclosures, six mixtures and weights, clipping/distance branches, ties,
exact guards, configuration witnesses, tier statuses and evaluation costs
are retained. Both the encoded files and decoded streams have byte sizes
and SHA-256 bindings in `experiment.json`.

The largest encoded shard is 16,489,609 bytes; the three decoded JSONL
streams together occupy 571,500,948 bytes. This is a fixed experiment
package. Future experiments should retain their own inputs and results,
without rewriting this experiment to maintain a global index.

The seven `producer-sources/<sha256>.py` files are the exact executed
source versions. `provenance.source_roles` maps each version to its
original module path; `provenance.producers` links the original producer
IDs in node tiers to those source versions, runtime versions and measured
work. They are source evidence for this experiment, not scripts to rerun
the completed search. The evaluator's historical module docstring refers
to GPU-returned rows; this experiment called its pure Arb expression from
the separate CPU driver. Package metadata reports Python 3.12.13 and
python-flint 0.8.0, with NumPy 2.0.2 and Torch 2.8.0 package metadata;
those package listings do not assert GPU use. The current repository
program documentation remains `tools/scripts/agent/prime_slabs/CPU.md`.

The total historical evaluation cost is **14,059,854,387 ns**:
73,933,081 ns in the pilot and 13,985,921,306 ns in the remaining window.
`B08-CPU-MEASUREMENT-PREHASH` applies to the original v1 wall/RSS values:
they cover the search phase before database hashing. The sum of those
search-phase wall measurements is 155,914,342,000 ns and their maximum
reported RSS is 46,596,096 bytes. Whole-command peaks of those terminated
arithmetic runs were not measured. The later zero-evaluation resume has
three distinct scopes in the metadata: its search-phase sample, its
post-hash sample excluding final small JSON/stdout publication, and the
external whole-command observation of 23.44 s and 53,444,608 bytes maximum
RSS. None replaces the missing historical whole-command measurements.
Per-invocation CPU times are process observations and are not the summed
per-tier evaluation clock; free-disk readings are observations, not a
measurement of bytes attributable to the experiment.

Decode and verify a shard with Python 3's standard library, without loading
the scientific evaluator. Replace the two absolute paths below with the
package directory and a new output JSONL path; select the exact shard
filename as the middle argument. Quoted paths may contain spaces and the
command works from any directory. Python runs in isolated mode. It holds
one armored shard and its compressed bytes in memory, then streams the
JSONL output in 1 MiB blocks. All three byte sizes and SHA-256 bindings are
checked; an existing output is refused and a failed decode removes its
new partial output.

```sh
python3 -I - "/absolute/path/to/package" "q23.rows.jsonl.xz.b64" "/absolute/path/to/new.jsonl" <<'PY'
import base64, hashlib, io, json, lzma, pathlib, sys
root, name, output = pathlib.Path(sys.argv[1]), sys.argv[2], pathlib.Path(sys.argv[3])
spec = json.loads((root / "experiment.json").read_text(encoding="utf-8"))
shard = next(s for s in spec["representation"]["shards"] if s["path"] == name)

def check(condition, message):
    if not condition:
        raise ValueError(message)

encoded = (root / name).read_bytes()
check(len(encoded) == shard["bytes"], "encoded size mismatch")
check(hashlib.sha256(encoded).hexdigest() == shard["sha256"], "encoded hash mismatch")
check(encoded.endswith(b"\n") and encoded.count(b"\n") == 1, "expected one LF-terminated line")
compressed = base64.b64decode(encoded[:-1], validate=True)
check(base64.b64encode(compressed) + b"\n" == encoded, "noncanonical base64")
check(len(compressed) == shard["decoded_xz_bytes"], "XZ size mismatch")
check(hashlib.sha256(compressed).hexdigest() == shard["decoded_xz_sha256"], "XZ hash mismatch")
del encoded
decoded_hash, decoded_bytes = hashlib.sha256(), 0
target = output.open("xb")
try:
    with target, lzma.open(io.BytesIO(compressed), "rb") as source:
        for block in iter(lambda: source.read(1024 * 1024), b""):
            decoded_hash.update(block)
            decoded_bytes += len(block)
            target.write(block)
    check(decoded_bytes == shard["reconstructed_jsonl_bytes"], "JSONL size mismatch")
    check(decoded_hash.hexdigest() == shard["reconstructed_jsonl_sha256"], "JSONL hash mismatch")
except BaseException:
    output.unlink()
    raise
PY
```

To make a local inspection database, create the two tables using
`representation.sql_schema` in `experiment.json`. Skip each JSONL header
and insert each subsequent array's values after the table name into
`(rowid, <representation.columns[table]>)`, using bound SQL parameters in
one transaction. Original rowids are unique across the three shards
within their table. The resulting `boxes` and `nodes` tables reproduce
every original cell, enabling ordinary SQLite queries such as:

```sql
SELECT key, status, sign,
       json_extract(document, '$.tiers[0].precision') AS bits,
       json_extract(document, '$.tiers[0].bounds.G') AS gap_interval
FROM nodes
WHERE key = '357f33ad87c36e4d87aaf16684fd914c8ed7026f5d1c8143d1a0ead3754ea854';

SELECT json_extract(document, '$.tiers[0].phase') AS phase,
       sum(json_extract(document, '$.tiers[0].evaluation_ns')) AS evaluation_ns
FROM nodes GROUP BY phase;
```

This inspection database is not a drop-in resume database. The retained
metadata deliberately excludes orchestration identities, scheduling
instructions, repeated input bodies, intermediate cumulative snapshots
and validation receipts. Producer IDs remain original data-production
join keys; they are not hashes of the selected public producer records.
Compression/base64 and the box/node row representation are reversible.
The metadata selection, original SQLite page layout and omitted fields
are not. Original input/database digests identify the source experiment;
they do not claim that the selected metadata reconstructs those original
bytes. No arithmetic replay is needed for decoding, cell reconstruction
or inspection.
