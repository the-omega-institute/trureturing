# Two xi7 pilots at the fixed missing23 A1 node

`verify.py` transports the complete prior future-label certificate using a same-cell positive-difference envelope. It tests exactly two new xi7: `(2,4,7,4)` succeeds for all `280^5` future choices; `(2,4,2,14)` fails this comparison only. Its failure is not an impossibility statement.

The consumer pins and calls `missing23-eta13-rest/verify.py` and its prior dependencies. It derives a conservative common live lower bound from the verified common query numerator and query upper bound, so no ordering of rounded ratios is used to identify an exact minimum.

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py
python3 -I -S -B geometry_replay.py --projection 2,4,7,4 --kind current7 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --projection 2,4,7,4 --kind difference --cache /explicit/cache
```

Default consumer execution writes only stdout; `--output` explicitly retains the certificate. The producer is cache-only by default. `--fresh` generates missing full-input SHA256 keys; `--regenerate` recomputes existing keys. Use `--base`, `--prior`, `--late`, `--first`, `--rest` on the consumer to override sibling package locations.

Each pilot has four current7 batches (108 queries) and four ordinary difference-envelope batches (3,024 queries). No later physical-label table is recomputed. The original source, license, pinned integer enumerator and multiplier definitions remain in the base package. Results are ordinary mathematical/computational evidence, not new Lean verification. Scope is the stated A1 node, thresholds and query16.
