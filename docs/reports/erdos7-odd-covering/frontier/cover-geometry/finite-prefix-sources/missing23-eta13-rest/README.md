# Fixed missing23 A1 node: the remaining six eta13 slices

`verify.py` checks all 67,200 ordered `(xi11,xi13)` pairs, with 280 independent physical choices at each later prime. It pins and reuses the three prior packages. Default execution writes only stdout; `--output` explicitly retains a report. The report stores 42 phase-block certificates after checking every pair.

Expected sibling packages: `missing23-eta14`, `missing23-late280`, `missing23-eta11-1-4`, `missing23-eta11-rest`. Override their locations with `--base`, `--late`, `--first`, `--rest`.

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py
python3 -I -S -B geometry_replay.py --stage 13 --projection 2,3,2,8 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --stage 17 --eta 14 --cache /explicit/cache
```

The producer is cache-only by default. `--fresh` generates missing full-input SHA256 geometry keys; `--regenerate` recomputes existing keys. Generated files stay in this package's `geometry-cache`. The pinned source and C++ integer enumerator, original source attribution and MIT license remain in the base package. No ambient desktop or home search is performed.

Reconstruction comprises 192 current13 representatives and 21 released late bounds. The remaining 48 current13 labels use the explicit source-preserving prefix permutation. Numerical inputs and ordinary mathematical comparison arguments are not new Lean verification. Scope is one fixed A1 node and one fixed xi7; the combined prior and new slices cover all five later physical projection choices at that node.
