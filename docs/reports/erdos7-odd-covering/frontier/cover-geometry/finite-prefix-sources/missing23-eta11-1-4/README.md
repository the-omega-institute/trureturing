# Two reused eta11 phase slices

This package keeps the same A1/xi7 prefix and query16 as the sibling
`missing23-late280` package. It adds eta11=1 or4, keeps eta13=14, and
allows each later prime17,19,29 all280 projections. Its3200 prefix rows
cover70246400000 full tuples. The worst upward query bound is28.9194656258,
and the minimum millionth-rounded slack is0.187251.

The mathematical comparison and its limitations belong in the accompanying
report. This package does not conclude another slice, anchor or xi7 and
contains no new Lean verification.

`source_current11.json` records the seven exact A1 bounds from Michael
Schroeder's *Nine Prime Divisors in Odd Distinct Covering Systems*, version
1.0.1, DOI10.5281/zenodo.22759614. It identifies the source archive, exact
`closing.json` member, verifier, node and xi7 by fixed hashes. The two
newly used source bounds are attributed prerequisites, not a new
independent computation of their geometry.

`verify.py` imports the byte-pinned sibling late280 consumer and reuses its
pinned predecessor. It performs exact arithmetic and checks all3200 rows.
Default output is only a summary; `--output` explicitly writes the full
coverage result. Checks remain active under `-O`.

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py --output /tmp/e7_eta11_1_4_coverage.json
```

A temporary installation may specify `--late PATH_TO_LATE280` and
`--base PATH_TO_ETA14`. No old package is copied or modified.

`geometry_replay.py` reuses the pinned prior geometric producer. Its
incoming current11 components are zero7 and positive7, the current
threshold is4, and the selected15 phase remains fixed. Heads3,5,9 are
released. The producer checks equality with the attributed source value.
For any `E` in `1 4 7 8 11 13 14`:

```sh
python3 -I -S -B geometry_replay.py --eta E --fresh
```

Without `--fresh` it only reads full-input-SHA cache keys and fails on a
missing key. Repeated `--cache DIR` supplies existing key stores;
`--regenerate` explicitly reruns cached keys. New geometry caches and a
locally compiled enumerator live in this package. A C++17 compiler is
required for generation, unless `--binary FILE` supplies a trusted binary.
Run this producer without `-O`, because the attributed source helpers
reject optimized Python. The eta14 command has been checked from existing
cache entries and reproduces the source value exactly; eta1 and4 remain
attributed source inputs in this delivery, with no new geometry generated.

The source code and full MIT attribution remain in
`../missing23-eta14/LICENSE-MIT.txt`. The current11 metadata pins original
verification data covered by that source license. The source manuscript
has its separate CC BY4.0 license and is cited rather than reproduced.
