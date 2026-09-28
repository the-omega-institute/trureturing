# Four remaining eta11 slices at the fixed node

This package fixes A1/xi7A and eta13=14, adds eta11 in7,8,11,13, and permits
all280 physical projections independently at17,19,29. It covers6400
prefix pairs and140492800000 full tuples. The worst upward query16 bound
is28.9500381606, with minimum millionth-rounded slack0.115893.

The mathematical argument belongs in the accompanying report. The scope
does not include another eta13, node or xi7; these are ordinary exact
comparisons, not new Lean verification.

`verify.py` pins `bounds.json` and the prior `missing23-late280/verify.py`,
which checks the inherited `missing23-eta14` inputs. Default execution only
prints a summary. `--output` explicitly writes the full6400-route result.
Normal Python and `-O` retain the same exception checks.

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py --output /tmp/e7_eta11_rest_coverage.json
```

For temporary layouts use `--late PATH_TO_LATE280` and
`--base PATH_TO_ETA14`. No earlier package is copied or modified.

The new input holds160 current11 labels from128 explicit representatives,
three actual-D current13 values and21 direct late phase bounds. The other
32 current11 labels carry their exact prefix-permutation map. The inherited
source code and full MIT notice remain in the original sibling package.

The separate `geometry_replay.py` imports the byte-pinned prior producer.
It is cache-only by default, with repeated `--cache DIR` for external key
stores. `--fresh` explicitly permits missing geometry; `--regenerate`
explicitly reruns existing keys. Generated files stay in this package's
`geometry-cache`, with a local C++17 enumerator or `--binary FILE`.
Run geometry replay without `-O`; the attributed source helpers reject
optimized Python.

For each current11 representative `(a,b,c,e)` with
`a in1,2`, `b in1..4`, `c in2,4,7,8`, `e in7,8,11,13`:

```sh
python3 -I -S -B geometry_replay.py --stage 11 --projection a,b,c,e --fresh
```

Third-coordinate5 labels use the retained2↔5 transport. The three current13
values fix xi11=(2,3,2,8):

```sh
python3 -I -S -B geometry_replay.py --stage 13 --projection 2,3,2,14 --fresh
python3 -I -S -B geometry_replay.py --stage 13 --projection 2,3,5,14 --fresh
python3 -I -S -B geometry_replay.py --stage 13 --projection 2,4,8,14 --fresh
```

For each `P in17,19,29` and each `E in1,4,7,8,11,13,14`, the direct late
producer fixes xi11=(2,3,2,8), xi13=(2,4,8,14), keeps all eight components,
and releases only heads3,5,9:

```sh
python3 -I -S -B geometry_replay.py --stage P --eta E --fresh
```

These152 commands reconstruct all new numerical inputs. Cached replay
checks their correspondence but does not independently rerun the maxima.
The default arithmetic consumer runs no geometry and requires no temporary
research directory.
