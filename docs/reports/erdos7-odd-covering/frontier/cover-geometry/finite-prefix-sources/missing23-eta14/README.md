# Fixed missing-23 eta14 comparison: reproduction

The mathematical argument and scope are in [Report462](../../../../profile-notes/arithmetic/450-499/462-the-final-stage-ledger-gives-a-seven-core-common-law.md#a-fixed-missing-23-comparison-node-closes-under-all-eta14-phases). Run the commands below from this directory.

## Verification and reconstruction

`inputs.sha256.json` pins the numerical prerequisites, unmodified source
helpers and C++ engine, license, two support reconstructions and their eight
raw geometry batches. Its own SHA256 is a literal in both consumers.
`verify.py` uses explicit exceptions rather than assertions, including when
Python runs with `-O`. Its default writes nothing and prints a JSON summary.
Only an explicit `--output` writes the complete 1600-route result.

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py --output /tmp/e7_eta14_coverage.json
```

The numerical tables in `bounds.json` are prerequisites to that arithmetic
check. `geometry_replay.py` reconstructs them using the pinned source's
carrier, weights, depth and coefficient helpers; it never invokes the
source's `main()` or its geometry routine. The source helpers deliberately
reject `-O`, so run the geometry producer without `-O`.

By default the producer only reads existing full-input-SHA geometry caches.
Missing entries raise an error. `--cache DIR` may be repeated and performs
only direct key lookups. To generate missing entries deliberately use
`--fresh`; it compiles the pinned `geometry.cpp` with a C++17 compiler if no
binary is present. `--binary FILE` supplies an explicitly trusted locally
compiled binary. Merely reusing a cache does not independently rerun its
integer maxima. `--fresh` allows missing-key generation; it does not bypass
an existing cache. To recompute even existing keys use the explicit
`--regenerate` option. It verifies the input pins first, then reruns the
integer engine and replaces generated cache entries. This option was not
used to claim additional research coverage.

For a replay with existing external cache directories append
`--cache DIR1 --cache DIR2 ...` to the following commands. For new geometry
append `--fresh`. Outputs are optional and require `--output FILE`.

```sh
# Prefix7 and the four ordinary fields in bounds.json.
python3 -I -S -B geometry_replay.py --stage 7
python3 -I -S -B geometry_replay.py --stage ordinary --part 0,0,0
python3 -I -S -B geometry_replay.py --stage ordinary --part 1,0,0
python3 -I -S -B geometry_replay.py --stage ordinary --part 0,1,0
python3 -I -S -B geometry_replay.py --stage ordinary --part 1,1,0

# Every charged11 label; A and flat11 charged13 tables.
python3 -I -S -B geometry_replay.py --stage 11 --all40
python3 -I -S -B geometry_replay.py --stage 13 --all40
python3 -I -S -B geometry_replay.py --stage 13 --flat11 --all40

# A,B uniform continuation tables. Base17 intentionally uses full13.
python3 -I -S -B geometry_replay.py --stage 17 --all40
python3 -I -S -B geometry_replay.py --stage 19 --all40
python3 -I -S -B geometry_replay.py --stage 29 --all40

# CC current13; then three released-head continuations with zero13.
python3 -I -S -B geometry_replay.py --stage 13 --xi11 2,4,8,14 --xi13 2,4,8,14 --projection 2,4,8,14
python3 -I -S -B geometry_replay.py --stage 17 --xi11 2,4,8,14 --xi13 2,4,8,14 --mode released --zero13
python3 -I -S -B geometry_replay.py --stage 19 --xi11 2,4,8,14 --xi13 2,4,8,14 --mode released --zero13
python3 -I -S -B geometry_replay.py --stage 29 --xi11 2,4,8,14 --xi13 2,4,8,14 --mode released --zero13
```

The fresh support reconstructions retain exactly eight batches and 6048
integer queries. Their mass, whole and all integer thresholds 1..28 agree
exactly with the plain and kappa7 entries of both input files. The other
prerequisites can be reconstructed with the commands above; cached replays
check producer-to-input correspondence without claiming new enumeration.

The C++ engine reads signed32 cell weights and offsets and signed64 loads.
The wrapper checks each input range, bounds every intermediate load, and
bounds each output by `sum_x w_x max(0,baseline+offset_x+sum(coeff)-threshold)`
below `2^63`. Products in the C++ source promote to its `long long` load
type before multiplication. Every returned row must have the requested
index/denominator and lie between zero and that derived upper bound.
This replaces any arbitrary small-output ceiling; it does not substitute
for the enumeration algorithm's correctness.

## Attribution and remaining scope

`source_model.py` and `geometry.cpp` are byte-identical copies of
`nine-prime-support/checks/verify.py` and `checks/geometry.cpp` from the
source v1.0.1 archive (archive SHA256
`9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`).
Their SHA256 values are respectively
`e3296d181686c0f1925e755583fdc4df2ffeb2bacbc36a77a2396bbe3b4a9135` and
`8d7ecf1981a413daf2d3835ebe2c046b20f03010f7ce24f247bd357136e24f04`.
The original verification material is copyright 2026 Michael Schroeder,
licensed under MIT; the full notice is included in `LICENSE-MIT.txt`.
The source manuscript/prose has its separate CC BY 4.0 license. This
package supplies its own argument and cites that manuscript rather than
relicensing or reproducing the manuscript.

The portable producer, arithmetic consumer, extended threshold comparisons,
field transfers, routing and result data belong to this new fixed-node
calculation. Scope expansion remains open: other eta values, other xi7,
other anchor nodes, continuous-node interpolation, and the unrestricted
covering problem require additional arguments. `--eta` and `--mode released`
expose a producer interface for future experiments; their existence is not
coverage, and eta14 has not been proved a worst case over eta.
