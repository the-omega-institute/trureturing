# The remaining 22 first-label choices at one missing23 A1 node

The scope is the fixed A1 node `(2,4,1,8,1,2,1,0,13)`, primes `(3,5,7,11,13,17,19,29)`, thresholds `(2,4,4,8,8,16)`, reserve `135/4`, and query 16. Each of the 22 explicitly listed first labels is certified for all `280^5 = 1,721,036,800,000` future physical label tuples. This package does not assert a result for other A1 nodes or resolve Erdős #7.

## Reusing comparison inputs without identifying actual sources

The 22 labels have 18 distinct zero7 numerator fields on the same 44 source cells. Equality is checked cell by cell using `(11,11,9,6,3)`, not inferred from equal costs or equal envelopes. An additional coordinate transport exchanges the modulo9 branches two and five while preserving modulo5, the source carrier, each named partition, and all four source weight fields. These two operations yield 16 comparison groups.

Nineteen group members use identical same-cell K7 fields, and three use that whole-coordinate transport. The former statement only identifies the complete inputs of the later comparison—K7 field, fixed source weights, positive7 law and thresholds. It does not identify the two actual sources or their full probability laws. Every member retains its own current7 upper bound. Under coordinate transport, all future labels are transported together.

## Finite bounds and exceptional joint interfaces

Each comparison group has 35 bounds retaining the current modulo15 phase and releasing the current modulo3/5/9 heads. Previous stages after seven are initially enlarged to their full multiplier laws. Fourteen selected stage11/13 phase tables then retain all 40 actual current labels. This suffices for 18 of the 22 sources.

For source `(1,3,7,8)`, exactly four prefix pairs remain: `{A,B}^2`, where `A=(2,4,2,14)` and `B=(2,4,5,14)`. Two direct actual11/current13 calculations cover `A/A` and `A/B`; the source-preserving branch swap covers `B/B` and `B/A`. These actual current13 bounds close the four pairs without subtracting an analytic credit.

The last three sources are `(1,4,7,4)`, `(1,4,7,7)` and `(1,4,7,13)`. Put `C=(2,4,8,14)`. For each source, the only remaining prefix pairs lie among `A/A`, `A/B`, `A/C`, `C/A` and their simultaneous branch swaps. The corresponding comparison preserves all three actual zero fields, at seven, eleven and thirteen, and all eight zero/positive components. Each of the twelve representative joint interfaces has 21 later bounds—seven phases at each of 17, 19 and 29—and eight complete ordinary envelopes for its own query numerator. A selected stage17 phase14 table retains all 40 actual labels for the `A/B` interface of each source. The other late phases remain covered by the phase bounds.

For each route, losses and query numerator refer to one common actual source and one coherent selection of the first labels. Multiplication by later full laws is a uniform enlargement, not a claim that independently maximizing layouts coexist. In particular, a current13 bound using one actual11 field is never spliced into a different actual11 source. All recorded full40 tables contain 40 physical labels; no 32-plus-8 shortcut is used.

The ordinary proof is monotonicity of the nonnegative padded kernels under these full-law enlargements, followed by the finite all-phase/all-label bounds. Exact arithmetic checks the strict condition

`14 * (135/4 - sum of six loss upper bounds) > H16`.

It also rounds every loss upward to a millionth and the query numerator upward to a millionth, and checks that strict positivity survives. Uniform cases are covered by a separable maximum; the four groups requiring conditional routes are checked over all 78,400 first-two-label pairs. Each later triple is covered uniformly, giving the full `280^5` domain per source.

The common query upper bound for these 22 sources is `28.9968048292 < 29`. The minimum strict slack after millionth rounding is `0.007424`. The routes cover `22 × 280^5 = 37,862,809,600,000` future parameter tuples, with a separately retained current7 bound for every source.

## Reproduction

```sh
python3 -I -S -B verify.py
python3 -I -S -B -O verify.py
python3 -I -S -B geometry_replay.py --group 0 --kind current7 --source 1,1,7,4 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --group 0 --kind query --cache /explicit/cache
python3 -I -S -B geometry_replay.py --group 0 --kind released --cache /explicit/cache
python3 -I -S -B geometry_replay.py --group 0 --kind four --prime 11 --eta 14 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --group 6 --kind actual13 --a 2 --b 5 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --group 4 --kind joint --a 2 --b 5 --cache /explicit/cache
python3 -I -S -B geometry_replay.py --group 4 --kind joint-four --a 2 --b 5 --prime 17 --eta 14 --cache /explicit/cache
```

`--base` locates the pinned `missing23-eta14` package. Default runs write only stdout; `--output` retains the result explicitly. The producer is cache-only by default and reads only explicitly named full-input SHA256 keys. Repeated `--cache` arguments add named directories; `--fresh` permits missing-key generation; `--regenerate` recomputes existing keys; `--binary` selects the enumerator. Source, license, multiplier laws and integer geometry are inherited from the pinned base package.

The arithmetic consumer has no assertion checks that disappear under `-O`. The geometry producer inherits the original source's explicit refusal of `-O`. Numerical input validation and arithmetic are separate from regeneration of geometric maxima. The finite comparisons and ordinary mathematical transport proof are not new Lean verification.
