# Exact affine divisor moments and actual cores

`affine_moments.py` needs Python 3.9+ and only the standard library. Run:

```sh
python3 affine_moments.py --out /tmp/affine-moments.json
```

The required output path is the only result file written. Optimized Python and
source overwrite, including symbolic and hard links, are rejected. The JSON
records the program's SHA-256, every finite input range and deterministic result
hashes. There are no timestamps, elapsed-time fields or floating-point values.

For each row below the program enumerates every integer multiplier from
`ceil(F_r/10)` through `floor(F_r/5)`, inclusive, and factors the actual integer
`N = g*F_r+1` by a prime sieve on that progression.

| Prime index r | Integer core cutoff y | Actual integers |
|---|---|---|
| 7 | 8 | 1 |
| 11 | 13 | 9 |
| 13 | 16 | 23 |
| 17 | 22 | 160 |
| 19 | 24 | 418 |
| 23 | 30 | 2,866 |
| 29 | 39 | 51,423 |
| 31 | 42 | 134,627 |

These 189,527 integers are the complete listed intervals. The cutoffs are
explicit integer inputs, not certified evaluations of a logarithmic formula.
The sieve computes the exact divisor sum, the complete small-prime-power core
`C_y(N)`, and its squarefree radical `R_y(N)`.

For each order `k=1,2,3`, set `Q=10^12`. For every actual integer, integer
quotient and remainder compute

`floor(Q*(sigma(N)/N)^k)` and `ceil(Q*(sigma(N)/N)^k)`.

Summing these integer endpoints and dividing by `Q*T` encloses the uniform
interval mean of `Z(N)^k`. Each enclosure has width at most `1/Q`; this avoids
adding all 189,527 rational values with unrelated denominators. The JSON
retains reduced rational endpoints. The recorded widths are all exactly
`1/1000000000000`.

The first and last multiplier and the first maximizers of the core, radical
and exact `Z(N)` are retained. A separate trial-division routine verifies their
factorizations. Fast-doubling Fibonacci reconstruction and an independent
integer greedy decoder verify each retained composition and its canonical
unit bit one. This source reconstruction covers the representatives; the
program does not claim to run a separate greedy decoder on every enumerated
integer.

The shared-divisibility test exhausts `V=1,...,6`, starting multipliers
`G0=1,...,4`, interval lengths `1,...,4`, and orders `k=1,2,3`. For every one
of these 96 intervals it enumerates all ordered tuples `(d_1,...,d_k)` in
`[1,X]^k`, where `X=V*G1+1`; thus `X<=43` and 779,360 tuples are checked.
Actual divisor-incidence intersections are compared with the single-residue
floor formula for `lcm(d_1,...,d_k)`. Exact rational sums independently agree
with the direct moment and satisfy `abs(mean-S_k(V,X)) <= H_X^k/T`.
The range includes noncoprime moduli, single-element intervals, and moduli
larger than the interval length that either hit once or miss. It does not
replace a joint event by a product of marginal probabilities.

The retained pointwise counterexample is

`r=29, V=514229, g=75085, N=38610884466`

with factorization `2*3^4*7^2*11*17*19*37^2`, canonical composition
`(5633252125,9114793405)` and unit bit one. At the explicit cutoff `y=39`,
`C_39(N)=N>V` and `R_39(N)=5521362>V`. Its core modulus exceeds the multiplier
interval length but has exactly one hit in that interval. This refutes the
stated pointwise core bounds; it is not an asymptotic or Robin counterexample.

These are finite exact diagnostics. They do not certify Euler constants,
logarithmic Robin budgets, limiting moments, density bounds, or any infinite
family theorem. No Robin margin or RH conclusion is computed. The analytic
arguments remain the responsibility of the theory text.
