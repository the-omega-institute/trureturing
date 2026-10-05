# Exact arithmetic identification and its stability boundary

[phase_readout.py](../../../experiments/arithmetic-observability/phase_readout.py)
searches observation fibers on an explicitly declared finite source set. The
observations are the ordered pair of squared norms before and after the same
linear update. It uses exact rational or prime-field arithmetic, with no
third-party dependencies. The general field criterion, real collision,
operator comparison and noise boundary are developed in
[source-domain research analysis, §§13–16](analysis.md).

Run from the repository root with Python 3.9 or newer:

```sh
python3 experiments/arithmetic-observability/phase_readout.py > /tmp/arithmetic-readout.json
cmp /tmp/arithmetic-readout.json docs/reports/arithmetic-observability/result.json
python3 -m unittest discover -s experiments/arithmetic-observability -p 'test_*.py' -v
python3 experiments/arithmetic-observability/phase_readout.py --input /path/to/model.json
```

An input supplies one matrix and distinct actual states. Entries are rational
strings. Omitting `modulus` selects rational arithmetic; supplying a prime
integer selects arithmetic modulo that prime. Rational denominators must be
nonzero modulo the prime. Duplicate states after field conversion, composite
moduli, malformed arrays and non-string entries are rejected.

```json
{
  "matrix": [["0", "1"], ["1", "1"]],
  "states": [["1/2", "1/3"], ["-1/2", "-1/3"]]
}
```

A result reports state count, discriminant of the first-step Gram matrix,
observation-bucket count, maximum bucket size, and number of buckets containing
a collision beyond global sign. A collision gives two actual states and their
common reading. The source set need not contain negatives of every state;
comparison beyond sign still uses equality in the declared field. Over a prime
field, “squared norm” means the quadratic form, which can vanish on a nonzero
state.

The default rational source set is the integer lattice `[-6,6]²`, containing
169 states. Each prime fixture enumerates the entire field square in
lexicographic order. All model inputs are included in `result.json`.

| Update/source | States | Buckets | Maximum bucket | Extra-collision buckets | Discriminant |
| --- | ---: | ---: | ---: | ---: | ---: |
| Fibonacci, rational lattice | 169 | 85 | 2 | 0 | 5 |
| diag(1,2), rational lattice | 169 | 49 | 4 | 36 | 9 |
| Fibonacci, F2 | 4 | 4 | 1 | 0 | 1 |
| Fibonacci, F3 | 9 | 5 | 2 | 0 | 2 |
| Fibonacci, F5 | 25 | 11 | 5 | 1 | 0 |
| Fibonacci, F7 | 49 | 25 | 2 | 0 | 5 |
| Fibonacci, F11 | 121 | 36 | 4 | 25 | 5 |
| Fibonacci, F13 | 169 | 85 | 2 | 0 | 5 |
| Fibonacci, F17 | 289 | 145 | 2 | 0 | 5 |
| Fibonacci, F19 | 361 | 100 | 4 | 81 | 5 |

The characteristic-two fixture lies outside the field theorem's assumptions.
The rational finite lattice does not prove identification on all rational
states. The general nonsquare-discriminant criterion supplies that conclusion
by ordinary mathematical derivation; the finite counts are independent evidence
for the listed domains only.

The eight `pell_near_collisions` rows use the exact recurrence
`p'=9p+20q, q'=4p+9q`, starting at `(1,0)`. Each row gives a rational
state `(-q/p,2q/p)`, both readings, their error from `(1,1)`, and the gap in
the target `a²` relative to `(1,0)`. The Pell invariant is `p²-5q²=1`.
The readout error is exactly `1/p²`, while the target gap is strictly greater
than `4/5`. The all-index induction and error bound `81^-n` are in the [research analysis, §15.2](analysis.md#152-无浮点平方根的任意精度近碰撞); computing eight rows does not certify the infinite statement.

The experiment supports finite collision search, counterexample discovery and
exact near-collision generation. It does not implement recovery from noisy
readings or certify an optimal decoder. This delivery retains no new Lean
wrapper: algebraic applications are reused, with temporary exact checks of the
nonsquare sufficient direction, rational Fibonacci specialization, shear
reconstruction identities and absence of a global continuous target decoder.
The full iff, all-history recurrence and quotient inverse discontinuity remain
ordinary mathematical derivations rather than newly frozen declarations.

License: Apache-2.0, under the repository LICENSE.

Independent verification reconstructed all default readouts and witnesses,
checked 495 symmetric B matrices and 3,107 update A matrices over F3/F5/F7
with zero mismatches, and independently expanded the eight Pell powers.
The supplied six tests pass; default output matches the saved JSON byte for
byte. The temporary Lean checks pass with only `propext`, `Classical.choice`
and `Quot.sound` in the inspected axiom closures. Full statements beyond those
scoped checks remain ordinary mathematical derivations.
