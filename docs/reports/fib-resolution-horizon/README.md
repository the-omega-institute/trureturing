# Exact finite terminal horizons

This standalone supplement derives 165 exact finite horizons for the actual
canonical reader of [theory §§104–110](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
It is a fixed mathematical experiment, not a generic formal solver or Lean
evidence. The ordinary proofs of the bounds for all moduli are in §§109–110;
the finite measurements here do not establish those uniform bounds.

The fixed scope is every positive divisor `d` of each `H=2..40` (157 tasks),
plus `H=64,128` with `d=1,2,4,8` (8 tasks). One graph is built per modulus:
41 graphs, 95,831 states and 479,155 directed state/window edges in total.

## Contract and outputs

A source is an actual initialized prefix `(epsilon, x)`, with either
`epsilon=0` or `epsilon=1` and any finite word `x` over
`000,100,010,101,001`. Bits run from low to high position. Past lengths are
arbitrary and may differ; illegal prefixes are included. There is no extra
phase clock, prefix-length input, or source rereading. Every comparison uses
the same literal suffix on both sources, including the empty word and words
that cause an illegal seam or improper End.

The live coordinates are `(s,E,r,u,v)`, initialized as
`(epsilon,epsilon,epsilon,2,3)` modulo `H`. After `j` legal windows the actual
next row is `(F_(3j+3),F_(3j+4))`, where `F_0=0,F_1=1`. A window
`b=(b0,b1,b2)` enters the absorbing sink if `s=b0=1`; otherwise it gives

```text
s' = b2
E' = (b != 000)
r' = r + (b0+b2)u + (b1+b2)v   modulo H
(u',v') = (u+2v, 2u+3v)       modulo H
```

End costs zero windows. It outputs the separate symbol `err` from the sink
or a live state with `E=false`. From a live state with `E=true`, the actual
integer is positive and the output is `eta_(H,d)(r)`. Residue zero is a valid
successful output. A whole last `000` clears `E`, even if earlier windows
contributed a positive value. Up to two high zero bits within a nonzero last
window are permitted. The three live tags, in enumeration order, are
`A=(0,false)`, `B=(0,true)`, `C=(1,true)`.

For each complete prime-power factor `p^h` of `H`, put `e=v_p(d)`, `k=h-e`
and let `t` be the truncated valuation of the local residue `x`, with `t=h`
at zero. The local label is

```text
S(t, x/p^t modulo p^k)   if t < e
D(x/p^e modulo p^k)      if t >= e
```

The two tags are disjoint. The quotient is formed using an integer
representative divisible by the indicated power; changing representatives
does not change the label. Coordinates modulo 1 are singletons. The global
label is the tuple in ascending prime order. At `d=1` this is the full
residue; at `d=H` it recodes `H/gcd(r,H)`. As an arithmetic interpretation,
eta records the entire allowed post-End response family from §104, not one
`F_H` query. Arithmetic is not interleaved with the counted window suffix.

The reported `depth` is `h_eta(H,d)`: the least nonnegative `L` such that
equality after every literal suffix of at most `L` windows implies equality
after every finite suffix. It measures windows before End, not state count,
query count, runtime, or length of a post-End arithmetic calculation.

## Why the graph is exactly the actual source image

The program discovers the exact orbit of `(2,3)` modulo `H` under
`T(u,v)=(u+2v,2u+3v)`, stopping at its first repeated row and checking that
this is the initial row. The matrix has determinant `-1`, so it is invertible
modulo every `H`. The resulting period is the actual stride-three period
`P(H)` of §105.2. The graph consists of every residue, every row of that
orbit, all three live tags, and one sink.

Every actual prefix maps into this graph by the recurrence and the error
rule. For the reverse inclusion, fix any phase `j0 mod P(H)` and take
arbitrarily large `j=j0+nP(H)`. With **both** initializations allowed,
§105.1 gives the actual integer images at that single `j`:

| Tag | Integer image | Length |
|---|---|---|
| A | `[0,F_(3j)-1]` | `F_(3j)` |
| B | `[F_(3j),F_(3j+2)-1]` | `F_(3j+1)` |
| C | `[F_(3j+2),F_(3j+3)-1]` | `F_(3j+1)` |

For sufficiently large `j`, all three lengths are at least `H`. Each
interval then contains every residue modulo `H` while the phase stays
fixed. Every listed live state consequently has an actual prefix witness.
For the successful tags B and C these representatives are positive,
including representatives of residue zero. The sink is reached from
`epsilon=1` by `100`. This is the same common-phase realization principle
used in §109. It does not assert that the product occurs at every small
prefix length or for a fixed initialization separately.

Thus the product is exactly the source image. Closure alone would prove
only coverage and would not justify exact lower bounds. The program does
not replace this reachability proof with a modular BFS.

## Exact refinement and minimality

State indices are `(phase*H+residue)*3+tag`, followed by the sink at
`3*P(H)*H`. Rows follow orbit order starting at `(2,3)`. The five successors
follow the window order above. `P0` groups equal End outputs. A refinement
signature consists of the state's **old class** and the five successor old
classes. Class IDs are assigned by first occurrence in increasing state
order, starting at zero.

By §107.4, `P_L` is equality of all responses through `L` windows: the old
class retains shorter words and each child class handles one common first
letter followed by a shorter suffix. If the full canonical vectors for
`P_L` and `P_(L+1)` are equal, the partition is a right congruence preserving
outputs; induction on suffix length proves all future equality. The first
such `L` is the exact horizon. Every earlier strict refinement supplies a
pair equal at that earlier budget and separated later; actual reachability
of every graph state makes these pairs valid source pairs.

The stopping test compares the **entire vectors**, before hashing the new
vector. Counts and hashes are never substituted for that comparison.
The program explicitly checks that no new class merges old classes and
that every nonterminal round strictly increases the class count. There can
be at most `states-|P0|` strict refinements, followed by one equality round.
All checks use explicit exceptions and remain active with `python -O`.

Independent finite consistency checks include:

- Every live state/window transition is compared with a separate literal
  three-bit implementation, including the resulting Fibonacci row.
- Every orbit row is primitive; both initial states are present; all five
  sink edges are absorbing; the illegal seam count is checked.
- Every successful zero residue remains distinct from `err`.
- For every task, eta's residue partition is compared with the partition
  obtained directly from all arithmetic response vectors
  `(H/gcd(a*r+d*b,H))`, with `0<=a<H` and `0<=b<H/d`.
  These exhaust the affine maps of §104.4 modulo `H`; `a=0` is realized by
  a positive multiplier `H`. This checks the terminal label interpretation,
  not an arithmetic query or runtime bound.
- Eta's zero fiber is a singleton; the full-residue and gcd endpoints are
  checked directly; all measured `d=1` horizons equal one.

## Files, data, and finite boundary

`certificate.py` derives all graphs, labels and partitions without reading
any input file. `results.json` is its deterministic output: sorted keys,
two-space indentation, ASCII JSON, and a final newline. It contains only
the mathematical contract, scope, graph data, per-task results and check
results. `README.md` supplies the proof interpretation and usage. These
files are covered by the [project license](../../../LICENSE).

Each graph records its orbit, state and edge counts, initialization indices
and transition-vector hash. Each task records its local `(p,h,e,M)` axes
with `M=p^(h-e)`, label count, depth, every partition cardinality, changed
vector positions, and every partition-vector hash. The cardinality and
hash lists start at `P0` and include the final repeated stable partition;
the change list starts at `P0 -> P1`. Thus `refinement_rounds=depth+1`.
Hashes encode concatenated unsigned 32-bit little-endian entries without
a header. They document vectors; they are not proof objects. `Q` is the
largest complete prime-power factor of `d`, and is `null` at `d=1`, where
the logarithmic expression is not used.

Selected exact finite measurements are:

| H | d | Q(d) | Horizon | Partition cardinalities through equality |
|---:|---:|---:|---:|---|
| 2 | 2 | 2 | 1 | 3, 7, 7 |
| 4 | 2 | 2 | 2 | 4, 21, 25, 25 |
| 23 | 23 | 23 | 5 | 3, 20, 132, 510, 552, 553, 553 |

The first two rows disprove an exact formula depending only on `Q(d)`.
The third records `h(23)=5` by finite enumeration. All 165 full task records
are in `results.json`; no inference from this finite range to all `H` is
made. The uniform ordinary bounds and their common-source assumptions are
proved in §§109–110. Optimal additive constants and unenumerated exact
horizons remain unspecified. Neither this program nor the theory prose
claims Lean kernel verification or a literature novelty result.

## Reproduction

Python 3.9 or newer and its standard library suffice. No package installation,
network, Git, repository discovery, scratch files or environment variables
are used by the program. The only file argument is the optional output
destination; its parent directory must already exist. Without `--output`,
only the same JSON is written to stdout. A failed check raises an exception
and exits nonzero before emitting a result.

From the repository root:

```sh
python3 docs/reports/fib-resolution-horizon/certificate.py --output /tmp/fib-horizon-normal.json
cmp docs/reports/fib-resolution-horizon/results.json /tmp/fib-horizon-normal.json
python3 -O docs/reports/fib-resolution-horizon/certificate.py > /tmp/fib-horizon-optimized.json
cmp /tmp/fib-horizon-normal.json /tmp/fib-horizon-optimized.json
```

To check a copied script with a different working directory and no shell
startup files (the `python3` interpreter must be on `PATH`):

```sh
mkdir -p '/tmp/fib horizon standalone'
cp docs/reports/fib-resolution-horizon/certificate.py '/tmp/fib horizon standalone/certificate.py'
(cd /tmp && env -i PATH="$PATH" python3 -I '/tmp/fib horizon standalone/certificate.py' --output '/tmp/fib horizon standalone/results.json')
cmp docs/reports/fib-resolution-horizon/results.json '/tmp/fib horizon standalone/results.json'
```
