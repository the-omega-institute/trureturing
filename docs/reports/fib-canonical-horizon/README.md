# Canonical Fibonacci coefficient and terminal horizons

This standalone exact-integer experiment accompanies §§106–107 of
[Fibonacci Atomic Relation Generation](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md).
It checks bounded common-coefficient constructions, the counting obstruction at
12 windows, four finite terminal-state covers, and an actual global lower witness.
The two depths concern different tasks: **13** is universal coefficient-pair
saturation at modulus 5040; **3** is the complete-future distinguishing horizon
for the specified terminal `F_5040`/error output. End costs no window.

## Files and reproduction

- `certificate.py`: all mathematical parameters, a fixed sample generator,
  exact integer checks, and finite-cover construction. Python 3.8 or later,
  standard library only; no input files, network, Git, Mathlib or repository
  environment are required.
- `results.json`: deterministic per-modulus summaries, six selected coefficient
  witnesses, local-cover counts and the global lower pair. Full coefficient
  tables and transition/partition vectors are computed and checked in memory.
- `README.md`: contracts, scope, reproduction and mathematical sources.

From the repository root, choose any writable output path:

```sh
python3 docs/reports/fib-canonical-horizon/certificate.py --output fib-canonical-results.json
cmp docs/reports/fib-canonical-horizon/results.json fib-canonical-results.json
```

Without `--output`, canonical JSON goes to standard output. The script also runs
from any working directory, including when copied alone. JSON uses sorted keys,
two-space indentation, ASCII encoding and a final newline. Checks run before
serialization; a failed mathematical condition prints its counterexample to
standard error and exits nonzero. Checks remain active under `python3 -O`.
Stored data are never loaded as answers by the program.

The delivered script was executed from a different working directory and as a
single-file copy in a path containing spaces, with a minimal environment and
different hash seeds; normal and `-O` executions both exited 0 and produced
byte-identical results matching `results.json`. This verifies those executions,
not every Python version or operating system. No official review or CI vote is
represented by this implementation result.

## Coefficient contract and finite scope

Digits are read from low to high; `F_0=0`, `F_1=1`. For an incoming weight row
`(u,v)`, successive weights follow `(u,v) -> (v,u+v)`. A word has exact integer
coefficients `(a,b)` obtained independently by evaluating it at `(1,0)` and
`(0,1)`; linearity of this recurrence gives value `a*u+b*v` for every row.
The modular target `(A,B)` is `(a mod H,b mod H)`.

For each checked `H`, take the first Fibonacci number `q=F_j>2H`, the least
`m` with `F_m >= H(q+1)`, and `L=ceil(m/3)`. Their minimality inequalities are
checked. For each target, inspect all `1 <= t <= q`, put `n=B+Ht`, and compute
`a=floor((n+1)/phi)` as `(isqrt(5*(n+1)^2)-(n+1))//2`.
Every evaluation also passes the independent integer inequalities
`0 <= 2a+n+1` and `(2a+n+1)^2 <= 5(n+1)^2 < (2a+n+3)^2`.

Greedy Zeckendorf decomposition independently reconstructs `n`, nonadjacent
support, and the exact coefficient pair `(a,n)`. Every target gets an actual
nonempty word starting `00`, legal after either incoming seam, with nonzero
final triple and at most `L` windows. At most two high zero bits are added.
Positivity is also checked on the actual row `(1,2)`; positive actual Fibonacci
weights make the same nonempty selection positive at every actual row. The
all-row linear identity and that semantic interpretation are ordinary arguments.

| Check | Scope | Result |
|---|---|---|
| Exhaustive coefficient targets | Every pair for each `H=2..64` | 89,439 targets; 228,435 candidate evaluations |
| Fixed coefficient sample | Exactly 256 pairs at `H=5040` | 256 covered; 2,802,176 candidate evaluations |
| 5040 upper parameters | Integer recurrence and inequalities | `q=10946`, `m=39`, `L=13` |
| Canonical padding bijection | Literal enumeration for `L=1..4` | Counts agree with `F_(3L+1)-1` and `F_(3L)-1` |
| 12-window counting obstruction | Fibonacci recurrence | `F_37-1=24157816 < 5040^2=25401600` |

The sample is fixed before coefficient evaluation. It starts with the ordered
Cartesian square of `[0,1,2,3,5036,5037,5038,5039]` (`A` outer, `B` inner).
For counters starting at zero, SHA-256 of ASCII
`fib-canonical-horizon-5040-sample-v1:` followed by the decimal counter supplies
two big-endian 16-byte integers, each reduced modulo 5040. Append unseen pairs
until there are 256. This consumes 192 counters. The result records the digest
of the compact JSON array of ordered pairs. Targets are never selected using
coverage results. Selected reported witnesses are `(0,0)` at `H=2,64`, and
`(0,0),(0,5039),(1,0),(5039,5039)` at `H=5040`.

No enumeration of all 25,401,600 coefficient pairs at 5040 is claimed. The
all-`H` shifted-grid argument and the all-`L` counting bijection belong to §106.
The latter counts nonempty words legal after both seams: the first bit is zero;
requiring a second initial zero gives the smaller count `F_(3L)-1`.
Padding to a fixed length is a counting map, not permission to accept a zero
final window. The ordinary upper construction and counting lower bound together
give `D(5040)=D00(5040)=13`. Finite samples alone do not prove that statement,
and this count gives no 13-window terminal-output lower bound.

## Finite terminal-cover contract

The alphabet is `000,100,010,101,001`. For each local modulus `h`, construct
from scratch the orbit of `(2,3) mod h` under
`(u,v) -> (u+2v,2u+3v) mod h`. The cover contains every tuple `(r,u,v,s,E)`
with `r mod h`, a row on that orbit, and `(s,E)` in
`{(0,false),(0,true),(1,true)}`, plus `INVALID`. Both initializations are
included: `(0,2,3,0,false)` and `(1,2,3,1,true)`, reduced modulo `h`.
The cover may contain states not generated by actual prefixes; reachability
of all its rows is not needed or claimed. Initial containment and closure
suffice to contain every initialized execution.

On block `(b0,b1,b2)`, an occupied incoming seam followed by `b0=1` enters
`INVALID`. Otherwise update the residue by
`(b0+b2)*u+(b1+b2)*v`, advance the row three steps, set `s=b2`, and set
`E=(block != 000)`. Every one of the five transitions at every tuple is checked
against an independent three-single-bit computation and for closure. `INVALID`
has five self-loops and always returns `ERROR`.

End returns `h/gcd(r,h)` when `E=true`, and `ERROR` otherwise. On actual
initialized executions, `E` means that the current last window is nonzero
(or the positive unit initialization has no windows); it is not an
ever-positive flag. Together with legality this implies positive canonical
End. A legal prefix with `E=false` can recover: the checker verifies that `010`
leads to a non-error output for every such state. A residue of zero with
`E=true` correctly outputs 1; it need not denote the integer zero.

Start `P0` with End labels. Form `P(k+1)` from the signature consisting of
the current `Pk` class and all five successor `Pk` classes. Every refinement
is checked not to merge classes. Canonical first-occurrence class IDs allow
comparison of the complete relation vectors; the stopping condition is exact
vector equality. The final relation is also independently checked for equal
outputs and congruent successors. Equality of class counts alone is not used
as the stopping certificate. By induction, `Pk` describes agreement on all
words of length at most `k`, including the empty word and errors; a stable
output/successor congruence preserves agreement for every longer word.

| `h` | Orbit rows | Cover states | Five-symbol edges | Class counts from `P0` | Stable depth |
|---:|---:|---:|---:|---|---:|
| 16 | 8 | 385 | 1925 | 6,59,161,193,193 | 3 |
| 9 | 8 | 217 | 1085 | 4,65,107,109,109 | 3 |
| 5 | 20 | 301 | 1505 | 3,30,76,76 | 2 |
| 7 | 16 | 337 | 1685 | 3,31,155,169,169 | 3 |
| Total | | 1240 | 6200 | | |

## Actual lower pair and proof boundary

The program greedily encodes and directly decodes the actual integers
`2179485` and `2182005`. They share next weights `(3524578,5702887)`, seam 1
and `E=true`. All 31 suffixes of lengths 0, 1 and 2 give equal `F_5040`/error
outputs, including 18 common errors. The suffix `000|000|010` gives
`104513640` and `104516160`, with gcds 840 and 1680 against 5040 and outputs
6 and 3. The concrete codes, integer decodings and length summaries are retained.

These computations supply the local finite upper certificates and a global
three-window lower witness. The ordinary semantic invariant connecting actual
integer prefixes to the local covers, and common-source CRT transport over
`5040=16*9*5*7`, are separate paper dependencies in §107. On the same actual
prefix and suffix, error status is shared and a successful global output is
the product of the four coprime local outputs; equality of such products also
determines their local factors. Together with the finite certificates this
gives the paper's exact terminal horizon 3. No global 5040 state graph is built.
This computation does not establish an unbounded all-`H` theorem, a Lean/kernel
proof, or a runtime/query-count bound.

## Sources and license

The mathematical source is the repository's
[Fibonacci Atomic Relation Generation, §§104–107](../../develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md):
§§104–105 supply the positive canonical-window reader, two initializations,
terminal error semantics and Fibonacci row recurrence; §§106–107 supply the
coefficient and CRT horizon arguments. Related reused background is identified
in [Katz interface notes §12](../../../Library/notes/katz2015goldeninterfaces.md#12-exact-zeckendorf-predictive-states-at-the-original-prime-square-scale).
The existing `ZeckendorfFutureKernel` and `PrimePowerAffineBehavior` results
cited by §105.9 have narrower formal contracts; citing them does not certify
the present experiment or its full paper statements in Lean.

This repository experiment and its result data use the repository's
[Apache License 2.0](../../../LICENSE). No external program or data set is bundled.
