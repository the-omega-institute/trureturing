---
slug: oeis-a008590-gcd-sum-parity-characterization
bibkey: sloane2017a008590
doi: null
url: https://oeis.org/A008590
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/RatajczakGcdSumParityCharacterization
---

# The A008590 gcd-filtered sums characterize the positive multiples of eight

## Problem

OEIS A008590, NAME (`%N`, verbatim):

> Multiples of 8.

Lechoslaw Ratajczak's COMMENT conjecture (`%C`, verbatim):

> From _Lechoslaw Ratajczak_, Sep 03 2017: (Start)
>
> Conjecture: let gcd_2(b,c) be the second greatest common divisor and lcd_2(b,c) be the second least common divisor of not coprime integers b and c. Consecutive elements of this sequence (for a(n) > 0) are consecutive integers m for which both Sum_{k=1..m, gcd(k,m)<>1} gcd_2(k,m) and Sum_{k=1..m, gcd(k,m) <>1} lcd_2(k,m) are even numbers.
>
> a(1) = 8 because 1+2+1+4 = 8 (8 is even) and 2+2+2+2 = 8 (8 is even).
>
> a(2) = 16 because 1+2+1+4+1+2+1+8 = 20 (20 is even) and 2+2+2+2+2+2+2+2 = 16 (16 is even).
>
> a(3) = 24 because 1+1+2+3+4+1+1+6+1+1+4+3+2+1+1+12 = 44 (44 is even) and 2+3+2+2+2+3+2+2+2+3+2+2+2+3+2+2 = 36 (36 is even).
>
> The conjecture was checked for 5*10^4 consecutive integers. (End)

For `d = gcd(k,m)`, the example at `m=24` fixes
`gcd2(k,m) = d / minFac(d)` and `lcd2(k,m) = minFac(d)`. Thus `gcd2`
is the greatest proper divisor of a nontrivial gcd and `lcd2` is its least
divisor greater than one. Define
`G(m) = Sum_{1<=k<=m, gcd(k,m) != 1} gcd2(k,m)` and
`L(m) = Sum_{1<=k<=m, gcd(k,m) != 1} lcd2(k,m)`.

The literal proved statement is
`forall m : Nat, 1 < m -> ((Even (G m) and Even (L m)) iff 8 divides m)`.
At `m=1` both filtered sums are empty and equal zero, hence both are even,
while one is not a positive multiple of eight; this is the unique mismatch in
the independent scan on `[1,6000]`, and the theorem explicitly assumes
`1 < m`. The knight-move, odd-square-difference, lattice-pair, square-frame,
and Catalan/Berdellé eight-odd-squares comments in A008590 are NOT claimed.
Values of `gcd2` and `lcd2` on coprime pairs are also NOT claimed.

## Motivation

The conjecture gives an arithmetic characterization of the positive terms of
A008590 through two independently defined gcd-filtered sums. Proving the
simultaneous parity condition converts Ratajczak's bounded check into a
classification for every natural `m` above the empty-sum boundary.

## Gap

On 2026-09-14, OEIS revision #116 still printed Ratajczak's 2017 comment as a
"Conjecture" and its revision history contained no settlement. The probe found
zero arXiv identifier or exact-phrase matches and zero MathOverflow matches.
OpenAlex returned one unrelated 2024 paper for the broad query and two
unrelated cognitive-science records for the exact phrase. GitHub returned 27
generic sequence implementations and five exact-phrase hits; the only relevant
one was an OEIS mirror, while four were unrelated programming exercises. The
orchestrator's two WebSearch queries returned zero relevant results. These
checked surfaces do not support an exhaustive literature or priority claim.

## Route

1. For any `f : Nat -> Nat`, delete the endpoint `k=m` and pair the remaining
   filtered indices by the involution `k |-> m-k`. In `ZMod 2` all nonfixed
   pairs cancel, and the unique possible fixed point is `m/2`. This proves the
   gcd-filtered parity identity with exact endpoint and fixed-point terms.
2. Apply the identity to `f(d)=d/minFac(d)` and to `f(d)=minFac(d)`. If `m` is
   odd, the `L` endpoint is odd; at `m=2`, the `G` endpoint is odd; and when
   `m` is two modulo four and exceeds two, the midpoint makes `L` odd.
3. If four divides `m`, both least prime factors are two. The `L` terms cancel,
   while `G` is even exactly when `m/4` is even, equivalently when eight
   divides `m`. Combining the four cases proves both directions of the iff.

## Falsifier

Any natural `m` with `1 < m` for which the simultaneous parity of `G(m)` and
`L(m)` differs from divisibility by eight would contradict the theorem. The
kernel-checked result quantifies over every such `m`.

## Evidence

- Lean module:
  `D5/S3/ArithSums/RatajczakGcdSumParityCharacterization.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 8.71 seconds, type checking
  192 milliseconds, and maximum resident set size 1,675,739,136 bytes.
- The orchestrator and probe independently found the mismatch set `{1}` on
  `[1,6000]`; at `m=1`, `G(1)=L(1)=0`.
- The gcd-filtered parity formula had zero violations on `[1,6000]` for both
  summands. The values `(G,L)` at `m=8,16,24` were `(8,8)`, `(20,16)`, and
  `(44,36)`, reproducing all three worked examples in the OEIS comment.
- The bounded checks support fault detection only; the Lean involution and
  residue-class proof carries the universal classification.

## Triage

`theorem`. Ratajczak's simultaneous parity classification is proved for every
natural `m` satisfying `1 < m`; the resolution is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

The bounded scans do not establish the universal statement. Historical
openness outside the checked OEIS history, arXiv, MathOverflow, OpenAlex,
GitHub, and WebSearch surfaces is unverified; no exhaustive literature or
priority claim is made.
