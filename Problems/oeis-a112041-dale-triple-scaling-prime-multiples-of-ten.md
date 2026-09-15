---
slug: oeis-a112041-dale-triple-scaling-prime-multiples-of-ten
bibkey: cami2015a112041
doi: null
url: https://oeis.org/A112041
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen
---

# The A112041 prime scalings force the index to be four or divisible by ten

## Problem

OEIS A112041, NAME (`%N`, verbatim):

> Numbers k such that 1*k + 1, 3*k + 1, 9*k + 1, 27*k + 1 are all primes.

Harvey P. Dale's COMMENT conjecture (`%C`, verbatim):

> Conjecture: all terms except the first are multiples of 10. - _Harvey P. Dale_, Mar 26 2015

The literal proved statement is
`forall k : Nat, 0 < k -> (Nat.Prime (k + 1) and
Nat.Prime (3 * k + 1) and Nat.Prime (9 * k + 1) and
Nat.Prime (27 * k + 1)) -> (k = 4 or 10 divides k)`.
Infinitude of A112041, a characterization beyond this implication, and all
other comments on A112041 are NOT claimed.

## Motivation

Dale's comment asserts a divisibility pattern for every term after the first.
The theorem settles that implication uniformly for every positive natural k,
including the exceptional first term k=4 as a separate disjunct.

## Gap

On 2026-09-15, the probe read OEIS revisions 1 through 22. Revision 14 adds
the conjecture, while later revisions contain approval, naming, example, and
program edits but no proof or refutation.

The same probe found zero arXiv results for each of the following searches:
`all:"A112041"`; `"3k+1" AND "9k+1" AND "27k+1"`;
`"admissible tuple" AND "3^i"`; `"Cunningham chain" AND "3k+1"`; and
`"Dickson conjecture" AND "27k+1"`. These checked surfaces do not establish
an exhaustive literature or priority claim.

## Route

If k is odd, primality forces k+1=2 and hence k=1, but then 3k+1=4 is
composite. Thus k is even. Split k modulo five. Residues 1, 2, and 3 make
9k+1, 27k+1, and 3k+1, respectively, divisible by five and larger than five.
Residue 4 forces the prime k+1 to equal five, so k=4. Residue 0 combines with
evenness to give divisibility by ten.

After the definition of `claim` and the local `have` statements are inlined,
this route is bind-only over pinned Mathlib prime-parity and prime-divisor
facts, hypothesis projection, residue case splitting, fixed-numeral `decide`,
and `omega` normalization. No escape witness is asserted.

## Falsifier

Any positive natural k for which all four displayed values are prime but k
is neither 4 nor divisible by 10 would contradict the theorem. A failure of
any required primality conjunct does not meet the theorem's hypothesis.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/DaleTripleScalingPrimeMultiplesOfTen.lean`.
- Main theorem: `result`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Kernel profile on this worktree: wall time 3.30 seconds, type checking
  123 milliseconds, and maximum resident set size 1,319,714,816 bytes.
- Deleting `Mathlib.Tactic.NormNum.Prime` makes the module fail to compile;
  deleting `Mathlib.Tactic.NormNum.Ineq` leaves a zero-exit build, so the
  latter import is not retained.
- The bounded scan for k at most 2,000,000 found 368 qualifying values and
  zero exceptions. Its first eight qualifying values are
  `4, 60, 180, 760, 910, 1020, 1230, 1600`.
- The bounded scan carries no proof; the kernel-checked parity and modulo-five
  argument carries the universal implication.

## Triage

`theorem`. Dale's divisibility implication is proved for every positive
natural k satisfying the four primality hypotheses; the resolution is
`proved`, not `refuted`.

## ASSUMED-UNVERIFIED

Literature completeness outside the checked OEIS revision history and arXiv
queries is unverified, and no priority claim is made. The bounded scan does
not establish the universal statement.
