---
slug: oeis-a328959-divisor-count-prime-factor-bound
bibkey: wiseman2019a328959
doi: null
url: https://oeis.org/A328959
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound
---

# The divisor-count prime-factor bound in A328959

## Problem

OEIS A328959, NAME (verbatim):

> a(n) = sigma_0(n) - 2 - (omega(n) - 1) * nu(n), where sigma_0 = A000005, nu = A001221, omega = A001222.

Here the entry's `omega` is A001222, the number of prime factors counted
with multiplicity, and its `nu` is A001221, the number of distinct prime
factors. In conventional notation these are respectively `Omega` and
`omega`.

COMMENT (verbatim; Gus Wiseman, Nov 02 2019; idea from Mats Granvik):

> Conjecture: All terms are nonnegative except for a(1) = -1.

The exception is exact: `a(1) = -1`. The target is therefore the
nonnegativity assertion for every `n >= 2`.

## Motivation

This 2019 OEIS conjecture asks for a uniform relation between the divisor
count and the prime-factor counts. Proving the full unbounded inequality
resolves the stated conjecture, including every composite and prime input
from `n = 2` onward.

## Gap

The checked surfaces on 2026-09-13 were the OEIS entry and all 10 revisions;
the related entries A320632, A322437, A307408, and A307409; an exact-identifier
search on arXiv; arXiv:2301.13566; an exact search on OpenAlex; the
MathOverflow API; and GitHub repository, commit, and issue search. GitHub code
search required login. A proof or refutation was not found in the checked
surfaces. This is a bounded search report, not an exhaustive literature or
priority claim.

## Route

Write `n = product_i p_i^(e_i)`, put `r = omega(n) >= 1`, and set
`b_i = e_i - 1`. Then `tau(n) = product_i (2+b_i)` and
`Omega(n) = r + sum_i b_i`. Induction on the finite prime set gives

`product_i (2+b_i) >= 2^r + 2^(r-1) * sum_i b_i`.

Two further inductive estimates give `r <= 2^(r-1)` and
`2 + r(r-1) <= 2^r`. Combining them yields
`tau(n) >= 2 + r(Omega(n)-1)`. Casting this natural-number inequality to
the integers proves the stated nonnegativity formula.

## Falsifier

Any natural `n >= 2` with
`sigma_0(n) < 2 + (Omega(n)-1) * omega(n)` would refute the result. A failure
of the finite-product estimate for nonnegative `b_i`, or either power bound
at a positive `r`, would invalidate the proof route. Finite computation alone
cannot establish the universal claim.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.lean`.
- Main theorem: `wiseman_a328959 : forall n, 2 <= n -> 0 <= a n`.
- Public definition: `a`, the integer-valued OEIS expression using
  `ArithmeticFunction.sigma 0`, `ArithmeticFunction.cardFactors`, and
  `ArithmeticFunction.cardDistinctFactors`.
- The theorem's axiom report is std3: `propext`, `Classical.choice`, and
  `Quot.sound`.
- The orchestrator's exact SymPy check for `1 <= n <= 10^5` found only
  `a(1) = -1` negative. The independent probe over the same range counted
  63,022 zeros and 36,977 positive values among `2 <= n <= 10^5`.

## Triage

`theorem`. The Lean theorem proves the entire conjectured nonnegative branch
for every natural `n >= 2`; the source's exceptional value at `n = 1` is not
part of that theorem.

## ASSUMED-UNVERIFIED

The source quotation, attribution, revision count, related-entry scope, and
numerical readings are external evidence rather than kernel-checked facts.
The literature search was bounded to the surfaces listed in Gap; GitHub code
search was unavailable without login. No exhaustive literature or
first-publication claim follows. The identification of the OEIS functions
with the corresponding Lean arithmetic functions is also not itself a
kernel-checked bibliographic fact.
