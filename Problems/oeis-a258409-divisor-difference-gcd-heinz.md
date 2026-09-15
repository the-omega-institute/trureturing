---
slug: oeis-a258409-divisor-difference-gcd-heinz
bibkey: wiseman2019a258409
doi: null
url: https://oeis.org/A258409
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz
---

# The divisor-difference gcd and Heinz decoding identity in A258409

## Problem

OEIS A258409, NAME:

> Greatest common divisor of all (d-1)'s, where the d's are the positive divisors of n.

COMMENT (Gus Wiseman, Oct 16 2019):

> Conjecture: a(n) = A289508(A328023(n)) = GCD of the differences between consecutive divisors of n. See A328163 and A328164.

OEIS A328023, NAME:

> Heinz number of the multiset of differences between consecutive divisors of n.

Its Heinz-number convention is:

> The Heinz number of an integer partition or multiset {y_1,...,y_k} is prime(y_1)*...*prime(y_k).

OEIS A289508, NAME:

> a(n) is the GCD of the indices j for which the j-th prime p_j divides n.

These OEIS prime indices are one-based, with prime(1)=2. Mathlib's
`Nat.nth Nat.Prime` is zero-based, so the Lean encoding of prime(delta) is
`Nat.nth Nat.Prime (delta - 1)`.

## Motivation

This is a first-tier OEIS conjecture recorded in 2019. The full target is the
three-term identity for every `n >= 2`, the sequence offset, rather than only
the equality between the two gcd descriptions.

## Gap

The search recorded on 2026-09-13 checked all 44 revisions of A258409, all 8
revisions of A328023, and all 41 revisions of A289508. It also checked three
identifier queries on OpenAlex, a GitHub repository search, and MathOverflow;
the MathOverflow occurrence concerned a different question. A proof or
refutation was not found in the checked surfaces. Three arXiv export API
queries timed out and therefore remain `ASSUMED-UNVERIFIED`. This bounded
search does not establish exhaustive literature coverage or publication
priority.

## Route

Write the sorted divisors as `1 = d_0 < ... < d_k = n`, and put
`Delta_i = d_i - d_(i-1)`. If `g` is the gcd of all `d_i - 1`, then `g`
divides every `Delta_i` by taking differences. Conversely, if `h` is the gcd
of all the `Delta_i`, then `h` divides
`d_i - 1 = Delta_1 + ... + Delta_i` by telescoping. Hence `g = h`.

The Heinz number `Product_i prime(Delta_i)` has prime-factor set
`{prime(Delta_i)}`. Its one-based prime indices are exactly the `Delta_i`, and
duplicates do not change a gcd. Therefore
`A289508(A328023(n)) = h = g`.

## Falsifier

A natural number `n >= 2` for which any two of the three displayed values
differ would contradict the assertion. A defect in the increasing divisor
ordering, the one-based prime-index bridge, or the prime-factor support of the
Heinz product would also invalidate the corresponding step of the route.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/DivisorDifferenceGcdHeinz.lean`.
- Main theorem: `wiseman_a258409`.
- Public definitions: `a`, `consecutiveDivisorDifferences`,
  `consecutiveDifferenceGcd`, `heinzDifferences`, and `primeIndexGcd`.
- The canonical Lean report gives all six public declarations exactly the
  std3 axioms: `propext`, `Classical.choice`, and `Quot.sound`.
- The orchestrator checked `2 <= n <= 5000` for the gcd half with zero
  mismatches and `2 <= n <= 300` for the full three-term identity using the
  actual Heinz encode/decode operations, also with zero mismatches.
- The probe independently checked the identical two ranges and reported zero
  mismatches. These finite checks support but do not replace the universal
  proof.

## Triage

`theorem`. The Lean theorem proves the complete three-term identity for every
natural `n >= 2`, matching the OEIS offset and resolving the stated conjecture.

## ASSUMED-UNVERIFIED

The OEIS quotations, revision counts, attribution, and the bounded external
search results were supplied by the search seat and preregistration record.
The three timed-out arXiv queries were not completed. No exhaustive
literature or priority claim follows. The numerical ranges were supplied by
the orchestrator and probe; this Stage-B seat did not recompute them.
Source-to-Lean identification is not itself a kernel-checked fact.
