---
slug: oeis-a092028-least-self-divisor-power-minus-one
bibkey: firoozbakht2004a092028
doi: null
url: https://oeis.org/A092028
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne
---

# The least self-divisor exponent in OEIS A092028

## Problem

OEIS A092028, NAME (`%N`, verbatim):

> a(n) is the smallest m > 1 such that m divides n^m-1

COMMENTS (`%C`, verbatim; Farideh Firoozbakht, Mar 26 2004):

> Conjecture 1: All terms of this sequence are primes.

> Conjecture 2: a(n) is the smallest prime factor of n-1 or for n>2, A092028(n) = A020639(n-1).

The literal formal claim is `∀ n > 2, a(n) = minFac(n − 1)`, where
`a(n) = sInf {m ∈ ℕ | 1 < m ∧ m ∣ n^m − 1}`. In the natural numbers,
`sInf ∅ = 0`; for every `n > 2`, the defining set is nonempty. Conjecture 1
is a corollary because `minFac(n − 1)` is prime, and is not formalized as a
separate public theorem.

## Motivation

The equality identifies the least solution of a self-referential divisibility
condition for every natural input above two. It proves the unbounded OEIS
conjecture rather than extending the entry's finite data.

## Gap

The searches recorded in preregistration issue #7526 and its probe on
2026-09-13 found that OEIS history entries #1 through #16, including revision
#16, still carry both conjectures. The sibling plus-sign entry A092067 was
proved by Neder in 2019; it supplied a search pattern only and is not imported.
Exact searches returned MathOverflow 0, Crossref 0, and GitHub issues 0.
arXiv, Semantic Scholar, and OpenAlex were rate-limited, while GitHub code
search was unauthenticated. Those unavailable surfaces are
`ASSUMED-UNVERIFIED`. The completed searches are bounded and establish no
priority claim.

## Route

For the upper bound, let `p = minFac(n − 1)`. The number `p` is prime and
`p ∣ n − 1`, hence `n^p ≡ 1 (mod p)` and `p` belongs to the defining set.
For the lower bound, take any `m > 1` with `m ∣ n^m − 1` and let
`q = minFac(m)`. The multiplicative order of `(n : ZMod q)` divides both `m`
and `q − 1`. Minimality of `q` gives `gcd(m, q − 1) = 1`, so the order is one.
Thus `q ∣ n − 1`, and `minFac(n − 1) ≤ q ≤ m`. Together the two bounds give
the claimed equality.

## Falsifier

One natural number `n > 2` for which the least `m > 1` dividing `n^m − 1`
differs from `minFac(n − 1)` would contradict the theorem.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.lean`.
- Main theorem: `firoozbakht_a092028`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator checked every `n` with `3 ≤ n ≤ 3000` and found zero
  mismatches.
- The probe checked all 9998 cases with `3 ≤ n ≤ 10000` and found zero
  mismatches. For `n = 3..12`, the values are `2, 3, 2, 5, 2, 7, 2, 3, 2,
  11`.

## Triage

`theorem`. The formal result proves the equality for every natural `n > 2`.

## ASSUMED-UNVERIFIED

arXiv, Semantic Scholar, and OpenAlex were rate-limited, and GitHub code search
was unauthenticated. The successful literature searches were bounded. No
claim of exhaustive literature coverage or first-publication priority is made.
