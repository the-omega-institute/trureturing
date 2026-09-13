---
slug: oeis-a254748-twin-prime-mean-no-superdivisor
bibkey: gerasimov2015a254748
doi: null
url: https://oeis.org/A254748
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor
---

# The A254748 twin-prime mean has no superdivisor

## Problem

OEIS A254748, NAME (`%N`, verbatim):

> Numbers without superdivisors: numbers n such that n/k + n fails to divide at least one of (n/k)^(n/k) + n, (n/k)^n + n/k or n^(n/k) + n/k for any divisor k of n.

COMMENT (`%C`, verbatim):

> Zerosuperdivisor numbers. Numbers n such that A247477(n) = 0.

COMMENT (`%C`, verbatim):

> Conjecture: Average of twin prime pairs (A014574) are zerosuperdivisor numbers.

AUTHOR (`%A`, verbatim):

> _Juri-Stepan Gerasimov_, Feb 07 2015

The A247477 superdivisor definition is: a divisor k is a superdivisor of n when
`n/k + n` divides each of `(n/k)^(n/k) + n`, `(n/k)^n + n/k`, and
`n^(n/k) + n/k`, with all division interpreted in `ℕ` (exact when `k ∣ n`).

The literal claim is
`∀ p : ℕ, Nat.Prime p → Nat.Prime (p + 2) → ∀ k : ℕ, 1 ≤ k → k ∣ p + 1 → ¬ IsSuperdivisor (p + 1) k`,
where `IsSuperdivisor` is the three-clause predicate above and the quotient is
natural-number division. The perfect-number sentence in A254748 is NOT claimed.

## Motivation

The conjecture asserts that the arithmetic mean of every twin-prime pair is a
zerosuperdivisor number. The theorem proves that every positive divisor of that
mean fails the A247477 superdivisor predicate.

## Gap

The dated surfaces recorded in preregistration issue #7602 and the probe were
OEIS A254748 all 34 revisions: revision #26 (2015-02-22) added the conjecture,
and revision #34 still carries it, with no proof or refutation. The A247477
Neder 2019 odd-d characterization and Greathouse 2015 parity/residue exclusions
do not prove the target. An arXiv search returned 0; the only `superdivisor`
hit was unrelated supergeometry. OEIS Open arXiv:2608.11941v2 and
LeanOpenProblems(-results) returned 0. The formal-conjectures search returned
0. A GitHub exact-sentence search found only an OEIS mirror. The MathOverflow API
returned 0 (HTML 403). The OpenAlex `/works` budget was exhausted and
autocomplete returned 0 - ASSUMED-UNVERIFIED. The result is elementary; no
priority claim is made.

## Route

Prove the stronger statement for every even n at least 4 with n - 1 prime. For
a divisor k of n put d = n/k. The first two superdivisor conditions, reduced in
`ZMod (k + 1)`, force the multiplicative order r of d to divide both d - 1 and
2(n - 1). Coprime cancellation gives r ∣ 2. The case r = 1 is excluded, so
r = 2. Then d is -1 modulo k+1 and n is 1 modulo k+1, making k+1 a proper
divisor of the prime n - 1, a contradiction. For a twin-prime mean n = p+1,
p is odd and prime, so the stronger statement applies.

## Falsifier

A prime p with p+2 prime and a positive divisor k of p+1 for which all three
A247477 divisibility conditions hold would refute the theorem.

## Evidence

- Lean module: `D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor.lean`.
- Main theorem: `gerasimov_a254748`, with std3 axiom closure
  `[propext, Classical.choice, Quot.sound]`.
- Orchestrator bounded checks: twin-prime means n <= 2 x 10^5 and even n <= 6 x
  10^4 with n - 1 prime, with 0 violations.
- Probe checks: all 2160 twin-prime pairs with p+2 <= 200000 (67037 divisor
  checks) and all 6056 even n <= 60000 with n - 1 prime (115865 checks), with
  0 violations.
- Controls: `IsSuperdivisor(3,1) = true`, `IsSuperdivisor(10,2) = true`,
  `IsSuperdivisor(4,1) = false`, and `IsSuperdivisor(6,2) = false`.

## Triage

`theorem`

## ASSUMED-UNVERIFIED

OpenAlex was exhausted, the bounded searches are finite, and no priority claim
is made. The literature search is not an exhaustive proof of novelty.
