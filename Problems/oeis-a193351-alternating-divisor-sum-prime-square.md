---
slug: oeis-a193351-alternating-divisor-sum-prime-square
bibkey: lagneau2012a193351
doi: null
url: https://oeis.org/A193351
triage: theorem
motivation_gids:
  - D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare
---

# Prime alternating divisor sums in OEIS A193351

## Problem

OEIS A193351, NAME (`%N`, verbatim):

> Numbers k such that A071324(k) is prime.

COMMENT (`%C`, verbatim):

> Numbers k such that the alternating sum of all divisors of k (divisors nonincreasing, starting with k) is prime.

CONJECTURE (`%C`, verbatim):

> For k > 3, if the alternating sum of all divisors of k (divisors nonincreasing, starting with k) is a prime number, then k is either a square or twice a square.

The entry also records:

> This conjecture is verified up to k <= 10^8. - _Shreyansh Jaiswal_, Apr 25 2025

With `T : ℕ → ℤ` denoting that literal alternating sum, the formal claim is
`∀ k : ℕ, 3 < k → Nat.Prime (T k).toNat → (∃ t : ℕ, k = t ^ 2) ∨
(∃ t : ℕ, k = 2 * t ^ 2)`. The use of `.toNat` makes the primality predicate
explicit; the proof establishes the required nonnegativity before using it.

## Motivation

The conjecture was recorded by Michel Lagneau in 2012. It gives a universal
structural classification, rather than a finite extension of the sequence's
table, and its conclusion is strong enough to be checked directly by the Lean
kernel.

## Gap

The bounded search surfaces recorded in issue #7548 and its probe comment on
2026-09-13 found 46 OEIS revisions with no proof and zero arXiv hits for the
identifiers and quoted phrases. The OEIS Open benchmark and
google-deepmind/formal-conjectures did not contain the conjecture. MathOverflow
and GitHub hits were implementations or mirrors only. Jaiswal's 2025 note
proves a lower bound, not this classification. A071324 `%F` records the parity
classification without proof attribution. OpenAlex returned HTTP 429 and is
therefore `ASSUMED-UNVERIFIED`. The mathematical core is the classical parity
fact that sigma(n) is odd exactly for squares and twice-squares; no priority
claim is made.

## Route

(a) Pair consecutive terms of the decreasing divisor list to obtain
`2*T(n) >= n`. The case `n=4` is a square; otherwise `n>=5`, and integrality
gives `T(n)>=3`. (b) A prime value at least three is not two and hence is odd.
(c) Alternating signs disappear modulo two, so `T(n)` is congruent to
`sigma(n)` modulo two. (d) If `sigma(n)` is odd, every odd-prime exponent in
the factorization of `n` is even. Thus `n=2^a*u^2`, which is a square when `a`
is even and twice a square when `a` is odd.

## Falsifier

One natural number `k>3` for which `(T k).toNat` is prime while `k` is neither
a square nor twice a square would contradict the theorem.

## Evidence

- Lean module: `D5/S3/Arith/LagneauAlternatingDivisorSumPrimeSquare.lean`.
- Main theorem: `lagneau_a193351`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator checked every `n<=10^6`: 213 prime values split into 118
  squares and 95 twice-squares, with zero counterexamples and zero violations
  of `T(n)>=n/2`.
- The search seat and the independent probe reported the same bounded readings.

## Triage

`theorem`. The formal result proves the full implication for every natural
number greater than three.

## ASSUMED-UNVERIFIED

OpenAlex coverage was not verified because its query returned HTTP 429. The
other literature searches were bounded and do not establish exhaustive
coverage. No first-publication or priority claim is made.
