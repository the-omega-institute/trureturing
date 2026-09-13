---
slug: oeis-a089610-square-interval-prime-count-eventual-increase-refutation
bibkey: hilliard2003a089610
doi: null
url: https://oeis.org/A089610
triage: theorem
motivation_gids:
  - D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation
---

# Refutation of the A089610 eventual strict-increase conjecture

## Problem

OEIS A089610 %N (verbatim):

> Number of primes between n^2 and (n+1/2)^2.

OEIS A089610 %C (verbatim sub-conjecture):

> There exists an n_1 such that a(n) is < a(n+1) for all n >= n_1.

OEIS A089610 %A (verbatim):

> _Cino Hilliard_, Dec 30 2003

The literal refuted statement is
`∃ N : ℕ, ∀ n : ℕ, N ≤ n → a(n) < a(n+1)`, where
`a(n) = ((Finset.Ioc (n*n) (n*n+n)).filter Nat.Prime).card`. Since
`(n+1/2)^2 = n^2+n+1/4`, this natural interval selects exactly the integer
primes between the endpoints printed in the NAME, as T. D. Noe's comment
notes. The separate conjecture that `a(n) > 1` after `n = 17` and Oppermann's
positivity conjecture `a(n) > 0` are not claimed or resolved here.

## Motivation

The entry proposes that the square-interval prime count eventually rises at
every step. A symbolic obstruction that produces a non-increase beyond every
threshold refutes that quantified conjecture without relying on a finite
counterexample or on an estimate for prime gaps.

## Gap

Preregistration issue #7621 and its probe report record searches dated
September 14, 2026. All 29 OEIS revisions were read: the conjecture is present
from revision #1 (2004-02-19), and no revision gives a proof or refutation.
Exact arXiv search returned 0 results. OpenAlex autocomplete returned 0;
OpenAlex `/works` returned HTTP 429 and is `ASSUMED-UNVERIFIED`. Crossref
returned 0. MathOverflow question 258197 cites A089610 only for the definition,
asks about positivity, and has 0 answers; exact-phrase MathOverflow search
returned 0. GitHub exact-phrase search returned 0. The pinned Mathlib contains
the parity and finite-cardinality injection lemmas used below but no
square-interval prime-count estimate. The Ribenboim and Oppermann bibliography
concerns the out-of-scope positivity question and was not read in full
(`ASSUMED-UNVERIFIED`). These are bounded search surfaces, and no priority
claim is made.

## Route

For every natural `k`, each prime counted by `a(2k)` is greater than two and
odd. Division by two injects these primes into the `k` positions in
`Ico(2k^2, 2k^2+k)`, so `a(2k) <= k`.

If `a` were strictly increasing throughout `[M, 2M+2)`, integer growth at each
step would give
`a(2M+2) >= a(M) + M + 2 >= M + 2`. The even-index bound at
`2M+2 = 2(M+1)` instead gives `a(2M+2) <= M + 1`, a contradiction. For any
proposed threshold `N`, take `M = max N 2`; the resulting non-increase occurs
after the threshold and contradicts eventual strict increase.

## Falsifier

The refutation would fail if a prime in the even-index interval could equal
two, if the division-by-two map failed to land in or inject into the stated
`k`-element interval, if strict increase of a natural-valued sequence did not
accumulate at least one unit per step, or if the final index were not
`2(M+1)`. Any proof of the literal eventual strict-increase claim would also
contradict the kernel theorem `result : not claim`.

## Evidence

- Lean module:
  `D5/S3/PrimeGaps/HilliardSquareIntervalPrimeCountEventualIncreaseRefutation.lean`.
- Main theorem: `result : not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The Step 0 profiler on the stamped hot tree reported 7.45 seconds wall time,
  45.2 ms cumulative type checking, and 1,456,095,232 bytes maximum RSS.
- The orchestrator's independent sieve through `(10^4)^2 + 10^4` gave
  `a(1..20) = 1, 1, 1, 2, 1, 2, 1, 2, 2, 4, 2, 2, 3, 2, 4, 4, 1, 2, 3, 3`,
  matching the OEIS `%S` line.
- The even-index bound held for every `k < 5000`, with maximum ratio
  `a(2k)/k = 1.0`.
- There were 5172 non-increases below `10^4`; the last occurred at
  `9990, 9991, 9993, 9994, 9995, 9998`. The longest strict-increase run had
  length 6.
- The window assertion had no failure for `M < 4000`. The probe reproduced
  the same numerical readings.

The bounded computations corroborate the statement but do not carry it. The
Lean theorem derives the contradiction symbolically from parity, an explicit
finite-set injection, and accumulated strict growth.

## Triage

`theorem`. The result refutes the literal eventual strict-increase conjecture
and does not assert a corrected asymptotic or resolve either positivity claim.

The module is classified `utility: none`: `a` and `claim` are definitions, and
`result` is a symbolic refutation producing a non-increase beyond every
threshold from a counting bound. None of `bounded-enumeration`, `checker`,
`numeric-reduction`, or `certified-instance` applies.

## ASSUMED-UNVERIFIED

The OpenAlex `/works` search returned HTTP 429. The Ribenboim and Oppermann
bibliography concerning positivity was not read in full. All literature and
repository searches and all numerical computations listed above are bounded;
they do not establish exhaustive publication coverage, priority, or an
unbounded computational verification.
