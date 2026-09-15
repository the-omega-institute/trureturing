---
slug: oeis-a302975-divisor-count-power-ratio-denominator-square
bibkey: krizek2018a302975
doi: null
url: https://oeis.org/A302975
triage: theorem
motivation_gids:
  - D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare
---

# OEIS A302975 divisor-count power-ratio denominator square

## Problem

OEIS A302975, NAME (`%N`, verbatim):

> a(n) = denominator of tau(n)^n / n^tau(n)

COMMENTS (`%C`, verbatim):

> tau(n) = the number of the divisors of n (A000005).

> Conjecture: all terms are squares.

The formal claim is the literal statement `∀ n ≥ 1, IsSquare (D n)`, where `D`
is the reduced denominator of the displayed rational ratio. The definition is
totalized with `D 0 = 1`; that value is not a source claim.

## Motivation

Krizek's 2018 OEIS conjecture asks whether every reduced denominator in this
divisor-count power ratio is a square. The theorem proves the universal positive
range and therefore resolves the conjecture rather than extending a finite table.

## Gap

The dated surfaces recorded in preregistration issue #7531 and its probe report
show OEIS history entries #1--#12 containing programs and the b-file only. The
MathOverflow search returned 0; GitHub returned only joeis and loda
implementations. The conjecture was not found in epoch-research/LeanOpenProblems
or google-deepmind/formal-conjectures. arXiv, Semantic Scholar, and OpenAlex
requests returned HTTP 429 and are `ASSUMED-UNVERIFIED`.

## Route

Write `t = tau(n)`. For every prime p,
`v_p(D n) = max(t * v_p(n) - n * v_p(t), 0)`. If `t` is odd, then `n` is a
square and all exponents are even. If `n` is even, both terms are even. If n is
odd and p divides t, the bounds `e(e+1) <= 3^e` and `f+1 <= q^f` imply
`t * v_p(n) <= n`, so the exponent is zero. The remaining odd-n primes do not
divide t and have even first term. Thus every valuation is even, and
`r = product p^(v_p(D n)/2)` reconstructs a square root.

## Falsifier

Any positive n for which the reduced denominator has an odd prime valuation, or
for which no natural r satisfies `D n = r * r`, would refute the claim.

## Evidence

- Lean module: `D5/S3/Arith/KrizekDivisorCountPowerRatioDenominatorSquare.lean`.
- Theorem: `krizek_a302975`; theorem axiom closure is std3.
- The orchestrator evaluated the exact Fraction ratio for `n <= 3000`: the first
  20 terms agree with `%S` and there are 0 non-squares. Its valuation scan found
  0 violations of the odd-n inequality through `n <= 300000`.
- The search seat checked the 1000-term b-file and scanned valuations through
  `10^6`; the probe recorded the same readings.

## Triage

`theorem`. The universal positive-range statement is proved in Lean.

## ASSUMED-UNVERIFIED

The arXiv, Semantic Scholar, and OpenAlex surfaces were rate-limited with HTTP
429. The literature checks are bounded and do not establish exhaustive coverage
or a priority claim.
