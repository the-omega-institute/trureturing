---
slug: oeis-a187941-least-even-divisor-count-power-of-two
bibkey: gerasimov2011a187941
doi: null
url: https://oeis.org/A187941
triage: theorem
motivation_gids:
  - D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo
---

# The positive-index A187941 power-of-two implication

## Problem

OEIS A187941, NAME (`%N`, verbatim):

> Least number with exactly n even divisors.

COMMENTS (`%C`, verbatim):

> The only odd term in the sequence is 1, having zero even divisors. All larger odd numbers also have zero even divisors.

> Conjecture: a(n) = 2^n only if n is prime or if n = 1.

FORMULA (`%F`, verbatim):

> a(n) = 2 * A005179(n) for n > 0.

OFFSET (`%O`, verbatim):

> 0,2

The positive-index form is
`forall n >= 1, a(n) = 2^n -> n is prime or n = 1`.

## Motivation

The offset-zero term refutes the literal comment, while the intended
positive-index implication remains a distinct universal problem. Proving that
form resolves the conjectural direction without asserting its converse.

## Gap

Preregistration issue #7567 and its probe report record searches dated
September 13, 2026. OEIS revisions #1 through #14 show that revisions #6 and
#7 introduced and corrected the conjecture comment, with no proof or
refutation supplied in the later revisions. OEIS Open (arXiv:2608.11941) and
formal-conjectures contained no A187941 entry, and the MathOverflow search
returned 0 results. The arXiv API timed out, OpenAlex returned HTTP 429, and
GitHub code search required login; those surfaces are `ASSUMED-UNVERIFIED`.
The bounded searches do not establish exhaustive literature coverage or
publication priority.

## Route

Argue by contrapositive. For composite `n`, put `d = minFac(n) >= 2` and
`e = n / d >= 2`, so `d*e = n`. The number
`m = 2^d * 3^(e-1)` satisfies `E(m) = d*e = n` by the multiplicative
even-divisor count. Moreover,
`m < 2^d * 4^(e-1) <= 2^d * 2^(d*(e-1)) = 2^n`.
Thus `a(n) <= m < 2^n`, ruling out `a(n) = 2^n` for composite positive `n`.

## Falsifier

A composite natural `n >= 1` satisfying `a(n) = 2^n` would contradict the
theorem. Equivalently, such an index would falsify either the multiplicative
count or the strict smaller-witness construction used in the proof.

## Evidence

- Lean module:
  `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.lean`.
- Main theorem: `gerasimov_a187941`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator and probe exhaustively searched `m <= 3*10^5` and obtained
  `a(0..18) = 1, 2, 4, 8, 12, 32, 24, 128, 48, 72, 96, 2048, 120, 8192, 384, 288, 240, 131072, 360`.
- In that bounded computation, `a(n) = 2^n` exactly for
  `n in {0, 1, 2, 3, 5, 7, 11, 13, 17}`.

The finite search is supporting evidence only; the theorem proves the
positive-index implication for every natural number.

## Triage

`theorem`. The formal result proves the implication for every positive index.
It does not claim the converse.

## ASSUMED-UNVERIFIED

No claim is made that every prime `p` satisfies `a(p) = 2^p`, and nothing is
asserted about A005179 beyond the entry's quoted formula. The arXiv API
timeout, OpenAlex rate limit, and unauthenticated GitHub code search leave
those bounded surfaces unverified. The literature search is bounded, the
even-divisor count is elementary, and no publication-priority claim is made.
