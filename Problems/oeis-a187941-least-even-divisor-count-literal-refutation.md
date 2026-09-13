---
slug: oeis-a187941-least-even-divisor-count-literal-refutation
bibkey: gerasimov2011a187941
doi: null
url: https://oeis.org/A187941
triage: theorem
motivation_gids:
  - D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo
---

# Refutation of the literal offset-zero A187941 power-of-two conjecture

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

With the offset-zero index `n = 0` included, the literal claim is
`forall n, a(n) = 2^n -> n is prime or n = 1`.

## Motivation

The entry has carried the conjecture since 2011, but its stated offset includes
an exceptional term that resolves the literal universal claim by refutation.
Separating this statement from the positive-index form preserves both the
source wording and the mathematically intended implication.

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

The number 1 has no even divisors, so `E(1) = 0`. It is positive and is the
least possible positive witness, hence `a(0) = 1 = 2^0`. But zero is neither a
prime number nor equal to one, which refutes the literal universal statement.

## Falsifier

A proof that `a(0) != 1`, that zero is prime, or that zero equals one would
falsify this refutation. Each alternative contradicts the kernel-checked
result and the defining least-witness calculation.

## Evidence

- Lean module:
  `D5/S3/Factorization/GerasimovLeastEvenDivisorCountPowerOfTwo.lean`.
- Main theorem: `result : Not claim`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator and probe exhaustively searched `m <= 3*10^5` and obtained
  `a(0..18) = 1, 2, 4, 8, 12, 32, 24, 128, 48, 72, 96, 2048, 120, 8192, 384, 288, 240, 131072, 360`.
- In that bounded computation, `a(n) = 2^n` exactly for
  `n in {0, 1, 2, 3, 5, 7, 11, 13, 17}`.

The bounded computation supports the source interpretation but is not used to
replace the formal witness at `n = 0`.

## Triage

`theorem`. The certified offset-zero instance refutes the literal universal
claim. The separate positive-index implication is recorded in its own dossier.

## ASSUMED-UNVERIFIED

The arXiv API timeout, OpenAlex rate limit, and unauthenticated GitHub code
search leave those bounded surfaces unverified. No exhaustive-literature or
priority claim is made.
