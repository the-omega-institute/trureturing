---
bibkey: meaux2019threshold
authors: Pierrick Meaux
year: 2019
title: On the Fast Algebraic Immunity of Majority Functions
doi: null
url: https://eprint.iacr.org/2019/999
claim: For positive threshold and degree, the threshold-function ANF coefficient is the parity of one binomial coefficient.
strata_touched:
  - D5/S3/ArithSums/A397434ThresholdAnf
license: citation-only
triage: anchor
---

# Algebraic normal forms of threshold functions

Pierrick Meaux's *On the Fast Algebraic Immunity of Majority Functions*,
Cryptology ePrint Archive 2019/999, states Theorem 1 on the algebraic normal
form of threshold functions. For positive threshold `t` and positive degree
`d`, the coefficient is the parity of `choose(d-1,t-1)`.

Carlet and Meaux restate the result as Lemma 2 in their later study of direct
sums of monomials and threshold functions. The source record cites this as
Meaux (2021), Lemma 2, and records its attribution to Meaux (2019), Theorem 1.

The local Lean theorem implements this coefficient reduction rather than
claiming it as new mathematical content. The subsequent adjacent-row identity
and parity classification are repository derivations.

## Verified locator

- URL: https://eprint.iacr.org/2019/999
