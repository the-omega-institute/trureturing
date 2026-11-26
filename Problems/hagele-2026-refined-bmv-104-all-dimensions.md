---
slug: hagele-2026-refined-bmv-104-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV44
  - D5/S3/Quantum/Analysis/RefinedBMVTracePower
---

# The refined BMV lower bound at (10,4)

## Problem

For positive semidefinite A and B in any finite complex dimension,
including singular A and B, the mean of the real parts of the 1001 word
traces with ten copies of A and four of B should dominate the real part
of the trace of (A^(5/2) B)^4, with the fractional power given by
spectral calculus.

## Motivation

This is the (10,4) case of Hägele's product lower comparison in Section 1.
Lemma 2 gives the corresponding lower bound by the trace of exp(10H + 4K)
for the word mean on exp H and exp K, where H and K are Hermitian.

## Gap

The bounded literature search covering arXiv:2611.00129, 0802.1153,
2611.03208, 2610.31851 and 2611.23122 did not identify an earlier proof
of this exact comparison in arbitrary finite dimension.

## Route

Compare the word mean with the trace of (A^3 B A^2 B)^2, whose cyclic
gaps are (3,2,3,2). Use three rational positive semidefinite Gram blocks
of sizes 21, 15 and 6 with respective weight pairs I/I, A/A and B/B.
Positivity follows from the weighted trace squares, including for singular
weights. With X = A^(1/4) and M = X^4 B X^6, trace Cauchy–Schwarz
bounds the real part of tr(M^4) by tr((M* M)^2), giving the
fractional-power comparison by cyclicity.

## Falsifier

A finite complex PSD pair A and B for which the word mean is strictly
below the real part of the trace of (A^(5/2) B)^4 would refute the
comparison.

## Evidence

The exact rational certificate checks all 73 cyclic coefficients of
the 1001 ordered words. The comparator class has seven words and its
coefficient in the difference is -994. Independent rational review
checked the three Gram factorizations, with 14, 12 and 3 positive
LDL pivots respectively, and the analytic trace comparison. The proof
treats singular A and B directly.

## Triage

`theorem`.

## ASSUMED-UNVERIFIED

Historical priority remains unverified. The literature search was bounded.
