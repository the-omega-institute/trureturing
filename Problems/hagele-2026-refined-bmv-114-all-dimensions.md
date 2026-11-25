---
slug: hagele-2026-refined-bmv-114-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV/NineFour
  - D5/S3/Quantum/Analysis/RefinedBMV/TenFour
---

# The refined BMV lower bound at (11,4)

## Problem

For positive semidefinite complex matrices A and B in any common
finite dimension, the mean of the real traces of the 1365 ordered
words with eleven copies of A and four of B should dominate the real
trace of `(A^(11/4) B)^4`.

## Motivation

This is the (11,4) case of Hägele's product lower comparison in
Section 1. Lemma 2 gives the corresponding lower bound by the trace
of `exp(11H + 4K)` for the word mean on `exp H` and `exp K`.

## Gap

Hägele's Theorem 1.2 covers all multiplicities in dimensions at most
two. The full comparison permits arbitrary finite dimension.

## Route

A rational Gram matrix on the 21 half-words with five copies of A
and two of B, weighted by A, compares the word mean with the cyclic
word with gaps (3,3,2,3). With `X = A^(1/4)`, two trace inequalities
compare the latter word with the fourth trace power of `X^11 B`.
The product proof also allows Hermitian B.

## Falsifier

A finite complex PSD pair whose word mean is strictly below the real
trace of `(A^(11/4) B)^4` refutes the comparison.

## Evidence

The rational certificate verifies the coefficients of all 56 classes
under cyclic rotation and reversal. The comparator class contains
fifteen words. The Gram matrix has fourteen positive LDL pivots.

## Triage

`theorem`.

## ASSUMED-UNVERIFIED

Historical priority remains unverified.
