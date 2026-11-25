---
slug: hagele-2026-refined-bmv-124-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV84
---

# The refined BMV lower bound at (12,4)

## Problem

For positive semidefinite complex matrices A and B in any common
finite dimension, the mean real trace of the 1820 ordered words with
twelve copies of A and four copies of B should dominate the real trace
of `(A^3 B)^4`.

## Motivation

This is the case with twelve copies of the first factor and four copies
of the second in Hägele's product lower comparison. Lemma 2 gives the
lower bound by the trace of `exp(12H + 4K)` when the factors are
`exp H` and `exp K`.

## Gap

Hägele's Theorem 1.2 proves the product comparison in dimensions at most
two. The problem permits arbitrary finite dimension.

## Route

Two rational Gram matrices weighted by the identity and A compare the
word mean with the trace of the fourth power of the Hermitian part
of `A B A^2`. The fourth-trace comparison for that Hermitian part
gives the product bound, including singular A and Hermitian B.

## Falsifier

A finite complex PSD pair whose word mean lies below the real trace of
`(A^3 B)^4` refutes the comparison.

## Evidence

The certificate checks the 72 classes under cyclic rotation and reversal.
Its two blocks use 28 and 21 half-words with 21 and 14 positive pivots.

## Triage

`theorem`.

## ASSUMED-UNVERIFIED

Historical priority remains unverified.
