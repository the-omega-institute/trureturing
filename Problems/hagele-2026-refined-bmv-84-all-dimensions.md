---
slug: hagele-2026-refined-bmv-84-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV44
  - D5/S3/Quantum/Analysis/RefinedBMVTracePower
---

# The refined BMV lower bound at (8,4)

## Problem

For finite complex positive semidefinite A and B, the mean trace
of the 495 words with eight copies of A and four of B should dominate
the trace of (A^2 B)^4.

## Motivation

This is the (8,4) case of Hägele's product inequality in Section 1.
Lemma 2 gives the corresponding exponential comparison.

## Gap

Burgdorf's Theorem 1.5 of arXiv:0802.1153v2 gives classical
coefficient positivity for four copies of the second factor.
The bounded search found no earlier proof of the unrestricted
lower comparison with the balanced fourth trace.

## Route

Use three rational Gram blocks to compare the mean with the fourth
trace of the Hermitian part of A^(3/2) B A^(1/2).
The quartic trace comparison then bounds the balanced product.

## Falsifier

A finite complex PSD pair for which the word mean is strictly below
the balanced fourth trace would refute the comparison.

## Evidence

Lean verifies the cyclic coefficients and exact rational LDL factors.
The comparison includes singular positive semidefinite inputs.

## Triage

`theorem`.

## ASSUMED-UNVERIFIED

Historical priority remains unverified.
