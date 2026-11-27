---
slug: hagele-2026-refined-bmv-64-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV54
  - D5/S3/Quantum/Analysis/RefinedBMVTracePower
---

# The refined BMV lower bound at (6,4)

## Problem

For finite complex positive semidefinite matrices A and B, the mean trace
of the 210 words with 6 copies of A and four of B should dominate the
trace of (A^(3/2) B)^4.

## Motivation

This is the (6,4) case of Hägele's product inequality in Section 1.
Lemma 2 gives the corresponding exponential comparison.

## Gap

The bounded search found no earlier proof of the exact unrestricted
lower comparison. Burgdorf's Theorem 1.5 gives the classical
coefficient positivity at four copies of the second factor.

## Route

The three rational Gram blocks compare the mean with the trace of (A^2 B A B)^2. One block is weighted by B on both sides.

## Falsifier

A finite complex PSD pair whose word mean lies strictly below the
fractional-power trace would refute the comparison.

## Evidence

Lean verifies the cyclic coefficients, the rational LDL factors, and
the comparison with the fractional fourth trace.

## Triage

`theorem`. The proof includes singular positive semidefinite inputs.

## ASSUMED-UNVERIFIED

Historical priority remains unverified.
