---
slug: hagele-2026-refined-bmv-74-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV54
  - D5/S3/Quantum/Analysis/RefinedBMVTracePower
---

# The refined BMV lower bound at (7,4)

## Problem

For finite complex positive semidefinite matrices A and B, the mean trace
of the 330 words with 7 copies of A and four of B should dominate the
trace of (A^(7/4) B)^4.

## Motivation

This is the (7,4) case of Hägele's product inequality in Section 1.
Lemma 2 gives the corresponding exponential comparison.

## Gap

The bounded search found no earlier proof of the exact unrestricted
lower comparison. Burgdorf's Theorem 1.5 gives the classical
coefficient positivity at four copies of the second factor.

## Route

The rational Gram block weighted by A compares the mean with the trace of (A^2 B)^3 A B. Fourth-root powers yield the fractional comparison also for singular A.

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
