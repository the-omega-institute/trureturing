---
slug: hagele-2026-refined-bmv-54-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV44
  - D5/S3/Quantum/Analysis/RefinedBMVTracePower
---

# The refined BMV lower bound with five and four factors

## Problem

For finite complex positive semidefinite matrices A and B, the mean trace
of the 126 words with five copies of A and four of B should dominate
the trace of (A^(5/4) B)^4.

## Motivation

This is the (5,4) case of Hägele's refined product inequality in
Section 1. Lemma 2 gives the corresponding exponential comparison.

## Gap

The bounded search found no previous proof of the unrestricted lower
comparison. Burgdorf's Theorem 1.5 and Example 2.1(b) in arXiv:0802.1153v2
give cyclic square decompositions for the classical coefficient bound.

## Route

Compare the word mean to the trace of A(AB)^4 using four squares
weighted by A. Compare the latter trace to the fourth trace power with
the positive fourth root of A by three Frobenius squares.

## Falsifier

A finite complex PSD pair for which the word mean is strictly below the
trace of (A^(5/4) B)^4 would refute the comparison.

## Evidence

The coefficient comparison uses a Lean permutation certificate on the
cyclic and reversal representatives of the 126 words.

## Triage

`theorem`. The product proof permits every Hermitian B and singular PSD A.

## ASSUMED-UNVERIFIED

The literature search is bounded. Historical priority remains unverified.
