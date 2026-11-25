---
slug: hagele-2026-refined-bmv-94-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV44
  - D5/S3/Quantum/Analysis/RefinedBMVTracePower
---

# The refined BMV lower bound at (9,4)

## Problem

For positive semidefinite A and Hermitian B in any finite complex
dimension, including singular A, the mean trace of the 715 words with
nine copies of A and four of B should dominate the trace of
(A^(9/4) B)^4, with the fractional power given by spectral calculus.

## Motivation

This is the (9,4) case of Hägele's product lower comparison in Section 1,
with the second factor allowed to be Hermitian. Lemma 2 gives the
corresponding lower bound by the trace of exp(9H + 4K) for the word mean
on exp H and exp K, where H and K are Hermitian.

## Gap

The bounded literature search found no earlier proof of the (9,4) lower
comparison in arbitrary finite dimension. It located lower bounds for
small p or restricted dimension (arXiv:2611.00129), results on upper-bound
failure (arXiv:2603.19927 and arXiv:2605.17782), and work on the Stieltjes
transform (arXiv:2611.03208).

## Route

Use one rational positive semidefinite Gram matrix on 15 half-words,
weighted by A, to compare the mean with the trace of the word with
cyclic gaps (3,2,2,2). Two trace Cauchy–Schwarz inequalities compare
that word trace with the balanced fourth trace.

## Falsifier

A finite complex pair with PSD A and Hermitian B for which the word
mean is strictly below the balanced fourth trace would refute the
comparison.

## Evidence

The proof uses an exact cyclic coefficient identity and a rational
positive semidefinite Gram certificate. It treats singular A directly.

## Triage

`theorem`.

## ASSUMED-UNVERIFIED

Historical priority remains unverified. The literature search was bounded.
