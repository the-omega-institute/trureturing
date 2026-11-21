---
slug: hagele-2026-refined-bmv-43-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV33
  - D5/S3/Quantum/Analysis/RefinedBMVLowerBound
---

# The refined BMV lower bound for four and three factors in all dimensions

## Problem

For finite complex Hermitian matrices `H, K` of the same size, the mean
trace of the 35 words with four `exp H` and three `exp K` factors should
be at least `Tr exp(4H + 3K)`. Hägele states the lower bound in Equation
(1) and names the higher-dimensional `(4,3)` case in Section 7(iii).

## Motivation

With three occurrences of the second factor, each term in the diagonal
expansion traces a three-step walk. Several walks share each edge in
higher dimension, so their coefficients must be estimated together.

## Gap

Theorem 1 of Hägele's paper establishes the bound through dimension
three. The bounded arXiv and citation searches found no proof of the
higher-dimensional lower bound for this word count.

## Route

Use the eigenvalues of the positive semidefinite cube root of the first
factor. Group the cubic walk expansion into centered quadratic forms.
A four-dimensional real Gram matrix and a weighted Cauchy kernel
certify the positivity of every coefficient matrix. The Schur product
theorem gives the trace-power comparison, which yields the exponential
comparison by the dyadic Lie–Trotter argument.

## Falsifier

Any finite complex Hermitian pair for which the 35-word mean falls
strictly below `Tr exp(4H + 3K)` would refute the bound.

## Evidence

The decomposition is an exact polynomial identity after clearing the
pair-sum denominators. The coefficient kernels extend to zero inputs
and repeated eigenvalues.

## Triage

`theorem`. The word counts are four and three in arbitrary finite
dimension.

## ASSUMED-UNVERIFIED

The literature search is bounded. Historical priority remains unverified.
