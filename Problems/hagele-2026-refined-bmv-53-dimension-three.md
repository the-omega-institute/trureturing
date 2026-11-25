---
slug: hagele-2026-refined-bmv-53-dimension-three
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV43
  - D5/S3/Quantum/Analysis/RefinedBMVLowerBound
---

# The refined BMV lower bound for five and three factors in dimension three

## Problem

For every pair of complex Hermitian matrices `H, K` of size three, the
mean trace of the 56 words with five `exp H` and three `exp K` factors
should be at least `Tr exp(5H + 3K)`. Daniel Hägele identifies this
dimension-three case in Section 7(iii) of arXiv:2611.00129v1.

## Motivation

The corresponding product comparison for all positive semidefinite
`A, B` of size three bounds the trace of `(A^(5/3) B)^3` by the
56-word mean. The larger word counts `(6,3)` and `(7,3)` share the
same three-dimensional reduction.

## Gap

Hägele's Theorem 1.1 covers three-dimensional inputs through total
word length seven. Section 7(ii) reduces cases with three copies of
the second letter to a scalar certificate.

## Route

In an eigenbasis of the positive semidefinite cube root of the first
factor, use Hägele's cubic walk expansion and group the repeated-index
terms in pairs. With nonnegative ordered eigenvalue gaps, a quartic
in the scalar deficits has nonnegative integer coefficients. Its sign
implies the geometric-mean bound for the single triangle. The
trace-power comparison then yields the exponential lower bound.

## Falsifier

A complex Hermitian pair of size three whose 56-word mean is strictly
below `Tr exp(5H + 3K)` would refute the claim.

## Evidence

The certificate also applies at `(6,3)` and `(7,3)`. The pairing
uses the single triangle on the three eigenvalue indices.

## Triage

`theorem`. The designated question concerns `(5,3)` in dimension three.
The exact Lean declarations are `RefinedBMV.DimThree.product_bound` and
`RefinedBMV.DimThree.exponential_bound`.

## ASSUMED-UNVERIFIED

Historical priority remains unverified.
