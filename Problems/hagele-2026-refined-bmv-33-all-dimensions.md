---
slug: hagele-2026-refined-bmv-33-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/TrotterProduct
  - D5/S3/Quantum/Analysis/RefinedBMV33
---

# The refined BMV lower bound for three letters of each kind in all dimensions

## Problem

For every pair of finite complex Hermitian matrices `H, K` of the same
size, the mean trace of the twenty words with three `exp H` and three
`exp K` is at least `Tr exp(3H + 3K)`. Hägele states the lower bound in
Equation (1) and identifies the `(3,3)` case for dimensions at least
four in Section 7(iii).

## Motivation

The cyclic trace expansion has several triangles sharing each edge in
higher dimension. The dimension-three pairing controls a single triangle
for each edge.

## Gap

Hägele proves the lower bound for this word count through dimension
three. A bounded arXiv and citation search located papers on the upper
bound and found no later proof of this higher-dimensional lower bound.

## Route

Choose a rational coefficient symmetric in the three eigenvalues along
a closed walk. It yields the same cubic trace defect and makes every
centered coefficient matrix a sum of a rank-one positive semidefinite
matrix and a diagonally scaled Cauchy matrix. Schur multiplication by
the second positive semidefinite matrix preserves positivity, yielding
the trace-power bound. The dyadic trace-power comparison followed by
Lie–Trotter gives the exponential bound.

## Falsifier

A finite Hermitian pair with the twenty-word mean strictly below the
exponential trace would refute the bound.

## Evidence

The rank-one and Cauchy decomposition is an exact identity for a positive
center. At zero eigenvalues it reduces to the same kernels with zero rows
in the Cauchy term. Repeated eigenvalues are allowed.

## Triage

`theorem`. The two word counts are fixed at three and the matrix dimension
is arbitrary.

## ASSUMED-UNVERIFIED

The literature search is bounded. Historical priority remains unverified.
