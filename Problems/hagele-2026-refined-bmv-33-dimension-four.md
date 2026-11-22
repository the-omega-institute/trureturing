---
slug: hagele-2026-refined-bmv-33-dimension-four
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/TrotterProduct
---

# The refined BMV lower bound for three letters of each kind in dimension four

## Problem

For every pair of complex Hermitian 4 × 4 matrices `H, K`, the
mean trace of the twenty words with three `exp H` and three `exp K`
should be at least `Tr exp(3H + 3K)`.
Hägele, arXiv:2611.00129v1, Equation (1) and Section 7(iii), gives
the inequality and names this open case.

## Motivation

The first case beyond dimension three requires control of several
triangles that share an edge in the cubic trace expansion.

## Gap

Hägele proves the bound for dimensions at most three at this word
length. The bounded arXiv and citation search found no later solution
of the four-dimensional lower bound. The upper-bound counterexamples
of Cha and Lee concern a different inequality.

## Route

Subtract the smallest eigenvalue of the first positive semidefinite
matrix. The trace-power gap can only decrease. Decompose the cubic
coefficient into quadratic forms in the entries incident to each
center. The Schur product theorem and explicit Schur complements
give the trace-power bound. A dyadic trace-power inequality followed
by Lie–Trotter yields the stated exponential bound.

## Falsifier

An explicit Hermitian pair in dimension four with mean trace strictly
below the exponential trace would refute the stated lower bound.

## Evidence

The coefficient identities are exact rational identities. The matrices
in the Schur complement argument can have complex entries, with the
real coefficient matrices acting by entrywise multiplication.

## Triage

`theorem`. This case fixes dimension four and the two word counts
at three.

## ASSUMED-UNVERIFIED

The literature search is bounded. Historical priority remains unverified.
