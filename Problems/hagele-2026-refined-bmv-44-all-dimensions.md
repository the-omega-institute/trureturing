---
slug: hagele-2026-refined-bmv-44-all-dimensions
bibkey: hagele2026refinedbmv
doi: 10.48550/arXiv.2611.00129
url: https://arxiv.org/abs/2611.00129v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Analysis/RefinedBMV43
  - D5/S3/Quantum/Analysis/RefinedBMVTracePower
---

# The refined BMV lower bound with four copies of each factor

## Problem

For finite complex positive semidefinite matrices A and B, the mean trace
of the seventy words with four copies of each factor should be at least
the trace of (AB)^4. For Hermitian H and K, applying the result to their
exponentials and using Lemma 2 gives the exponential lower bound
Tr exp(4H + 4K).

## Motivation

The comparison is the (4,4) case of Hägele's product inequality in
Section 1. Section 7(iii) identifies the three-dimensional case.

## Gap

Hägele proves this word count through dimension two. The arXiv and citation
searches found no earlier proof of the arbitrary-dimensional lower bound.
Ando, Hiai and Okubo prove the corresponding upper bound in Corollary 2.4.

## Route

Group the cyclic word classes using the fourth trace moment of the
Hermitian part of AB. The difference becomes a positive linear
combination of Frobenius and weighted commutator squares and the
fourth-moment comparison from unitary triangularization.

## Falsifier

A finite complex PSD pair whose normalized word trace is strictly below
the trace of (AB)^4 would refute the product comparison.

## Evidence

The seventy words are enumerated exactly in the proof. The weighted
commutator estimates use the same inequalities as Corollary 2.2(ii) of
Ando, Hiai and Okubo, https://doi.org/10.7153/mia-03-32.

## Triage

`theorem`. Both statements allow arbitrary finite dimension. The product
comparison includes singular inputs.

## ASSUMED-UNVERIFIED

The search was bounded. Historical priority remains unverified.
