---
bibkey: zhang2026weakmajorizationtaylor
authors: T. Zhang
year: 2026
title: 'Weak majorization inequalities for the cubic and quartic coefficients of e^{(A+B)t} versus e^{At}e^{Bt}'
doi: 10.48550/arXiv.2601.07286
url: https://arxiv.org/abs/2601.07286
claim: 'Conjecture 5.5 compares the nonincreasing eigenvalue lists of (A+B)^k and the Hermitian part of the ordered binomial coefficient for all Hermitian A and B and every k at least five, without a positivity assumption.'
strata_touched:
  - D5/S3/Quantum/Matrix/TaylorMajorization/Defs
  - D5/S3/Quantum/Matrix/TaylorMajorization/Result
license: citation-only
triage: anchor
---

# Taylor coefficients and weak majorization

T. Zhang, *Weak majorization inequalities for the cubic and quartic
coefficients of e^{(A+B)t} versus e^{At}e^{Bt}*, arXiv:2601.07286v1
(12 January 2026).

## Verified locator

https://arxiv.org/abs/2601.07286

Section 5, Conjecture 5.5; notation in Section 1 and the abstract.
The pinned text is version 1. The abstract and Section 1 define $H_n$
as all complex Hermitian matrices of size $n$. The conjecture states:

> For A, B ∈ Hₙ and every k ≥ 5, λ(H^k) ≺_w λ(R_k).

Here $H=A+B$,
$Q_k=\sum_{p=0}^k\binom{k}{p}A^pB^{k-p}$ and
$R_k=\operatorname{Re}Q_k=(Q_k+Q_k^*)/2$.
The eigenvalue lists are nonincreasing, and weak majorization compares
all initial sums, including the full trace sum. There is no positivity
assumption on $A$ or $B$.

## Scope

The source proves the comparisons for $k=3,4$ and supplies a sufficient
commutator-decomposition condition for higher orders. Its singular-value
Problem 1.1 is a separate question. The shifted Pauli refutation of
Conjecture 5.5 is a repository result, not a result attributed to Zhang.
