---
bibkey: lin2017dtimajorization
authors: Minghua Lin
year: 2017
title: On a determinantal inequality arising from diffusion tensor imaging
doi: 10.1142/S0219199716500449
url: https://arxiv.org/abs/1604.04141v1
claim: Conjecture 4.3 asserts that lambda(A² + |BA|^p) majorizes lambda(A² + |AB|^p) for positive semidefinite A and B and every real p > 0.
strata_touched:
  - D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1142/S0219199716500449

Source: https://arxiv.org/abs/1604.04141v1

Communications in Contemporary Mathematics 19, no. 5, 1650044.

## Source statements

Conjecture 4.3, arXiv v1 p. 6:

> Let A and B be n × n positive semidefinite matrices. Then λ(A² + |BA|^p) ≻ λ(A² + |AB|^p) for all p > 0.

Section 1, p. 1:

> Here, for a complex matrix X, the absolute value of X is defined as |X| = (X*X)^{1/2}, the unique positive semidefinite square root of X*X.

Section 2, p. 2:

> we say that x weakly majorizes y, written as x ≻_w y, if Σ_{i=1}^k x↓_i ≥ Σ_{i=1}^k y↓_i for k = 1, …, n. We say x majorizes y, denoted by x ≻ y, if x ≻_w y and the sum of all elements of x equal to the sum of all elements of y.

> For an n × n matrix A with all eigenvalues real, we denote the vector of eigenvalues by λ(A) = (λ₁(A), …, λ_n(A)), and we assume that the components of λ(A) are in descending order.

## Encoding

Complex matrices have carrier `Matrix (Fin n) (Fin n) ℂ`. The absolute power is
`cfc (fun x : ℝ => x ^ p) (CFC.sqrt (Xᴴ * X))`. The eigenvalue list is
`List.ofFn h.eigenvalues` sorted by `decide (b ≤ a)`, with an empty-list extension
outside Hermitian matrices. Majorization compares all positive-length prefixes and
requires equality of total sums. The refutation fixes `n = 3` and `p = 4`.

## Literature boundary

The source and literature screen are specified by
[issue #18700](https://github.com/the-omega-institute/trureturing/issues/18700).
The later determinant inequalities recorded there do not establish this majorization
conjecture. Completeness of that screen is `ASSUMED-UNVERIFIED`; in particular the
Lemos–Soares paper, DOI 10.1016/j.laa.2018.02.015, and the remaining citing works were
not independently read for this formalization.
