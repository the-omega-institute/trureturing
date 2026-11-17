---
bibkey: bhatiajainlim2018wasserstein
authors: Rajendra Bhatia; Tanvi Jain; Yongdo Lim
year: 2018
title: Inequalities for the Wasserstein mean of positive definite matrices
doi: null
url: https://arxiv.org/abs/1803.03357
claim: "Equation (2) defines the weighted Wasserstein mean as the positive definite minimizer of the weighted sum of squared Bures–Wasserstein distances."
strata_touched:
  - D5/S3/Quantum/Matrix/HwangKimNearOrderRefutation
license: citation-only
triage: anchor
---

# Inequalities for the Wasserstein mean of positive definite matrices

## Verified locator

Source: https://arxiv.org/abs/1803.03357

## Source definition

Page 1, equation (2):

> Let $A_1,\dots,A_m$ be given positive definite matrices and let $w=(w_1,\dots,w_m)$ be a vector of weights; i.e., $w_j\geq0$ and $\sum_{j=1}^m w_j=1.$ Then the (weighted) Wasserstein mean, or the Wasserstein barycentre of $A_1,\dots,A_m$ is defined as

$$
\Omega(w;A_1,\ldots,A_m)=\underset{X\in\mathbb P}{\arg\min}
\sum_{j=1}^{m}w_j d^2(X,A_j).
$$

For admissible inputs the positive definite minimizer is unique. The Lean
definition uses `Classical.epsilon` on the minimizer predicate, with `n`
counting the inputs, `m` the matrix dimension, and `Fin n` indexing the inputs.

## Established transport and comparison results

The complete revision2 intake at [#29594](https://github.com/the-omega-institute/trureturing/issues/29594)
includes a primary-source check of Bhatia–Jain–Lim, *On the Bures–Wasserstein
Distance Between Positive Definite Matrices*, arXiv:1712.01504v1,
Theorem 8 and equations (62)–(63). Its unique positive minimizer satisfies
the weighted transport equation; equation (9) supplies the unique positive
Riccati solution. The finite certificate in `BuresWassersteinTransport`
returns this established characterization to the actual argmin definition.
The elementary dual proof is also Lemma 2 in Ma–Zhang revision2; it is not
a new scientific optimality characterization.

In arXiv:1803.03357v1, equations (18) and (22) give the commuting formulas;
Theorem 1 / (19) proves weak log-majorization. Conjecture 1 / (25) concerns
weak majorization, equivalently all unitarily invariant norms, of
$Q_{1/2}=(\sum_jw_jA_j^{1/2})^2$ by the Wasserstein mean. Equation (54)
separately proves entrywise spectral comparison of LE with $Q_{1/2}$.
An obstruction to the stronger entrywise $Q_{1/2}$ comparison does not
refute Conjecture 1. $Q_{1/2}$ is not the Wasserstein barycenter.

Hiai arXiv:2508.20309v2, Propositions 4.6–4.7, compares LE with the binary
quasi-arithmetic mean $A_{\alpha,q}$; at $q=1/2$ that is $Q_{1/2}$.
Those results do not identify that mean with the Wasserstein barycenter.
