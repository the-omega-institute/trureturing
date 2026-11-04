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
