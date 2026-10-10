---
bibkey: mayumi2024weightedbw
authors: Aina Mayumi; Gen Kimura; Hiromichi Ohno; Dariusz Chruściński
year: 2024
title: "Böttcher-Wenzel inequality for weighted Frobenius norms and its application to quantum physics"
doi: 10.1016/j.laa.2024.07.013
url: https://arxiv.org/abs/2403.04199v2
claim: "Conjecture 1, case (ii), equation (15), bounds the weighted commutator norm by sqrt((lambda_min + lambda_max)/lambda_min) times the weighted norm of A and the Frobenius norm of B."
strata_touched:
  - D5/S3/Quantum/Matrix/WeightedBotcherWenzel
license: citation-only
triage: anchor
---

# Böttcher-Wenzel inequality for weighted Frobenius norms and its application to quantum physics

## Verified locator

DOI: https://doi.org/10.1016/j.laa.2024.07.013

Source: https://arxiv.org/abs/2403.04199v2

The weighted norm is defined on page 2, equation (2):

> In what follows we call ω-weighted Frobenius norm

$$\|A\|_\omega := \sqrt{\operatorname{tr}(A^\ast A\omega)}.$$

Conjecture 1 (page 6; cases (i) and (ii)):

> Conjecture 1. For any matrices $A, B \in M_n(\mathbb{C})$,

$$\|[A,B]\|_\omega \leq \sqrt{\frac{\lambda_m+\lambda_{sm}}{\lambda_m\lambda_{sm}}}\|A\|_\omega\|B\|_\omega,\tag{14}$$

$$\|[A,B]\|_\omega \leq \sqrt{\frac{\lambda_m+\lambda_M}{\lambda_m}}\|A\|_\omega\|B\|,\tag{15}$$

and on page 7:

> and (as a corollary of (14))

$$\|[A,B]\| \leq \sqrt{\frac{\lambda_m+\lambda_{sm}}{\lambda_m^2\lambda_{sm}}}\|A\|_\omega\|B\|_\omega.\tag{16}$$

> All bounds are tight, i.e., there are non-zero matrices A and B that attain the equalities.

Here $\omega$ is positive definite, $\lambda_m$ and $\lambda_M$ are the smallest and largest eigenvalues, and $\lambda_{sm}$ is the second-smallest eigenvalue. Equation (15) is case (ii); cases (i) and (iv) are equations (14) and (16). The settling claim is equation (15) squared. Its sharpness example is $A=|\lambda_M\rangle\langle\lambda_m|$, $B=A^\ast$ (page 7). The relaxation-rate application is equation (28) in Section 3.2, conditional there on equation (15).
