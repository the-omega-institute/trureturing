---
bibkey: audenaert2009variance
authors: Koenraad M. R. Audenaert
year: 2009
title: "Variance bounds, with an application to norm bounds for commutators"
doi: null
url: https://arxiv.org/abs/0907.3913
claim: "Cartesian variance is the density expectation of (A* A + A A*)/2 minus the squared modulus of the mean; numerical-range convexity and the maximal variance control matrix commutators."
strata_touched:
  - D5/S3/Quantum/Matrix/WeightedBotcherWenzel
license: citation-only
triage: anchor
---

# Variance bounds, with an application to norm bounds for commutators

## Verified locator

Source: https://arxiv.org/abs/0907.3913

Section 7, page 17, defines the Cartesian modulus and variance:

> For that reason we need a name for the expression ((X∗X + XX∗)/2)1/2, and we have chosen to call it the Cartesian modulus.

> Each modulus builds a different variance, which we’ll distinguish by the corresponding subscript too.

Equation (27) reads $\operatorname{Var}_{\ast}(X)=\operatorname{Tr}[\rho|X|_{\ast}^{2}]-|\operatorname{Tr}[\rho X]|^{2}$, where the subscript is L, R or C. For C, $|X|_{C}^{2}=(X^{\ast}X+XX^{\ast})/2$.

The numerical range on pages 17–18 is $W(X)=\{\psi X\psi^{\ast}:\psi\in\mathbb{C}^{d},\|\psi\|=1\}$.

Theorem 9 and its proof relate the maximum Cartesian variance to the Cartesian radius; the proof uses the Toeplitz-Hausdorff convexity of the complex numerical range. The commutator application uses the density matrix $(B^\ast B+BB^\ast)/(2\|B\|_F^2)$ for nonzero $B$. The pure maximizer is represented by a normalized vector, whose rank-one matrix is $vv^\ast$.
