---
bibkey: barrykevrekidis2013vortex
authors: Anna M. Barry, Panayotis G. Kevrekidis
year: 2013
title: "Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability"
doi: 10.1088/1751-8113/46/44/445001
url: https://arxiv.org/abs/1306.1545v2
claim: "The paper studies equilibria and linear stability of few-vortex clusters in the precessing point-vortex model of a Bose–Einstein condensate and conjectures (Conjecture 4.4) that for N >= 6 the regular N-gon of alternating charges has N/2 - 2 distinct pairs of real eigenvalues."
strata_touched:
  - D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum
  - D5/S3/FluidDynamics/Vortices/InverseChordCirculant
license: citation-only
triage: anchor
---

# Barry–Kevrekidis, few-particle vortex cluster equilibria

## Verified locator

DOI: 10.1088/1751-8113/46/44/445001

Source: https://arxiv.org/abs/1306.1545v2

J. Phys. A: Math. Theor. 46 (2013), no. 44, 445001, published 18 October 2013.

A. M. Barry and P. G. Kevrekidis, arXiv:1306.1545v2 [nlin.PS] (10 June 2013, the latest version).

## Statement

The model is the precessing point-vortex system (Section 2, Eqs. (1)–(2), with $b=2$)
$$\dot x_j=-S_j\Omega y_j-\frac b2\sum_{k\ne j}S_k\frac{y_j-y_k}{|\mathbf x_j-\mathbf x_k|^2},\qquad \dot y_j=S_j\Omega x_j+\frac b2\sum_{k\ne j}S_k\frac{x_j-x_k}{|\mathbf x_j-\mathbf x_k|^2}.$$
Section 4.1 takes alternating charges $S_j=(-1)^{j+1}$ at $z_j=e^{2\pi ij/N}$; Lemma 4.2 gives the equilibrium with $\Omega=1/2$ for even $N$. The paper states:

> **Conjecture 4.4.** For $N\geq 6$, the $N$-gon has $\frac{N}{2}-2$ distinct pairs of real eigenvalues.

## Encoding and boundary

The repository defines the vector field of Eqs. (1)–(2) with $b=2$ and $\Omega=1/2$, the regular unit $N$-gon and the Jacobian matrix of partial derivatives at it. It proves that for $N=2m$, $m\ge3$, the nonzero real eigenvalues are exactly $\pm\frac{(m-k)\sqrt{k^2-2}}2$, $2\le k\le m-1$, and that these $m-2$ values are distinct. The Gross–Pitaevskii PDE stability, odd $N$, other charge patterns, eigenvectors and Krein signatures are outside this conclusion.
