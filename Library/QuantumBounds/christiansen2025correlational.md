---
bibkey: christiansen2025correlational
authors: Martin Ravn Christiansen
year: 2025
title: "A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators"
doi: null
url: https://arxiv.org/abs/2505.21167v1
claim: "Conjecture 3 asks for a universal positive C bounding the two-body Rayleigh expectation by N(1-(N-2)/2 sum lambda_k^4+C(N lambda_max^2)^2) for even N with N lambda_max^2 <= 1."
strata_touched:
  - D5/S3/Quantum/FermionicCorrelationalBound/SourceCorrelationalBound
license: citation-only
triage: anchor
---

# A Correlational Bound for Eigenvalues of Fermionic 2-Body Operators

## Verified locator

DOI: null. Crossref title search returns no exact title match.

Source: https://arxiv.org/abs/2505.21167v1

Section 1.1: Theorems 1 and 2 and Conjecture 3. Section 2: identity (2.4).

## Conjecture 3

Section 1.1, p. 4:

> Let $\Phi\in\mathfrak{h}\wedge\mathfrak{h}$ be normalized with canonical form $\Phi=\sum_{k=1}^{\infty}\lambda_k u_k\wedge v_k$. Then there exists a constant $C>0$, independent of $\Phi$, such that for every $N\in2\mathbb{N}$ with $N\lambda_{\max}^2\le1$
>
> $$\sup_{\Psi\in\bigwedge^N\mathfrak{h},\,\|\Psi\|=1}\langle\Phi,\gamma_2^\Psi\Phi\rangle\le N\left(1-\frac{N-2}{2}\sum_{k=1}^{\infty}\lambda_k^4+C(N\lambda_{\max}^2)^2\right).$$

Here $u\wedge v=(u\otimes v-v\otimes u)/\sqrt2$, the pair vectors are mutually orthonormal, the coefficients are nonnegative with square sum one, and $\lambda_{\max}=\max_k\lambda_k$. The physical RDM has trace $N(N-1)$. A supplied canonical family can be finite or countable; all remaining one-particle modes are retained as spectators.

Theorem 1 requires $\Phi$ to be an eigenvector. Conjecture 3 and Theorem 2 concern its Rayleigh expectation without that requirement. Identity (2.4) reads $\langle\Phi,\gamma_2^\Psi\Phi\rangle=2\langle\Psi,B^*B\Psi\rangle$, where $B=\sum_k\lambda_k c(v_k)c(u_k)$.

## Two-body density matrix

Section 1, p. 1, equation (1.1):

> Given a normalized state $\Psi\in\bigwedge^N\mathfrak{h}$ we define the 2-body operator associated to $\Psi$, $\gamma_2^\Psi:\mathfrak{h}\otimes\mathfrak{h}\to\mathfrak{h}\otimes\mathfrak{h}$, by
>
> $$\langle\varphi_1\otimes\varphi_2,\gamma_2^\Psi(\psi_1\otimes\psi_2)\rangle=\langle\Psi,c^*(\psi_1)c^*(\psi_2)c(\varphi_2)c(\varphi_1)\Psi\rangle$$
>
> for any $\varphi_1,\varphi_2,\psi_1,\psi_2\in\mathfrak{h}$, where $c^*(\cdot)$ and $c(\cdot)$ denote the fermionic creation and annihilation operators.
