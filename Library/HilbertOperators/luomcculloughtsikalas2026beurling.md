---
bibkey: luomcculloughtsikalas2026beurling
authors: Shuaibing Luo, Scott McCullough and Georgios Tsikalas
year: 2026
title: Beurling Criteria for Reproducing Kernels
doi: null
url: "https://arxiv.org/abs/2607.25088v2"
claim: "Question 9.3 asks whether a complete pseudo-Pick pair of reproducing kernels with non-vanishing k must satisfy ell/k positive semidefinite."
strata_touched:
  - D5/S3/HilbertOperators/ReproducingKernels/CompletePseudoPickQuotientRefutation
license: citation-only
triage: anchor
---

# Complete pseudo-Pick pairs and quotient positivity

Shuaibing Luo, Scott McCullough and Georgios Tsikalas, *Beurling Criteria for Reproducing Kernels*, arXiv:2607.25088v2.

## Verified locator

Source: https://arxiv.org/abs/2607.25088v2

## Statements

Question 9.3, PDF page 45:

> Let $(k, \ell)$ be a pair of reproducing kernels with $k$ non-vanishing. If $(k, \ell)$ is complete pseudo-Pick, do we have $\ell/k\succeq 0$?

Definition 9.2, PDF page 45:

> A pair $(k, \ell)$ on a set $X$ is a *complete pseudo-Pick* pair if, whenever positive integer $n$ and $k$, points $z_1, \dots, z_n\in X$ and matrices $W_1, \dots, W_n\in M_k(\mathbb C)$ satisfy
> $$(I-W_iW_j^*)k(z_i,z_j)\succeq 0,$$
> there exists a contractive multiplier $\Phi\in\operatorname{Mult}(\mathcal H_\ell\otimes\mathbb C^k,\mathcal H_\ell\otimes\mathbb C^k)$ such that $\Phi(z_i)=W_i$ for all $i$.

Section 3, PDF page 15:

> In this case, $\Phi$ induces a bounded operator $M_\Phi:\mathcal H_\kappa\otimes\mathcal F\to\mathcal H_\lambda\otimes\mathcal E$ whose norm is the smallest $C\ge 0$ such that
> $$X\times X\ni(a,b)\mapsto C^2\lambda(a,b)I_\mathcal E-\Phi(a)\Phi(b)^*\kappa(a,b)$$
> is positive semi-definite.

The finite block matrix uses every ordered pair of observations, including repeated nodes. The matrix-size letter is written `m` in Lean. The contractive multiplier predicate specializes the norm characterization to $C=1$, $\kappa=\lambda=\ell$, and coefficient spaces $\mathbb C^m$.

## Scope

The three-point pair with coordinates $(1/10,1,2)$, $k(i,j)=1+x_ix_j$ and $\ell(i,j)=1+\delta_{ij}x_i^2$ is complete pseudo-Pick for all matrix sizes. Its quotient has quadratic form $-10/33$ at $(-2,1,1)$.

The source kernel has a dependence among its three kernel vectors. The result imposes neither strict positive definiteness of the source nor holomorphicity. Infinite-rank extensions and the separate implication to BLH are open here; the source's established theorems are unaffected. Completeness of the literature search is ASSUMED-UNVERIFIED.
