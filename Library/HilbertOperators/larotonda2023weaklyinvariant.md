---
bibkey: larotonda2023weaklyinvariant
authors: Gabriel Larotonda and Iván Rey
year: 2023
title: "Weakly invariant norms: Geometry of spheres in the space of skew-Hermitian matrices"
doi: 10.1016/j.laa.2023.08.023
url: "https://arxiv.org/abs/2302.05957v1"
claim: "Problem 3.13 asks whether commutation with every norming matrix at V forces local constancy of the norm on V+s[X,V]."
strata_touched:
  - D5/S3/HilbertOperators/LarotondaReyNormingFlatnessRefutation
license: citation-only
triage: anchor
---

# Weakly invariant norms and Problem 3.13

Gabriel Larotonda and Iván Rey, Linear Algebra and its Applications 678, 136–168. The source used here is arXiv:2302.05957v1.

## Verified locator

DOI: 10.1016/j.laa.2023.08.023

Source: https://arxiv.org/abs/2302.05957v1

## Statements

Problem 3.13, PDF page 26, asks:

> Does $[N,X_C]=0$ for all $N$ norming $V$ imply that $\|V+s[X,V]\|=\|V\|$ in some interval $|s|<\delta$?

Definition 2.1, PDF page 3, states:

> It is a function $\|\cdot\|:\mathfrak u_n\to\mathbb R_{\ge0}$ such that for any $X,Y\in\mathfrak u_n$
>
> 1. $\|X\|=0$ if and only if $X=0$ (non-degenerate)
> 2. $\|X+Y\|\le\|X\|+\|Y\|$ (subadditive)
> 3. $\|\lambda X\|=\lambda\|X\|$ for any $\lambda\in\mathbb R_{\ge0}$ (positively homogenous)
> 4. $\|UXU^*\|=\|X\|$ for any $U\in\mathsf{\mathbf U}(n,\mathbb C)$ (Ad-invariant).

The trace-duality remark, PDF page 4, states:

> We say that $\varphi\in \mathfrak u_n'$ is a unit norming functional of $V\in\mathfrak u_n$ if $\varphi(V)=\|V\|$ and $\|\varphi\|=1$.

It defines $\|\varphi\|=\max\{\varphi(X):\|X\|\le1\}$ without the modulus and uses $\varphi_N(Y)=-\operatorname{tr}(NY)$ on the skew-Hermitian space. Definition 2.30, PDF page 14, states:

> Let $0\ne V\in\mathfrak u_n$, write $V=i\sum_{k\in F}v_kP_k$ with $v_1>v_2>\dots>v_F$ a diagonalization of $V$ where the eigenvalues are different and ordered decreasingly. Each $P_k$ is an orthonormal projection onto the corresponding eigenspace and $P_kP_j=0$ for $k\ne j$.

> For any $X\in\mathfrak u_n$ we can decompose $X=X_D+X_C$, where $X_D=\sum_kP_kXP_k$ and $X_C=\sum_{k\ne j}P_kXP_j$, the block-diagonal and block-codiagonal parts of $X$.

Theorem 3.11 instead uses a norming functional of the endpoint $V+[X,V]$. The counterexample to Problem 3.13 does not refute that endpoint criterion.

## Scope

The repository theorem refutes the recorded ambient-matrix formulation using a polar supremum in dimension two. Its witness is nondegenerate, subadditive, absolutely real homogeneous and Ad-invariant. A complete identification with the compact-body gauge, rank-one normalization and higher-dimensional extensions are not part of the theorem. Literature-search completeness remains ASSUMED-UNVERIFIED: the preregistration reports blocked citation endpoints and unread works.
