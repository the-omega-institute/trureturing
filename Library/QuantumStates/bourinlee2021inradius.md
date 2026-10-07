---
bibkey: bourinlee2021inradius
authors: J.-C. Bourin and E.-Y. Lee
year: 2021
title: "Eigenvalue inequalities for positive block matrices with the inradius of the numerical range"
doi: 10.1142/S0129167X22500094
url: https://arxiv.org/abs/2111.15180v1
claim: "Let $X\\in\\mathbb{M}_n$. If the inequality $\\left\\| \\begin{bmatrix} A &X \\\\ X^* &B\\end{bmatrix}\\right\\|_\\infty \\le \\|A+B\\|_\\infty$ holds for all positive block-matrix with $X$ as off-diagonal block, then $X$ is essentially Hermitian."
strata_touched:
  - D5/S3/Quantum/BlockNorm/SpikeEdgeEstimate
  - D5/S3/Quantum/BlockNorm/EssentiallyHermitian
license: citation-only
triage: anchor
---

# Positive block matrices and essentially Hermitian off-diagonal blocks

## Verified locator

DOI: 10.1142/S0129167X22500094

Source: https://arxiv.org/abs/2111.15180v1

Conjecture 3.3 is on printed page 6 of the arXiv v1 PDF. Crossref identifies
the same title and authors with the IJM DOI above. Theorem 3.2 on the same
page quotes Hayashi's Theorem 2.5 (arXiv:1808.00181).

Conjecture 3.3, verbatim, with its displayed formula:

> Let $X\in\mathbb{M}_n$. If the inequality
>
> $$\left\|\begin{bmatrix}A&X\\X^*&B\end{bmatrix}\right\|_\infty\le\|A+B\|_\infty$$
>
> holds for all positive block-matrix with $X$ as off-diagonal block, then $X$ is essentially Hermitian.

The preceding sentence is: "If W(T) is line segment, then T is a so-called
essentially Hermitian matrix." The binding convention in
https://github.com/the-omega-institute/trureturing/issues/13752 encodes this
as the literal affine Hermitian expression $X=\alpha H+\beta I$, with
$H=H^*$ and $\alpha,\beta\in\mathbb C$. The claim quantifies over every
$n\ge1$, all complex $n\times n$ matrices $X$, and every positive
semidefinite completion. The norm is the Euclidean operator norm, identified
in Lean with `Matrix.toEuclideanCLM` by definitional equality.

Hayashi's quoted theorem says, verbatim:

> Suppose that $X\in\mathbb{M}_n$ is invertible with $n$ distinct singular values. If the inequality
>
> $$\left\|\begin{bmatrix}A&X\\X^*&B\end{bmatrix}\right\|_\infty\le\|A+B\|_\infty$$
>
> holds for all positive block-matrix with $X$ as off-diagonal block, then $X$ is normal.

Proposition 3.4 on printed page 6 states the Frobenius-norm characterization:
the same inequality for every positive completion holds if and only if $X$
is normal. This is a proved result in the source; the operator-norm claim
has the stronger conclusion of an affine Hermitian matrix. The argument
for other unitarily invariant norms is not supplied here.

## Formal mechanism

Positive scalar shifts force the top and bottom spectral edges of
$K_X(D)=\begin{bmatrix}D&X\\X^*&-D\end{bmatrix}$ to sum to zero for every
Hermitian $D$. Rank-one probes $D=t vv^*+S$, with $Sv=0$, have a two-sided
edge expansion with error $1782L^4/t^3$ for $t\ge96L$ and
$L\ge\max(1,\|K_X(S)\|)$. The coefficient of $1/t$ forces normality;
the coefficient of $1/t^2$, tested with the difference of two projected
rank-one matrices, forces their equality. Unitary diagonalization then
makes the spectrum collinear and reconstructs $X=\alpha H+\beta I$.

## Code provenance

The private normal-operator and normal-matrix diagonalization proofs are
adapted from the TauCeti contributors, commit
`7c8d7117e41432d613582fc600dcb0a3be7dba30`, under Apache-2.0.
Copyright (c) 2026 The Tau Ceti contributors. The license text is available
at https://www.apache.org/licenses/LICENSE-2.0. No TauCeti Lake dependency
is used. Pinned Mathlib supplies the simultaneous eigenspace decomposition
of the self-adjoint real and imaginary parts and the subordinate
orthonormal basis construction.
