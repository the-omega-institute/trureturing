---
bibkey: hiai2025quasiarithmetic
authors: Fumio Hiai
year: 2025
title: Various inequalities between quasi-arithmetic mean and quasi-geometric type means for matrices
doi: null
url: https://arxiv.org/abs/2508.20309
claim: Section 2.1 defines the quasi-arithmetic and quasi-harmonic means; Section 5 (4) asks whether their universal order comparison forces both positive exponents to be at least one.
strata_touched:
  - D5/S3/Quantum/Matrix/HiaiHarmonicArithmetic
license: citation-only
triage: anchor
---

# Quasi-harmonic and quasi-arithmetic matrix means

## Verified locator

Source: https://arxiv.org/abs/2508.20309.
DOI: null.

The checked source is arXiv:2508.20309v2 (2025-09-25), Section 2.1
and Section 5 (4). Section 5 (4) states:

> We have also Hα,p ≤ Aα,q for any p, q ≥ 1 since Theorem 4.16 yields Hα,p ≤ Gα,1 ≤ Aα,q . An interesting problem left open is whether Hα,p ≤ Aα,q holds only if p, q ≥ 1 or not. Here note that for any q > 0, Hα,p ≤ Aα,q fails to hold at least for sufficiently small p > 0

## Source definitions

Section 2.1 uses $0\le\alpha\le1$, $p>0$ and positive semidefinite
matrices $A,B$ in any finite dimension. It defines

$$
\mathcal A_{\alpha,p}(A,B)=(A^p\nabla_\alpha B^p)^{1/p}
=((1-\alpha)A^p+\alpha B^p)^{1/p}.
$$

On positive definite complex inputs, for a real parameter $t\ne0$, set

$$
M_t(A,B)=\bigl((1-\alpha)A^t+\alpha B^t\bigr)^{1/t}.
$$

The weighted harmonic mean on positive definite inputs and the
quasi-harmonic mean are

$$
A!_\alpha B=\bigl((1-\alpha)A^{-1}+\alpha B^{-1}\bigr)^{-1},
\qquad
\mathcal H_{\alpha,p}(A,B)=\bigl(A^p!_\alpha B^p\bigr)^{1/p}.
$$

For positive semidefinite inputs, Section 2.1 defines

$$
A!_\alpha B=\lim_{\varepsilon\downarrow0}
 (A+\varepsilon I)!_\alpha(B+\varepsilon I),
$$

and sets $A^0=s(A)$, the support projection. All powers are spectral
powers. On positive definite inputs, consequently,

$$
\mathcal H_{\alpha,p}(A,B)
=\bigl((1-\alpha)A^{-p}+\alpha B^{-p}\bigr)^{-1/p}
=M_{-p}(A,B).
$$

The comparison uses the Loewner order: $X\le Y$ means that $Y-X$ is
positive semidefinite.

## Source question

Section 5 (4) asks whether the comparison for all positive semidefinite
pairs can hold only when $p,q\ge1$. For $\alpha=0$ or $\alpha=1$,
both means reduce to $A$ or $B$, respectively, for every $p,q>0$.
The necessity question therefore concerns $0<\alpha<1$.
Its formalized restriction states that the comparison

$$
\mathcal H_{\alpha,p}(A,B)\le\mathcal A_{\alpha,q}(A,B)
\quad\text{for every positive definite complex pair }A,B
$$

can hold only when $p\ge1$ and $q\ge1$, already when testing only
positive definite pairs of size $2\times2$:

$$
\begin{aligned}
&\forall\alpha\in(0,1),\ \forall p,q>0,\\
&\quad\left[
\forall A,B\in\mathbb P_2(\mathbb C),\quad
\mathcal H_{\alpha,p}(A,B)\le\mathcal A_{\alpha,q}(A,B)
\right]
\ \Longrightarrow\ (p\ge1\ \text{and}\ q\ge1).
\end{aligned}
$$

Here $\mathbb P_2(\mathbb C)$ denotes the positive definite Hermitian
complex matrices of size two. Real symmetric positive definite pairs
are included in this quantifier domain. Section 5 (4) gives sufficiency
for $p,q\ge1$ through Theorem 4.16; that result applies on the source's
positive semidefinite domain and is not formalized here.

The Lean necessity result is restricted to $0<\alpha<1$ and positive
definite complex $2\times2$ matrices. Direct sums extend its counterexamples
to every dimension at least two on paper; positive definite inputs already
belong to the positive semidefinite domain. Completeness of later
literature and worldwide priority are not asserted.
