---
bibkey: connesconsani2021archimedean
authors: Alain Connes and Caterina Consani
year: 2021
title: Weil positivity and trace formula the archimedean place
doi: 10.1007/s00029-021-00689-4
url: https://arxiv.org/abs/2006.13771v1
claim: The archimedean Sonin trace supplies a positive comparison on a fixed prime-free support interval, with a rank-one correction and a specified Mellin vanishing condition. The theorem does not supply the corresponding signed comparison for growing semilocal place sets.
strata_touched: []
license: citation-only
triage: anchor
---

# Archimedean Sonin trace and its arithmetic transfer obligation

The inspected primary manuscript is [arXiv:2006.13771v1](https://arxiv.org/pdf/2006.13771v1), 24 June 2020, 57 pages, SHA-256 `b8e0b54ade8535cf3ca633d1ef325bfc5c793b407da577a83d111726935b58e0`. The [publisher metadata](https://link.springer.com/article/10.1007/s00029-021-00689-4) identifies *Selecta Mathematica* 27 (2021), paper 77, DOI [10.1007/s00029-021-00689-4](https://doi.org/10.1007/s00029-021-00689-4). The locators and equations below refer to the inspected manuscript; equality with the publisher edition is not asserted. This note reuses published results, without a new Lean implementation, proof audit or independent reproduction of the source's numerical bounds.

## Keep the source normalization

The physical Hilbert space is $H_\infty=L^2(\mathbb R)_{\rm ev}$ with inner product $\frac12\int_{\mathbb R}\overline{\eta(x)}\xi(x)\,dx$. Equation (17), manuscript p.7, identifies it unitarily with multiplicative $L^2$ through $w\xi(u)=u^{1/2}\xi(u)$, using $d^*u=du/u$. Equation (61), p.23, gives the unitary scaling action

$$
(\vartheta(u)\xi)(x)=u^{-1/2}\xi(u^{-1}x).
$$

For a multiplicative test $g$, use the source transform $\widehat g(s)=\int_0^\infty g(u)u^{-is}\,d^*u$ and convolution involution $g^*(u)=\overline{g(u^{-1})}$. Section 1's $W_\infty$ uses the half-density transformation and the positivity sign of the source, with $W_\infty=-W_{\mathbb R}$ in its notation. The sign and half-density cannot be dropped when relating it to the project's [actual full Weil form](frankliebseiringer2006hardy.md).

Let $R_\infty$ be the orthogonal projection onto the Sonin space $\mathcal S(1,1)$: physical even functions whose values and Fourier transforms vanish on $[-1,1]$. This is a physical phase-space cutoff, distinct from the support of the multiplicative test.

## Reuse the trace identity and the signed local estimate

Theorem 4.7, manuscript pp.27–28, equations (83)–(84), gives the exact trace identity

$$
\operatorname{Tr}(\vartheta(h)R_\infty)=W_\infty(h)+E_\infty(h),
\qquad
E_\infty(h)=\int_0^\infty h(u^{-1})\epsilon(u)\,d^*u,
$$

for $h\in C_c^\infty(\mathbb R_+^*)$. The source defines $\epsilon$ by its prolate expansion. This trace functional is positive on convolution squares. The positive trace alone does not determine the sign of $W_\infty$: the correction $E_\infty$ is part of the same identity.

Theorem 6.11, manuscript pp.48–49, strengthens this to

$$
W_\infty(g*g^*)\ge
\operatorname{Tr}\bigl(\vartheta(g)R_\infty\vartheta(g)^*\bigr)
-C\lvert\widehat g(0)\rvert^2,
$$

when $g\in C_c^\infty(\mathbb R_+^*)$ has support in $[2^{-1/2},2^{1/2}]$ and $\widehat g(-i/2)=0$. Equivalently, this last condition is $\int g(u)u^{-1/2}\,d^*u=0$, as explicitly used in the theorem's proof. Here $C=4\gamma_*/\log2$ with the source's $\gamma_*\simeq2.94355$, distinct from Euler's constant. The introduction reports $13<C<17$. With $\widehat g(0)=0$ the correction disappears. The introduction writes a different sign for the imaginary vanishing point; this note follows Theorem 6.11 and its integral formula.

The estimate uses Lemma 6.10, a finite-rank operator approximation and source numerical bounds, including Fact 6.1. Those calculations are supplier evidence and are not rerun or promoted to kernel verification here.

The support of $g*g^*$ is contained in $[1/2,2]$. Smoothness makes the endpoint prime contribution vanish, so this is the prime-free archimedean comparison. In additive coordinates $u=e^x$ it corresponds to $\lvert x\rvert\le\frac12\log2$ for $g$ and $\lvert x\rvert\le\log2$ for its autocorrelation. Enlarging that interval introduces prime-power terms; the theorem supplies no signed estimate for them.

## Vanishing constraints and the remaining semilocal comparison

Appendix C, Proposition C.1, manuscript p.51, supplies the existing constrained Weil criterion: a fixed finite set of Mellin zeros disjoint from the nontrivial zeta zeros and containing $\{0,1\}$ may be imposed while retaining equivalence to RH over **all compact supports**. It does not turn positivity at this single small support into RH. Transporting the particular constrained family into a project test family still requires the transform, involution and pole normalization to agree.

The [semilocal dual maps](connesconsanimoscovici2024semilocal.md) preserve an exact pairing and identify the corresponding Sonin spaces, but have different norm and operator contracts. For a growing finite place set $S$, the useful missing supplier would be an identity for the **same actual arithmetic form**, including the finite-place distributions and the pole convention, together with an upper bound on its trace correction analogous to $E_\infty(g*g^*)\le C\lvert\widehat g(0)\rvert^2$. The source identity, support restriction and bound should be reused; none is a new theorem of this project.

The [fixed-test trace remainder](connes1999trace.md) concerns a distinct cutoff limit and supplies no favorable signed correction by itself. No semilocal extension of the displayed signed bound has been obtained here. RH and cofinal actual Weil positivity remain unproved.
