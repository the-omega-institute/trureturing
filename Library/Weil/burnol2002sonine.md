---
bibkey: burnol2002sonine
authors: Jean-François Burnol
year: 2002
title: Sur les « espaces de Sonine » associés par de Branges à la transformation de Fourier
doi: 10.1016/S1631-073X(02)02546-3
url: https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/S1631-073X(02)02546-3.pdf
claim: The physical even Sonin projection has an explicit truncated-Fourier resolvent formula, and its completed Mellin space has a genuine entire de Branges generator. The source does not estimate the projection after an Euler-factor change of metric.
strata_touched: []
license: citation-only
triage: anchor
---

# Physical Sonin projection and its entire generator

The inspected primary source is the [published article](https://comptes-rendus.academie-sciences.fr/mathematique/item/10.1016/S1631-073X(02)02546-3.pdf), *C. R. Acad. Sci. Paris, Ser. I* 335 (2002), pp.689–692, DOI [10.1016/S1631-073X(02)02546-3](https://doi.org/10.1016/S1631-073X(02)02546-3). Its four-page PDF has SHA-256 `799586f60b1b591dabfd4eddf02d7270bbb186182551315954d99a462666f7a5`. The following are supplier results, reused without a new proof, numerical reproduction, or Lean declaration. Inspection of the statements and accompanying argument is not a complete proof audit.

## Carrier, Fourier normalization and projection

Sections 2–3 use even physical functions with norm

$$
\|\xi\|^2=\int_0^\infty|\xi(t)|^2\,dt,
\qquad
(\mathcal F_+\xi)(x)=2\int_0^\infty\cos(2\pi xy)\xi(y)\,dy.
$$

For each $\lambda>0$, let $Q_\lambda$ be the orthogonal cutoff to $(-\lambda,\lambda)$, $F_\lambda=Q_\lambda\mathcal F_+Q_\lambda$ and $D_\lambda=F_\lambda^2$, acting on the even cutoff space. The physical Sonin space $K_\lambda$ consists of functions whose values and Fourier transforms vanish on that interval. It is distinct from the compact support of a multiplicative test integrating dilations.

The discussion preceding Theorem 4, printed p.691, gives $\|F_\lambda\|<1$. Theorem 4 gives the **orthogonal** projection

$$
\begin{aligned}
\pi_\lambda\xi={}&\xi
-(I-D_\lambda)^{-1}
\bigl(Q_\lambda\xi-F_\lambda\mathcal F_+\xi\bigr)\\
&-\mathcal F_+(I-D_\lambda)^{-1}
\bigl(Q_\lambda\mathcal F_+\xi-F_\lambda\xi\bigr).
\end{aligned}
$$

The inverse acts on the cutoff space; its outputs are extended by zero when regarded as physical functions. The source also identifies $D_\lambda$ with the kernel $\sin(2\pi\lambda(x-y))/(\pi(x-y))$ restricted to even cutoff functions. Corollary 5 gives specialized formulas, including for inputs already vanishing on the physical interval. These formulas should be reused rather than reconstructed from finite Gram matrices.

At $\lambda=1$, the carrier, norm and Fourier convention agree with the physical even Sonin setup of the [archimedean trace source](connesconsani2021archimedean.md). This statement concerns the source conventions; no new compiled project application is claimed.

## The entire generator is additional source data

Theorem 8, printed p.692, constructs an **entire** function $E_\lambda$ satisfying the de Branges condition for $\operatorname{Re}w>1/2$. It identifies $B(E_\lambda)$ isometrically with the completed Mellin transforms of $K_\lambda$, using the critical-line measure $dt/(2\pi)$. Theorem 9 identifies $E_\lambda$ with $\sqrt\lambda$ times the jump of the completed Mellin evaluator at the physical cutoff. Section 1, equation (1), gives the reproducing kernel in terms of the genuine entire generator.

The $S$-dependent local-factor product in the [semilocal source](connesconsanimoscovici2024semilocal.md) specifies its weighted norm; it is not thereby this entire generator. Substitution into a de Branges kernel formula requires an actual generator and the corresponding isometry.

## Remaining arithmetic interface

The source supplies the unweighted physical projection and its kernel ingredients. It does not estimate their deformation under the finite Euler-factor metric supplied by $\theta_S$, or the correction to the orthogonal compressed dilation trace. A physical projection formula alone does not determine that correction's sign.

The integrating Weil test remains separate from the even physical vectors. An odd additive test can integrate this physical representation without becoming an odd physical vector. No estimate for the [full same-test arithmetic form](frankliebseiringer2006hardy.md), including all prime powers, follows here. The actual semilocal signed comparison remains unresolved.
