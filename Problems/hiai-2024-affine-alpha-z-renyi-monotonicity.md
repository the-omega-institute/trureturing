---
slug: hiai-2024-affine-alpha-z-renyi-monotonicity
bibkey: hiai2024affinerenyi
doi: 10.1007/s44146-024-00142-w
url: https://arxiv.org/abs/2402.16067
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Divergence/AlphaZAffine/Result.result
---

# Hiai's affine alpha-z Renyi monotonicity question

## Problem

Fumio Hiai, arXiv:2402.16067v3, Section 3, Remark 3.2, asks whether the
alpha-z Renyi divergence is nondecreasing along every nonnegative affine
parameter line. The source statement fixes the following target.

For every finite-dimensional pair of positive semidefinite complex
matrices $\rho\ne0$ and $\sigma$, every $\kappa,z_0\ge0$ with
$\kappa+z_0>0$, and all $0<\alpha\le\beta$,

$$
D_{\alpha,\kappa\alpha+z_0}(\rho\Vert\sigma)
\le
D_{\beta,\kappa\beta+z_0}(\rho\Vert\sigma).
$$

Here $Q_{\alpha,z}=\operatorname{Tr}
|\rho^{\alpha/(2z)}\sigma^{(1-\alpha)/(2z)}|^{2z}$ when
$\alpha\in[0,1]$ or $s(\rho)\le s(\sigma)$, and $+\infty$
otherwise. For $\alpha\ne1$,
$D_{\alpha,z}=\log(Q_{\alpha,z}/\operatorname{Tr}\rho)/(\alpha-1)$.
At one it is the normalized Umegaki value
$\operatorname{Tr}\rho(\log\rho-\log\sigma)/\operatorname{Tr}\rho$
under the support condition, and $+\infty$ otherwise. Negative powers
vanish on the kernel and invert on the support.

## Motivation

The fixed-$z$ result is identified as Theorem 3.1(ii) in the supplied
source statement. The affine question links that result to the families
with $z$ proportional to $\alpha$ and retains the actual noncommutative
trace, the normalization by $\operatorname{Tr}\rho$, and the Umegaki
value at one. A comparison on just one side of one does not settle the
question.

## Gap

The terminal theorem proves the supported semidefinite comparison for
$\kappa>0$ and $z_0\ge0$ on all of $(0,\infty)$, including the
prescribed value at one and comparisons across one. It assumes only
positive semidefiniteness, $\rho\ne0$, and
$\ker\sigma\subseteq\ker\rho$, the support condition written
in kernel form. The fixed-$z$ case $\kappa=0$ and the unsupported
extended-value cases remain source-level consequences described below;
they are not added as Lean conclusions.

The Lean theorem quantifies only $\alpha>0$. If $z_0=0$, alpha zero
also gives $z=0$ and is outside the original definition. If $z_0>0$,
the source endpoint at alpha zero is defined but not quantified by
`result`. For positive alpha tending to zero the rho power tends to
$s(\rho)$ on the fixed finite spectrum, giving the source trace and
divergence by continuity. Theorem 3.1 and this continuity bridge give
the endpoint comparison: source literature proved or paper derived,
not formalized. The totalized Lean expression at zero uses $\rho^0=I$
instead of $s(\rho)$ and is not claimed to match the source there.
The cancellation of the extra kernel component of $\sigma^0=I$
concerns alpha one only.

## Route

For positive definite inputs set

$$
A=\rho^{-z_0/(2\kappa)},\quad
B=\sigma^{(\kappa+z_0)/(2\kappa)},\quad
Z=\rho^{1/(2\kappa)}\sigma^{-1/(2\kappa)}.
$$

For $z=\kappa\alpha+z_0$ the product
$A^{1/z}ZB^{1/z}$ is
$\rho^{\alpha/(2z)}\sigma^{(1-\alpha)/(2z)}$. This identifies the
Bourin-Lee form; the proof uses the direct two-parameter interpolation
instead of assuming a Bourin-Lee theorem.

Complex three-lines interpolation applies to every compound matrix of
the exponential family. Its norm controls each prefix product of
singular values, giving weak log-majorization. With
$z_t=(1-t)z_0+tz_1$ and $\theta=tz_1/z_t$, the powers satisfy
$(1-\theta)2z_t=(1-t)2z_0$ and
$\theta2z_t=t2z_1$. The power-sum estimate and scalar Holder inequality
therefore prove joint convexity of $\log Q_{\alpha,z}$ on
$\mathbb R\times(0,\infty)$.

An affine restriction remains convex. Since
$Q_{1,z}=\operatorname{Tr}\rho$, its normalized secant slopes from one
are the divergences away from one. On $z=1$, the product rule and
$A^a=\exp(a\log A)$ compute the derivative as the normalized Umegaki
trace. Joint convexity and the constant value along $\alpha=1$ supply
the same supporting affine function at every positive scale. A fixed
positive interpolation weight gives a differentiable upper envelope
with the same derivative. The upper and lower errors squeeze the
affine restriction's error to little-o of $\alpha-1$, proving its full
two-sided derivative. Convex secants then lie on the appropriate sides
of the Umegaki value.

For singular supported inputs the proof uses the common
regularizations $\rho+\varepsilon I$ and $\sigma+\varepsilon I$.
On the kernel of $\sigma$, both original matrices vanish. The positive
and negative powers in their product contribute a net exponent
$1/(2z)>0$, so this kernel contribution vanishes as
$\varepsilon\downarrow0$. The supported part is treated on its fixed
finite spectrum. Passing the actual trace limits through the positive
definite inequalities gives the supported semidefinite conclusion away
from one. At one, the supported part of the matrix logarithm converges
on its fixed finite spectrum; the kernel correction in the cross term
is $\varepsilon\log\varepsilon$ times the kernel projection. The
self term uses continuity of $x\log x$ at zero. Thus the actual
normalized Umegaki trace also converges, and the same limit argument
includes the point one.

## Falsifier

A terminal statement would fail to answer the source if it assumed
positive definiteness, omitted $\alpha=1$, assumed joint convexity or
the desired regularization limit, treated only commuting matrices or a
fixed dimension, or asserted only comparisons within one side of one.
The displayed matrix product must agree with the supported-power
convention, including zero eigenvalues, rather than using ordinary
negative powers on the whole space.

Joint convexity alone does not imply convexity after composition with
an arbitrary convex curve $z(\alpha)$. Such a deduction needs an
additional order condition in the second coordinate, or a separate
argument. For example, the perspective quadratic
$F(a,z)=(a-1)^2/z$ is jointly convex for $z>0$ and satisfies
$F(1,z)=0$. On the convex curve $z(a)=a^2$, its normalized secant is
$(a-1)/a^2$, whose derivative $(2-a)/a^3$ is negative for $a>2$.
This is a counterexample to the proposed inference, not a counterexample
to any Renyi-divergence claim.

## Evidence

The source identity and exact parameter conventions are recorded in
`Library/Divergence/hiai2024affinerenyi.md`. The public theorem
`D5.S3.Quantum.Divergence.AlphaZAffine.result` proves
`MonotoneOn (fun a => hiaiD rho sigma a (affineZ kappa z0 a)) (Set.Ioi 0)`
for arbitrary finite complex matrices under positive semidefiniteness,
nonzero rho, support inclusion, positive kappa and nonnegative offset.
Its total real-valued `hiaiD` uses the normalized Umegaki expression at
one and the logarithmic quotient elsewhere; the theorem restricts it to
the supported domain where Hiai's values are finite.

The private auxiliary theorems establish the spectral interpolation,
derivative transfer and singular-support limits in the module rather
than supplying them as hypotheses.

## Triage

**Proved in Lean:** For positive definite inputs, joint logarithmic
convexity on $\mathbb R\times(0,\infty)$ and the affine logarithmic
trace derivative at one; for supported semidefinite inputs, affine-line
monotonicity on the full positive axis, including the normalized Umegaki
value at one. The mechanism is compound-matrix three-lines interpolation,
weak log-majorization, finite Holder interpolation, convex secants and
common positive regularization.

**Derived on paper, not formalized:** The Bourin-Lee substitution in Route is an algebraic
identification of the same power product. For Hermitian matrices, range
is the orthogonal complement of kernel, so the theorem's kernel inclusion
is equivalent to support inclusion. The method counterexample
$F(a,z)=(a-1)^2/z$, $z(a)=a^2$ in Falsifier has normalized secant
derivative $(2-a)/a^3<0$ for $a>2$. It refutes the general inference
from joint convexity to convex-curve monotonicity, not a Renyi claim.

**Proved in the source, not formalized:** For $\kappa=0$, $z_0>0$, Theorem 3.1(ii)
gives fixed-z monotonicity. Without support inclusion, the values at one
and above one are $+\infty$, and the below-one comparison uses the
source result. These extended-value cases are not additional Lean claims.

**Derived on paper, not formalized:** For $z_0>0$, the source alpha-zero comparison follows from
Theorem 3.1 and the right-continuity bridge in Gap; it is not formalized.
For $z_0=0$, alpha zero lies outside the source domain because $z=0$.

**Open:** An arbitrary convex-curve extension of the Renyi comparison
remains unproved; joint convexity alone does not establish it.

## ASSUMED-UNVERIFIED

The version, DOI, source numbering and mathematical source statement
are supplied task data. The literal Remark wording has not been independently compared with
the manuscript.
Exhaustive later-literature completeness and worldwide priority are
unverified. The formal conclusion is the supported semidefinite theorem
for positive kappa; its combination with Hiai's fixed-z and
extended-value results is a mathematical source comparison, not a
separate compiled extended-real theorem.
