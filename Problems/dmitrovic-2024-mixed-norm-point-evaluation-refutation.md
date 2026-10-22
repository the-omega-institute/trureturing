---
slug: dmitrovic-2024-mixed-norm-point-evaluation-refutation
bibkey: dmitrovic2024norm
doi: 10.7153/oam-2024-18-42
url: https://doi.org/10.7153/oam-2024-18-42
triage: theorem
motivation_gids:
  - D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.claim
---

# Dmitrović: constant-one mixed-norm point evaluation

## Problem

D. Dmitrović, *Norm of composition operator on mixed norm spaces*,
Operators and Matrices 18(3) (2024), 697–710,
[doi:10.7153/oam-2024-18-42](https://doi.org/10.7153/oam-2024-18-42),
end of section 2, page 705, states:

> CONJECTURE. From the previous discussion, we conjecture that for all 0 < p, q ⩽ ∞, 0 < α < ∞ and f ∈ H^{p,q,α}: |f(z)| ⩽ ‖f‖_{p,q,α} / (1 − |z|²)^{α + 1/p}.

The definitions on page 697 are:

$$
\|f\|_{p,q,\alpha}
=\left(2\alpha q\int_0^1 r(1-r^2)^{\alpha q-1}M_p^q(r,f)\,dr\right)^{1/q}
\qquad(0<q<\infty),
$$

$$
\|f\|_{p,\infty,\alpha}
=\sup_{0<r<1}(1-r^2)^\alpha M_p(r,f),
\qquad
M_p(r,f)=\left(\frac1{2\pi}\int_0^{2\pi}|f(re^{i\theta})|^p\,d\theta\right)^{1/p}.
$$

Here $M_\infty$ is the supremum over $\theta$. The space $H^{p,q,\alpha}$
consists of holomorphic functions on the unit disc with finite mixed norm.
The convention is $1/\infty=0$.
The Lean claim multiplies the inequality by the strictly positive weight
$(1-|z|^2)^{\alpha+1/p}$; this is equivalent to the displayed quotient form.

## Motivation

Lemma 2 proves the constant-one estimate for $p=\infty$ and for finite
positive $q\le p$. For finite $q>p$ it gives the larger upper constant
$2^{\alpha+3/p}$, and for finite $p$, $q=\infty$ it gives
$2^\alpha(1+3|z|)^{1/p}(1+|z|)^{1/p}$.
The conjecture asks whether the constant can nevertheless be one
throughout the remaining parameter range.

## Gap

For every finite $p>0$, every $q\in(p,\infty]$, and every $\alpha>0$,
the constant-one estimate fails. The witnesses are bounded holomorphic
functions

$$
f_a(w)=\exp\left(\frac2p\operatorname{Log}(1+aw)\right),
\qquad 0<a<1,\qquad z=\frac{a}{1+\alpha p},
$$

with the principal logarithm. On the unit disc,
$\operatorname{Re}(1+aw)>1-a>0$ and
$|f_a(w)|\le(1+a)^{2/p}$.
The refutation was derived with the assistance of the ChatGPT Pro model.

## Route

The full-period angular integral gives the exact identity

$$
M_p(\rho,f_a)^p=1+a^2\rho^2.
$$

For finite $q>p$, put $t=a^2$, $r=q/p$, $\beta=\alpha q$, and
$c=1/(1+\alpha p)$. The q-th powers of the norm and normalized evaluation
are respectively

$$
N(t)=2\alpha q\int_0^1\rho(1-\rho^2)^{\alpha q-1}(1+t\rho^2)^r\,d\rho,
\qquad
L(t)=(1+ct)^{2r}(1-c^2t)^{\beta+r}.
$$

Convexity bounds the radial power by its chord and yields

$$
N(t)\le U(t):=1+\frac{(1+t)^r-1}{\beta+1}\quad(t\ge0).
$$

The endpoint-singular weights are integrable for every $\beta>0$.
The comparison functions satisfy $L(0)=U(0)=1$ and

$$
L'(0)=\frac{r}{1+\alpha p},\qquad U'(0)=\frac{r}{1+\alpha q},\qquad
D:=L'(0)-U'(0)=\frac{r\alpha(q-p)}{(1+\alpha p)(1+\alpha q)}>0.
$$

Consequently $L(t)>U(t)\ge N(t)$ for some $t\in(0,1)$.
Taking positive q-th roots gives the strict point-evaluation violation.
The normalized evaluation grows at first order $r/(1+\alpha p)$ while
the radial norm has the upper comparison slope $r/(1+\alpha q)$; equality of these
slopes is exactly $q=p$.

For $q=\infty$, the weighted circle mean
$(1-u)^\alpha(1+tu)^{1/p}$ is nonincreasing on $[0,1)$ if
$0<t\le\alpha p$. Its supremum is one, approached as the radius tends
to zero. The normalized evaluation

$$
E(t)=(1+ct)^{2/p}(1-c^2t)^{\alpha+1/p}
$$

satisfies $E(0)=1$ and $E'(0)=1/[p(1+\alpha p)]>0$.
A sufficiently small positive $t$ therefore violates constant one.

## Falsifier

For the universal conjecture, a single holomorphic function of finite
mixed norm and an interior point giving a strict reversed inequality is
a counterexample. The general failure theorem has the stronger target
of such a counterexample for every finite $p>0$, every $q>p$ including
infinity, and every $\alpha>0$. A parameter triple in that range for
which all normalized evaluations are bounded by the norm would refute
that stronger theorem. An error in a circle integral, the endpoint
integrability, or the strict slope comparison would invalidate the
corresponding argument without proving the conjecture.

## Evidence

The pinned source model is in
[Defs.lean](../D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs.lean).
[CircleMean.lean](../D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/CircleMean.lean)
proves holomorphy, boundedness, the exact angular mean, the radial norm
identity, and the infinite-q refutation.
[FirstOrderGap.lean](../D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/FirstOrderGap.lean)
proves the strict radial gap for all finite $0<p<q$ and $\alpha>0$.
[Result.lean](../D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Result.lean)
combines the two cases in `fails_off_contractive_range` and proves
`result : ¬ claim`, using $p=1$, $q=2$, $\alpha=1$ for the final
contradiction. No optimal norm formula is asserted.

## Triage

- PROVED (formalized): the estimate fails for every finite $p>0$, every $q\in(p,\infty]$, and every $\alpha>0$. The bounded holomorphic witnesses are the principal-branch powers $f_a(w)=(1+aw)^{2/p}$ at $z=a/(1+\alpha p)$. The exact circle mean satisfies $M_p(\rho,f_a)^p=1+a^2\rho^2$. The finite-q first-order gap is $D=r\alpha(q-p)/[(1+\alpha p)(1+\alpha q)]>0$, where $r=q/p$.
- PROVED (paper proof, not formalized here): Lemma 2 of the source gives constant one when $p=\infty$ or $0<q\le p<\infty$. Together with the formalized failure set, the constant-one estimate holds exactly when $p=\infty$ or $q\le p$.
- PROVED (formalized mechanism): the q-th power of normalized evaluation has first-order slope $r/(1+\alpha p)$, exceeding the radial mixed-norm upper comparison slope $r/(1+\alpha q)$ precisely for $q>p$; the slopes agree exactly at $q=p$.
- COMPUTED (`mpmath`, 30-digit arithmetic, outside the Lean development): violations occur at $(p,q,\alpha,a)=(1,2,0.5,0.2)$, $(0.7,1.9,1.3,0.15)$, $(2,4,0.25,0.25)$, and $(3,3.5,2,0.1)$. For $q=\infty$ they occur at $(p,\alpha,a)=(1,1,0.3)$, $(0.5,2,0.2)$, $(2,0.5,0.4)$, and $(3,0.3,0.3)$. There is no violation at the controls $(1.5,1.4,1,0.2)$ and $(1,1,1,0.2)$. These numerical checks are not part of the formal proof.
- OPEN: the exact norm of point evaluation on $H^{p,q,\alpha}$ for $q>p$. The source's upper constants and the lower bounds of Lemma 2 are not matched here.
- OPEN: the analogous sharp composition-operator norm bound derived from Lemma 2.

## ASSUMED-UNVERIFIED

Searches covered the arXiv API for Llinares, mixed norms with contractive
inequalities, point evaluation and pointwise estimates, and Dmitrović;
web results for mixed-norm point evaluation and sharp constants; the
repository's D5, Problems, Library and Blueprint collections; GitHub
code and discussion indexes; and Formal Conjectures entries for mixed
norms, Dmitrović and composition operators.
No settlement of the conjecture was found in that scope. Citation indexes
were not exhaustively checked; this is not a priority certification.

Llinares–Vukotić, *Contractive inequalities for mixed norm spaces and the
Beta function*, arXiv:2107.05542, characterizes inclusions
$H(p,q,a)\subset H(u,v,b)$ for $p\ge u$.
The present point-evaluation conjecture has $p<u=\infty$, outside that
range. The [Llinares–Vukotić note](../Library/AnalyticClosure/llinares2021contractive.md)
binds the arXiv locator; the [Dmitrović note](../Library/AnalyticClosure/dmitrovic2024norm.md)
binds the journal DOI and conjecture locator. The author's dissertation
reportedly restates the conjecture on printed page 55; that dissertation
statement is unverified and has no role in the proof. The literature
scope and paper's positive-range attribution are bibliographic evidence,
not additional Lean theorems.
