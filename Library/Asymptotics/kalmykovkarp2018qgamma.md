---
bibkey: kalmykovkarp2018qgamma
authors: S. I. Kalmykov and D. B. Karp
year: 2018
title: Inequalities for series in q-shifted factorials and q-gamma functions
doi: 10.1016/j.jmaa.2017.11.041
url: https://arxiv.org/abs/1702.03788
claim: "Conjecture 1 extends Theorem 3 from positive integral alpha to all positive real alpha, including the coefficient positivity assertion under its remaining parameter restrictions."
strata_touched:
  - D5/S3/Analytic/QGammaTuran/Result
  - D5/S3/Analytic/QGammaTuran/FunctionResult
license: citation-only
triage: anchor
---

# Reciprocal q-gamma Turanian coefficients

## Verified locator

DOI: 10.1016/j.jmaa.2017.11.041

Source: https://arxiv.org/abs/1702.03788

Pinned source: https://arxiv.org/abs/1702.03788v1. Journal publication:
*Journal of Mathematical Analysis and Applications* 460 (2018), 332–351.
The page numbers below are the printed pages of the arXiv version.

## Source statements

Conjecture 1, p. 12:

> All conclusions of Theorem 3 are valid for all α > 0, while conditions on other parameters remain intact. In particular, µ → g(µ; x) is log-concave for each fixed 0 < x < Rg.

Theorem 3, p. 11:

> For a real sequence {gₙ}ₙ≥₀ and fixed 0 < q < 1 define
>
> $g(\mu;x)=\displaystyle\sum_{n=0}^{\infty}\frac{g_nx^n}{\Gamma_q(\mu+n)}.$ (16)
>
> Suppose {gₙ}∞ₙ₌₀ is doubly positive. Then (16) has a positive radius of convergence Rg and the generalized Turánian
>
> $\Delta_g(\alpha,\beta;x)=g(\mu+\alpha;x)g(\mu+\beta;x)-g(\mu;x)g(\mu+\alpha+\beta;x)$
>
> is positive for 0 < x < Rg if α ∈ N, β > 0 and µ ≥ max(−β, −1). If, in addition, α ≤ β + 1, then Δg(α, β; x) has positive power series coefficients at all powers of x.

Definition (6), p. 4:

> The q-gamma function is defined by
>
> $\Gamma_q(z)=(1-q)^{1-z}\displaystyle\frac{(q;q)_\infty}{(q^z;q)_\infty}$ (6)
>
> for |q| < 1 and all complex z such that qᶻ⁺ᵏ ≠ 1 for k ∈ N₀.

The sequence definition on p. 3 reads:

> A sequence f : N₀ → R₊ is PF₂ (Pólya frequency sub two) or doubly positive if it is nontrivial, log-concave, fₖ² ≥ fₖ₋₁fₖ₊₁, k ∈ N, and has no internal zeros. The last claim means that fN = 0 implies either fN+i = 0 for all i ∈ N₀ or fN−i = 0 for i = 0, . . . , N.

## Mathematical correspondence

The reciprocal of (6), on real arguments and $0<q<1$, is

$$R_q(x)=\frac{\prod_{j\ge0}(1-q^{x+j})}
{\left(\prod_{j\ge0}(1-q^{j+1})\right)(1-q)^{1-x}}.$$

The numerator vanishes at $x\in-\mathbb N_0$, giving the reciprocal
extension by zero. This is the object `Result.rqgamma`. The existing
`D5.S3.Analytic.ReciprocalGammaTuran.Defs.AdmissibleSeq` expresses exactly
the printed sequence assumptions, including nonnegativity from the
codomain $\mathbb R_+$.

`Result.qturanCoeff` is the finite Cauchy coefficient of the Turanian.
`Result.claim` states the coefficient clause for real $\alpha,\beta>0$,
$\mu\ge\max(-\beta,-1)$ and $\alpha\le\beta+1$.
`Result.result` refutes that clause. The function clause is separately refuted by `FunctionResult.result`;
log-concavity restricted to nonnegative parameters $\mu$ remains **OPEN**.
The bounded literature scope and computational evidence are stated in
`Problems/kalmykov-karp-2018-qgamma-turanian-coefficients.md`.

## Function clause

`FunctionResult.qseries` is the infinite sum in (16), and
`FunctionResult.radius q µ g` is Mathlib's scalar-series radius of (16)
at the given $\mu$, with coefficients $g_nR_q(\mu+n)$. The claim
requires $0<x<R_g$ for this radius. On p. 12 the source specifies:

> Writing Rg > 0 for the radius of convergence in (16), we claim that the next conjecture is true.

For the unit sequence, put $y=x(1-q)$ and

$$H(a,y)=\sum_{n\ge0}y^n(aq^n;q)_\infty.$$

Then $g(s;x)=H(q^s,y)/((q;q)_\infty(1-q)^{1-s})$.
For $s\ge-1$ the terms after index zero are nonnegative and bounded by
a geometric sequence when $0\le y<1$. At the example, absolute
summability at $x=3/2$ proves $3/2\le R_g$, so
$0<93/100<3/2\le R_g$. All four shifted series also converge
absolutely at $x=93/100$.
The function clause quoted from Theorem 3 above imposes no
$\alpha\le\beta+1$ restriction. Its extension to positive real $\alpha$
is false at $q=(93/100)^{10}$, $g_n=1$, $\mu=-7/10$,
$\alpha=3/10$, $\beta=7/10$ and $x=93/100$.
The corresponding dossier is
`Problems/kalmykov-karp-2018-qgamma-turanian-function.md`.

As a consequence in prose of `FunctionResult.witness_negative`, at the
same $q,x$ and $g_n=1$ the function cannot be log-concave on an interval
containing $[-7/10,3/10]$. The two convex combinations
$-2/5=(7/10)(-7/10)+(3/10)(3/10)$ and
$0=(3/10)(-7/10)+(7/10)(3/10)$ have respective right-endpoint weights
$3/10$ and $7/10$. Log-concavity at both points would imply, after
multiplication, $g(-2/5;x)g(0;x)\ge g(-7/10;x)g(3/10;x)$,
contradicting the proved strict reverse inequality. The endpoint values
are strictly positive by the normalized lower bounds and positive
denominators. This consequence is not a separate Lean theorem.
Log-concavity restricted to nonnegative parameters $\mu$ remains **OPEN**.
