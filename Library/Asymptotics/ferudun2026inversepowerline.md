---
bibkey: ferudun2026inversepowerline
authors: Alper Ferudun
year: 2026
title: Equilibria of Inverse-Square Repulsion on the Line Are Arithmetic Progressions
doi: 10.48550/arXiv.2610.06944
url: https://arxiv.org/abs/2610.06944v1
claim: "Remark 5.3 asks whether the arithmetic-progression classification holds for every real exponent s > 2."
strata_touched:
  - D5/S3/StatisticalMechanics/InversePowerLineBasics
  - D5/S3/StatisticalMechanics/InversePowerLineConductance
  - D5/S3/StatisticalMechanics/InversePowerLineNetwork
  - D5/S3/StatisticalMechanics/InversePowerLinePowerPacking
  - D5/S3/StatisticalMechanics/InversePowerLineEquilibria
license: citation-only
triage: anchor
---

# Inverse-power line equilibria

## Verified locator

DOI: 10.48550/arXiv.2610.06944

Source: https://arxiv.org/abs/2610.06944v1

## Definition 1.1, page 2

> Let $s>1$. An $s$-equilibrium is a set $X\subset\mathbb R$ with at least
> two points that is locally finite (every bounded interval contains only
> finitely many points of $X$) and satisfies, for every $x\in X$,
> $$\sum_{y\in X\setminus\{x\}}|y-x|^{-s}<\infty,\tag{1}$$
> $$\sum_{y\in X\setminus\{x\}}\operatorname{sgn}(y-x)\,|y-x|^{-s}=0.\tag{2}$$

The following source sentence fixes unordered absolute convergence:

> Condition (1) says that the total force exerted on each particle from each
> side is finite. It makes the series in (2) absolutely convergent, so that
> (2) does not depend on an order of summation.

## Theorem 1.2, page 2

> Let $1<s\le2$, and let $X$ be an $s$-equilibrium, that is, a locally finite
> set $X\subset\mathbb R$ with at least two points, such that for every $x\in X$ the
> total force (1) from both sides is finite and the net force (2) is zero.
> Then $X=\{\alpha n+\beta:n\in\mathbb Z\}$ for some $\alpha>0$ and
> $\beta\in\mathbb R$. Equivalently, if $(a_n)_{n\in\mathbb Z}$ is the
> increasing enumeration of $X$ (Lemma 2.1), then $a_n=\alpha n+\beta$
> for all $n$. Conversely, every such set is an $s$-equilibrium.

## Lemma 2.3, page 3

> For integers $n\ne j$ put $D=|a_j-a_n|$ and $D'=|a_{j+1}-a_{n+1}|$, and let
> $$c(n,j)=\frac{D^{-s}-D'^{-s}}{D'-D}\quad\text{if }D\ne D',\qquad
> c(n,j)=sD^{-s-1}\quad\text{if }D=D'.$$

The Lean expression expands both distances and sets the diagonal to zero.

## Energy, page 4

> The energy of $f\colon V\to\mathbb R$ is
> $\mathcal E_c(f)=\frac12\sum_{x,y}c(x,y)(f(x)-f(y))^2\in[0,\infty]$.

The real-valued Lean `energy` uses `tsum`. Its applications establish
summability for the finitely supported functions in question. This expression
does not represent extended infinite energy for nonsummable series.

## Remark 5.3, page 8

> Lemmas 2.1 to 2.4 and the bound (14) hold for every $s>1$, with the same
> proofs. For $s>2$, however, the integral in (10) is of order $g_n^{2-s}$.
> Then the argument above controls $S_1$ only through
> $R^{-2}\sum_{n\in I}g_n^{3-s}$, which is large when many gaps are small.
> We make no claim for $s>2$; whether the conclusion of Theorem 1.2 holds
> there remains open.

The Lean predicate uses real points, finiteness of intersection with each
closed bounded interval, a subtype excluding the point of evaluation,
`Real.rpow`, magnitude `Summable` and signed `HasSum ... 0`. The progression
is the range of the affine map on all integers. The extension concerns all
real $s>2$ and imposes no global upper or lower bound on consecutive gaps.
Principal-value sums and variable particle strengths are outside this statement.

The source supplies the ordered enumeration, gap comparison, conductance
construction and reciprocal transform. The induced-sublevel capacity argument
is derived in the repository. It does not assert recurrence of the full network.

## Literature boundary

The screen and its unread fulltexts are specified in issue
[#27202](https://github.com/the-omega-institute/trureturing/issues/27202).
Completeness is ASSUMED-UNVERIFIED. The earlier Zenodo release,
DOI 10.5281/zenodo.23113437, includes an unclaimed restricted sketch and is
not treated as a proof of the all-exponent assertion.
