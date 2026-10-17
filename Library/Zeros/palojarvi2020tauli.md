---
bibkey: palojarvi2020tauli
authors: Neea Palojärvi
year: 2020
title: Explicit Zero-Free Regions and a tau-Li-type Criterion
doi: 10.51286/albjm/1608313766
url: https://arxiv.org/abs/1807.01506v3
claim: Theorem 2.1 bounds the real high-zero contribution to generalized Li coefficients; at tau equal to two it gives an unconditional polynomial supplier for the signed transfer back to classical Li coefficients.
strata_touched: []
license: citation-only
triage: anchor
---

# A published growth supplier at the noncritical parameter

Source locators refer to Neea Palojärvi,
[arXiv:1807.01506v3](https://arxiv.org/abs/1807.01506v3), version
29 April 2020, rather than an identification with an uninspected
publisher edition. The DOI records the publication metadata.

The definitions in the introduction, equations (1)--(2), use the
unnormalized coefficients

$$
\Lambda_n(\tau)=\lim_{T\to\infty}
\sum_{\substack{\rho\in Z(\zeta)\\|\Im\rho|\le T}}
\left[1-\left(\frac{\rho}{\rho-\tau}\right)^n\right].
$$

At $\tau=2$ the zero strip $0<\Re\rho<1$ implies
$|\rho/(\rho-2)|<1$. Every real zero contribution therefore belongs to
$[0,2]$; conjugation makes the complete coefficient real.

Theorem 2.1 assumes $\tau>1/e$, the stated zero-counting conditions,
and an integer $n\ge\max\{e,T_0/(e\tau)\}$. With $T(n)=ne\tau$, it
bounds the real contribution of $|\Im\rho|>T(n)$ by
$K_{F,1}(\tau)n\log n$, with a constant independent of $n$.
For $F=\zeta$, $\tau=2$, all nontrivial zeros are included, there is no
zero at $2$, and the classical Riemann--von Mangoldt count, including
both signs of the height, supplies the required counting assumptions.
In particular the low set has
$\mathcal N_\zeta(2en)=O(n\log n)$ elements. Applying the published
high-zero estimate and the bound $2$ to each low-zero contribution
therefore gives, after increasing a constant over the finite initial set,

$$
\boxed{0\le\Lambda_m(2)\le C\,m\log(m+1),\qquad m\ge1.}
\tag{PL1}
$$

This is a parameter application of Theorem 2.1, not a new zero-counting
or Li growth theorem. It supplies the convergent coefficient budget in
the [finite signed transfer](freitas2006li.md). It does not imply a
polynomial bound for $\Lambda_m(1)=\lambda_m$, the two critical
Fibonacci probes, or the original arithmetic middle.

The finite zero-free-region results of Theorems 3.1 and 3.3 retain their
own hypotheses and finite index ranges. They are not used here to infer
an estimate for every sufficiently large Fibonacci index. This source
application has no Lean certification or literature-priority claim.
