---
bibkey: radziwill2012mollifying
authors: Maksym Radziwiłł
year: 2012
title: "Limitations to mollifying ζ(s)"
doi: null
url: https://arxiv.org/abs/1207.6583v1
claim: "Theorem 1 gives an unconditional positive lower bound for normalized dyadic critical-line mollifier error at fixed polynomial length; the actual Selberg polynomial satisfies its conditions at both active height scales, so a vanishing unweighted error is unavailable as a joint-term supplier."
strata_touched: []
license: citation-only
triage: anchor
---

# A lower bound for normalized mollifier error

The inspected author version is
[arXiv:1207.6583v1](https://arxiv.org/pdf/1207.6583v1), submitted
27 July 2012. Its 17-page PDF has SHA-256
`57b3135287f911a1f8ee9e9e96e8df03ae079704c5f29291a5afca2a2047d621`.
Equation (1) and Theorem 1, printed p.2, were also checked in the
[versioned HTML](https://arxiv.org/html/1207.6583v1). This note pins
that preprint; it makes no claim about a later journal version and
supplies no Lean verification.

## The source's exact contract

Fix $\theta>0$. Let
$$
M_T(s)=\sum_{n\le T^\theta}a_T(n)n^{-s},\qquad
 a_T(1)=1,\qquad a_T(n)\ll_\varepsilon n^\varepsilon.
$$
For such polynomial families, Theorem 1 gives an absolute $c>0$ and,
for sufficiently large $T$,
$$
\frac1T\int_T^{2T}
 |1-\zeta(1/2+it)M_T(1/2+it)|^2\,dt\ge c/\theta.
\tag{RL1}
$$
The exponent $\theta$ is fixed; this note does not assume uniform
starting thresholds when it varies. The coefficient condition is
uniform in the family. No RH, simple-zero or inverse-$\zeta'$
moment condition is assumed in Theorem 1. Theorems 2--3 impose RH
and additional conditions to obtain stronger lower bounds; they are
not used for (RL1).

## Exact maps for the original Selberg polynomial

The [actual residual application](corvalan2023interpolation.md)
uses
$$
V_N(s)=\sum_{n\le N}\mu(n)
 \left(1-\frac{\log n}{\log N}\right)n^{-s}.
$$
Its first coefficient equals one and every coefficient has absolute
value at most one, so it meets the source's uniform growth condition.
At $T=\sqrt N$, take $\theta=2$, giving directly
$$
\frac1{\sqrt N}\int_{\sqrt N}^{2\sqrt N}
 |1-\zeta(1/2+it)V_N(1/2+it)|^2\,dt\ge c/2.
\tag{RL2}
$$
This is the height scale of the residual smoothing
$\nu=N^{-1/2}$ in (I84)--(I86), rather than the much larger contour
height $T_N\asymp N^4$ used only to pay horizontal edges.

For the smooth-frequency height in (I82),
$T\asymp(\log N)^2/h$ with
$h\asymp N^{-1/4}e^{\lambda\Omega}$, one has
$\log N/\log T\to4$. Choose the fixed exponent $\theta=5$ and
pad the coefficient list by zero for $N<n\le T^5$.
Eventually $N\le T^5$, so (RL1) yields
$$
\frac1T\int_T^{2T}
 |1-\zeta(1/2+it)V_N(1/2+it)|^2\,dt\ge c/5.
\tag{RL3}
$$
This avoids substituting a varying exponent into a fixed-parameter
theorem. Padding changes neither the actual polynomial nor its
first coefficient.

## What this excludes and what it leaves open

Equations (RL2)--(RL3) exclude a supplier requiring these unweighted,
normalized dyadic mean-square errors to tend to zero. They do not
supply an upper bound or sign for the project's jointly signed
functional, whose arithmetic coefficients and weights differ.

After restoring the Nyman--Beurling weight $(1/4+t^2)^{-1}$, the
corresponding window lower bound furnished by (RL1) is only of order
$1/T$, which tends to zero. Thus (RL1) is compatible with the full
weighted norm tending to zero. A positive mean-square lower bound
also remains compatible with a particular signed interaction tending
to zero. Neither a contradiction to RH nor a noncancellation theorem
for the project's full residue sum follows from this source.
