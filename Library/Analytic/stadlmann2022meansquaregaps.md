---
bibkey: stadlmann2022meansquaregaps
authors: Julia Stadlmann
year: 2022
title: On the mean square gap between primes
doi: null
url: https://arxiv.org/abs/2212.10867v1
claim: Theorem 1 gives an unconditional prime-gap square sum. Its application bounds actual CA price-residence lengths and count-to-price transport, without controlling the signed Robin excess.
strata_touched: []
license: citation-only
triage: anchor
---

# Prime-gap moments and actual CA residence lengths

Julia Stadlmann, *On the mean square gap between primes*,
[arXiv:2212.10867v1](https://arxiv.org/abs/2212.10867v1),
Theorem 1, PDF p.1, states unconditionally that, for every fixed
$\epsilon>0$,

$$
\sum_{p_n\le x}(p_{n+1}-p_n)^2
\ll_\epsilon x^{123/100+\epsilon}.
\tag{R1}
$$

The versioned [HTML](https://arxiv.org/html/2212.10867v1) and
[PDF](https://arxiv.org/pdf/2212.10867v1) supply the primary statement.
This note uses that theorem without re-proving or independently
auditing its proof, and makes no claim that its exponent is the best
available in all later literature. The following is an application
to the project's existing actual CA path, not a theorem stated by
Stadlmann, an originality claim, or Lean certification.

## Transport the existing gap moment to the actual price clock

Use the [existing full CA optimizer](../Arith/caveney2012sacaga.md#transport-one-selected-source-into-an-actual-ca-price-interval)
$C_b$ at $g(b)=1/(b\log b)$, choosing the largest optimizer and
retaining all activation ties and repeated prime-power layers.
Put $B(b)=\log C_b$; it is generally not $b$. No regularity or
GA1 condition is imposed on subsequent states.

The [existing first-layer activation rule](mantovanelli2026primeworkload.md)
places the event for prime $p$ at the unique $\tau(p)>1$ with

$$
g(\tau(p))=\frac{\log(1+1/p)}{\log p}.
$$

The already used bounds $1/(p+1)<\log(1+1/p)<1/p$, together
with decreasing $g$, give $p<\tau(p)<p+1$. Consequently the
first-layer parent cell has length

$$
\tau(p_{n+1})-\tau(p_n)
\le p_{n+1}-p_n+1\le2(p_{n+1}-p_n).
$$

For sufficiently large $X$, let $J_j$ be the complete
positive-length intervals on which $C_b$ is constant and whose intersection with $[X,3X]$ has
positive length. Write $\ell_j=|J_j|$ for their full lengths,
including any portion outside that observation interval.
Every $J_j$ lies in one first-layer parent cell. All higher
layers merely subdivide that cell; simultaneous ties add no
positive-length interval. Within each parent cell, the sum of
the squared lengths of any subcollection is at most the square
of the parent's length. Every relevant parent's left event is
at most $3X$, hence its left prime is less than $3X$.
Applying (R1) at $3X$ therefore gives

$$
\boxed{\sum_j\ell_j^2\ll_\epsilon X^{123/100+\epsilon}.}
\tag{R2}
$$

The original theorem includes the gap whose left prime is below
the cutoff even if its right prime is above it. Thus (R2) pays
both boundary-straddling cells without dropping any full length.
Endpoint conventions have zero price measure.

For any collection $\mathcal J$ of $K$ such plateaus, Cauchy's
inequality gives the actual-price measure bound

$$
\boxed{\left|[X,3X]\cap\bigcup_{j\in\mathcal J}J_j\right|
\ll_\epsilon X^{123/200+\epsilon/2}\sqrt K.}
\tag{R3}
$$

The collection may depend on the actual prime data; no independence
assumption is made. Likewise the price measure occupied by full
plateaus longer than $\sqrt X$ satisfies

$$
\left|\{b\in[X,3X]:|J(b)|>\sqrt X\}\right|
\ll_\epsilon X^{73/100+\epsilon}.
\tag{R4}
$$

Indeed, each such length obeys $\ell_j\le\ell_j^2/\sqrt X$.
Choosing the theorem's free parameter $\epsilon=1/100$ gives
$O(X^{74/100})$, smaller than
$X^{1-\eta'/2}\sqrt{\log X}$ for each fixed
$0<\eta'<1/2$. This does not discard those plateaus from a signed
mean: their excess amplitudes would still need a bound.

## The remaining count must retain the Robin sign

Use the particular fixed $\eta'\in(0,1/2)$, $c>0$ and
$\delta=c/(4\,2^{\eta'})$ from the
[existing selected-source persistence application](../Arith/caveney2012sacaga.md#a-wider-actual-price-interval-for-the-same-supplied-power-excess).
Let $K_{\eta',\delta}(X)$ count the plateaus above for which
$\log G(C_b)-\gamma>\delta X^{-\eta'}$.
The quantity is constant on each plateau. An actual selected
source with $A=\log N\in[X,2X]$ supplies an interval within
$[X,3X]$ of length at least

$$
\lambda X^{1-\eta'/2}
\exp\!\left(\frac{(\log X)^{1/4}}2\right)
$$

entirely above that threshold. Combining its length with (R3)
forces, on any such scale,

$$
K_{\eta',\delta}(X)
\gg_{\epsilon,\lambda}
X^{77/100-\eta'-\epsilon}
\exp\!\left((\log X)^{1/4}\right).
\tag{R5}
$$

The sufficient arithmetic count bound would therefore be
$o\!\left(X^{77/100-\eta'-\epsilon}
 e^{(\log X)^{1/4}}\right)$ for any one fixed
$0<\epsilon<27/100$. No such sign-sensitive count or directed mean
bound is supplied. The unconditional input (R2) controls
residence lengths; the existing persistence supplies amplitude
only when a selected excess source already exists. Neither
controls how often actual CA states exceed the threshold.
The complete original Robin tail and RH remain unproved.
