---
bibkey: ye2026shortstripdensity
authors: Yangbo Ye
year: 2026
title: Zero density in short strips and short-interval bounds toward Hypothesis S
doi: null
url: https://arxiv.org/abs/2610.15989v1
claim: Theorem 1.2 improves zeta zero-density exponents in short ordinate strips, and Theorem 1.3 gives power savings for smoothed prime-power sums with phase exp(2 pi i alpha n^beta); no FIB phase transport or pointwise Robin bound is supplied.
strata_touched: []
license: citation-only
triage: anchor
---

# Zero density in short strips and short-interval bounds toward Hypothesis S

The inspected source is [arXiv:2610.15989v1](https://arxiv.org/pdf/2610.15989v1), submitted 11 October 2026. It is a preprint; this card records its theorem interfaces and their limits for the FIB Robin program. No independent proof audit or Lean verification is claimed.

## The zero-density input

For the Riemann zeta function, Theorem 1.2 gives, for $2/3\le a\le1$ and $1/2\le\sigma<1$,

$$
N_\zeta(\sigma;T,T+T^a)
\ll_{a,\varepsilon}T^{aB(\sigma)+\varepsilon},
$$

with

$$
B(\sigma)=
\begin{cases}
\dfrac{3(1-\sigma)}{2-\sigma},&\frac12\le\sigma\le\frac7{10},\\[4pt]
\dfrac{15(1-\sigma)}{3+5\sigma},&\frac7{10}\le\sigma\le\frac45,\\[4pt]
\dfrac{3(1-\sigma)}{3\sigma-1},&\frac45\le\sigma\le\frac56,\\[4pt]
2(1-\sigma),&\frac56\le\sigma<1.
\end{cases}
$$

The middle branch improves the earlier Ye--Zhang exponent on $7/10<\sigma<4/5$; at $\sigma=3/4$ it changes the coefficient from $3/5$ to $5/9$. The case $a=1$ recovers the corresponding global density bound, while $a<1$ localizes it to short ordinate intervals.

## The oscillatory application

For a smooth compactly supported weight and fixed $\alpha\ne0$, $0<\beta\le1$, Theorem 1.3 defines

$$
S_\zeta(\alpha,\beta;K,L)
=
\sum_{n\ge1}\Lambda(n)e(\alpha n^\beta)
\,\varphi\!\left(\frac{n-K}{L}\right),
\qquad e(x)=e^{2\pi i x},
$$

and gives a power-saving bound in the range $L=K^\delta$ described by the paper. The estimate is uniform after replacing $\alpha$ by $m\alpha$ for $1\le m\le K^R$, with an explicit $m^{-1/2}$ cost. The smallest threshold in the zeta application is $\delta>2/3$, attained at $\beta=8/9$.

## Boundary for FIB and Robin

The source does not use the project's five-window Zeckendorf address, the affine family $1+F_rg$, or the complete point value

$$
\frac{\sigma(N_*)}{N_*}.
$$

Its phase $e(\alpha n^\beta)$ is also not the golden-conjugate coordinate $\psi^r$ or a proven readout of the FIB recursive state. A usable transport would need, on the same actual source, a coefficient-preserving map from the FIB phase or divisor increments to this oscillatory sum, together with the smoothing and endpoint conditions. Nothing in Theorems 1.2--1.3 supplies that map.

Consequently the paper is a new short-strip and oscillatory-sum supplier, but it does not bound the complete signed Robin residual, the prime-power correction at one $N_*$, or the FIB-to-Robin source fiber. It should not be substituted for the existing signed-tail estimates or counted as an RH route until those bridges are proved.
