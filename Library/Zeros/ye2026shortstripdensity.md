---
bibkey: ye2026shortstripdensity
authors: Yangbo Ye
year: 2026
title: Zero density in short strips and short-interval bounds toward Hypothesis S
doi: null
url: https://arxiv.org/abs/2610.15989v2
claim: Theorem 1.2 supplies short-strip zeta density bounds. Using the cited seven-eighths zero-free input, Theorem 1.3 and Corollary 1.1 supply explicit frequency-dependent prime-power bounds, including square-root phases on intervals with exponent greater than 17/30; no FIB phase transport or signed Robin bound is supplied.
strata_touched: []
license: citation-only
triage: anchor
---

# Zero density in short strips and short-interval bounds toward Hypothesis S

The inspected source is [arXiv:2610.15989v2](https://arxiv.org/pdf/2610.15989v2),
revised 14 October 2026, with 26 printed pages and PDF SHA-256
`315819f42df41c3980ada66a171d7c2d257679c3f7100670ed298cb0bb2634f1`.
Theorem 1.2, printed p.2, Theorem 1.3 and Corollary 1.1, pp.4–5,
and their zeta application in §4, pp.17–20, were inspected. This is
a preprint source interface, without an independent audit of the
complete proofs, the cited analytic inputs or Lean verification.

## The zero-density input

Count zeros with multiplicity, with strict $\Re\rho>\sigma$ and
inclusive $T\le\Im\rho\le T+T^a$. For the Riemann zeta function,
Theorem 1.2 gives, for $T\ge3$, $2/3\le a\le1$ and $1/2\le\sigma<1$,

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

Fix $\varphi\in C_c^\infty((-1,1))$, $\alpha\ne0$,
$0<\beta\le1$, $1-\beta<\delta<1$ and $R>0$. The source defines

$$
S_\zeta(\alpha,\beta;K,L)
=
\sum_{n\ge1}\Lambda(n)e(\alpha n^\beta)
\,\varphi\!\left(\frac{n-K}{L}\right),
\qquad e(x)=e^{2\pi i x},
$$

For $u=\log m/\log K$, put

$$
\nu_m=\max\{\beta+\delta-1+u,\ 1-\delta,\ 2(\beta+u)/3\},
$$

$$
Q(x)=\begin{cases}
\dfrac78+\dfrac x4,&0\le x\le91/230,\\[3pt]
\dfrac7{10}+\dfrac{9x}{13},&91/230\le x\le169/300,\\[3pt]
2+3x-2\sqrt{3x},&169/300\le x\le3/4,\\[3pt]
\dfrac12+x,&x\ge3/4.
\end{cases}
$$

Theorem 1.3, equation (1.11), gives, uniformly for integers
$1\le m\le K^R$ as $K\to\infty$,

$$
S_\zeta(m\alpha,\beta;K,K^\delta)
\ll K^{Q(\nu_m)+\varepsilon}
       \min\{K^{\delta-1},m^{-1/2}K^{-\beta/2}\}.
\tag{YS1}
$$

The implied constant can depend on the fixed data and $\varepsilon$.
The exponent $Q(\nu_m)$ itself depends on $m$; the displayed
$m^{-1/2}$ factor alone is not the total frequency dependence.

For $0<\beta<13/20$, Corollary 1.1 gives a strict saving at $m=1$
whenever $\max\{17/30,1-\beta\}<\delta<1$. In particular the
square-root phase permits every $\delta>17/30$ below $1$.
Equation (1.14), printed p.5, gives the source's explicit uniform example

$$
S_\zeta(m\alpha,1/2;K,K^{3/5})
\ll K^{15/26+\varepsilon},\qquad 1\le m\le K^{1/10}.
\tag{YS2}
$$

Its saving over interval length is $3/130$ before the arbitrarily
small $\varepsilon$ loss. More generally, equations (1.12)–(1.13)
give a fixed $\omega(\beta,\delta)>0$ in the supplied saving range
and a bound $m^{1/2}K^{\delta-\omega+\varepsilon}$; a uniform strict
saving from that bound requires $m\le K^r$ with fixed $r<2\omega$.
Uniformity of (YS1) for a fixed $R$ does not imply a saving for every
frequency up to $K^R$.

## The zero-free premise and the role of localization

The proof of Theorem 1.3, printed p.17, explicitly uses the
[cited seven-eighths zero-free input](../Analytic/openai2026quasirh.md)
to truncate the real-part integral at $7/8$. Possible zeros on that
boundary remain in the weighted sum. Its use here is conditional on
that external input; this card does not certify its full proof or
compiled dependency and axiom closure. The short-strip density
Theorem 1.2 has its separate mean-value inputs and does not require
this truncation.

The source's comparison on printed p.19 uses the same zero-free
boundary in both arguments. At $\beta=1/2$, $\delta=3/5$, $m=1$,
the zero height is of order $K^{1/2}$ but the ordinate window has
length of order $K^{2/5}$. At real part $7/10$, the global density
input gives weighted exponent $68/65>1$, while localization gives
$127/130<1$. Keeping the short-strip window is therefore part of
the source's saving mechanism; replacing it by a full-height density
estimate does not preserve this calculation.

These statements directly reuse the source's theorem, corollary and
comparison, rather than supplying a new exponential-sum estimate.

## Boundary for FIB and Robin

The source does not use the project's five-window Zeckendorf address, the affine family $1+F_rg$, or the complete point value

$$
\frac{\sigma(N_*)}{N_*}.
$$

Its phase $e(\alpha n^\beta)$ is also not the golden-conjugate coordinate $\psi^r$ or a proven readout of the FIB recursive state. A usable transport would need, on the same actual source, a coefficient-preserving map from the FIB phase or divisor increments to this oscillatory sum, together with the smoothing and endpoint conditions. Nothing in Theorems 1.2--1.3 supplies that map.

In particular, the fixed $\alpha\ne0$ theorem gives no uniform
extension as $\alpha\to0$, so the unmodulated coefficients of the
[original signed Robin tail](../Arith/caveney2012sacaga.md#retain-the-original-oscillation-exponent-on-the-regular-ga1-source)
cannot be recovered by simply setting its oscillation to zero.
That tail also retains all prime powers, the infinite endpoint,
the actual selected integer and its full CA reserve.

The paper supplies the stated short-strip and oscillatory-sum bounds,
but no estimate for that complete signed tail or a transport from the
FIB source to it. A shorter admissible oscillatory interval does not
by itself pay the same-source Robin estimate or prove RH.
