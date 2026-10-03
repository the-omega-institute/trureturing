---
bibkey: trudgian2014pnt
authors: Tim Trudgian
year: 2014
title: Updating the error term in the prime number theorem
doi: null
url: https://arxiv.org/abs/1401.2689v2
claim: The unconditional all-prime-power Chebyshev error bound gives an explicit exterior deficit modulus for the original theta prime diagonal, in terms of two unevaluated theta constants. It supplies no signed discrepancy or spectral exclusion.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# An explicit exterior modulus for the original prime diagonal

## Source and preserved arithmetic quantity

The inspected source is [arXiv:1401.2689v2](https://arxiv.org/pdf/1401.2689v2),
13 pages, arXiv stamp 17 October 2014 and title-page date 20 October 2014,
SHA-256
`72594a54fe04ad73eb1e142e0365d4b3d7e576de2fad234dc2eff5b5e5ea8d79`.
The following locator refers to that preprint; a journal edition is not
claimed inspected.

Theorem 1, printed p.3, states unconditionally

$$
|\Psi(y)-y|\le y b(\log y)\quad(y\ge23),\qquad
b(t)=\sqrt{\frac8{17\pi}}
       \left(\frac{t}{6.455}\right)^{1/4}
       \exp\left(-\sqrt{\frac{t}{6.455}}\right),
$$

where $\Psi(y)=\sum_{n\le y}\Lambda(n)$ includes all prime powers.
Its separate estimate for $\theta(y)$ starts at $149$ and is not used here.
The proof's finite verified zero range is not a global RH premise.
This PNT theorem is reused, rather than proved anew.

## Exact Abel and continuum comparison

Retain the original positive even theta kernel, its normalization
$\int\Phi(u)\cosh(u/2)\,du=1/2$, and the complete prime diagonal
$a_p$ from the [mixed spectral realization](lenz2010compactness.md).
Write $d(x)=2\cosh(x/2)$, $E(y)=\Psi(y)-y$ and

$$
\begin{aligned}
F_x(y)&=y^{-1/2}\bigl(\Phi(x+\log y)+\Phi(x-\log y)\bigr),\\
a_p(x)&=\frac1{d(x)}\int_{(1,\infty)}F_x(y)\,d\Psi(y),\\
a_0(x)&=\frac1{d(x)}\int_1^\infty F_x(y)\,dy.
\end{aligned}
$$

Abel integration gives

$$
a_p(x)-a_0(x)
=\frac{2\Phi(x)-\int_1^\infty E(y)F_x'(y)\,dy}{d(x)}, \tag{AB}
$$

with

$$
F_x'(y)=y^{-3/2}\left[
-\frac{\Phi(x+\log y)+\Phi(x-\log y)}2
+\Phi'(x+\log y)-\Phi'(x-\log y)\right].
$$

The endpoint is positive because $E(1)=-1$ and $F_x(1)=2\Phi(x)$.
The upper boundary vanishes by the original theta tail and the linear-size
PNT bound. No prime power or crossing interaction is removed.
The change $y=e^t$ also gives

$$
a_0(x)=\frac1{d(x)}\int\Phi(u)e^{|x-u|/2}\,du.
$$

Evenness and the normalization yield

$$
\frac12-a_0(x)
=\frac1{d(x)}\int\Phi(u)e^{-|x-u|/2}\,du,
\qquad 0<\frac12-a_0(x)\le e^{-|x|}. \tag{CT}
$$

For the identity, add the two exponentials and integrate
$2\cosh((x-u)/2)$. For the bound at $x\ge0$, use
$e^{-|x-u|/2}\le e^{-x/2}e^{u/2}$,
$\int\Phi e^{u/2}=1/2$ and $d(x)\ge e^{x/2}$; evenness handles $x<0$.
The displayed bound is deliberately loose. The comparison $a_0$ imposes
no favorable sign on $a_p-1/2$.

## An explicit deficit bound with the same theta constants

Define

$$
H(u)=\tfrac12\Phi(u)+|\Phi'(u)|,\qquad
H_\infty=\sup H,\qquad M_H=\int H(u)e^{u/2}\,du.
$$

The original theta and derivative tails make both constants finite;
$H$ is even. No certified numerical values are supplied here.
Let $B_0=1+\log23$. Below $23$, $\Lambda(n)\le\log n$ gives
$|E(y)|/y\le B_0$ for $1\le y<23$. Above $23$, $b(\log y)\le1<B_0$.
Indeed, writing $X=\sqrt{t/6.455}$ gives
$\sqrt X e^{-X}\le1$. Also
$b'(t)/b(t)=1/(4t)-1/(2\sqrt{6.455t})$, so $b$ decreases for
$t\ge\log23$.

After $y=e^t$, the absolute error integral in (AB), divided by $d(x)$,
is at most

$$
\frac1{d(x)}\int_0^\infty e^{t/2}
\frac{|E(e^t)|}{e^t}\bigl(H(x+t)+H(x-t)\bigr)\,dt.
$$

For $x\ge R\ge2\log23$, split at $t=x/2$. The short part is at most
$4B_0H_\infty e^{-x/4}$. On the long part use $b(t)\le b(x/2)$ and

$$
\begin{aligned}
\int_0^\infty e^{t/2}\bigl(H(x+t)+H(x-t)\bigr)\,dt
&=\int H(u)e^{|x-u|/2}\,du\\
&\le\int H(u)\bigl(e^{(x-u)/2}+e^{(u-x)/2}\bigr)\,du\\
&=d(x)M_H.
\end{aligned}
$$

Discard only the favorable positive endpoint in (AB) and use (CT).
All right-hand terms decrease in the stated range, giving

$$
\boxed{
\delta_R:=\sup_{|x|\ge R}(\tfrac12-a_p(x))_+
\le e^{-R}+4B_0H_\infty e^{-R/4}+M_H b(R/2),
\quad R\ge2\log23.
} \tag{PM}
$$

This supplies the exterior-deficit input to the existing
[fixed-gap eigenfunction tail estimates](lenz2010compactness.md).
Certified upper values of $H_\infty,M_H$ remain necessary for a numerical
radius satisfying $\delta_R\le\varepsilon/2$. The full $B_p$ tail input,
interior discretization and complete spectral exclusion remain separate.
The bound supplies no favorable signed discrepancy, uniform
$\varepsilon\to0$ exclusion, numerical Poincare constant or RH/Robin proof.

Trudgian supplies the PNT theorem. The Abel identity, continuum comparison
and deficit modulus are paper-level model transfers, independently
reviewed, without new Lean certification or an originality claim.
