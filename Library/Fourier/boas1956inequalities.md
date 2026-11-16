---
bibkey: boas1956inequalities
authors: R. P. Boas, Jr.
year: 1956
title: Inequalities for functions of exponential type
doi: 10.7146/math.scand.a-10453
url: https://journals.msp.org/mscand/article/download/2866/2865
claim: Equation (1.3), printed p.29, bounds a phase-weighted sum of conjugate-height evaluations of an entire function of exponential type bounded on the real axis; phase pi/2 gives the hyperbolic-sine difference bound.
strata_touched:
  - D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket
license: citation-only
triage: anchor
---

# Conjugate-height differences and a compact-support budget

The primary article is available through the [DOI](https://doi.org/10.7146/math.scand.a-10453)
and the [publisher PDF](https://journals.msp.org/mscand/article/download/2866/2865).
The inspected scan has four pages, printed pp.29–32. The relevant statement
is equation (1.3) on printed p.29.

Let $f$ be entire of exponential type $\tau$, with $|f(x)|\le M$ on the
real axis. The source allows complex-valued $f$; being real on the real
axis is not a hypothesis of (1.3). For real $x,y,\omega$, that equation is

$$
\left|f(x+iy)e^{-i\omega}+f(x-iy)e^{i\omega}\right|
\le 2M\sqrt{\cosh^2(\tau y)-\sin^2\omega}.
$$

Taking $\omega=\pi/2$ gives

$$
|f(x+iy)-f(x-iy)|\le 2M\sinh(\tau|y|).
$$

For the angular Fourier–Laplace convention
$F(z)=\int_{\mathbb R}e^{-izx}g(x)\,dx$, an integrable function supported
in $[-R,R]$ gives an entire transform of exponential type at most $R$ and
$\sup_{t\in\mathbb R}|F(t)|\le\|g\|_1$. This maps the published bound
to the compact-support interpolation budget without a $2\pi$ factor.

The [unit-support packet application](../../Blueprint/D5/S3/Weil/BurnolGram/UnitSupportBurnolPacket.md)
also uses evenness to retain the factor $\min(1,R|t|)$, derives the
finite-error and second-derivative bounds directly from the actual kernel,
and substitutes the signed orbit data. These are application calculations,
not new mathematical declarations or a claim of literature novelty.
Neither the published inequality nor the application supplies an off-line
zeta zero, uniform interpolation budgets or a complexity theorem.
