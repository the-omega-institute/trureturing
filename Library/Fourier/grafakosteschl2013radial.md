---
bibkey: grafakosteschl2013radial
authors: Loukas Grafakos and Gerald Teschl
year: 2013
title: On Fourier transforms of radial functions and distributions
doi: 10.1007/s00041-012-9242-5
url: https://arxiv.org/abs/1112.5469v4
claim: The published radial Fourier dimension recurrence and distribution carrier realize the actual matched-source Laplace reciprocity as a nine-dimensional Fourier anti-eigenrelation. The original sixth moment suffices for this tempered-distribution realization, without an unweighted Hankel norm. Analytic uniqueness excludes every positive square-root-exponential source moment for a nonzero reciprocal source.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Radial Fourier suppliers and the actual weighted source

The inspected primary is [arXiv:1112.5469v4](https://arxiv.org/pdf/1112.5469v4),
*J. Fourier Anal. Appl.* 19 (2013), 167--179,
[DOI:10.1007/s00041-012-9242-5](https://doi.org/10.1007/s00041-012-9242-5).
Its 12-page author PDF has SHA-256
`35ab79d8223c1786b0fb4129bf89fcb7c6d9e403370befa1e7a91d54ace9e0a8`.
Theorem 1.1, formula (1), gives, with Fourier kernel $e^{-2\pi iz\cdot\xi}$,

$$
\mathcal F_{n+2}(f)(r)=-\frac1{2\pi r}\frac d{dr}
\mathcal F_n(f)(r).
$$

It assumes integrability of the same radial profile in dimensions
$n$ and $n+2$; Schwartz profiles meet these conditions. Section 2 gives
the radial Fourier--Bessel normalization. Proposition 3.2 says a radial
tempered distribution is determined by radial Schwartz tests. Section 4
and Remark 4.2 supply its distributional Hankel realization at half-integer
order. These are `literature-attested` suppliers, not new transform theorems.

The other inspected primary is Laurent Schwartz,
[*Rappels divers*, Séminaire Schwartz 3, exposé 2](https://www.numdam.org/item/SLS_1955-1956__3__A2_0.pdf),
section 4, Proposition 1, printed p.2-04. It gives Laplace holomorphy
and uniqueness for distributions with nonnegative support and an
exponentially tempered bound. The seven-page scan includes its cover;
the article itself has six pages. Only these classical supplier results
are used below. The following source correspondence is `repo-derived`
paper mathematics, without Lean certification or a priority claim.

## The actual weighted source in nine dimensions

Keep the [actual source domain](../Weil/suzuki2026screw.md), with
$M(F)=\int_\pi^\infty(x/\pi)^6|F|^2dx<\infty$.
Put $w(x)=(x/\pi)^6-1$, $v=wF$, extended by zero below $\pi$, and
$L_F(s)=\int_\pi^\infty v(x)e^{-sx}dx$ for $\Re s>0$.
Define the radial density on $\mathbb R^9$ by

$$
T_F(z)=(\pi|z|^2)^{-7/2}v(\pi|z|^2),\qquad
T_F=0\quad(|z|\le1).
$$

Polar coordinates, with $x=\pi r^2$, give radial volume
$x^{7/2}dx/\Gamma(9/2)$ and the exact identity

$$
\int_{\mathbb R^9}|T_F(z)|^2|z|^{-5}dz
=\frac{\pi^{5/2}}{\Gamma(9/2)}
 \int_\pi^\infty x^{-6}|v(x)|^2dx
\le\frac{\pi^{-7/2}}{\Gamma(9/2)}M(F).             \tag{RF1}
$$

This makes $T_F$ locally square integrable and tempered: pairing with a
Schwartz test is bounded by the left-hand square-root norm times
$\||z|^{5/2}\phi\|_2$. It does not put $T_F$ in ordinary $L^2$.

For $G_s(z)=e^{-\pi s|z|^2}$, $\Re s>0$, the same coordinates and
the classical Gaussian Fourier formula give

$$
\langle T_F,G_s\rangle=\frac{L_F(s)}{\Gamma(9/2)},
\qquad \mathcal F_9G_s=s^{-9/2}G_{1/s}.             \tag{RF2}
$$

Consequently the exact correspondence is

$$
\boxed{L_F(s)=-s^{-9/2}L_F(1/s)\quad(\Re s>0)
\iff \mathcal F_9T_F=-T_F\text{ in }\mathcal S'(\mathbb R^9).}
                                                               \tag{RF3}
$$

To pay the forward implication, $U=\mathcal F_9T_F+T_F$ annihilates
every $G_s$ by RF2. Push this radial tempered distribution forward by
$p(z)=\pi|z|^2$: the continuous map
$\phi\mapsto\phi\circ p$ on Schwartz spaces defines $p_*U$ with
support in $[0,\infty)$. Define its Laplace pairing using
$\chi(t)e^{-st}$, with $\chi=1$ on $[-1/2,\infty)$ and zero
for $t\le-1$; this is a Schwartz test and its composition with $p$
is $G_s$. Its Laplace transform is zero, so the cited uniqueness gives
$p_*U=0$. This pushforward is injective on radial
distributions. Indeed every radial Schwartz test is
$\phi(\pi|z|^2)$: smoothness at the origin gives a smooth profile in
$r^2$, its derivatives decay rapidly at infinity, and that half-line
profile has a Schwartz extension to the real line. Proposition 3.2
then gives $U=0$. The reverse implication is immediate from RF2.

On ordinary integrable inputs, Section 2 identifies the scalar kernel,
for $u(x)=x^{-7/4}v(x)$, as
$\int_0^\infty J_{7/2}(2\sqrt{xy})u(y)dy$.
Thus the Bessel order is $9/2-1=7/2$. For present general inputs the
assertion RF3 remains on the radial distribution carrier; no pointwise
oscillatory integral or multiplication of an arbitrary distribution by
a fractional power at the origin is assumed. An unweighted $L^2(dx)$
norm of $u$ would require
$\int x^{-7/2}w(x)^2|F(x)|^2dx<\infty$, whose tail weight is
$x^{17/2}$. RF1 pays RF3 without claiming this stronger moment or
boundedness of a Hankel transform in the original weighted norm.

## Analytic uniqueness restricts the original physical tail

Suppose a nonzero source satisfying RF3 had
$\int_\pi^\infty e^{2\varepsilon\sqrt{x}}|F(x)|^2dx<\infty$
for some $\varepsilon>0$. For $0<a<\varepsilon\sqrt\pi$,

$$
\int_{\mathbb R^9}|T_F(z)|e^{a|z|}dz
=\Gamma(9/2)^{-1}\int_\pi^\infty
w(x)|F(x)|e^{a\sqrt{x/\pi}}dx<\infty.             \tag{RF4}
$$

Cauchy--Schwarz proves the last bound: its remaining factor is a
polynomial times $e^{-2(\varepsilon-a/\sqrt\pi)\sqrt{x}}$.
Classical Fourier analytic continuation therefore makes
$\mathcal F_9T_F$ holomorphic on the connected tube
$|\Im\xi|<a/(2\pi)$. RF3 makes it zero on the open real unit ball.
Real-analytic uniqueness and Fourier injectivity force $F=0$, a
contradiction. Thus every nonzero reciprocal actual source lacks every
positive square-root-exponential $L^2$ moment.

This is an application of analytic uniqueness, not a new uncertainty
principle. The [common-gap source adaptation](../Weil/burnol2002sonine.md#nonzero-actual-sources-with-the-matched-laplace-reciprocity)
shows RF3 has nonzero actual sources. Their complete Weil energy sign
and the exclusion of the selected matched negative branch remain
undetermined. No RH or all-integer Robin proof follows from RF3.
