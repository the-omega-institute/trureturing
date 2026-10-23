---
bibkey: grafakosteschl2013radial
authors: Loukas Grafakos and Gerald Teschl
year: 2013
title: On Fourier transforms of radial functions and distributions
doi: 10.1007/s00041-012-9242-5
url: https://arxiv.org/abs/1112.5469v4
claim: The published radial Fourier dimension recurrence and distribution carrier realize the actual matched-source Laplace reciprocity as a nine-dimensional Fourier anti-eigenrelation. The original sixth moment suffices for this tempered-distribution realization, without an unweighted Hankel norm. Analytic uniqueness excludes every positive square-root-exponential source moment for a nonzero reciprocal source. For the selected matched global-null source, the owned Sobolev estimate and the published weighted Hankel theorem additionally supply every original physical moment below nine and the ordinary radial/Hankel L2 domain.
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


## The matched actual null enters the ordinary Hankel domain

This `repo-derived` application combines the
[owned MR11, JC13/JC23 and LR3/RF3 interfaces](../Weil/hernandezsantamaria2025optimal.md)
with [Airapetyan--Witt's weighted Hankel theorem](airapetyanwitt2001hankel.md),
Theorem 1(a),(d), and standard Sobolev localization and interpolation.
It keeps one original global-null source throughout. The published
mapping theorem is used directly; the additional work is its actual
source and Fourier-distribution correspondence. These are paper
estimates, without Lean/kernel certification or a literature-priority claim.

Suppose on the actual complex domain $\mathcal V$ that

$$
 Q_\lambda=\mathfrak E+\lambda(M_6-H)\ge0,
 \qquad Q_\lambda(F)=0,\qquad\lambda>0.                 \tag{HI1}
$$

The complete energy and every actual theta dilation and debit are
those of MR/JC/LR. For every fixed $0<s<3/2$, this SAME source satisfies

$$
 \boxed{M_{6+2s}(F)<\infty.}                            \tag{HI2}
$$

In particular $M_{17/2}(F)<\infty$, and all original physical moments
$M_k(F)$ with $k<9$ are finite. The following domain and parameter
checks supply the application; no weighted replacement is assumed null.

### Enter the published input space with the actual boundary factor

Write $T_F(z)=\tau_F(|z|)$ for RF3's original radial density and set

$$
 \begin{aligned}
 \varphi(\rho)&=\rho^{7/2}\tau_F(\rho),\qquad y=\log\rho,\quad t=2y,\\
 \tau_F(\rho)&=(\pi\rho^2)^{-7/2}(\rho^{12}-1)F(\pi\rho^2)
                  \mathbf1_{\rho>1}.
 \end{aligned}
$$

Keep JC's ORIGINAL full-line coordinate $X$, with
$X(t)=\pi^{9/4}e^{7t/2}F(\pi e^t)$ for $t\ge0$.
The exact input transport is

$$
 e^{-3y/2}\varphi(e^y)
 =\pi^{-23/4}(1-e^{-12y})\mathbf1_{y>0}X(2y).
                                                               \tag{HI3}
$$

JC23 gives $X\in H^s(\mathbb R)$ for every fixed $s<3/2$.
Multiplication by $(1-e^{-12y})\mathbf1_{y>0}$ is bounded on these
spaces by the existing JC13 metric-multiplier estimate and a fixed
change of scale. Its linear vanishing at zero pays the extension;
no zero trace of $X$ or $F$ is inserted. The supplier's equation (38)
therefore gives

$$
 \varphi\in\mathcal H^{s,2},\qquad
 \|\varphi\|_{\mathcal H^{s,2}}\le C_s\|X\|_{H^s}.
                                                               \tag{HI4}
$$

### Identify the continuous Hankel extension before using reciprocity

For the Fourier convention $e^{-2\pi iz\cdot\xi}$, the radial formula
in the inspected Grafakos--Teschl Section 2 is

$$
 \rho^{7/2}\widehat T_F(\rho)
 =2\pi(\mathsf H_{7/2}\varphi)(2\pi\rho).              \tag{HI5}
$$

Its continuous extension is identified without assuming ordinary
unweighted $L^2$. Indeed $\mathcal H^{s,2}\subset L^2(\rho^{-4}d\rho)$
for $s>0$, and the map from $\varphi$ to its radial density
$|z|^{-7/2}\varphi(|z|)$ is continuous into $\mathcal S'(\mathbb R^9)$.
After radial averaging of a Schwartz test, its pairing is a fixed
constant times

$$
 \int_0^\infty
 (\rho^{-2}\varphi(\rho))
 (\rho^{13/2}\psi_{\rm av}(\rho))\,d\rho.
$$

The second factor is in $L^2(d\rho)$ at both endpoints. Approximate
$\varphi$ by compact smooth inputs in $\mathcal H^{s,2}$ and use
Theorem 1's continuous mapping to pass HI5 to radial tests supported
away from radius zero. On the output side convergence in
$\mathcal H^{s-5/2,-3}$ implies distributional convergence on
$(0,\infty)$. No restriction of an arbitrary distribution to a ray,
unweighted Hankel inversion or pointwise oscillatory integral is used.

RF3's SAME-source equality $\widehat T_F=-T_F$ now gives

$$
 (\mathsf H_{7/2}\varphi)(\sigma)
 =-\frac1{2\pi}\varphi\!\left(\frac\sigma{2\pi}\right)
 \quad\text{in }\mathcal D'((0,\infty)).                \tag{HI6}
$$

The supplier parameters are $\nu=7/2$, $\delta=5/2$, within
$|\delta|<1+\nu=9/2$. Fixed positive dilation preserves each Mellin
Sobolev space. Applying Theorem 1(a) to HI4 and then HI6 yields

$$
 \varphi\in\mathcal H^{s-5/2,-3},\qquad
 \|\varphi\|_{\mathcal H^{s-5/2,-3}}
 \le C_s\|X\|_{H^s}.                                  \tag{HI7}
$$

### Combine the two norms of this same function

In logarithmic coordinates put

$$
 f(y)=e^{-3y/2}\varphi(e^y),\qquad
 g(y)=e^{7y/2}\varphi(e^y)=e^{5y}f(y).
$$

HI4 and HI7 say $f\in H^s$ and $g\in H^{s-5/2}$.
Use standard smooth localization on unit intervals $y\approx j$;
local multiplication by $e^{5(y-j)}$ has uniformly bounded derivatives
and inverse derivatives. Sobolev interpolation with $\theta=2s/5$
has order $(1-\theta)s+\theta(s-5/2)=0$. Hölder in the interval index,
with the usual square-sum localization of both positive and negative
Sobolev orders, gives on these ACTUAL profiles

$$
 \|e^{2sy}f\|_2
 \le C_s\|f\|_{H^s}^{1-2s/5}
          \|g\|_{H^{s-5/2}}^{2s/5}
 \le C_s\|X\|_{H^s}.                                  \tag{HI8}
$$

Thus $\varphi\in\mathcal H^{0,2-2s}$. The precise original-source
weight is

$$
 \begin{aligned}
 \|\varphi\|_{\mathcal H^{0,2-2s}}^2
 &=\int_0^\infty\rho^{3+4s}|\tau_F(\rho)|^2d\rho\\
 &=\frac1{2\pi^8}\int_\pi^\infty
       (x/\pi)^{6+2s}[1-(\pi/x)^6]^2|F(x)|^2dx.
 \end{aligned}                                                \tag{HI9}
$$

On $x\ge2\pi$ the bracket is bounded below by $1-2^{-6}$.
On $[\pi,2\pi]$ the existing $M_6$ pays the entire compact part.
Consequently

$$
 M_{6+2s}(F)\le C_s[M_6(F)+\|X\|_{H^s}^2].             \tag{HI10}
$$

For the $H$-normalized selected representative, JC23 retains the cost

$$
 M_{6+2s}(F)\le C_{s,\eta}K_F
 \left[1+\lambda^{-1}\Lambda_\lambda
                   e^{C_{s,\eta}\Lambda_\lambda}\right].       \tag{HI11}
$$

Its actual $K_F$ is finite and parameter dependent. No cap-four
substitution or uniform small-$\lambda$ estimate is made.

### Consume order five-fourths in the ordinary radial domain

At $s=5/4$, HI8 gives
$\varphi\in\mathcal H^{0,-1/2}=L^2(\rho\,d\rho)$.
Equivalently, with $u(x)=x^{-7/4}w(x)F(x)$,

$$
 u\in L^2(dx),\qquad
 \|T_F\|_{L^2(\mathbb R^9)}^2
 =\Gamma(9/2)^{-1}\|u\|_2^2<\infty.                    \tag{HI12}
$$

RF3 therefore belongs to the ordinary unitary Fourier domain, or the
normalized unitary Hankel domain of order $7/2$. The stronger moments
HI2 are compatible with LR5's exclusion of every positive
square-root-exponential moment. The endpoint $M_9$ is not supplied:
this input route stops at $s<3/2$, where the boundary multiplier's
derivative may have a jump. No boundary cancellation is asserted.

The joint improvement uses JC regularity and LR reciprocity of one
selected source. Reapplying VHN to its weighted replacement would
require a new null equation and is unnecessary here. The complete
Weil energy sign, exclusion of the matched negative branch, uniform
vanishing allowance, RH and strict Robin for every integer above
5040 remain unresolved.
