---
bibkey: hernandezsantamaria2025optimal
authors: Víctor Hernández-Santamaría, Luis Fernando López Ríos, and Alberto Saldaña
year: 2025
title: Optimal boundary regularity and a Hopf-type lemma for Dirichlet problems involving the logarithmic Laplacian
doi: 10.3934/dcds.2024084
url: https://arxiv.org/abs/2401.18033v2
claim: The published boundary theorem requires an exterior-zero equation with bounded solution and forcing. Actual cap-four features can have uniformly bounded logarithmic Fourier moments of every fixed order while their profile values at zero diverge. Smooth actual sources also give opposite unbounded full-prime dilation difference quotients with controlled origin data. These paper-level interface counterexamples supply neither a negative minimizer nor an RH or Robin bound.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Actual-source interfaces for boundary values and arithmetic dilation

## What the published theorems provide

The journal locator is [DOI:10.3934/dcds.2024084](https://doi.org/10.3934/dcds.2024084),
*Discrete and Continuous Dynamical Systems* 45 (2025), 1--36.
The inspected primary is [arXiv:2401.18033v2](https://arxiv.org/abs/2401.18033v2),
version 3 July 2024, [PDF](https://arxiv.org/pdf/2401.18033v2).
Theorem 1.1, printed p.2, assumes a bounded open domain with a uniform
exterior sphere condition and a weak solution

$$
L_\Delta u=f\quad\text{in }\Omega,\qquad
u=0\quad\text{on }\mathbb R^N\setminus\Omega,
\qquad
u\in\mathcal H(\Omega)\cap L^\infty,\quad f\in L^\infty(\Omega).
$$

Here $L_\Delta$ has symbol $2\log|\xi|$. With
$\ell(r)=|\log\min(r,0.1)|^{-1}$, its conclusion is
$|u(x)|\le C\ell(\operatorname{dist}(x,\partial\Omega))^{1/2}$.
Theorem 1.2, pp.2--3, establishes optimality on small-ball torsion
solutions. Theorem 1.4, p.4, is a Hopf lemma with an additional
nonnegative supersolution assumption. These are `literature-attested`
results, not statements about the actual Weil source operator.

The predecessor [Chen--Weth primary](https://arxiv.org/pdf/1710.03416v6),
Theorem 1.11, printed p.5, has the same bounded-solution and bounded-forcing
requirements and gives every boundary exponent $\tau<1/2$.
Its underlying Dirichlet framework is for bounded domains; the proof
of its restatement, Theorem 5.4, uses that boundedness on printed p.29.
Neither result is a theorem for an arbitrary nonnegative form with a
comparable logarithmic multiplier.

The related preprint [arXiv:2411.15985v2](https://arxiv.org/abs/2411.15985v2),
*Nonlocal elliptic equations involving logarithmic Laplacian: Existence,
non-existence and uniqueness results*, is explicitly withdrawn by its
authors, citing "a crucial error in Proof of Pohozaev identity".
Its claimed Pohozaev identity is therefore not used as a proved supplier
here. This withdrawal does not decide the actual minimizing-source estimate.

## Keep the actual two profiles distinct

Use the [owned actual physical source and complete form](suzuki2026screw.md),
W317, W331 and W338. On $H=L^2([\pi,\infty),dx)$ put

$$
M(F)=\int_\pi^\infty(x/\pi)^6|F(x)|^2dx,\qquad
(\mathscr TF)(x)=\sum_{n\ge1}n^4F(n^2x),
$$

$$
(BU)(x)=U(x)-\frac3{2x}\int_x^\infty U(y)dy.
$$

The zero-extended Gamma profile and the even arithmetic profile are

$$
u_F(t)=(\pi e^t)^{9/4}\mathscr TF(\pi e^t)\,\mathbf1_{t\ge0},
\qquad
g_F(r)=(\pi e^{2|r|})^{9/4}B\mathscr TF(\pi e^{2|r|}).
\tag{LB1}
$$

The complete form is $\mathfrak E=\mathcal P-\mathfrak J$, where
$\mathcal P(F)=\int p(\xi)|\widehat u_F(\xi)|^2d\xi$ and
$p(\xi)\asymp1+\log(2+|\xi|)$; its domain is
$\mathcal V=\{F:M(F)+\mathcal P(F)<\infty\}$.
Write $\mathcal L_k(g)=\int[\log(2+|\tau|)]^k|\widehat g(\tau)|^2d\tau$.

The [actual minimizer bootstrap](platttrudgian2021rh.md#bootstrap-the-actual-minimizing-source-before-paying-its-moment-loss)
already provides its stated logarithmic bounds and branch estimates.
Those estimates are reused. The following source-specific application
shows why bounds on $M$ and $\mathcal L_k$ alone cannot supply an
additional bounded-value or continuous-trace assumption. It is
`repo-derived` paper analysis, without Lean certification or a claim
to literature priority.

## A logarithmic cusp is inside the actual cap-four domain

Fix $a>0$ small enough that $\pi e^a<\pi+1/8$. Choose a nonnegative
smooth cutoff $\chi$ on $[0,\infty)$, equal to one near zero and zero
for $t\ge a$. Set, up to values at the single point zero,

$$
u(t)=\mathbf1_{t>0}\chi(t)\log(1/t),\qquad
F(x)=x^{-9/4}u(\log(x/\pi))\quad(x>\pi).
\tag{LB2}
$$

The cutoff may be chosen with $a<1$, so $F$ is nonzero and nonnegative.
Since its physical support is below $4\pi$, every $n\ge2$ term of
$\mathscr TF(x)$ vanishes for $x\ge\pi$. Thus
$\mathscr TF=F$ exactly, and $u_F=u$.
The normalized feature $\widetilde F=F/\|F\|_H$ has

$$
\|\widetilde F\|_H=1,\qquad
M(\widetilde F)\le\left(1+\frac1{8\pi}\right)^6<4.
\tag{LB3}
$$

For $R=|\xi|\ge2$, split the Fourier integral of $u$ at $1/R$.
The first piece is at most $CR^{-1}\log R$. Integrate by parts on
the rest; its endpoint value and the integral of $|u'|$ on
$[1/R,a]$ are at most $C\log R$. Hence

$$
|\widehat u(\xi)|\le
\frac{C\log(2+|\xi|)}{1+|\xi|},\qquad
u\in H^s(\mathbb R)\quad(0<s<1/2).
\tag{LB4}
$$

In particular $\mathcal P(F)<\infty$, so this is an actual feature
in $\mathcal V$, not a freely assigned boundary profile.
Changing variables in the ACTUAL $B$ integral gives, for $t\ge0$,

$$
b(t):=g_F(t/2)
=u(t)-\frac32\int_0^\infty e^{-5v/4}u(t+v)dv.
\tag{LB5}
$$

The integral term is uniformly bounded by Cauchy--Schwarz. Therefore
$b(t)=\log(1/t)+O(1)$ as $t\downarrow0$: the completed arithmetic
profile is unbounded and has no finite continuous trace at zero.
The right-convolution in (LB5) is bounded on $H^s(\mathbb R)$ by
its integrable kernel. Restriction to the half-line followed by even
reflection is bounded on $H^s$ for, in particular, $s=1/4$.
These standard Sobolev operations give $g_F\in H^{1/4}(\mathbb R)$,
and thus $\mathcal L_k(g_F)<\infty$ for every fixed finite $k$.
No Sobolev embedding into $L^\infty$ is asserted at this exponent.

## The failure persists as a uniform bound on smooth features

Take an even, nonnegative, smooth mollifier $\rho$ supported in
$[-1,1]$ with integral one. For $\delta_j\downarrow0$ put

$$
w_j=\rho_{\delta_j}*u,\qquad
u_j=\mathbf1_{t\ge0}w_j(t),\qquad
F_j(x)=x^{-9/4}w_j(\log(x/\pi))\quad(x\ge\pi).
\tag{LB6}
$$

Choose every $\delta_j$ small enough that the physical support is
inside $[\pi,\pi+1/4]$. These features are smooth up to the physical
endpoint and compact at the upper endpoint. They are not claimed to
belong to $C_c^\infty((\pi,\infty))$.
Again $\mathscr TF_j=F_j$. The classical boundedness of the half-line
cutoff on $H^{1/4}$, mollification and (LB4) give

$$
\sup_j\|u_j\|_{H^{1/4}}<\infty,\qquad
u_j\longrightarrow u\quad\text{in }L^2.
$$

The same right-convolution and reflection as in (LB5) bound
$\|g_{F_j}\|_{H^{1/4}}$ uniformly. The $H$ norms of $F_j$ converge
to the nonzero $H$ norm of $F$. Normalize each feature in $H$;
then

$$
M(F_j)\le\left(1+\frac1{4\pi}\right)^6<4,\qquad
\sup_j\bigl[\mathcal P(F_j)+\mathcal L_k(g_{F_j})\bigr]<\infty
\quad\text{for every fixed finite }k.
\tag{LB7}
$$

The mollifier samples the positive logarithmic cusp on half its mass:

$$
w_j(0)=\frac12\log(1/\delta_j)+O(1).
$$

The integral term of (LB5) remains bounded, and normalization has a
positive finite limit. Consequently

$$
g_{F_j}(0)\longrightarrow+\infty,
\qquad \sup_j\|g_{F_j}\|_\infty=\infty.
\tag{LB8}
$$

This is a single jointly realized family: its physical moment,
Gamma profile and arithmetic profile all come from the SAME $F_j$.
It does not combine independently optimized observables.

## Smooth boundary data do not control arithmetic dilation difference quotients

There is a separate actual-source obstruction even when the starting
arithmetic profiles are smooth at zero. Reuse the actual inverse (LB5),
classical modulation, and support isolation of the sole $n=2$ prime term,
as in the [existing prime cross-term account](frankliebseiringer2006hardy.md).
The additional conclusion concerns their JOINT physical realization and
dilation difference quotient, not a new modulation or inverse theorem. It is
paper analysis without Lean certification or a priority claim.

For $s\ge0$ use the physical variation

$$
D_sF(x)=e^{7s/2}F(e^sx),\qquad
h_F(t)=\sqrt\pi e^{7t/2}F(\pi e^t).
$$

The actual $\mathscr T,B$ commute with this physical scaling, so
$h_{D_sF}(t)=h_F(t+s)$ and
$g_{D_sF}(r)=e^{5s/4}g_F(|r|+s/2)$.
This is a folded translation of the profile, not a full-line translation.
Put

$$
C_\ell(g)=\Re\int_{\mathbb R}\overline{g(r)}g(r+\ell)dr,
\qquad
\mathfrak T(g)=2\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}C_{\log n}(g).
\tag{PD1}
$$

If $g(r)=f(|r|)$ and $G_a(r)=f(|r|+a)$, the two same-side
pieces and the folded piece give exactly

$$
C_\ell(G_a)=2\Re\int_a^\infty\overline{f(t)}f(t+\ell)dt
+\Re\int_a^{\ell+a}\overline{f(t)}f(\ell+2a-t)dt.
\tag{PD2}
$$

The second piece moves its reflection center throughout the correlation
interval. It is not confined to a deleted neighborhood of zero.

Let $L=\log2$ and choose
$0<\varepsilon<\min\{L/8,(\log3-L)/4\}$ and a nonzero real even
$\phi\in C_c^\infty(-\varepsilon,\varepsilon)$. For $N\to\infty$ set

$$
\omega_N=e^{-\sqrt{\log(2+N)}},\qquad
f_N^\pm(r)=\omega_N\phi(r-L/2)
\cos\bigl(N(r-L/2)\pm\pi/4\bigr)\quad(r\ge0).
\tag{PD3}
$$

Here is one actual source realizing each profile. Write
$(I_bv)(t)=\int_0^\infty e^{-by}v(t+y)dy$ and put

$$
v_N^\pm(t)=\pi^{-7/4}e^{5t/4}f_N^\pm(t/2),\qquad
h_N^\pm=(I+\tfrac32I_1)v_N^\pm,\qquad
F_N^\pm(\pi e^t)=\pi^{-1/2}e^{-7t/2}h_N^\pm(t).
\tag{PD4}
$$

The reused resolvent identity
$(I-\tfrac32I_{5/2})(I+\tfrac32I_1)=I$ gives the actual $B$ inverse.
Also $h_N^\pm$ is supported in $[0,L+2\varepsilon]\subset[0,\log4)$.
Thus $\mathscr TF_N^\pm=F_N^\pm$, and substitution in (LB5) gives
$g_{F_N^\pm}(r)=f_N^\pm(|r|)$ exactly.
These physical sources are smooth up to $\pi$.

Their moment is $O(\omega_N^2)$. Their Gamma form is
$O(\omega_N^2\log(2+N))$: the usual right-convolution, smooth-multiplier
and half-line-cutoff bounds on $H^\sigma$ are uniform for
$0\le\sigma\le1/4$, by interpolation of the two endpoints.
Apply them to the fixed smooth envelope modulated at frequency $N/2$,
with $\sigma=1/\log(2+N)$ for sufficiently large $N$, and use
$p(\xi)\le C\sigma^{-1}(1+\xi^2)^\sigma$.
For every fixed finite $k\ge0$, classical modulation likewise gives
$\mathcal L_k(g_{F_N^\pm})\le C_k\omega_N^2[\log(2+N)]^k$.

To impose the SAME normalized cap, choose a fixed nonzero real even
smooth profile $g_0$ supported in $(-d,d)$, $0<d<L/16$.
Use (PD4)'s inverse to realize it by $F_0$, then normalize $H(F_0)=1$.
Its physical support gives $M(F_0)\le e^{12d}<4$. Set

$$
Z_N^\pm=\frac{F_0+F_N^\pm}{\|F_0+F_N^\pm\|_H}.
\tag{PD5}
$$

The denominator tends to one. For all sufficiently large $N$ these
actual sources satisfy $H(Z_N^\pm)=1$, $M(Z_N^\pm)<4$, and uniform
bounds on $\mathcal P$ and every fixed $\mathcal L_k$.
Their arithmetic profiles are smooth at zero, with every fixed
origin derivative uniformly bounded: the added packets vanish near zero.

For the packet alone, all same-side prime correlations vanish and
all folded correlations with $n\ge3$ vanish. Its even support has
diameter $L+2\varepsilon<\log3$. The fixed profile and the packets
have no prime cross terms, since every distance between a base-profile
point and a packet point is less than $L$. These facts persist at $s=1/N$ for large $N$.
Hence the COMPLETE sum in (PD1), before and after that variation,
has only the packet's $n=2$ term.

For $I(a)=\int\phi(y+a)\phi(y-a)dy$ and
$J_N(a)=\int\phi(y+a)\phi(y-a)\cos(2Ny)dy$, product-to-sum in (PD2)
gives the exact packet expression
$C_L(G_a)=\omega_N^2[\cos(2Na\pm\pi/2)I(a)+J_N(a)]/2$.
Both $I,J_N$ are even, with uniformly bounded second derivatives.
At $s=1/N$, $a=s/2$, this yields, including the actual factor
$e^{5s/2}$ and the common normalization,

$$
\frac{\mathfrak T(g_{D_{1/N}Z_N^\pm})-
      \mathfrak T(g_{Z_N^\pm})}{1/N}
=\mp\frac{L\sin1}{\sqrt2}\|\phi\|_2^2
N\omega_N^2[1+o(1)].
\tag{PD6}
$$

Since $N\omega_N^2\to\infty$, the two signs are unbounded in opposite
directions. The starting sources obey the normalized cap; the varied
sources are not renormalized again or asserted to preserve that cap.
Thus the given moment and logarithmic bounds, even together with
smooth controlled origin data, do not supply a uniform bound on
arithmetic dilation difference quotients. This does not assert that these sources
are minimizing or $q$-null, or rule out cancellation with the other
terms of the COMPLETE energy on actual minimizers.

## What remains necessary for an actual minimizing source

The family (LB6) is not claimed to be $q$-null, to have nonpositive
complete energy, or to be an original finite Gaussian family. It
therefore does not refute boundedness or improved estimates that
use the actual minimizer equation in addition to its moment and
logarithmic bounds.

The profile $g_F$ is even on the whole line, so zero is an interior
point rather than an exterior Dirichlet boundary. The profile $u_F$
does vanish on the negative half-line, but its minimizing equation
contains the full theta/Möbius pullback and both physical metrics.
It is not the equation $L_\Delta u=\mu u$. A bounded forcing estimate,
the required domain identification, localization errors and uniform
constants must be established before applying the published boundary
theorem. Its $\log^{-1/2}$ pointwise boundary decay also does not by
itself bound the complete reconstructed sixth-moment heat remainder.

Thus (LB7)--(LB8) exclude a shortcut from the CURRENT moment and
logarithmic regularity bounds alone to the theorem's bounded-value
premise. They supply no favorable sign for the original complete
form, improved Robin error, full RH proof or Lean/kernel result.
