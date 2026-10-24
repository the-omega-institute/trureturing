---
bibkey: hernandezsantamaria2025optimal
authors: Víctor Hernández-Santamaría, Luis Fernando López Ríos, and Alberto Saldaña
year: 2025
title: Optimal boundary regularity and a Hopf-type lemma for Dirichlet problems involving the logarithmic Laplacian
doi: 10.3934/dcds.2024084
url: https://arxiv.org/abs/2401.18033v2
claim: The published boundary theorem requires an exterior-zero equation with bounded solution and forcing. Actual cap-four features can have uniformly bounded logarithmic Fourier moments of every fixed order while their profile values at zero diverge. Smooth actual sources also give opposite unbounded full-prime dilation difference quotients with controlled origin data. A fixed actual source also has a signed critical metric defect quadratic in log log log N, while its regularized original moment and actual Gamma form, including a fixed spatial weight, remain uniformly bounded. The separate excess-quotient selection and exactly matched global-null branch give conditional Sobolev regularity and an actual physical-dilation derivative. None of these paper-level applications proves an RH or Robin bound.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Actual-source interfaces for boundary values, dilation and critical payment

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


## A fixed actual source excludes a universal Gamma-only critical payment

Reuse the [actual inverse and critical signed-defect calculation](platttrudgian2021rh.md#a-critical-signed-quadratic-defect-on-a-fixed-actual-source),
VHC5--VHC7 and VHC17--VHC26, the finite-cap range construction VHS1,
and [W338's comparison of the actual Gamma and arithmetic forms](suzuki2026screw.md#compare-the-full-logarithmic-forms-with-a-bounded-boundary-cost).
The half-line projection bound in the logarithmic form is the existing
Carleman interface used in VHD1. None of those suppliers is reproved.
Compact symbol localization and the logarithmic-frequency calculation
below are classical tools. The additional `repo-derived` interface is a
FIXED actual source for which the critical signed defect grows faster
than its uniformly bounded actual Gamma payment, including a spatially
weighted Gamma payment. No literature-priority or Lean/kernel certification is claimed.

### Statement with the original source and the regularized source separated

Keep the unitary Fourier convention of VHC and fix $c>q=5/4$.
Use exactly its critical regularizer and exponential tilt,
$$
 j_N(\xi)=\left(\frac{c^2+\xi^2}{c^2+\xi^2/N^2}\right)^{1/4},
 \quad J_N=j_N(D),\quad L_N=e^{qt}J_Ne^{-qt},\quad N\ge2,
$$
and its signed defect
$$
 D_B^L(X)=\langle L_NX,BL_NX\rangle
             -\Re\langle BX,L_N^2X\rangle.
$$
For every prescribed $K_*>1$ and fixed real $\lambda\ne\mu$, there
is a FIXED real actual source $F\in\mathcal V$, independent of $N$,
with $\mathcal H(F)=1$ and $M(F)<K_*$, such that its actual finite-cap
sources $F_{J_N}$ satisfy
$$
 \begin{aligned}
 M(F_{J_N})&=O(1),\\
 \mathcal P(F_{J_N})&=O(1),\\
 \mathcal G(e^{rt}u_{F_{J_N}})&=O_r(1)
                  &&(1/4<r<1/2),
 \end{aligned}
 \tag{GCP1}
$$
where $\mathcal G(v)=\int p(\xi)|\widehat v(\xi)|^2d\xi$ and
$u_{F_{J_N}}$ is the ACTUAL zero-extended theta coordinate. Meanwhile,
with $B=\lambda P_+-\mu e^{-6t}P_+$,
$$
 D_B^L(X)=\kappa(\log\log\log N)^2+O_{\lambda,\mu}(1+\log\log\log N),
 \qquad \kappa>0.
 \tag{GCP2}
$$
The estimates and the asymptotic are for $N\to\infty$. The constants
can depend on the fixed source, $c$, the fixed weight
$r$, and the fixed multipliers. Every original spatial moment and
$\mathcal G(e^{rt}u_F)$ is finite and independent of $N$. The cap is
on the ORIGINAL $F$, not on $F_{J_N}$.

Consequently no finite coefficient, even one allowed to depend on
those fixed original-source budgets, bounds this positive defect
by $\mathcal P(F_{J_N})+M(F_{J_N})$ uniformly in $N$. The same is true
with $\mathcal G(e^{rt}u_{F_{J_N}})$ in place of $\mathcal P(F_{J_N})$.
The source is not asserted to be GLOBAL null, minimizing, or of
nonpositive complete energy. These are indispensable scope exclusions.

### Choose a fixed symbol with two inverse logarithms

Choose $\vartheta\in C^\infty(\mathbb R)$, zero on $(-\infty,2]$,
one on $[3,\infty)$, and taking values in $[0,1]$. Put
$$
 a(s)=\begin{cases}\vartheta(s)/(s\log s),&s>2,\\0,&s\le2.\end{cases}
$$
It is bounded, of finite total variation, and in $L^2(0,\infty)$.
For $\ell\ge3$,
$$
 \int_0^\ell a(s)ds=\log\log\ell+c_\vartheta,
 \qquad
 \int_0^\infty(1+s)a(s)^2ds<\infty.
 \tag{GCP3}
$$
Define real-even $A_0$ and real-odd $B_0$ by
$$
 \widehat A_0(\xi)=\frac{a(\log|\xi|)}{|\xi|},
 \qquad
 \widehat B_0(\xi)=-i\frac{a(\log|\xi|)}{\xi},
 \tag{GCP4}
$$
with both symbols zero for $|\xi|\le1$. They belong to $H^{1/2}$:
the high-frequency half-derivative integral is $\int a(s)^2ds$.
For either symbol $h$, $|h(\xi)|\le C/|\xi|$ and
$|h'(\xi)|\le C/|\xi|^2$ for $|\xi|\ge1$.

For fixed smooth compact $m$, the unitary convolution formula gives
$$
 \widehat{m h^\vee}(\xi)=m(0)h(\xi)+O(|\xi|^{-2}).
 \tag{GCP5}
$$
Indeed subtract $m(0)h(\xi)$ under the convolution. On
$|\eta|\le|\xi|/2$, the mean-value bound is
$C|\eta||\xi|^{-2}$; $\widehat m$ has finite first absolute moment.
On the complement, its rapid decay and boundedness of $h$ give the
same bound. The low-frequency remainder is in $L^2$, so the entire
remainder is in $H^1$. This assertion is about each localized packet;
remote translated packets are retained separately.

Take VHC4's real-even cutoff $\chi$, equal to one near zero and
supported in $(-\varepsilon,\varepsilon)$, with
$$
 t_0=2\log2,\qquad
 \varepsilon<\tfrac1{10}\min(t_0,2\log3-t_0),\qquad
 e^{6\varepsilon}<K_*.
$$
For a small real parameter $C$, put $D=\sqrt2C$ and
$$
 \beta_C(t)=\chi(t)A_0(t)
 +D[\chi(t-t_0)B_0(t-t_0)-\chi(t+t_0)B_0(t+t_0)].
 \tag{GCP6}
$$
Oddness of $B_0$ makes this real-even. Use precisely VHC5--VHC6:
$$
 \begin{aligned}
 Y(t)&=\int_0^\infty e^{v/4}\beta_C(t+v)dv,
 &u(t)&=\beta_C(t)+\tfrac32Y(t)\quad(t\ge0),\\
 U(x)&=x^{-9/4}u(\log(x/\pi)),
 &F_C(x)&=\sum_{n\ge1}\mu(n)n^4U(n^2x)\quad(x\ge\pi).
 \end{aligned}
$$
Only $n=1,2$ occur in this physical inverse. The same finite divisor
identity gives $\mathscr TF_C=U$, and the Volterra identity gives
$g_{F_C}(r)=\beta_C(2r)$. Also $Y'=-\beta_C-Y/4$, so $Y$ is
half-line $H^1$ with bounded support. Its zero extension has at most
a bounded jump. The logarithmic-form projection bound and GCP4--GCP5
therefore give $F_C\in\mathcal V$, with bounded physical support
and every fixed exponentially weighted original Gamma norm finite.
No converse to W338 is assumed to manufacture the source.

At $C=0$, this source is nonzero and supported in
$[\pi,\pi e^\varepsilon]$. To verify nonvanishing, the inverse cosine
integral for $A_0$ below frequency $1/|t|$ has positive main growth
$\log\log\log(1/|t|)$, with bounded error; one integration by parts bounds
the remaining oscillatory tail by $C/[\log(1/|t|)\log\log(1/|t|)]$. Thus $A_0$ is
nonzero near zero, and the actual inverse identity gives $F_0\ne0$.
Reuse VHC27's strict-cap continuity argument: $F_C=F_0+CF_1$ in
$H_6$, and $M(F_0)<K_*\mathcal H(F_0)$. A sufficiently small nonzero
$C$ of either sign preserves that strict inequality. Fix it with
$(\lambda-\mu)C>0$, then normalize by $\sqrt{\mathcal H(F_C)}$.
Only after fixing and normalizing this source is $N$ allowed to grow.
The following calculations use the unnormalized profile $\beta_C$;
normalization divides their quadratic forms by $\mathcal H(F_C)$.

### Retain every arithmetic shift in the critical Fourier coordinate

Use VHP3's exact whole-line reconstruction
$$
 w=e^{qt}\beta_C,\quad
 S=\sum_{n\ge1}\mu(n)n^{-3}T_{2\log n},\quad
 K=I+\tfrac32I_1,\quad X=KSw.
$$
For $\xi>0$, applying GCP5 at all three centers gives
$$
 \widehat w(\xi)=\frac{a(\log\xi)}\xi
 \left[1-iDe^{qt_0}e^{-it_0\xi}
           +iDe^{-qt_0}e^{it_0\xi}\right]+O(\xi^{-2}).
 \tag{GCP7}
$$
The multipliers of $S$ and $K$ are respectively
$\sum\mu(n)n^{-3}e^{2i\log n\,\xi}$ and $1+O(\xi^{-1})$.
There are exactly two zero-phase terms: the first packet with $n=1$
and the positive-center odd packet with $n=2$. Their sum is
$(1+iC)a(\log\xi)/\xi$, because
$\mu(2)2^{-3}[-iDe^{qt_0}]=iC$.
Every other phase has fixed distance at least $d_*>0$ from zero,
as in VHC13, and its coefficients are absolutely summable.
Consequently, for $s\ge0$,
$$
 c^{-1/2}e^s\widehat X(e^s)
 =c^{-1/2}(1+iC)a(s)+E(s),
$$
$$
 \|E\|_\infty+\|E\|_2<\infty,\qquad
 \int_0^\ell|E(s)|ds=O(1+\log\log\ell),\qquad
 \sup_{\ell\ge0}\left|\int_0^\ell E(s)ds\right|<\infty.
 \tag{GCP8}
$$
Each remote term is a constant times $a(s)e^{i\tau e^s}$,
$|\tau|\ge d_*$. VHC16's oscillatory primitive bound and integration
by parts against the finite variation of $a$ give a uniform primitive
bound $C/|\tau|$. Sum the absolute coefficients. The $O(\xi^{-2})$
Fourier remainder becomes $O(e^{-s})$ and is integrable. This proves
GCP8 while retaining all remote interactions. GCP7 also gives
$X\in H^{1/2}$, hence $\|J_NX\|_2+\|L_NX\|_2=O(1)$ by VHC25.
The actual identity $M(F_{J_N})=\pi^{-7/2}\|P_+L_NX\|_2^2$
proves the first line of GCP1.

### Evaluate the same signed four-block form with its actual cap

Set $\ell=\log N$ and reuse exactly VHC17--VHC23's four kernels.
The present logarithmic-frequency input has bounded $L^2$ norm
and total $L^1$ norm $O(1+\log\log\ell)$. Its exterior $L^1$ factors
are uniformly bounded. The kernel errors are bounded by
$C[\omega_N(s)+\omega_N(t)]$, with
$\omega_N(s)=e^{-2s}+e^{-2(\ell-s)}$ on $[0,\ell]$.
Their weighted $L^1$ factor is bounded and the other is
$O(1+\log\log\ell)$. Thus the entire rational cap, lower-frequency
and exterior-frequency errors cost $O(1+\log\log\ell)$.

For the same-sign homogeneous kernels, write
$\tanh(z/4)=\operatorname{sgn}z+r(z)$ with $r\in L^1$.
Young's inequality pays the $r$ term by the bounded $L^2$ norm.
The main/main sign term vanishes by antisymmetry. Terms involving
$E$ cost $O(1+\log\log\ell)$: its primitive is bounded by GCP8;
for the main/error term integrate the resulting main primitive by
parts against that bounded error primitive, using
$\int_0^\ell a=O(1+\log\log\ell)$.

For the opposite-sign blocks, the sech part likewise costs $O(1)$.
With $f=c^{-1/2}(1+iC)a+E$, their constant parts are exactly
$$
 2\Re\left[\frac{i}{4\pi}
       \left(\int_0^\ell\overline{f(s)}ds\right)^2\right]
 =\frac{C}{\pi c}(\log\log\ell)^2+O(1+\log\log\ell).
 \tag{GCP9}
$$
Here $\int E=O(1)$ and
$\Re[i(1-iC)^2]=2C$. This keeps real-source conjugacy in both
negative-frequency blocks.

For $C_6=(1-e^{-6t})P_+$, VHC's exact additional Fourier factor
$6/[6+i(\xi-\eta)]$ is absolutely integrable against the bounded
middle-quadrant kernels; exterior interactions cost
$O(1+\log\log\ell)$. Thus $D_{C_6}^{J}(X)=O(1+\log\log\ell)$.
VHC25--VHC26 retain the ORIGINAL exponential tilt; since
$\|J_NX\|_2=O(1)$, their error here is $O_B(1)$.
Use $B=(\lambda-\mu)P_++\mu C_6$ to obtain GCP2 with
$$
 \kappa=\frac{(\lambda-\mu)C}{\pi c\,\mathcal H(F_C)}>0.
$$
At each finite $N$, the symmetric Fourier-cutoff limit is exactly
the one in VHC18; the finite logarithmic $L^1$ bounds above supply
absolute domination. No sharp-cut surrogate for $j_N$ is used.

### Pay the actual Gamma form and its spatially weighted version

The ACTUAL finite-cap arithmetic profile is
$\beta_{F_{J_N}}=J_N\beta_C$. GCP5 gives its logarithmic squared
norm the upper bound
$$
 C+C\int_1^\infty(1+\log\xi)j_N(\xi)^2
                       \frac{a(\log\xi)^2}{\xi^2}d\xi
 =O(1).
 \tag{GCP10}
$$
Use $j_N(\xi)^2\le C(1+|\xi|)$ uniformly in $N$ and the finite
integral in GCP3. The $O(\xi^{-2})$ Fourier remainder contributes
a uniformly integrable logarithmic density as well.
W338's UPPER comparison, with
$S(F_{J_N})\le CM(F_{J_N})=O(1)$, now proves
$\mathcal P(F_{J_N})=O(1)$.
This is the actual zero-extended theta Gamma form, not
$\mathcal G(X_{J_N})$ substituted for it.

For fixed $1/4<r<1/2$, put $\beta_r=e^{rt}\beta_C$.
GCP5 gives the same spectral bounds for this fixed compact profile.
The analytic strip $c>q>r$ and VHC25's vertical derivative bound give
$$
 \begin{aligned}
 \mathcal G(e^{rt}J_N\beta_C)
 &=\mathcal G(j_N(D+ir)\beta_r)\\
 &\le C_r[\mathcal G(J_N\beta_r)+\mathcal G(\beta_r)]
 \le C_r.
 \end{aligned}
 \tag{GCP11}
$$
The equality follows from exponential conjugation in that strip;
the bounded difference from the real-axis symbol is uniform in $N$.
On the positive half-line the SAME actual Volterra inverse reads
$$
 e^{rt}u_{F_{J_N}}(t)=e^{rt}\beta_{F_{J_N}}(t)
 +\frac32\int_0^\infty e^{-(r-1/4)v}
               e^{r(t+v)}\beta_{F_{J_N}}(t+v)dv.
$$
First apply $P_+$ to $e^{rt}\beta_{F_{J_N}}$, then the full-line
forward resolvent of parameter $r-1/4>0$, then $P_+$ again.
Forward shifts give exactly this half-line inverse. The resolvent
is a bounded multiplier in the logarithmic form. Both projections
use the EXISTING logarithmic-form Carleman bound of W338/VHD1:
the two half-line diagonal energies sum to the full energy up to
a bounded $L^2$ cross term with kernel bounded by $C/(s+t)$.
No boundedness of $P_+$ on $H^{1/2}$ is assumed. This proves the
weighted Gamma line of GCP1 without applying any null estimate to
$F_{J_N}$.

### Consequence for the remaining minimizer argument

Taking $N=\exp(\exp(\exp L))$, the positive signed defect is
$\kappa L^2+O(L)$, while every Gamma payment in GCP1 is $O(1)$
and the regularized original moment is bounded. Fixed spatial
budgets and the actual strictly weighted Gamma payment therefore
do not supply a universal pure-critical linear absorption estimate.
This is stronger than the earlier moment-only obstruction and
rules out that proposed substitute for the missing endpoint step.

The source has not been made GLOBAL null. Such a null equation
could impose phase relations excluding or cancelling GCP9's
coefficient. A SAME-null joint regularizer/weight estimate remains
unproved. The [weighted-null compactification](platttrudgian2021rh.md#direct-physical-compactification-with-the-original-cap)
is unchanged. No critical minimizer regularity, physical-dilation
first derivative, improved uniform allowance, RH or full Robin
conclusion follows from this generic-source counterexample.


## Select an attained negative representative with exactly matched multipliers

Reuse [W266, W317--W320 and W326](suzuki2026screw.md), including
the small-excess positivity, actual finite-source form core and
original-feature compactness. The published generalized Rayleigh
supplier is [Jacob--Langer--Trunk, Theorem 2.4](../Eigenstructure/jacoblangertrunk2016variational.md);
its exact common-domain and parameter correspondence is recorded there.
Classical polarization and lower semicontinuity are used within this
application; no general min--max theorem is asserted as new. The additional
`repo-derived` interface is selection of a negative actual representative
whose two ORIGINAL supporting multipliers agree exactly. This is a
paper derivation, without Lean/kernel certification or a priority claim.

## 1. Exact quantities and target

Write

$$
 H(F)=\|F\|_{L^2(\pi,\infty)}^2,\qquad
 M(F)=\int_\pi^\infty(x/\pi)^6|F(x)|^2dx,
 \qquad D(F)=M(F)-H(F).
$$

This `D` is the quadratic excess, not W261's differently normalized square-root excess. Retain

$$
 \mathcal V=\{F:M(F)+\mathcal P(F)<\infty\},\qquad
 \mathfrak E(F)=\mathcal P(F)-\mathfrak J(F,F),\qquad
 \mathcal P(F)\ge0.
$$

For every nonzero F in this domain,

$$
 D(F)=\int_\pi^\infty[(x/\pi)^6-1]|F(x)|^2dx>0.       \tag{MR1}
$$

The strict inequality uses positivity of the weight almost everywhere on the open half-line; a nonzero L2 function cannot be supported at the single endpoint. All three quadratic forms are homogeneous of degree two.

**Conditional application.** If there is ANY completed actual F in V with E(F)<0, then there exist a real actual F_* in V and a number lambda>0 such that

$$
 D(F_*)=1,\qquad\mathfrak E(F_*)=-\lambda<0,
$$

$$
 Q(G):=\mathfrak E(G)+\lambda M(G)-\lambda H(G)\ge0
 \quad(G\in\mathcal V_{\mathbb C}),\qquad Q(F_*)=0.     \tag{MR2}
$$

Thus the GLOBAL supporting form has exactly mu=lambda, not just a stationary equation or approximate multiplier agreement. F_* need not be a finite Gaussian feature. A finite original negative source is included through its actual physical feature, and a failed RH is linked to such a feature by the already existing W254/W256–W257 interface; that interface is not reproved here.

## 2. Transfer the existing small-excess positivity into the completed domain

Let delta_*>0 and A_* be the fixed constants of W266. We may shrink delta_* so it is at most one. W257's exact original-source identities say, for the physical feature G of an original Gaussian source at A,

$$
 Q_H=4\pi^3 A H(G),\qquad
 Q_{6,A}/Q_H=M(G)/H(G),\qquad
 Q_{\mathcal K_A^g}=\mathfrak E(G).
$$

Consequently W266 says, on those actual finite features and at A>=A_*,

$$
 D(G)/H(G)\le\delta_*\quad\Longrightarrow\quad
 \mathfrak E(G)\ge\frac{\pi^3}{2}H(G)>0.              \tag{MR3}
$$

Set epsilon_*=delta_*/2. Suppose a nonzero completed F satisfies D(F)/H(F)<=epsilon_*. By W326, choose actual finite-source features G_j converging to F in the FULL V norm; their original starts may be chosen above A_* and above the source-core start for each requested accuracy, in a fixed positive-width window. No uniform start over all targets is required.

The V convergence implies H(G_j)->H(F), M(G_j)->M(F), and E(G_j)->E(F): M is part of the graph norm, H is weaker, P is continuous in its own form norm, and W317's entire debit is continuous in N, with N^2<=CM. Hence H(G_j)>0 and D(G_j)/H(G_j)<delta_* for all sufficiently large j. Apply MR3 and pass to the limit:

$$
 D(F)/H(F)\le\epsilon_*
 \quad\Longrightarrow\quad
 \mathfrak E(F)\ge\frac{\pi^3}{2}H(F)>0.              \tag{MR4}
$$

No endpoint exact-budget repair is needed because epsilon_* is strictly smaller than delta_*; W327 is available but is not consumed here. In particular EVERY completed negative F satisfies

$$
 D(F)/H(F)>\epsilon_*.                              \tag{MR5}
$$

This is the necessary original excess gap. It is not a positive lower bound on H when D=1.

## 3. The negative D=1 quotient is finite and attained

Assume there is a negative F_0 and define

$$
 \rho=\inf\{\mathfrak E(F):F\in\mathcal V_{\mathbb R},\ D(F)=1\}.
                                                                  \tag{MR6}
$$

The choice of real field loses no negative source and does not change the infimum. The forms have real coefficients and V is closed under real and imaginary parts, as already recorded before W345. If F=f+ig is nonzero, then

$$
 D(F)=D(f)+D(g),\qquad \mathfrak E(F)=\mathfrak E(f)+\mathfrak E(g).
$$

Each nonzero component has strictly positive D by MR1. Therefore E(F)/D(F) is a convex weighted average of the ratios for its nonzero real components. In particular a complex negative direction has a real negative direction, and the real and complex excess-quotient infima coincide. No separate balanced-moment rank-one extraction is needed for this single positive quadratic denominator.

Scale a real negative direction to D=1. Then rho<0. For ANY negative F with D(F)=1, MR5 gives

$$
 H(F)<\epsilon_*^{-1},\qquad M(F)=1+H(F)<K_D,
 \qquad K_D:=1+\epsilon_*^{-1}.                       \tag{MR7}
$$

By W317 and N(F)^2<=CM(F), there is a fixed C_0 with |J(F,F)|<=C_0 M(F). Therefore all such negative vectors satisfy

$$
 \mathfrak E(F)\ge-C_0K_D,\qquad
 0\le\mathcal P(F)=\mathfrak E(F)+\mathfrak J(F,F)\le C_0K_D.
                                                                  \tag{MR8}
$$

Positive energies cannot lower the negative infimum, so -infinity<rho<0. Take a real minimizing sequence F_j with D(F_j)=1, E(F_j)<0 and E(F_j)->rho. MR7–MR8 give uniform M and P bounds.

Apply the already proved precompactness consequence of W318–W319: a subsequence converges in H and N to a real F_*. This is the bounded-M/P compactness statement used to prove W320; it does not require that this unnormalized sequence has H=1. Lower semicontinuity of M and P, continuity of H, and continuity of the COMPLETE J in N give

$$
 F_*\in\mathcal V,\qquad D(F_*)\le1,\qquad
 \mathfrak E(F_*)\le\rho<0.                          \tag{MR9}
$$

More explicitly, M(F_*)<=liminf M(F_j)=1+H(F_*), since H converges strongly. The actual theta profiles converge in L2 by W310; the closed positive Fourier multiplier gives the stated lower semicontinuity of P. Subtract the convergent J to obtain E(F_*)<=liminf E(F_j). No continuity of the full Gamma form or strong sixth-moment convergence is asserted.

The negative energy makes F_* nonzero; MR1 gives d:=D(F_*)>0. If d<1, the ACTUAL vector F_*/sqrt(d) is still in V, has D=1 and has energy

$$
 \mathfrak E(F_*)/d\le\rho/d<\rho,
$$

contradicting MR6. Thus d=1. The defining infimum now also gives E(F_*)>=rho, hence

$$
 D(F_*)=1,\qquad\mathfrak E(F_*)=\rho.               \tag{MR10}
$$

This negative scaling argument pays precisely the possible loss of excess mass in the compact limit; simply declaring D=1 closed under H convergence would be invalid.

## 4. Global positivity and exact multiplier matching

For every nonzero real or complex G in V, MR1 and the common quotient infimum give E(G)/D(G)>=rho. Put lambda=-rho>0. Then

$$
 \mathfrak E(G)+\lambda D(G)\ge0\quad(G\in\mathcal V),
 \qquad\mathfrak E(F_*)+\lambda D(F_*)=0.             \tag{MR11}
$$

This proves MR2 with mu=lambda. Because Q is a positive semidefinite Hermitian form, Q(F_*,G)=0 for every G in V. Equivalently, use the nonnegative quadratic polynomial Q(F_*+zG) for real and imaginary z. The resulting mixed equation is GLOBAL on the same actual domain, not an Euler equation proved only on compact tests.

The number lambda is fixed by the ONE infimum over the entire actual domain; it is not tuned after choosing each source or regularizer. MR8 gives lambda<=C_0K_D. There is no positive numerical lower bound supplied for lambda. No finite source is asserted to attain this new quotient.

## 5. Normalize in H without misstating the original cap

Let h_*=H(F_*)>0 and set Fhat=F_*/sqrt(h_*). Then

$$
 H(Fhat)=1,\quad M(Fhat)=1+h_*^{-1},\quad
 \mathfrak E(Fhat)=-\lambda/h_*<0,\quad Q(Fhat)=0.     \tag{MR12}
$$

The multipliers of the SAME global Q remain mu=lambda under this rescaling. Importantly MR7 only gives an UPPER bound on h_*; it does not give an upper bound on M(Fhat). One must not replace the true normalized cap by K_D or by four.

A finite cap can be bounded using W317's existing infinitesimal moment estimate. Write |J(F,F)|<=(lambda/2) M(F)+C_{lambda/2} H(F), with C_{lambda/2} chosen nonnegative. Since P>=0, MR10 yields

$$
 -\lambda=\mathfrak E(F_*)
 \ge-\frac\lambda2-(\lambda/2+C_{\lambda/2})h_*.
$$

Consequently

$$
 h_*\ge\frac{\lambda}{\lambda+2C_{\lambda/2}}>0,
 \qquad
 M(Fhat)\le K_\lambda:=2+\frac{2C_{\lambda/2}}{\lambda}<\infty.
                                                                  \tag{MR13}
$$

This bound depends on the selected global quotient value lambda and on W317's fixed relative-bound constants. Because the actual form is fixed, lambda is a single conditional global number, independent of the initially supplied negative direction; nevertheless MR13 supplies neither an explicit universal numerical cap nor cap four, nor constants uniform as lambda decreases to zero. A theorem on ALL matched positive-lambda global null vectors can consume MR11 directly. A theorem restricted to unit cap-four minimizers cannot automatically be applied to Fhat. Likewise Fhat is not asserted to minimize the old cap-four problem.

## Applicability of the selected representative

Excluding all negative matched-multiplier representatives satisfying
MR11--MR13 would exclude every negative actual source. This selects
SOME representative; it does not show that the old cap-four minimizer
or every negative vector has equal supporting multipliers. Any
subsequent estimate must cover the actual domain and its true
normalization, including the parameter-dependent original cap.
The negative quotient is still a premise, not a contradiction or a
sign theorem. RH and strict Robin for all integers above 5040 remain
unproved.


## Regularity and actual dilation on the selected matched branch

The preceding selection supplies the exact hypotheses below whenever
a negative actual source exists. It changes the representative and
retains its true moment ratio; it does not impose matched multipliers
on an arbitrary vector or on the previous cap-four minimum.

### Exact assumptions and consequences

Keep the SAME selected nonzero ACTUAL source F in V, with its GLOBAL
matching supporting form

$$
 Q_\lambda(G)=\mathfrak E(G)+\lambda M(G)-\mu\mathcal H(G)\ge0
 \quad(G\in\mathcal V),\qquad Q_\lambda(F)=0.
$$

Assume exactly

$$
 \lambda=\mu>0.                                           \tag{JC1}
$$

Normalize $\mathcal H(F)=1$ by a scalar, which preserves the GLOBAL
null equation, and put $K_F=M(F)<\infty$. More generally the
scale-invariant parameter is $K_F=M(F)/\mathcal H(F)$. Since
$(x/\pi)^6>1$ almost everywhere on the source domain, $K_F>1$.
The exact null identity gives

$$
 \mathfrak E(F)=-\lambda(K_F-1)<0.
$$

No cap-four hypothesis, VHP7 multiplier upper bound, or uniformity
as $\lambda\to0$ is assumed. The complete energy, actual theta
source, all prime powers, both poles and both original metrics are
retained. The independent selection of such a matching representative
is an input to this manuscript, not proved here.

Under these hypotheses the consequences are:

* For EVERY fixed 0<s<3/2, the actual arithmetic profile g_F belongs
  to H^{s,log}(R), with norm defined by the Fourier weight
  (1+tau^2)^s log(2+|tau|). The same original full-line moment
  reconstruction X belongs to H^s(R).
* These have explicit inverse-multiplier costs of the existing form
  K_F Lambda_lambda exp(C_s Lambda_lambda), where
  Lambda_lambda=1+(1+lambda)^{1/theta}lambda^{-kappa},
  theta=(4-2eta)/5 and kappa=(1-theta)/theta>1/4.
  The moment-coordinate bound has an additional lambda^{-1}.
* In particular s=1 produces an ACTUAL source-space dilation
  generator A=(7/2)F+xF' in V. For the original physical dilation
  D_aF(x)=exp(7a/2)F(exp(a)x),

$$
 (D_aF-F)/a\longrightarrow A\quad\hbox{in }\mathcal V
 \quad(a\downarrow0),                                   \tag{JC2}
$$

  where the V norm is M+P, not an unweighted profile norm. Therefore

$$
 Q_\lambda(D_aF)=a^2Q_\lambda(A)+o(a^2),\qquad
 \left.\frac d{da}\mathfrak E(D_aF)\right|_{0+}
       =6\lambda\mathcal H(F)=6\lambda.                  \tag{JC3}
$$

This is a genuine consumed regularity conclusion. The positive
energy derivative in (JC3) is not a negative-energy contradiction.
No H^{3/2} endpoint or uniform lambda->0 estimate is supplied.

Classical weighted Schur, analytic multipliers, Fourier translation and
closed-form arguments are used within the actual-source application.
The existing full inverse, Gamma comparison and bounded-regularizer
range statements are reused. The additional source-relative composition
is `repo-derived` paper mathematics, without a literature-priority claim
or Lean/kernel certification.

### 1. Actual bounded regularizers and the exact mixed account

Write q=5/4. For a fixed order 0<s<3/2 choose a base c>q, to be
made sufficiently large depending only on s and the fixed original
reconstruction constants. Set

$$
 j_{s,N}(\xi)=
 \left(\frac{c^2+\xi^2}{c^2+\xi^2/N^2}\right)^{s/2},
 \quad J=j_{s,N}(D),\quad L=e^{qt}Je^{-qt},\quad N\ge2.
                                                               \tag{JC4}
$$

These are even and Schwarz-real on |Im z|<c, with the branch positive
on the real line. The range argument is not restricted to s<1/2.
For EVERY fixed finite N,

$$
 j_{s,N}-N^s=O(|\xi|^{-2}),\qquad
 j_{s,N}^2-N^{2s}=O(|\xi|^{-2})
$$

on each smaller closed strip, with the same property for derivatives.
Their convolution terms map the actual exponentially weighted L2
profile into weighted H1. The original beta(t)=g_F(t/2) has its
weight-q L2 bound from M(F). Since c>q, the smoothed terms can be
reconstructed by the SAME actual half-line Volterra and Mobius
inverse as VHS1/VHP1. Their half-line Gamma coordinate is H1;
zero extension introduces at most a bounded jump, which belongs to
the logarithmic form. Add N^s F or N^{2s}F for the scalar terms.
Thus there are ACTUAL F_J,F_{J^2} in V with

$$
 \beta_{F_J}=J\beta,\quad \beta_{F_{J^2}}=J^2\beta,
 \quad X_{F_J}=LX,\quad X_{F_{J^2}}=L^2X.                 \tag{JC5}
$$

Membership constants at this preliminary step may depend on N.
The subsequent estimates will not. This uses no unbounded-order
profile as an admissible test before its domain has been proved.

The entire energy commutation identity VHS2 still holds:

$$
 \mathfrak E(F_J)=\Re\mathfrak E(F,F_{J^2}).                \tag{JC6}
$$

The full Gamma multiplier and every prime-power translation commute
with J. The TWO pole frequencies in the beta coordinate are +/-i/4,
where j has the same real value. The strip margin preserves the
exponential profile weight for each fixed N. Thus the complete prime
sums and both pole functionals converge, and no term is deleted or
given a separate favorable sign in (JC6).

Let B=C_6=(1-exp(-6t))P_+, a bounded real multiplication operator,
0<=B<=1. By JC1, VHS3 becomes exactly

$$
 0\le Q_\lambda(F_J)=\lambda\pi^{-7/2}D_B^L(X),
 \quad
 D_B^L(X)=\langle LX,BLX\rangle
                    -\Re\langle BX,L^2X\rangle.           \tag{JC7}
$$

The hard-cut coefficients have canceled in their ORIGINAL joint
metric. No individual P_+ endpoint commutator is claimed bounded.

### 2. A small relative C6 commutator at every fixed s<3/2

Put a_xi=(c^2+xi^2)^{1/2}. Differentiation gives

$$
 0\le\frac{d\log j_{s,N}}{d\log a}\le s.
$$

Therefore, whenever a_xi>=a_eta,

$$
 1\le j(\xi)/j(\eta)\le(a_\xi/a_\eta)^s;
$$

when the a ordering is reversed the corresponding ratio lies between
(a_xi/a_eta)^s and 1. These statements are uniform in N.

The non-diagonal Fourier kernel of B is

$$
 b(\xi,\eta)=\frac6{2\pi i(\xi-\eta)[6+i(\xi-\eta)]}.
                                                               \tag{JC8}
$$

Its diagonal delta part cancels from [J,B]. Thus the relative
commutator T=JBJ^{-1}-B has kernel bounded by

$$
 |T(\xi,\eta)|\le C
 \frac{|j(\xi)/j(\eta)-1|}
 {|\xi-\eta|\sqrt{36+(\xi-\eta)^2}}.                     \tag{JC9}
$$

Use weighted Schur with p(xi)=a_xi^{-1/2}. Here are BOTH row and
column payments; in particular a far column is not silently omitted.
We take c>=12.

#### Comparable frequencies

On 1/2<=a_xi/a_eta<=2, the derivative bound and the one-Lipschitz
function a(xi) give, with a any comparable a value,

$$
 |j(\xi)/j(\eta)-1|
   \le C_s\min\{|\xi-\eta|/a,1\}.
$$

The Schur weight ratios are bounded there. Each row and column is
therefore at most

$$
 C_s\int_{\mathbb R}
 \frac{\min(a^{-1},|h|^{-1})}{\sqrt{36+h^2}}dh
 \le C_s\frac{\log(2+a)}a
 \le C_s\frac{\log(2+c)}c.                               \tag{JC10}
$$

The integrand has no diagonal singularity: near zero it is O(1/a).

#### Region a_xi>=2 a_eta

Here |xi-eta| is comparable to a_xi, and the kernel in (JC9) is at
most C_s a_xi^{s-2} a_eta^{-s}. The WEIGHTED row integral is bounded by

$$
 C_s a_\xi^{s-3/2}
       \int_{a_\eta\le a_\xi/2}a_\eta^{-s-1/2}d\eta.
                                                               \tag{JC11}
$$

For s>1/2 the integral is O_s(c^{1/2-s}); for s=1/2 it is
O(log(2+a_xi/c)); for s<1/2 it is O_s(a_xi^{1/2-s}). Each case is
O_s(1/c) after its displayed prefactor, because s<3/2.
The WEIGHTED column integral is bounded by

$$
 C_s a_\eta^{1/2-s}
       \int_{a_\xi\ge2a_\eta}a_\xi^{s-5/2}d\xi
 \le\frac{C_s}{(3/2-s)a_\eta}\le C_s/c.                  \tag{JC12}
$$

This is the exact place where the strict s<3/2 range is used.

#### Region a_eta>=2 a_xi

The ratio j(xi)/j(eta) is at most 1, so the kernel is bounded by
C a_eta^{-2}. Its weighted row and column bounds are respectively

$$
 C a_\xi^{1/2}\int_{a_\eta\ge2a_\xi}a_\eta^{-5/2}d\eta
       \le C/a_\xi,
$$

$$
 C a_\eta^{-3/2}\int_{a_\xi\le a_\eta/2}a_\xi^{-1/2}d\xi
       \le C/a_\eta.
$$

Both are at most C/c. The elementary a-integrals can be estimated
directly in the original xi/eta variables; near zero a>=c, and in
the far regions a is comparable to the absolute frequency.

Weighted Schur consequently proves the UNIFORM operator estimate

$$
 \boxed{\quad
 \|[J,B]J^{-1}\|_{2\to2}
 \le K_s(c):=C_s\frac{\log(2+c)}c\longrightarrow0.
 \quad}                                                    \tag{JC13}
$$

This does not assert an endpoint half-space projection bound. The
extra factor 6/(6+i(xi-eta)) from the CONTINUOUS C6 metric is retained
in the entire kernel. The divergence of JC12 at s=3/2 is a limitation
of this absolute Schur argument, not a refutation of every endpoint
estimate.

### 3. Pay the actual exponential tilt with relative, not absolute, symbols

For c>=2q and |Im z|<=q,

$$
 (\log j_{s,N})'(z)
   =s z\left[(c^2+z^2)^{-1}-(N^2c^2+z^2)^{-1}\right],
$$

and its modulus is at most C_s/c, uniformly in N. Integrating along
the vertical segment gives

$$
 L=(I+R)J,\qquad
 \rho:=\|R\|=\sup_\xi|j(\xi+iq)/j(\xi)-1|
 \le C_s q/c.                                            \tag{JC14}
$$

Choose c large enough that rho<=1/2. No uniform estimate for the
ABSOLUTE derivative of j, or absolute L-J, is needed at s>1.

Write Y=JX and T=JBJ^{-1}-B. Moving the self-adjoint J in the
un-tilted defect gives

$$
 |D_B^J(X)|\le\|T\|\|Y\|_2^2.
$$

The first tilted term differs by at most
(2rho+rho^2)||B|| ||Y||_2^2. In the second tilted term,
L^2-J^2=(2R+R^2)J^2, and moving one J gives JBX=(B+T)Y.
Hence

$$
 |D_B^L(X)-D_B^J(X)|
 \le(2\rho+\rho^2)(2\|B\|+\|T\|)\|Y\|_2^2.
$$

Together with JC13--JC14,

$$
 \boxed{\quad
 |D_B^L(X)|\le\varepsilon_s(c)\|JX\|_2^2,
 \quad
 \varepsilon_s(c)\le C_s\left[
 \frac{\log(2+c)}c+\frac qc\left(1+\frac{\log(2+c)}c\right)\right]
 \longrightarrow0.
 \quad}                                                    \tag{JC15}
$$

The second tilted term is paid using the SAME relative commutator;
it is not bounded by an unjustified absolute-symbol estimate.

VHP3's actual full-line reconstruction inequality has a constant
C_rec independent of c,N, since the original K,S,q are fixed:

$$
 \|X_{F_J}\|_2^2\le C_{\rm rec}M(F_J).
$$

JC5 and JC14 therefore give

$$
 \|JX\|_2^2\le(1-\rho)^{-2}C_{\rm rec}M(F_J).              \tag{JC16}
$$

Fix c=c_s once and for all, sufficiently large that

$$
 \pi^{-7/2}(1-\rho)^{-2}C_{\rm rec}\varepsilon_s(c)\le1/4.
                                                               \tag{JC17}
$$

This choice depends only on the fixed order s and the owned original
constants, not on N,lambda,K_F or F. JC7 now gives the required
actual-source absorption

$$
 0\le Q_\lambda(F_J)\le\frac\lambda4M(F_J).                \tag{JC18}
$$

### 4. Retain all multiplier costs in the regularity limit

Fix eta in (0,2) as in VHB16, with

$$
 \theta=(4-2\eta)/5,\qquad
 \kappa=(1-\theta)/\theta>1/4,\qquad
 \Lambda_\lambda=1+(1+\lambda)^{1/\theta}\lambda^{-\kappa}.
$$

A bounded-multiplier premise from VHP7 is NOT used. For every ACTUAL
G in V, write s_G=||g_G||_2^2 and m_G=M(G). W317's complete debit,
H(G)<=C N(G)^2, and VHB16 give

$$
 \begin{aligned}
 \mathcal P(G)+\lambda M(G)
 &=Q_\lambda(G)+\mathfrak J(G,G)+\lambda\mathcal H(G)\\
 &\le Q_\lambda(G)+C(1+\lambda)\mathcal N(G)^2\\
 &\le Q_\lambda(G)+C_\eta(1+\lambda)
                         s_G^\theta m_G^{1-\theta}.
 \end{aligned}
$$

Young absorption into lambda m_G/2 yields the exact cost

$$
 \mathcal P(G)+\frac\lambda2M(G)
 \le Q_\lambda(G)+C_\eta(1+\lambda)^{1/\theta}
                            \lambda^{-\kappa}s_G.
$$

Using JC18 on the SAME F_J consequently gives

$$
 \mathcal P(F_J)+\frac\lambda4M(F_J)
 \le C_\eta\Lambda_\lambda\|g_{F_J}\|_2^2.                \tag{JC19}
$$

W338 and $S(F_J)\le\mathcal P(F_J)$, since $p\ge1$, give

$$
 \mathcal L_1(g_{F_J})+c_1\lambda M(F_J)
 \le C_\eta\Lambda_\lambda\|g_{F_J}\|_2^2,
 \qquad
 \mathcal L_1(g)=\int\log(2+|\tau|)|\widehat g(\tau)|^2d\tau.
                                                               \tag{JC20}
$$

Choose log R=C_eta Lambda_lambda with a sufficiently large fixed coefficient.
The |tau|>R portion of the right side of JC20 is absorbed by its
logarithmic left side. On |tau|<=R,

$$
 j_{s,N}(\tau/2)^2
 \le(1+\tau^2/(4c_s^2))^s\le C_s\exp(C_{s,\eta}\Lambda_\lambda).
$$

The original normalized finite moment gives ||g_F||_2^2<=C K_F by
W338 and W324. Thus, uniformly in N,

$$
 \begin{aligned}
 \|g_{F_J}\|_2^2&\le C_{s,\eta}K_F\exp(C_{s,\eta}\Lambda_\lambda),\\
 \mathcal P(F_J)+\mathcal L_1(g_{F_J})+\lambda M(F_J)
 &\le C_{s,\eta}K_F\Lambda_\lambda\exp(C_{s,\eta}\Lambda_\lambda).
 \end{aligned}                                             \tag{JC21}
$$

No inverse multiplier has disappeared. Every fixed lambda>0 and
fixed K_F<infinity has finite displayed costs. Their small-lambda
behavior still includes exp(C_s lambda^{-kappa}); no uniformity in
lambda or K_F is claimed.

For fixed frequency, j_{s,N}^2 increases with N to

$$
 j_{s,\infty}(\xi)^2=(1+\xi^2/c_s^2)^s.
$$

Monotone convergence in JC21 proves the EXACT endpoint-weighted
statement, valid for every fixed s<3/2:

$$
 \boxed{\quad
 \int_{\mathbb R}\log(2+|\tau|)
        (1+\tau^2/(4c_s^2))^s|\widehat g_F(\tau)|^2d\tau
 \le C_{s,\eta}K_F\Lambda_\lambda\exp(C_{s,\eta}\Lambda_\lambda).
 \quad}                                                    \tag{JC22}
$$

Since c_s is now fixed, this is equivalent to the H^{s,log} norm
claimed above. In particular s=1/2 is an ACTUAL arithmetic-profile
half-derivative plus its logarithmic Gamma weight, not merely an
unweighted H^{1/2} assertion. This endpoint alone is not used to
claim a trace or a physical derivative.

JC16 and the actual moment bound in JC21 also give

$$
 \boxed{\quad
 \|X\|_{H^s}^2
 \le C_{s,\eta}K_F\lambda^{-1}\Lambda_\lambda
                         \exp(C_{s,\eta}\Lambda_\lambda).
 \quad}                                                    \tag{JC23}
$$

One may identify an actual unbounded-multiplier source AFTER this
estimate: JC21 bounds F_J in the Hilbert form norm M+P for fixed
lambda>0. A weakly convergent subsequence has a limit F^(s) in V.
The bounded linear actual profile map H6->L2 sends that weak limit
to the strong L2 limit j_{s,infinity}(D/2)g_F, identified by JC22.
Thus F^(s) is actual and has this profile, with the same P and moment
bounds by weak lower semicontinuity. No unbounded source was used in
JC6 or JC7 before this domain conclusion, and no nullity of F^(s)
is asserted.

### 5. Consume s=1 in the ORIGINAL physical dilation

Choose s=1 in the preceding result. Then X is H1 on the full line
and beta(t)=g_F(t/2) satisfies

$$
 \int (1+\xi^2)\log(2+|\xi|)|\widehat\beta(\xi)|^2d\xi
       <\infty.                                          \tag{JC24}
$$

Let h(t)=sqrt(pi)exp(7t/2)F(pi exp t) for t>=0. The original source
identity is h=pi^{-7/4}X on that half-line, so h belongs to
H1(0,infinity). Its positive-half-line trace h(0) therefore exists.
We do NOT multiply X by P_+ in H1 or H^{1/2}.

For G_a=D_aF-F the exact VHD1 formula gives

$$
 h_{G_a}/a=[h(\cdot+a)-h]/a\longrightarrow h'
       \quad\hbox{in }L^2(0,\infty).                     \tag{JC25}
$$

This is the forward-translation derivative on the half-line; it
requires no zero boundary trace. The actual folded arithmetic action
is

$$
 \beta_{D_aF}(t)=e^{qa}\beta(|t|+a).
$$

By JC24, ordinary Fourier difference quotients converge to beta'
in the full LOGARITHMIC form. Restrict those quotients with P_+ or
P_- ONLY in that logarithmic form, where the owned cross-half-line
Carleman argument bounds both projections. It follows that

$$
 \beta_{G_a}/a\longrightarrow
       q\beta+\operatorname{sgn}(t)\beta'(t)
       \quad\hbox{in the logarithmic form}.              \tag{JC26}
$$

No derivative of a half-space indicator is inserted: the fixed cuts
combine the two translation quotients before taking their limits.
The expression on the right is even, as required by the actual
arithmetic profile convention.

Each G_a/a is ACTUAL and in V by the existing VHD1 membership result.
Apply W338's UPPER comparison to the difference of two such actual
quotients. It gives the bound

$$
 \mathcal P(H)\le C[\|\beta_H\|_{\log}^2+M(H)]
 \quad(H\in\mathcal V),                                 \tag{JC27}
$$

with all scale constants fixed; the bounded S(H) remainder is paid
by the original moment. By JC25--JC26 the quotients are Cauchy in
M+P. Closedness of the ORIGINAL positive form gives a limit A in V.
The M-coordinate limit h' identifies it uniquely with

$$
 A(x)=\frac72F(x)+xF'(x),                                 \tag{JC28}
$$

where the derivative is the actual weak derivative on (pi,infinity).
This proves JC2 in the original source norm, including its full
Gamma coordinate. W317 then pays every complete debit and both
metrics on the SAME quotient differences. For example the bounds
above give

$$
 M(A)+\mathcal P(A)
 \le C_\eta K_F(1+\lambda^{-1})\Lambda_\lambda\exp(C_\eta\Lambda_\lambda).
$$

The generator exists for this restricted branch, with its explicit
nonuniform multiplier cost.

### 6. Exact metric and complete-energy derivatives

Since h is H1 on the positive half-line, VHD1 implies

$$
 \left.\frac d{da}M(D_aF)\right|_{0+}=-|h(0)|^2,
$$

$$
 \left.\frac d{da}\mathcal H(D_aF)\right|_{0+}
     =6\mathcal H(F)-|h(0)|^2.                            \tag{JC29}
$$

The boundary terms come from the true moving original-domain
endpoint; none is suppressed. The complete quadratic form is
continuous in the V norm. JC2 consequently gives its derivative
2 Re E(F,A). GLOBAL mixed nullity gives

$$
 \left.\frac d{da}\mathfrak E(D_aF)\right|_{0+}
 =-\lambda M'(0+)+\mu\mathcal H'(0+)
 =6\lambda\mathcal H(F),                                \tag{JC30}
$$

because lambda=mu. Thus it is 6lambda on the unit source. The
boundary charges cancel in this SAME joint account, consistent with
the continuous multiplier C6 used in the regularity proof.

Finally Q_lambda(F,A)=0 and JC2 imply

$$
 0\le Q_\lambda(D_aF)=Q_\lambda(G_a)
     =a^2Q_\lambda(A)+o(a^2)=o(a).                       \tag{JC31}
$$

This consumes the stronger regularity in an original-source
variation and includes its full Gamma energy, original moment,
every prime power and both poles. It does not renormalize the
varied source or assert that the normalized dilation stays inside
the original moment ratio K_F.

This manuscript takes the selected matching GLOBAL-null representative
as an input; it does not assert the equality for every negative
minimum. Its dilation derivative is positive, not a contradiction
to its negative energy. The inverse-multiplier and K_F constants
remain nonuniform. Hence no improvement of VHR1, RH, or strict Robin
for all integers above 5040 is claimed by this branch result.


## The selected null obeys a weighted Laplace reciprocity

Reuse the actual mixed source identity W255, the odd complete kernel,
W317's continuous form and W326's finite-Gaussian core in the
[owned source account](suzuki2026screw.md). The null-direction mechanism
of W347/W354 and the [classical derivative family](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate)
are already available. The additional `repo-derived` application is
their constraint on the SAME MR11 representative, including its physical
tail. This is paper mathematics, without Lean certification or a
literature-priority claim.

Keep $m(x)=(x/\pi)^6$, $w=m-1$, $D=M-H$, and assume on the actual
complex domain $\mathcal V$ that

$$
Q_\lambda=\mathfrak E+\lambda D\ge0,\qquad
Q_\lambda(F)=0,\qquad \lambda>0.                 \tag{LR1}
$$

For each real $a$, put
$f_a(x)=e^{9a/2}e^{-e^{2a}x}$ and $z_a=f_a+f_{-a}$.
These fixed Gaussian features belong to $\mathcal V$.
W255 and oddness give
$\mathfrak E(z_a,f_b)=L_0(a,b)+L_0(-a,b)=0$ for every real $b$.
The owned core and form continuity extend this to every actual test.
Positive-semidefinite mixed nullity in LR1 consequently gives

$$
\mathfrak E(z_a,G)=0\ (G\in\mathcal V),\qquad
D(z_a,F)=0\quad(a\in\mathbb R).                 \tag{LR2}
$$

Define, without assuming ordinary unweighted integrability,

$$
L_F(s)=\int_\pi^\infty w(x)F(x)e^{-sx}dx,
\qquad \Re s>0.
$$

Weighted Cauchy--Schwarz pays every derivative locally in this half-plane.
With the real $z_a$ in the antilinear slot, LR2 is precisely
$e^{9a/2}L_F(e^{2a})+e^{-9a/2}L_F(e^{-2a})=0$.
The holomorphic identity theorem extends the positive-real identity to

$$
\boxed{L_F(s)=-s^{-9/2}L_F(1/s)\quad(\Re s>0).}   \tag{LR3}
$$

The power uses the right-half-plane principal branch. For an arbitrary
actual source, LR3 is equivalent to all the orthogonalities in LR2;
it does not imply LR1 or a negative energy.

### Pay the endpoints in the original moment

For $u=\Re s>0$ the original $M$ norm gives

$$
|L_F(s)|^2\le M(F)\int_\pi^\infty
\frac{w(x)^2}{m(x)}e^{-2ux}dx.
$$

Writing $x=\pi+t$ and $y=1+t/\pi$,
$(y^6-1)^2/y^6\le36(t/\pi)^2(1+t/\pi)^4$.
Thus, with a fixed constant independent of $F$,

$$
\begin{aligned}
|L_F(s)|&\le C\sqrt{M(F)}u^{-3/2}e^{-\pi u}
&& (u\ge1),\\
|L_F(s)|&\le C\sqrt{M(F)}s^{-3}e^{-\pi/s}
&& (0<s\le1,\ s\text{ real}).
\end{aligned}                                                    \tag{LR4}
$$

The second line consumes LR3. Its flatness at zero is not an analytic
extension across zero. An additional positive exponential $L^2$ moment
would give such an extension by Cauchy--Schwarz, forcing $L_F=0$ and
$F=0$ by Laplace uniqueness.

There is a stronger actual-source consequence. The
[radial-distribution correspondence](../Fourier/grafakosteschl2013radial.md#the-actual-weighted-source-in-nine-dimensions)
retains the original sixth moment and identifies LR3 with a Fourier
anti-eigenfunction in nine dimensions, in the sense of tempered
distributions. Its simultaneous spatial and Fourier gap gives

$$
F\ne0\quad\Longrightarrow\quad
\int_\pi^\infty e^{2\varepsilon\sqrt{x}}|F(x)|^2dx=\infty
\quad\text{for EVERY }\varepsilon>0.              \tag{LR5}
$$

This uses classical Fourier analytic uniqueness with the displayed
source conversion; it does not assume ordinary $L^2$ Hankel membership.
In particular a nonzero LR1 vector has neither compact physical support
nor a finite Gaussian representation. W326's form-norm approximation
by such features does not preserve an additional exponential moment.

### A real representative must continue changing sign

Every nonzero real source satisfying LR3 has both a positive set and
a negative set of positive measure beyond EVERY $R>\pi$. Here is the
classical positive-moment argument on this exact source.

Suppose $v=wF\ge0$ almost everywhere beyond some $R$. Split $L_F$
into its compact part and nonnegative tail. LR4 and monotone convergence
give $v\in L^1$ and $L_F(0)=\int v=0$. For $n\ge1$,

$$
\int_\pi^\infty v(x)
 \left(\frac{1-e^{-hx}}h\right)^n dx
=h^{-n}\sum_{j=0}^n(-1)^j\binom njL_F(jh)\longrightarrow0.
$$

On the tail the bracket increases to $x$ as $h\downarrow0$;
on the compact part dominated convergence applies. Hence all tail
moments are finite and
$\int_R^\infty x^nv\le R^n\int_\pi^R|v|$.
Nonzero tail mass beyond any $r>R$ would instead give a lower bound
$r^n\int_r^\infty v$, a contradiction as $n\to\infty$.
The tail therefore vanishes; the remaining compact source vanishes
by LR5. Apply the same argument to $-v$ to exclude the opposite sign.

### Keep the arithmetic sign and the selected source together

The reciprocal subspace is nontrivial even inside the actual
$\mathcal V$: the [published common-gap supplier and its source adaptation](burnol2002sonine.md#nonzero-actual-sources-with-the-matched-laplace-reciprocity)
give nonzero smooth examples. Thus LR3 is not a density argument that
forces $F=0$. Nor does it make the complete Weil form positive.

Centering by the older actual radical directions preserves the energy
but generally leaves this selected subspace. If $z\ne0$ is any actual
mixed-radical vector and $c\ne0$, LR1 gives $D(z,F)=0$ and therefore

$$
\mathfrak E(F+cz)=\mathfrak E(F),\qquad
Q_\lambda(F+cz)=\lambda|c|^2D(z)>0.                 \tag{LR6}
$$

The nonzero radical combination used to center a moment must consequently
not be treated as the same global-null source. A sign estimate must
control W359/W362's COMPLETE arithmetic form on this one constrained
source, or separately pay the change of constraints. No such estimate,
exclusion of the matched negative branch, RH or strict all-integer Robin
conclusion is obtained here.
