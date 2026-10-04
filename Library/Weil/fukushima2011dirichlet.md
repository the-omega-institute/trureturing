---
bibkey: fukushima2011dirichlet
authors: Masatoshi Fukushima, Yoichi Oshima, and Masayoshi Takeda
year: 2011
title: Dirichlet Forms and Symmetric Markov Processes, second revised and extended edition
doi: 10.1515/9783110218091
url: https://doi.org/10.1515/9783110218091
claim: The symmetric-kernel construction and regular minimal-extension theorem apply to the actual continuous-plus-prime-graph theta energy in the pole measure. They supply its minimal closed realization, not the one-half variance lower bound or equality with the maximal domain.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# The minimal mixed theta jump form

## Source contract

The inspected source is an [HTML reproduction of the second edition](https://dokumen.pub/dirichlet-forms-and-symmetric-markov-processes-2nd-rev-and-ext-ed-9783110218091-9783110218084.html),
whose title page gives print ISBN 9783110218084 and electronic ISBN
9783110218091. Some reproduced mathematical markup is damaged; the legible
operator-domain characterization below is used instead of transcribing the
unreadable square-root display. No publisher PDF was retrieved.

The source is Fukushima–Oshima–Takeda, second revised and extended edition,
Example 1.2.4, printed pp.14–15, conditions (j.1)–(j.3) and equations
(1.2.22)–(1.2.25), together with Theorem 3.1.2, printed p.110.
The first construction permits a measurable destination kernel $j(x,dy)$,
including atoms, when $m(dx)j(x,dy)$ is symmetric, its off-$\varepsilon$
rates are locally integrable and its local small-jump second moment is
finite. More explicitly, (j.1) is
$x\mapsto j(x,X\setminus U_\varepsilon(x))\in L^1_{\rm loc}(m)$ for
every $\varepsilon>0$, (j.2) is symmetry of $m(dx)j(x,dy)$, and (j.3)
is the finite $|x-y|^2$ moment on every compact $K\times K$.
Its maximal finite-energy domain is closed when it is dense in $L^2(m)$. The regular
minimal-extension theorem has separate algebra, cutoff and Markov
hypotheses; it does not automatically equate that extension to the maximal
domain.

Theorem 3.1.2 assumes a closable nonnegative Markovian symmetric form on
$L^2(X;m)$, with $X$ locally compact separable metric and $m$ a full-support
positive Radon measure. Its initial domain must be a uniformly dense
subalgebra of compactly supported continuous functions, admitting a
nonnegative cutoff equal to one on any compact $K$ and zero outside any
relatively compact open $G$ containing $K$. The conclusion is a regular
minimal closed extension with that initial domain as a special standard
core. The theorem's additional locality assertion is conditional on the
initial form being local and is not invoked for this jump form.

Theorem 1.3.1, printed p.20, and Corollary 1.3.1, printed p.21,
equation (1.3.10), give the unique associated self-adjoint generator $A$:
$D(A)\subset D[\mathcal E]$ and
$\mathcal E(u,v)=(-Au,v)$ for $u\in D(A)$ and $v\in D[\mathcal E]$.
We use the nonnegative convention $T=-A$.

## The exact energy, speed and graph atoms

Use the [theta-weighted even Weil interface](lagarias2004li.md), with
$\rho(x)=2\Phi(x)\cosh(x/2)$ and $d\nu=\rho(x)\,dx$.
The original positive smooth even $\Phi$ makes $\nu$ a full-support Radon
probability, equivalent to Lebesgue measure. Put
$\psi(t)=e^{-t/2}/(1-e^{-2t})$ and
$w_n=\Lambda(n)/\sqrt n$, retaining every prime power.
The actual conductance measure off the diagonal is

$$
\begin{aligned}
J_\Gamma(dx,dy)&=\Phi(x)\Phi(y)\psi(|x-y|)\,dx\,dy,\\
J_p(dx,dy)&=\sum_{n\ge2}w_n\Phi(x)\,dx\,
\left[\Phi(x+\log n)\delta_{x+\log n}(dy)
+\Phi(x-\log n)\delta_{x-\log n}(dy)\right].
\end{aligned}
$$

With $J=J_\Gamma+J_p$, the real preform is exactly

$$
D(h)=\tfrac12\iint |h(y)-h(x)|^2J(dx,dy)
=E_\Gamma(h)+E_{\rm prime}(h).
$$

FOT (1.2.23) has no prefactor one-half. Its conductance measure must
therefore be $J_{\rm FOT}=J/2$, with $m=\nu$. The corresponding measurable
destination kernel, set to zero on the diagonal, is exactly

$$
j_{\rm FOT}(x,dy)=\frac1{4\cosh(x/2)}
\left[\Phi(y)\psi(|x-y|)\,dy
+\sum_{n\ge2}w_n\left(
\Phi(x+\log n)\delta_{x+\log n}(dy)
+\Phi(x-\log n)\delta_{x-\log n}(dy)\right)\right].
$$

Thus $\nu(dx)j_{\rm FOT}(x,dy)=J(dx,dy)/2$ preserves the normalization.
Translation exchanges the two prime graphs, so $J$ is symmetric. The
continuous part and each integrated graph marginal charge no $\nu$-null
set. This is not pointwise absolute continuity of $j(x,\cdot)$: that would
exclude the actual atoms.

## The integrability checks retain all long edges

[Romik's theta tail](../Analytic/romik2021orthogonal.md) gives
$\Phi(x)\le Ce^{-2|x|}$. Thus, for $t\ge0$,

$$
C_\Phi(t):=\int\Phi(x)\Phi(x+t)\,dx
\le C^2(t+\tfrac12)e^{-2t}.
$$

The actual global second jump moment is finite:

$$
M_2:=\iint |x-y|^2J(dx,dy)
=2\int_0^\infty t^2\psi(t)C_\Phi(t)\,dt
+2\sum_{n\ge2}w_n(\log n)^2C_\Phi(\log n)<\infty.
$$

At zero use $C_\Phi(t)\le\|\Phi\|_2^2$ and
$\psi(t)\sim(2t)^{-1}$; at infinity use exponential decay. For the prime
part, $\Lambda(n)\le\log n$ gives the summable majorant
$C(\log n)^3(\log n+1/2)n^{-5/2}$, without PNT or RH.
Off any fixed diagonal band the total $J$ mass is finite, and the row
prime sums are uniformly finite on compact $x$ sets, since
$\Phi(x\pm\log n)\le C_Kn^{-2}$ there.
The Gamma row rate at the diagonal is infinite; these hypotheses concern
off-diagonal mass and square differences, not a finite total Gamma rate.

In particular every compact Lipschitz $h$ has
$D(h)\le\operatorname{Lip}(h)^2M_2/2$.
Use compact Lipschitz functions as the uniformly dense algebra for the
minimal-extension theorem: this domain is closed under unit clipping and
admits the required compact-set/open-set cutoffs. Compact smooth functions
are not literally closed under that clipping.

They have the same form closure here. For compact Lipschitz $h$, ordinary
mollification gives compact smooth $h_\varepsilon$ with common support
in a slightly larger compact set, uniform convergence and
$\operatorname{Lip}(h_\varepsilon)\le\operatorname{Lip}(h)$.
The difference increments converge pointwise and their squares are
bounded by $4\operatorname{Lip}(h)^2|x-y|^2$. Dominated convergence using
$M_2$ gives $D(h_\varepsilon-h)\to0$; the $L^2(\nu)$ error also tends to
zero. This verifies the smooth-core interface rather than assuming
clipping preserves smoothness.

## Minimal closure, constants and the even restriction

Let $\mathcal F_{\max}=\{h\in L^2(\nu):D(h)<\infty\}$ and

$$
\mathcal F_{\min}
=\overline{C_c^\infty(\mathbb R)}^{\,\|\cdot\|_{D,1}},
\qquad \|h\|_{D,1}^2=\|h\|_{L^2(\nu)}^2+D(h).
$$

The preceding smooth inclusion makes the maximal domain dense in $L^2(\nu)$.
The source construction supplies a closed maximal form and a regular
minimal form with $\mathcal F_{\min}\subseteq\mathcal F_{\max}$.
The initial compact Lipschitz form is closable as a restriction of that
closed maximal form, so the minimal-extension theorem applies. Equality
of the minimal and maximal domains is not used or asserted.
For $0\le\chi\le1$ even compact smooth and one on $[-1,1]$, put
$\chi_R(x)=\chi(x/R)$. Then

$$
\|\chi_R-1\|_{L^2(\nu)}\to0,
\qquad D(\chi_R)\le\frac{\|\chi'\|_\infty^2M_2}{2R^2}\to0.
$$

Thus $1\in\mathcal F_{\min}$ with zero energy, including all prime tails.
Reflection preserves both $\nu$ and $J$. Averaging a function with its
reflection is contractive in the form norm and preserves the smooth
core, hence

$$
\overline{C_{c,\rm even}^\infty}^{\,\|\cdot\|_{D,1}}
=\mathcal F_{\min}\cap L^2_{\rm even}(\nu).
$$

Complexification gives the even complex closed realization in that even
Hilbert space. It is not claimed densely defined on the full non-even
Hilbert space. Denote its associated nonnegative self-adjoint operator by $T$.
The cited representation gives

$$
h\in D(T)\iff h\in\mathcal F_{\min,\rm even}
\text{ and }D(h,g)=\langle u,g\rangle_\nu
\text{ for some }u\in L^2_{\rm even}(\nu)
\text{ and every }g\in\mathcal F_{\min,\rm even},
\qquad Th=u.
$$

The energy and speed measure are the original ones. Here the pairing is
linear in its first argument and $D(h,g)$ is the polarized complex form.

This is a source application and model-specific verification, without new
Lean certification or an originality claim. The source supplies no
one-half Poincare constant or spectral description. The same-test target
$D(h)\ge\operatorname{Var}_\nu(h)/2$, hence RH and full Robin, remains
unproved. The minimal realization suffices for the compact-test target;
no stronger maximal-domain core equality is a prerequisite.

## Weighted Fourier cutoff and a complete finite cosine family

The [sharp-band center interface](../../docs/reports/theta-mixed-matrix/sharp-center.md)
uses the same even minimal realization and full operator with the later
high-block gap. It supplies actual operator-domain cosine columns and
an analytic approximation of their complete Schur center. A prescribed
rank at most 96 pays a 1/16 center remainder at $c=3/8$; retained matrix
positivity, high residuals and cofinal control remain unresolved.

Use (JE), (BT), (JF) and (JR) from the
[same-form exterior analysis](lenz2010compactness.md). This alternative
to the translated-kernel mesh retains the original minimal realization,
full measure and complete operator. Write $A=T$ for its even operator
above and $P_\varepsilon=\mathbf1_{[0,1/2-\varepsilon]}(A)$.
The
[original-series coefficient suppliers](../Analytic/romik2021orthogonal.md)
give $s\in H^3(\mathbb R)$, bounded $s,s'$, and
$\sum_{n\ge2}\|b_n'\|_\infty<\infty$ for

$$
Uh=\sqrt\rho\,h,\qquad s=\sqrt{\Phi/(2\cosh(x/2))},\qquad
b_n(x)=w_ns(x)s(x+\log n).
$$

These are paper-level model deductions from the cited inputs. They
provide a prescribed finite map with uniform form error on each whole
fixed-gap spectral subspace. They do not certify a matrix sign, useful
numerical size, cofinal bound, originality or new Lean result.

### Transformed form and a global derivative comparison

Write $\|h\|_{\mathcal F}^2=\|h\|_\nu^2+D(h)$ and transport this norm
by $U$. Formula (JE) gives exactly

$$
\widetilde D(v)=\tfrac12\|v\|_2^2+G_{\rm flat}(sv)
 +c_\Gamma\|sv\|_2^2-\langle Bv,v\rangle,\qquad -8<c_\Gamma<0,
\quad B=\sum_{n\ge2}(M_{b_n}\tau_n+(M_{b_n}\tau_n)^*). \tag{WF1}
$$

Every prime power and shifted adjoint remains present. Let
$M_2=\int_0^\infty t^2\psi(t)dt
=\sum_{k\ge0}2/(2k+1/2)^3$. Translation differences and
$|a+b|^2\le2|a|^2+2|b|^2$ give, for even $v\in H^1(\mathbb R)$,

$$
\begin{aligned}
\|U^{-1}v\|_{\mathcal F}^2
&\le c_0\|v\|_2^2+c_1\|v'\|_2^2,\\
c_0&=\tfrac32+\|B\|+2M_2\|s'\|_\infty^2,\qquad
c_1=2M_2\|s\|_\infty^2.
\end{aligned} \tag{WF2}
$$

The negative $c_\Gamma$ term is dropped only for this upper bound.
Compact smooth even approximants, with (WF2) applied to their
differences, put $U^{-1}v$ in the actual minimal form domain. Neither a
compact minimum density nor an identification with a maximal domain is
used.

### High-frequency coercivity and the scalar deficit

Use the unitary Fourier convention. The flat multiplier is

$$
\begin{aligned}
m(\xi)&=2\sum_{k\ge0}\frac{\xi^2}{a_k(a_k^2+\xi^2)},
\qquad a_k=2k+\tfrac12,\\
\tfrac12\log|\xi|-1&\le m(\xi)
\le16(1+\log(1+|\xi|))\qquad(|\xi|\ge1).
\end{aligned} \tag{WF3}
$$

The symbol is nonnegative and increasing in $|\xi|$; its upper bound
also holds below one. For $X=|\xi|\ge1$ and
$K=\lfloor(X-1/2)/2\rfloor$, retaining $a_k\le X$ gives
$m(X)\ge\sum_{k=0}^K1/a_k
\ge\tfrac12\log(4K+5)\ge\tfrac12\log(2X)$.
The complementary split and inverse-cubic tail give
$m(X)\le4+\log(2X)+2/X+1/2\le13/2+\log(2X)$,
which implies the displayed upper bound; monotonicity covers $X<1$.

Define the complete symmetric row and its comparison potential by

$$
R_B(x)=\sum_{n\ge2}(b_n(x)+b_n(x-\log n)),\qquad
W(x)=\tfrac12+c_\Gamma s(x)^2-R_B(x).
$$

The symmetric graph inequality yields
$|\langle Bv,v\rangle|\le\int R_B|v|^2$.
The coefficient estimate underlying (BT) bounds the sum of both
coefficient supremum bounds outside $[-R,R]$ by $b_R^*$.
Thus $R_B(x)\le b_R^*$ there; this is a row estimate, rather than an
inference from the operator norm. With $p_R$ from (JL),
$W\ge1/2-d_R$ outside that interval. For $0<\varepsilon\le1/2$ set

$$
\beta=\tfrac12-\varepsilon/2,\qquad
\mu_\varepsilon=\sup_x
\frac{(\beta-W(x))_+}{s(x)^2}<\infty. \tag{WF4}
$$

For example, $R\ge\tfrac12\log((8/3)\log(320/\varepsilon))$
makes $d_R\le\varepsilon/2$. The numerator then vanishes outside
that interval, while positivity and continuity of $s$ bound the quotient
inside. This deficit uses the same theta row tail as (JL), without a
quantitative prime-counting remainder; it does not remove the PNT input
from the earlier model construction.

If $\widehat v$ is supported in $|\xi|\ge N$, Young's inequality and
Cauchy–Schwarz on the Fourier tail of $s$ give

$$
\|\mathbf1_{|\mathsf D|<N/2}sv\|_2\le\eta_N\|v\|_2,
\qquad \eta_N\le\sqrt{\frac8{3\pi}}N^{-3/2}\|s''\|_2. \tag{WF5}
$$

Indeed, the Fourier convolution bound is
$(2\pi)^{-1/2}\|\mathbf1_{|\omega|>N/2}\widehat s\|_1$;
use $\omega^{-2}$ in Cauchy–Schwarz. Consequently

$$
\widetilde D(v)\ge
\int(m(N/2)s^2+W)|v|^2
-m(N/2)\eta_N^2\|v\|_2^2.
$$

For $a=1/2-\varepsilon$, the conditions
$m(N/2)\ge\mu_\varepsilon$ and
$m(N/2)\eta_N^2\le\varepsilon/4$ give a high-frequency lower
bound $a+\varepsilon/4$. An explicit sufficient threshold is

$$
N\ge N_0(\varepsilon):=
\max\left\{2e^{2\mu_\varepsilon+2},
\sqrt{\frac{512}{3\pi\varepsilon}}\|s''\|_2,2\right\}. \tag{WF6}
$$

Formula (WF3) supplies the first condition. For the second, use
$m(N/2)\le16N$ for $N\ge2$ in (WF5). This threshold is sufficient;
direct symbol and leakage bounds can permit smaller bandwidths.

The [direct actual-theta supplier](../../docs/reports/theta-mixed-matrix/derivative-bandwidth.md)
verifies both conditions at $\varepsilon=1/4$, $N=64$, without claiming
that this meets the coarse displayed $N_0$ formula. The
[joint full-row floor](../../docs/reports/theta-mixed-matrix/joint-high-floor.md)
further gives $\widetilde D\ge0.4133682545007734\|v\|_2^2$ on the
even high-frequency restriction, above $c=3/8$. Its positive variance
gap retains the complete operator and mean term. The low-frequency block
and its coupling still require estimation.

### The full Fourier commutator and the whole projector

Fix a real even $p\in C_c^\infty(\mathbb R)$ with $0\le p\le1$,
$p=1$ on $[-1,1]$ and $p=0$ outside $[-2,2]$. Put
$p_N=p(\mathsf D/N)$, $Q_N=I-p_N$, $L_p=\|p'\|_\infty$ and
$C_p=\int|x||\check p_0(x)|dx$, where $\check p_0$ is the inverse
transform normalized by $(2\pi)^{-1}$.
On the even core (WF1) has operator
$M_sm(\mathsf D)M_s+M_{1/2+c_\Gamma s^2}-B$.

Translations commute with $p_N$, so the full prime commutator has bound
$2C_pN^{-1}\sum_n\|b_n'\|_\infty$, including shifted adjoints.
The potential commutator has bound
$8C_pN^{-1}\|(s^2)'\|_\infty$. For the principal double Fourier
kernel put $u=\xi-\zeta$, $v=\zeta-\eta$. A nonzero cutoff difference
implies $\min\{|\xi|,|\eta|\}\le2N$, and its Lipschitz bound and
(WF3) give, for $N\ge2$,

$$
m(\zeta)|p(\eta/N)-p(\xi/N)|
\le\frac{32L_p(1+\log N)}N
(1+|u|)(1+\log(1+|u|))
(1+|v|)(1+\log(1+|v|)).
$$

For $F(\omega)=(1+|\omega|)(1+\log(1+|\omega|))
|\widehat s(\omega)|$, Cauchy–Schwarz gives
$(2\pi)^{-1/2}\|F\|_1\le\sqrt2\|s\|_{H^3}$.
One sufficient integral estimate uses
$\log(1+t)\le\sqrt t$, $(1+t)^2\le2(1+t^2)$ and
$(1+\sqrt t)^2\le2(1+t)$, giving a bound $2\pi+4<4\pi$.
Two Young inequalities give a principal bound with coefficient $64$;
the following retains the conservative coefficient $128$:

$$
\begin{aligned}
\|[\widetilde A,p_N]\|&\le\kappa_N
:=K_p\frac{1+\log N}{N},\\
K_p&=128L_p\|s\|_{H^3}^2+
C_p\left(8\|(s^2)'\|_\infty+
2\sum_n\|b_n'\|_\infty\right).
\end{aligned} \tag{WF7}
$$

All coefficient hypotheses are supplied by (WC1)–(WC5) in the linked
original-series note. No derivative of the separate prime diagonal or
regularity assumption on unknown spectral vectors enters this estimate.

At fixed $N$, $p_N:L^2\to H^1$, and (WF2) bounds its output in the
actual minimal form norm by $(c_0+4N^2c_1)^{1/2}$ times the input norm.
Core approximation therefore extends the bounded form commutator to
that minimal domain. The operator representation of the form gives
$p_ND(\widetilde A)\subset D(\widetilde A)$ and the displayed bounded
operator commutator there. This establishes the Fourier domain passage
without an operator-core or maximal-domain identification.

Let $P=UP_\varepsilon U^{-1}$, $\mathcal L=\operatorname{ran}P$ and
$A_\mathcal L=\widetilde A|_\mathcal L$. Restrict the closed form to
even functions supported in $|\xi|\ge N$ in Fourier space, and denote
its associated operator by $C_N$. Even $H^1$ functions with bounded
Fourier support in that set give density. By (WF6),
$C_N\ge a+\varepsilon/4$. Since $Q_N\mathcal L\subset D(C_N)$,
restriction of the full operator identity yields

$$
C_NQ_N|_\mathcal L-Q_N|_\mathcal L A_\mathcal L
=\mathbf1_{|\mathsf D|\ge N}[\widetilde A,Q_N]|_\mathcal L.
$$

Reuse the separated-spectra semigroup argument of (LP) to obtain
$\|Q_NP\|\le4\kappa_N/\varepsilon$.
Because $A_\mathcal L$ preserves the whole subspace, the same form
estimate as (JF) then gives

$$
\begin{aligned}
\|Q_NP\|_{L^2\to\widetilde{\mathcal F}}^2
&\le\kappa_N^2\left(\frac{16(1+a)}{\varepsilon^2}
 +\frac4\varepsilon\right)
\le\frac{26\kappa_N^2}{\varepsilon^2},\\
\|(I-U^{-1}p_NU)P_\varepsilon\|_{L^2(\nu)\to\mathcal F}
&\le\frac{6K_p}{\varepsilon}\frac{1+\log N}{N}.
\end{aligned} \tag{WF8}
$$

This is a bound for the entire fixed-gap subspace, with no scalar
eigenvalue assigned to a spectral mixture.

### Spatial multiplier and prescribed finite cosine generators

Let $\chi_R=1-\eta_R$ be the real even smooth cutoff of (JR).
It is one on $[-R,R]$, zero outside $[-R-2,R+2]$, between zero and
one, and Lipschitz with constant at most one. Put
$J=\int_0^\infty\psi(t)\min\{t^2,1\}dt$.
The existing short- and long-jump estimates give
$J\le3/4+2e^{-1/2}/(1-e^{-2})<9/4$.
For example, $e^2>7$ and $e>8/3$ give the strict upper bound
$3/4+35/24=53/24<9/4$.

The product difference yields
$G_{\rm flat}(\chi_Rf)\le2G_{\rm flat}(f)+2J\|f\|_2^2$.
Use this in the same (WF1), retaining complete $B$ and dropping the
negative $c_\Gamma$ term only for the upper bound. Since
$\|B\|\le216/5$ and $\|s\|_\infty^2\le9/5$,

$$
\begin{aligned}
\|\chi_Rh\|_{\mathcal F}^2
&\le2D(h)+\left(\tfrac12+3\|B\|
 +(16+2J)\|s\|_\infty^2\right)\|h\|_\nu^2\\
&\le2D(h)+167\|h\|_\nu^2
\le169\|h\|_{\mathcal F}^2.
\end{aligned} \tag{FF1}
$$

Core approximation extends this multiplier to the actual minimal
domain. Thus $\|M_{\chi_R}\|_{\mathcal F\to\mathcal F}\le13$,
independently of $R$.

Fix $0<\varepsilon\le1/2$, $0<\tau\le1$, and choose exactly

$$
R=\max\left\{2,\tfrac12\log\left(\tfrac83
\log\frac{728}{\varepsilon\tau}\right)\right\}. \tag{FF2}
$$

Then (JF)–(JR) give
$\|(I-M_{\chi_R})P_\varepsilon\|_{\nu\to\mathcal F}
\le\sqrt7\,\tau/8<\tau/3$.
For $N\ge N_0(\varepsilon)$ put

$$
X_R=\|x\chi_R\|_2,\qquad
Y_R=\|\chi_R+x\chi_R'\|_2,\qquad
K_{R,N}^2=(c_0+4N^2c_1)X_R^2+c_1Y_R^2. \tag{FF3}
$$

Partition $[0,2N]$ into $m=\lceil2N/\Delta\rceil$ equal cells $I_j$,
with midpoints $\xi_j$ and width at most $\Delta$. Define

$$
\begin{aligned}
\varphi_j(x)&=\frac{\chi_R(x)}{\sqrt{\rho(x)}}\cos(\xi_jx),\\
c_j(h)&=\frac2{\sqrt{2\pi}}\int_{I_j}
 p(\xi/N)\widehat{Uh}(\xi)d\xi,\qquad
Vh=\sum_{j=1}^mc_j(h)\varphi_j.
\end{aligned} \tag{FF4}
$$

The generators lie in the original compact smooth even core, because
$\rho$ is positive smooth and even on their support. The Fourier cell
integrals are bounded linear functionals, with
$\|c_j\|\le\sqrt{|I_j|/\pi}$; point values of an arbitrary $L^2$
transform are not required. The map is complex linear with real
generators. For complex even $Uh$, its Fourier transform is even,
without conjugation, giving the factor two in (FF4).

For the even generator $g_\xi=U^{-1}(\chi_R\cos(\xi x))$, put
$a_x=x\chi_R$ and $b_x=\chi_R+x\chi_R'$. The weighted frequency
derivative $-a_x\sin(\xi x)$ is even. The pointwise identity

$$
(b_x\sin(\xi x)+\xi a_x\cos(\xi x))^2+
(b_x\cos(\xi x)-\xi a_x\sin(\xi x))^2=b_x^2+\xi^2a_x^2
$$

and the even comparison (WF2) give
$\|\partial_\xi g_\xi\|_{\mathcal F}^2
\le c_0X_R^2+c_1(Y_R^2+\xi^2X_R^2)\le K_{R,N}^2$
for $|\xi|\le2N$. The second square is used only in this algebraic
identity; no odd-form comparison is applied.
Midpoint displacement is at most $\Delta/2$, and positive frequencies
carry half the squared Fourier norm. The Bochner triangle inequality
and Cauchy–Schwarz therefore give

$$
\|M_{\chi_R}U^{-1}p_NU-V\|_{\nu\to\mathcal F}
\le\Delta K_{R,N}\sqrt{N/(2\pi)}. \tag{FF5}
$$

Combine (FF1), (WF8), (FF2), and (FF5) on the same original projector:

$$
\|(I-V)P_\varepsilon\|_{\nu\to\mathcal F}
\le\frac{\sqrt7}{8}\tau+
\frac{78K_p}{\varepsilon}\frac{1+\log N}{N}
+\Delta K_{R,N}\sqrt{N/(2\pi)}. \tag{FF6}
$$

Make the count-producing choices exact:

$$
\delta=\min\left\{\tfrac14,\frac{\varepsilon\tau}{234K_p}\right\},
\qquad N=\max\{N_0(\varepsilon),2\delta^{-1}\log(2/\delta)\},
\qquad \Delta=\frac{\tau\sqrt{2\pi/N}}{3K_{R,N}}. \tag{FF7}
$$

The second and third errors in (FF6) are each at most $\tau/3$,
while the first is strictly smaller. For the bandwidth estimate set
$L=\log(2/\delta)$ and use $\log L\le L-1$ and monotonicity of
$(1+\log N)/N$ on $N\ge1$. Thus the total error is $<\tau$, and

$$
\operatorname{rank}V\le m
\le1+\frac{6K_{R,N}N^{3/2}}{\tau\sqrt{2\pi}}. \tag{FF8}
$$

For fixed $\varepsilon$, all coefficient constants and
$N_0(\varepsilon)$ are independent of $\tau$. These exact choices give
$N=O_\varepsilon(\tau^{-1}\log(e/\tau))$,
$R=O_\varepsilon(\log\log(e^e/\tau))$, and
$K_{R,N}=O(N(R+2)^{3/2})$. Hence the prescribed generator count is

$$
O_\varepsilon\!\left(\tau^{-7/2}\log(e/\tau)^{5/2}
\log\log(e^e/\tau)^{3/2}\right)\qquad(\tau\downarrow0).
$$

This controls accuracy dependence, not actual feasible size or matrix
conditioning. With $\tau=\varepsilon/8$, PSD of the complete original
form/full-variance matrix on these generators at
$c_\varepsilon=1/2-\varepsilon/2$ feeds the existing
[complete-window transfer (MT)](jarohsweth2020local.md).
Its entries, signs and cofinal $\varepsilon\downarrow0$ certificates
remain uncomputed. The translated-kernel/FIB construction retains its
own margin and floor conditions. This cosine construction supplies no
arithmetic advantage from relabeling frequency cells by FIB addresses.
