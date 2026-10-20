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

The [sharp-band center interface](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/sharp-center.md)
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

The [direct actual-theta supplier](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/derivative-bandwidth.md)
verifies both conditions at $\varepsilon=1/4$, $N=64$, without claiming
that this meets the coarse displayed $N_0$ formula. The
[joint full-row floor](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/joint-high-floor.md)
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


## Ordered-transition hypotheses must be checked separately

The [Karlin–McGregor source application](karlinmcgregor1959coincidence.md)
tests the unchanged minimal even semigroup in radial order. Three
separated nonnegative core functions give a strictly negative ordered
two-by-two bilinear minor for all sufficiently small positive times.
The Gamma conductance alone supplies the crossing. Thus the inherited
positivity preservation does not supply all-times order-two positivity
for a spectral-ordering argument. This paper application retains every
prime power and supplies no sharp Poincare or RH conclusion.

## Even polynomials in the same minimal form norm

The following is a paper application of the existing theta tail,
cutoff and Fourier-approximation estimates, without a new generic
density theorem, originality claim or Lean certification. It concerns
the unchanged $J$, $\nu$ and $\mathcal F_{\min,\rm even}$ above. The
[Fourier/Laurent core at bounded support](connesconsanimoscovici2026spectral.md)
belongs to a different realization and is not used as a core theorem
for this domain. The project's finite polynomial Mellin windows likewise
do not establish density in this form norm.

First let $h$ be smooth, with
$|h(x)|+|h'(x)|\le C e^{a|x|}$ for some fixed $C,a>0$.
The [original theta bound](../Analytic/romik2021orthogonal.md#weighted-fourier-coefficient-suppliers)
implies, for every fixed $0<b<\pi$,
$\Phi(x)\le C_b\exp(-b e^{2|x|})$. In particular
$h\in L^2(\nu)$. For Gamma jumps $0<t<1$, the square increment is
bounded by $C_a t^2 e^{2a|x|}$; boundedness of $\Phi(x+t)$ and
integrability of $e^{2a|x|}\Phi(x)$ pay the diagonal singularity.
For $t\ge1$, use the two separate bounds
$|h(x+t)-h(x)|^2\le2C^2(e^{2a|x|}+e^{2a|x+t|})$ and
$\psi(t)\le C e^{-t/2}$. The resulting double integral is finite.

For the prime shifts put $t=\log n$ and
$S=e^{2|x|}+e^{2|x+t|}$. Absorbing the fixed exponential growth into
the two theta tails gives, with a fixed $b>0$,

$$
\begin{aligned}
\Phi(x)\Phi(x+t)|h(x+t)-h(x)|^2
&\le C_a e^{-bS}\\
&\le C_a e^{-bn}\exp\!\left(-\tfrac b2e^{2|x|}\right),
\qquad S\ge2n. \tag{PC1}
\end{aligned}
$$

The final factor is integrable in $x$; multiplication by
$\Lambda(n)/\sqrt n\le\log n/\sqrt n$ leaves a summable series.
Thus (PC1) pays every prime power, rather than integrating a constant
over an infinite line. The same majorants, with constants uniform in
$R\ge1$, apply to $(1-\chi_R)h$ and its derivative. Their increments
tend pointwise to zero. Dominated convergence yields
$\chi_Rh\to h$ in the original form norm, hence
$h\in\mathcal F_{\min}$. Even $h$ lies in its even restriction.

Next fix $h\in C_{c,\rm even}^\infty$. Choose an even smooth Fourier
cutoff $\eta$ supported on $[-1,1]$, equal to one near zero, and put

$$
h_A(x)=\frac1{2\pi}\int_{-A}^A
\eta(\xi/A)\widehat h(\xi)e^{i\xi x}\,d\xi.
$$

Fourier inversion and integrability of $\widehat h$ and
$\xi\widehat h$ give uniform convergence of $h_A$ and $h_A'$ to
$h$ and $h'$. Each $h_A$ is even and entire, with bounded function
and derivative on the real line, so the preceding cutoff argument
puts it in the same minimal domain. The global second moment gives
directly, also for these noncompact Lipschitz differences,

$$
D(h_A-h)\le\tfrac12M_2\|h_A'-h'\|_\infty^2\longrightarrow0.
\tag{PC2}
$$

For fixed $A$, let $p_{A,N}$ be the Taylor polynomial of $h_A$ through
degree $2N$. Odd coefficients vanish. Termwise integration of the
finite Taylor sum, and then the exponential series, give

$$
|p_{A,N}(x)|\le C_A e^{A|x|},\qquad
|p_{A,N}'(x)|\le A C_A e^{A|x|},
$$

uniformly in $N$. Both polynomials and their derivatives converge
pointwise to $h_A$ and $h_A'$. The complete Gamma and prime majorants
above therefore show $p_{A,N}\to h_A$ in the same form norm.
Combining this with (PC2) and the established compact smooth even core
shows that even polynomials are form-dense in
$\mathcal F_{\min,\rm even}$.

For $j,k\ge1$ define the original finite matrices

$$
H^{(m)}_{jk}=D(x^{2j},x^{2k})
-\tfrac12\left[\nu(x^{2j+2k})-\nu(x^{2j})\nu(x^{2k})\right],
\qquad 1\le j,k\le m.
$$

Constants have zero energy and variance. Continuity in the original
form norm consequently makes the full half-bound equivalent to
$H^{(m)}\succeq0$ for **every** $m$. The
[two-direction polynomial certificate](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/theta-polynomial-energy-bounds.md)
only addresses $m=2$. No all-degree PSD result, effective exhaustion
rate, uniformly conditioned polynomial basis or RH/Robin conclusion
is supplied by this density argument.

## Quantitative polynomial approximation by published weighted estimates

The [weighted Favard and Brascamp–Lieb application](../Analytic/itoh2015weightedapproximation.md)
uses (WF2), the original coefficient suppliers and the same full
fixed-gap spectral map to obtain a conditional polynomial approximation
in this minimal form norm. It projects the physical derivative in an
admissible auxiliary weight and integrates that one projection; it does
not treat a Fourier cutoff of $Uh$ as a physical-bandlimited input.
For fixed $\varepsilon$, its prescribed dimension has asymptotic cost
$O_\varepsilon(\tau^{-3}\log(e/\tau)^5)$, with unevaluated external
Favard constant. This is an application of published approximation
and variance inequalities, not a new generic core theorem or a numerical
rank certificate. Original matrix positivity and cofinal control remain
unproved, so it supplies no RH or Robin conclusion.

## The sharp pointwise gradient route fails on the original core

This is a conditional paper check of a sufficient semigroup mechanism,
using the same minimal even form, original measure and all prime powers.
It reuses the Markov semigroup's invariance, the
[existing critical eigenvector](lagarias2004li.md#the-full-derivative-family-and-the-remaining-estimate)
and the [original PNT rate argument](lenz2010compactness.md#exact-prime-diagonal-and-bounded-off-diagonal-operator). It supplies no new
generic curvature theorem, numerical acquisition or Lean certification.

Write $L=-T$, $P_t=e^{-tT}$, and for a real even form input define its
jump energy density

$$
\mathcal G(h)(x)=\frac1{4\cosh(x/2)}\left[
 \int\Phi(y)\psi_\Gamma(|x-y|)|h(y)-h(x)|^2dy
 +\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 \sum_{\epsilon=\pm1}\Phi(x+\epsilon\log n)
 |h(x+\epsilon\log n)-h(x)|^2\right]. \tag{SG1}
$$

The diagonal integral uses squared increments, not a finite total jump
rate. Tonelli gives $\int\mathcal G(h)d\nu=D(h)$; in particular this
nonnegative function lies in $L^1(\nu)$. The original minimal jump
representation supplies its almost-everywhere value on the form domain.

Consider the sharp pointwise semigroup estimate

$$
\mathcal G(P_t h)\le e^{-t}P_t\mathcal G(h)
\quad\nu\text{-almost everywhere},\qquad t>0, \tag{SG2}
$$

for every real even compact smooth $h$. The semigroup on the right
uses its invariant $L^1(\nu)$ extension. This is the explicit estimate
being tested. It is a standard sufficient gradient route toward a
one-half Poincare inequality; no diffusion chain rule is assumed and
no equivalence to a curvature condition on an unspecified algebra is
claimed for this jump operator.

First transport (SG2) through the existing minimal closure. The actual
increment representation and Cauchy--Schwarz give

$$
\|\mathcal G(f)-\mathcal G(g)\|_{L^1(\nu)}
\le\sqrt{D(f-g)}\,[\sqrt{D(f)}+\sqrt{D(g)}]. \tag{SG3}
$$

The spectral semigroup contracts the form norm, and its invariant
$L^1$ extension contracts the $L^1$ norm. Thus core approximation and the
closed positive cone of $L^1$ extend (SG2) to every real even form input.
These are standard continuity properties applied to the unchanged
increment maps; (SG3) does not replace the original covariance.

Use the already established $v=\Phi''/\Phi-1/4$, with
$v\in D(T)$ and $Tv=v/2$. If (SG2) held, $P_t v=e^{-t/2}v$ would give

$$
\mathcal G(v)\le P_t\mathcal G(v). \tag{SG4}
$$

Invariance makes the two $L^1$ integrals equal, so (SG4) is equality
almost everywhere. Every invariant nonnegative $g\in L^1(\nu)$ here
is constant: Jensen applied to $g\wedge M$ and invariance make each
bounded truncation invariant, and the spectral theorem puts it in
$\ker T=\mathbb R1$. Taking $M\to\infty$ gives the assertion for $g$.
This uses the known constant kernel of the same operator, rather than
positivity on the unknown critical quotient. Consequently (SG2)
would force $\mathcal G(v)$ to be constant.

That conclusion fails in the actual prime geometry. Differentiating
the normally convergent theta series twice and retaining its first term
and differentiated tail gives

$$
v(x)\sim4\pi^2e^{4x}\qquad(x\to+\infty). \tag{SG5}
$$

This does not differentiate an asymptotic remainder. Choose a real even
nonzero $0\le\zeta\le1$ in $C_c^\infty(-1,1)$ and put
$M=\sup_{|y|\le1}|v(y)|$. The incoming compact-target rate is

$$
a_\zeta(x)=\frac1{2\cosh(x/2)}\sum_{n\ge2}
 \frac{\Lambda(n)}{\sqrt n}\Phi(x-\log n)\zeta(x-\log n).
$$

The existing ordinary PNT rate argument applies to the same smooth
compact weight $y^{-1/2}\Phi(\log y)\zeta(\log y)$, giving

$$
a_\zeta(x)\longrightarrow
 A_\zeta:=\int_{\mathbb R}e^{r/2}\Phi(r)\zeta(r)dr>0. \tag{SG6}
$$

It retains every prime power; the target interval restricts only a
nonnegative lower minorant. For all sufficiently large $x$, positivity
of the other energy terms yields

$$
\mathcal G(v)(x)\ge\frac12a_\zeta(x)(|v(x)|-M)^2
\longrightarrow\infty. \tag{SG7}
$$

The original density is strictly positive, so this is also a
nonconstant almost-everywhere function. It contradicts the required
constant energy density. Hence the all-input sharp estimate (SG2)
cannot hold even when first requested only on the original compact core.
The argument uses no prime truncation, fixed-zero-height hypothesis,
finite matrix signs or RH assumption.

This excludes that sufficient pointwise gradient route at rate
$e^{-t}$. It excludes neither a weaker gradient estimate nor an
integrated or directly estimated global half-bound. The [accepted conditional $921/2000=0.4605$ lower bound](https://github.com/the-omega-institute/trureturing-experiments/blob/e5c5d8bf2b157e5c94af05ba724e18f4131b4c88/docs/reports/theta-mixed-matrix/target-correction.md#reuse-the-positive-blocks-when-a-requested-gap-test-fails)
remains reusable, while positivity on
the complete critical quotient, the one-half bound, Robin and RH
remain unresolved. No precise smaller optimal curvature constant is
asserted.


## Spatially weighted high inverse at every subcritical parameter

The spatial comparison in (WF5) is reused before taking its scalar
minimum. This is a conditional paper application of (WF1)–(WF6) on the
same minimal even form, using the classical variational inverse comparison.
It retains the complete prime row, Gamma term and original ground.
It supplies an inverse-coupling allowance, not a low-block sign,
cofinal positivity or Lean certification.

Fix $0<\varepsilon\le1/2$, put
$c=1/2-\varepsilon$, $\delta=\varepsilon/4$, and choose

$$
N\ge N_w(\varepsilon):=
\max\left\{2e^{4\mu_\varepsilon+4},
\sqrt{\frac{512}{3\pi\varepsilon}}\|s''\|_2,2\right\}.
\tag{WH1}
$$

Here $\mu_\varepsilon$ is exactly (WF4), computed from the same
complete $W$ and $s$. Let $P=\mathbf1_{|\mathsf D|<N}$, $Q=I-P$,
$v_0=\sqrt\rho$, and
$T_c=\widetilde A-cI+c|v_0\rangle\langle v_0|$.
Denote its actual high closed form and associated operator by $C$.
Set

$$
m_N=m(N/2),\qquad a_N=m_N-\mu_\varepsilon,\qquad
V_{\varepsilon,N}(x)=\delta+a_Ns(x)^2.
\tag{WH2}
$$

The existing symbol estimate gives $m_N\ge2\mu_\varepsilon+1$,
so $a_N\ge\mu_\varepsilon+1>0$.
The leakage estimate (WF5) and $m_N\le16N$ give
$m_N\eta_N^2\le\varepsilon/4$ under (WH1).
Definition (WF4) supplies the pointwise relation
$W+\mu_\varepsilon s^2\ge1/2-\varepsilon/2$.
Retain its unused spatial term in the same high-form calculation:
for every $q$ in the actual high form domain,

$$
\begin{aligned}
C[q]
&\ge\int(m_Ns^2+W-c)|q|^2dx
 -m_N\eta_N^2\|q\|_2^2+c|\langle v_0,q\rangle|^2\\
&\ge\int V_{\varepsilon,N}(x)|q(x)|^2dx.
\end{aligned}
\tag{WH3}
$$

The nonnegative ground term is dropped only in the last lower bound.
This uses the closed high restriction of the original form, rather
than a new maximal domain. The sharp low projection maps $L^2$ into
$H^1$ and the original operator domain as in the
[complete-column interface](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/sharp-center.md#operator-domain-and-complete-block).
Consequently its complementary projection preserves the minimal form
domain. The original core approximation and (WF1), (WF5) extend the
same inequality to that high form domain.

Since $V_{\varepsilon,N}\ge\delta>0$ and $s$ is bounded,
$w_{\varepsilon,N}=V_{\varepsilon,N}^{-1}$ is bounded and positive.
For every $r\in QL^2_{\rm even}(dx)$, variational inversion of (WH3)
gives

$$
\langle r,C^{-1}r\rangle
\le\int w_{\varepsilon,N}(x)|r(x)|^2dx.
\tag{WH4}
$$

Indeed the left side is the supremum of
$2\Re\langle r,q\rangle-C[q]$ over the high form domain.
After (WH3), enlarging that supremum to all even $L^2$ and completing
the pointwise square gives the right side. No commutation of $Q$ with
the multiplier, or equality of inverse and compression, is asserted.

The accepted original cap $\|s\|_\infty^2\le9/5$ used in (FF1)
yields the explicit saving

$$
\begin{aligned}
\delta^{-1}\|r\|_2^2-\int w_{\varepsilon,N}|r|^2
&=\frac{a_N}{\delta}
 \int\frac{s^2|r|^2}{\delta+a_Ns^2}dx\\
&\ge b_{\varepsilon,N}\|sr\|_2^2,\qquad
b_{\varepsilon,N}:=
\frac{a_N}{\delta(\delta+9a_N/5)}>0.
\end{aligned}
\tag{WH5}
$$

For every nonzero $r$ this saving is strictly positive because $s>0$.
There is no claimed uniform fractional saving for arbitrary sources:
$s(x)\to0$ at spatial infinity. The
[same-residual consumer](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/sharp-center.md#retain-this-spatial-weight-in-the-complete-inverse-residual)
uses (WH4)–(WH5) before any scalar residual norm is taken.
The low Schur and complementary-low signs on the same bandwidth
sequence remain unproved; no saved fixed-band matrix is transported to
(WH1).


## Keep the high constraint and the exact ground term

At the same (WH1) parameter and bandwidth, let $H=L^2_{\rm even}(dx)$,
write $M_V,M_w$ for multiplication by (WH2) and its inverse, and put
$V_{\max}=\delta+9a_N/5$. The existing cap gives
$V_{\max}^{-1}I\preceq M_w\preceq\delta^{-1}I$. On $PH$ and $QH$ set

$$
A=PM_wP\big|_{PH},\qquad D=QM_VQ\big|_{QH},\qquad
R=Q(M_w-M_wPA^{-1}PM_w)Q\big|_{QH}.
\tag{WH6}
$$

Both compressed positive multipliers have bounded inverses; $P$ is
infinite-dimensional. Reuse the standard positive block inverse identity:
$R=D^{-1}$. The bounded positive shorting reference is
[Antezana--Corach--Stojanoff, Theorem 2.2(4), p.5](https://arxiv.org/pdf/math/0410573v1),
with operator $M_w$ and closed subspace $QH$; (SC2) supplies the
existing positive block-elimination interface. For this application, the vector
$q=M_w(r-PA^{-1}PM_wr)$ satisfies $Pq=0$ and $QM_Vq=r$ for every
$r\in QH$. No commutation of $P$ with $M_w$ is assumed.

Set $g=Qv_0$ and $\beta=c/(1+c\langle g,Rg\rangle)$. Before dropping
the ground term, (WH3) gives $C[q]\ge\langle q,Dq\rangle+
 c|\langle g,q\rangle|^2$ on the original high form domain.
Variational inversion and the standard rank-one inverse identity yield

$$
C^{-1}\preceq(D+c|g\rangle\langle g|)^{-1}
=R-\beta|Rg\rangle\langle Rg|.
\tag{WH7}
$$

The rank-one identity reuses the general-ring Woodbury proof
[`Matrix.invOf_add_mul_mul`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/LinearAlgebra/Matrix/Invertible.lean#L196).
Take its central factor to be $I$ and absorb $c$ into the update factor,
including $c=0$. Its algebra applies to bounded endomorphism entries; finite block
indices impose no finite-dimensional assumption on $QH$. Invertibility
here comes from $D\succeq\delta I$ and $c\ge0$, not from that formula.
The inspected shorting PDF SHA-256 is
`449b7d53831f8f2ddec744ad297e43f5bbbbff3804df19833e48a1181cb90066`.
Only the variational supremum is enlarged to $QH$; the actual high
operator and domain remain those of (WH3). Define, for $r\in QH$,

$$
\begin{aligned}
J(r)&=\int w|r|^2dx
 -\langle P(wr),A^{-1}P(wr)\rangle
 -\beta|\langle Rg,r\rangle|^2,\\
\langle r,C^{-1}r\rangle&\le J(r),\qquad
\int w|r|^2dx-J(r)\ge\delta\|P(wr)\|_2^2.
\end{aligned}
\tag{WH8}
$$

Here $A\preceq\delta^{-1}I$ gives the last inequality. The projection
and ground corrections are jointly valid because the latter uses the
same constrained $R$, not the unconstrained $M_w$. Each correction can
vanish; at $c=0$ the ground correction vanishes. The
[same-residual application](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/sharp-center.md#keep-the-projection-and-ground-corrections-on-the-same-residual)
keeps all cross entries and the exact ground trial cost.
This is a conditional paper application of existing block and rank-one
inverse tools. It supplies no evaluated entries, low or complementary-low
signs, cofinal certificate, endpoint half-bound, RH/Robin proof or Lean
certification.

## Verified zero height and a whole-projector strip-tail budget

This is a conditional application of (WF7)–(WF8), (FF1)–(FF7), the
existing compact theta–Weil identity and the existing inverse-fourth
zero count. Fourier modulation and the spectral-projector contradiction
are reused tools. No new general theorem, originality, numerical gap or
Lean certification is asserted. The purpose is to bind a finite verified
zero height to the actual whole-subcritical-projector map without a
finite generator Gram or a matrix-sign calculation.

Fix $0<\varepsilon\le1/2$, put $\tau=\varepsilon/8$ and take the
unchanged $p,K_p,N_0,R,N$ of (WF7), (WF6), (FF2), (FF7). Fix one
admissible smooth transition-width-two cutoff of (FF1)–(FF2), and charge
that same cutoff throughout. Define

$$
W=M_{\chi_R}U^{-1}p_NU,\qquad a_R=s\chi_R,\qquad
\mathcal A_2(R)=\int_{\mathbb R}e^{|x|/2}|a_R''(x)|\,dx.
\tag{VH1}
$$

The cutoff is smooth and compact, so $\mathcal A_2(R)<\infty$.
No quantitative bound for its second derivative is inferred from its
Lipschitz bound. Equations (FF1), (FF2), (WF8) and the bandwidth choice
in (FF7) give

$$
\begin{aligned}
\|(I-W)P_\varepsilon\|_{\nu\to\mathcal F}
&\le\frac{\sqrt7}{8}\tau+
 \frac{78K_p}{\varepsilon}\frac{1+\log N}{N}\\
&\le\left(\frac{\sqrt7}{8}+\frac13\right)\tau<\tau.
\end{aligned}
\tag{VH2}
$$

This is the whole original spectral subspace estimate. It omits only
the midpoint approximation used to make (FF4) finite, not any part of
the actual energy. The map $W$ generally has infinite rank; (FF8)'s
finite generator count is not asserted for it. For every even complex
$h\in L^2(\nu)$, $Wh$ is
compact smooth and even: $p_NUh$ has compact Fourier support and bounded
derivatives of every order, while $\rho$ is smooth and positive on the
cutoff support.

### Keep the frequency translation before taking a strip bound

Put $f=\Phi Wh=a_Rp_NUh$. Use the unitary Fourier transform on $Uh$
and the nonunitary transform $\widehat f(z)=\int e^{-izx}f(x)dx$ on
physical tests. Fubini gives

$$
\widehat f(z)=\frac1{\sqrt{2\pi}}
\int_{-2N}^{2N}p(\xi/N)\widehat{Uh}(\xi)
\widehat{a_R}(z-\xi)\,d\xi.
\tag{VH3}
$$

This is the usual multiplication/modulation rule, already used for
[cosine packets](../../D5/S3/Weil/ZeroInfinitude/CosinePacket.lean),
`paperFT_cosineModulation`; it is not a new Fourier construction.
Let $H>2N$, $|\Re z|>H$ and $|\Im z|\le1/2$. Two integrations by parts
on $a_R$, before combining the modulated factors, imply

$$
|\widehat{a_R}(z-\xi)|
\le\frac{\mathcal A_2(R)}{|z-\xi|^2}
\le\frac{\mathcal A_2(R)}{(|\Re z|-2N)^2}.
$$

There are no boundary terms because $a_R$ is compact smooth. Since
$0\le p\le1$, Plancherel and Cauchy–Schwarz on $[-2N,2N]$ give

$$
|\widehat f(z)|
\le\sqrt{\frac{2N}{\pi}}
\frac{\mathcal A_2(R)}{(|\Re z|-2N)^2}\|h\|_\nu.
\tag{VH4}
$$

Thus differentiating a modulated factor at frequency up to $2N$ is
unnecessary for this bound. That direct two-derivative bound would
introduce an $N^2$ term before squaring; (VH4) retains the frequency
separation instead. Its loss is the explicit separation requirement
$H>2N$.

### Reuse the inclusive verified head and the strict actual zero tail

For an integer $H\ge5$ set

$$
\begin{aligned}
L_H&=\lfloor\log_2(H+4)\rfloor+1,\\
\mathscr R_4(H)&=\frac{256}{H}
\left[\left(\frac2{H^3}+\frac1{2H^2}\right)L_H+
\frac{2/H^2+1/H}{H+4}\right].
\end{aligned}
\tag{VH5}
$$

The existing
[`finite_inverse_fourth_tail_le`](../../D5/S3/Weil/BurnolGram/ExplicitWeilFourthMomentTail.lean)
applies with $\gamma=\Im\rho$, full analytic multiplicities, $A=128$,
$T=H$, $L=L_H$, and its proved actual unit-window count. Taking the
supremum over finite subsets of $|\Im\rho|>H$ gives

$$
\sum_{|\Im\rho|>H}\frac{m_\rho}{(\Im\rho)^4}
\le\mathscr R_4(H).
\tag{VH6}
$$

This uses the finite ordinate-tail estimate directly. The neighboring
`zeroData_fourth_moment_tail_rational` additionally assumes a finite
head containing a spectral ball of radius $H+1$ and bounds its spectral
envelope; that corollary alone cannot be applied to the height-$H$
head. Zeros at height exactly $H$ remain in the head, counted with their
full multiplicity. The two-sided count already includes negative
ordinates, so no extra factor two is inserted.

Suppose all nontrivial zeros through height $H$ lie on the critical line.
The existing compact-test formula gives

$$
q(Wh):=D(Wh)-\tfrac12\operatorname{Var}_\nu(Wh)
=\sum_\rho m_\rho\widehat f(z_\rho)
 \overline{\widehat f(\overline{z_\rho})},\qquad
z_\rho=\Im\rho-i(\Re\rho-1/2).
$$

Its inclusive head is nonnegative. Off the critical line the paired
product is retained, not replaced by an absolute square. Apply (VH4)
to both factors in that product, then use (VH6). The complete real
slack therefore satisfies, for all even complex $h\in L^2(\nu)$,

$$
\begin{aligned}
q(Wh)&\ge-\mathcal E_H\|h\|_\nu^2,\\
\mathcal E_H&=\frac{2N}{\pi}\mathcal A_2(R)^2
 \left(1-\frac{2N}{H}\right)^{-4}\mathscr R_4(H).
\end{aligned}
\tag{VH7}
$$

All prime powers remain in $D$. Only the zero-side remainder is bounded
absolutely. This is an all-input estimate for this specified map, not
an operator-norm tail claim on bare $L^2(\nu)$ without smoothing.

### A sufficient fixed-gap supplier, with its unpaid inputs

If $\mathcal E_H\le\varepsilon/2$, (VH2) and (VH7) exclude every
centered unit $h\in\operatorname{ran}P_\varepsilon$. Indeed,
$q(h)\le-\varepsilon$ and $\|h\|_{\mathcal F}\le\sqrt{3/2}$.
The polarized form $q$ is bounded by the product of the $\mathcal F$
norms: apply Cauchy–Schwarz to the energy and covariance parts, then to
the resulting two scalar components. Consequently

$$
|q(Wh)-q(h)|
\le\tau(2\sqrt{3/2}+\tau)<3\tau=3\varepsilon/8,
\qquad q(Wh)<-5\varepsilon/8.
$$

This contradicts (VH7). Constants are treated separately using $T1=0$;
no projection of a noncompact source is discarded. The spectral theorem
then gives the conditional all-form-domain conclusion

$$
D(h)\ge(1/2-\varepsilon)\operatorname{Var}_\nu(h)
\qquad(h\in\mathcal F_{\min,\mathrm{even}}).
\tag{VH8}
$$

The published finite-height premise can be reused at
$H_0=3\cdot10^{12}$: Platt–Trudgian,
[*The Riemann hypothesis is true up to $3\cdot10^{12}$*,
arXiv:2004.09765v1](https://arxiv.org/pdf/2004.09765v1), Theorem 1,
printed p.2, verifies through $3000175332800$. This result is already
used in the [finite-height Robin supplier](../Analytic/polak2026finiterobinca.md).
No zero verification is repeated here. No bounds establishing
$2N<H_0$ and $\mathcal E_{H_0}\le\varepsilon/2$ have been supplied
for (VH1). A numerical improvement to the actual spectral gap does not
follow from these conditional formulas alone.

Finally $K_p>0$ because $s$ is nonzero and the cutoff $p$ changes from
one to zero. The unchanged (FF7) gives
$\delta\le\varepsilon^2/(1872K_p)$ and
$N\ge2\delta^{-1}\log(2/\delta)$. Hence $N\to\infty$ as
$\varepsilon\downarrow0$. For a fixed verified height $H_0$, the
hypothesis $H_0>2N$ of this particular absolute shifted-tail bound
therefore fails eventually. Even success at one fixed gap would not
supply a cofinal half-bound by this same formula. This restriction
concerns this supplier; it does not rule out signed tails, a different
justified approximation map or a different height-to-form transfer.
The endpoint half-bound, RH and strict Robin remain unresolved.

## A fixed unwindowed transfer to the original variance gap

The [existing saved comparison](https://github.com/the-omega-institute/trureturing-experiments/blob/e5c5d8bf2b157e5c94af05ba724e18f4131b4c88/docs/reports/theta-mixed-matrix/target-correction.md#reuse-the-positive-blocks-when-a-requested-gap-test-fails)
already supplies the conditional global constant $921/2000=0.4605$.
The application below uses the same original even minimal form and
accepted scalar suppliers, and supplies $15/32>921/2000$. It reuses the
Fourier commutator, whole-projector argument, weighted theta tails,
actual zero count and published verified height. It introduces no new
generic method, priority claim or Lean certification.

### The unwindowed image has an actual paired zero formula

Put $W_N=U^{-1}p_NU$, without a spatial multiplier. For every even
complex $h\in L^2(\nu)$, $g=p_NUh$ belongs to $H^1$, and (WF2) puts
$h_N=U^{-1}g$ in the original minimal form domain. Its physical test is
$f=\Phi h_N=sg$.

Use the scaled smooth cutoffs from the
[theta mixed-nullity passage](lagarias2004li.md#mixed-nullity-needs-a-domain-bridge),
with uniformly bounded scaled derivatives. Then
$(\chi_R-1)g\to0$ in $H^1$, so (WF2) gives
$\chi_Rh_N\to h_N$ in the actual form norm. Compact frequency support
makes every derivative of $g$ bounded. The original (WC2) tails therefore
give

$$
\int e^{|x|/2}\left(|(\chi_R-1)f|
 +|((\chi_R-1)f)''|\right)dx\longrightarrow0.
\tag{UG1}
$$

The existing closed-strip integration-by-parts bound and actual
multiplicity-weighted inverse-fourth summability let the compact paired
zero formula pass to this limit. Consequently

$$
q(h_N)=\sum_\rho m_\rho\widehat f(z_\rho)
 \overline{\widehat f(\overline{z_\rho})}.
\tag{UG2}
$$

Only this specified noncompact image is added to the compact-test
identity. No maximal-domain equality or discarded critical-projection
tail is used. The energy and every prime power pass through the original
closed form. The sign and normalization of the off-line paired product
remain those in (VH7).

### A prescribed smooth frequency cutoff

Let $w=15/16$. Define the even trapezoid $p_0$ to equal one on
$[-33/32,33/32]$, decrease linearly to zero at $\pm63/32$, and vanish
outside. Let $b_0(x)=64(1-64|x|)_+$, fix one nonnegative even smooth
unit-mass $b_1$ supported in $[-1/64,1/64]$, and put
$b=b_0*b_1$, $p=p_0*b$.
This one fixed construction has the original (WF7) hypotheses,
$L_p\le16/15$ and $\|b\|_2^2\le128/3$.
The four translates in $p_0''*b$ have disjoint supports. Young's
inequality, Cauchy–Schwarz and Plancherel in the stated normalization give

$$
\begin{gathered}
\|p'\|_2^2\le\frac{32}{15},\qquad
\|p''\|_2^2\le\frac{131072}{675},\\
C_p^2\le\tfrac12(\|p'\|_2^2+\|p''\|_2^2)<100.
\end{gathered}
\tag{UG3}
$$

Here $\check p_0=(2\pi)^{-1}\int e^{ix\xi}p(\xi)d\xi$ in the
(WF7) definition of $C_p$; the subscript does not denote the trapezoid.
For the last bound apply Cauchy–Schwarz with weight $(1+x^2)^{-1}$.

### Charge the constants from accepted original-theta inputs

The accepted
[derivative supplier](https://github.com/the-omega-institute/trureturing-experiments/blob/e5c5d8bf2b157e5c94af05ba724e18f4131b4c88/docs/reports/theta-mixed-matrix/derivative-bandwidth.md)
gives $S_j=\|s^{(j)}\|_2^2$ with
$S_0<1/2$, $S_1<2$, $S_2<42$, $S_3<28000$. Thus
$\|s\|_{H^3}^2=S_0+3S_1+3S_2+S_3<28133$.
These saved inputs are reused without recomputing theta derivatives.

The same (WC1) series constants admit the elementary bounds
$C_0<60$, $C_1<650$, $C_2<7200$. To check them, use
$P_{1,a}=a-2z$, $P_{2,a}=a^2-4(a+1)z+4z^2$,
$3<\pi<22/7$ and $e^3>20$ (its positive Taylor polynomial through
degree eight exceeds twenty). Coefficient caps are respectively
$59n^4$, $(1281/2)n^6$, $6969n^8$; the omitted tail after $n=1$
is at most $2^{4+2j}/7992$ times that coefficient cap, because
$e^{-3\pi}<1/8000$ and the shared ratio is below $1/1000$.

It follows that $A_1<19$, $A_2<885$, $B_2<1250$ in (WC1)–(WC2).
For $\zeta=\pi/2-3/8>9/8$, the same scalar maxima give
$M_1<1$, $M_3<(8/3)^3/20<1$ and
$M_5<(40/9)^5/32<55$. Therefore

$$
\begin{gathered}
K_0<8,\quad K_1<152,\quad K_2<550000,\\
\|(s^2)'\|_\infty<2432,\qquad
\sum_n\|b_n'\|_\infty<3648,\\
\mathcal A_*:=\int e^{|x|/2}|s''(x)|dx
 \le K_2\int_1^\infty u^{-3/4}e^{-3u/8}du<2^{21}.
\end{gathered}
\tag{UG4}
$$

For the prime sum use (WC4) and $r=e^{-3/4}<1/2$; its bracket is
less than $3/2$. For the last integral use $u^{-3/4}\le1$ and
$\int_1^\infty e^{-3u/8}du<8/3$.

Reuse the principal coefficient $64$ obtained explicitly in the proof
above (WF7), before its conservative enlargement to $128$. Keep the
old $K_p$ definition and all old consumers intact, and define this
application's sharper constant by

$$
\begin{aligned}
K_p^\sharp&=64L_p\|s\|_{H^3}^2+
 C_p\left(8\|(s^2)'\|_\infty+2\sum_n\|b_n'\|_\infty\right)\\
&<\frac{1024}{15}\,28133+267520
 =\frac{32820992}{15}<9\cdot2^{18}.
\end{aligned}
\tag{UG5}
$$

### One fixed reuse of the complete saved high rows

Fix $\varepsilon=1/32$, $a=15/32$, $N=2^{40}$ and
$H=3\cdot10^{12}$. The proof of (WF3) gives
$m(N/2)\ge\tfrac12\log N>40/3$.
The saved $m(32)$ upper bound is below $22/3$.
For each accepted positive cell let $J_i$ and $s_{i,-}^2$ be its saved
joint floor and squared-theta lower endpoint. The single fixed rational
application checks

$$
J_i+6s_{i,-}^2>31/64\qquad(0\le i<128).
\tag{UG6}
$$

The [fixed rational application](https://github.com/the-omega-institute/trureturing-experiments/blob/9188d87ac0c5bf1f36e248f2cb3c835af6f05c9e/docs/reports/theta-mixed-matrix/verified-height-unwindowed-gap.md)
checks all 128 cells and its
[exact saved result](https://github.com/the-omega-institute/trureturing-experiments/blob/9188d87ac0c5bf1f36e248f2cb3c835af6f05c9e/docs/reports/theta-mixed-matrix/verified-height-unwindowed-gap-result.json)
has every fixed budget comparison true. These are new inequalities on
the accepted data, with no theta,
operator action, Gram or old producer executed. They bound the complete
$W(x)+m(N/2)s(x)^2$ on every cell. On the entire exterior reuse the
[saved $W$ floor](https://github.com/the-omega-institute/trureturing-experiments/blob/e5c5d8bf2b157e5c94af05ba724e18f4131b4c88/docs/reports/theta-mixed-matrix/sharper-exterior.md),
which exceeds $31/64$ before adding the positive symbol term.
The same (WF5) leakage, with $m(N/2)\le16N$ and $S_2<42$, is below
$2^{-70}<1/128$. Hence the full even high restriction is at least
$61/128=a+\varepsilon/4$.

The whole-projector argument of (WF8) now applies with this supplied
high restriction and $K_p^\sharp$. It does not require the separate
coarse sufficient choice $N_0(\varepsilon)$. Since $\log2<7/10$,

$$
\|(I-W_N)P_\varepsilon\|_{\nu\to\mathcal F}
\le\frac{6K_p^\sharp}{\varepsilon}\frac{1+\log N}{N}
<\frac{783}{65536}<\frac1{80}.
\tag{UG7}
$$

### Pay the actual zero tail on this same map

The (VH3)–(VH7) strip argument applies with $s$ in place of $a_R$;
(WC2) removes its integration-by-parts boundary terms. At the fixed $H$,
$L_H=42$ and $\mathscr R_4(H)<2^{-109}$.
Also $3H>8N$, so $(1-2N/H)^{-4}<256$. Using
$2N/\pi<N$ and (UG4) gives

$$
q(W_Nh)\ge-\mathcal E\|h\|_\nu^2,\qquad
\mathcal E<2^{40}2^{42}2^8 2^{-109}=2^{-19}.
\tag{UG8}
$$

The inclusive verified head is precisely the already published
Platt–Trudgian input; the strict tail keeps all actual multiplicities
and off-line paired factors. No zero computation is repeated.

For a centered unit $h\in\operatorname{ran}P_\varepsilon$,
$q(h)\le-1/32$ and $\|h\|_{\mathcal F}\le\sqrt{47/32}<49/40$.
The same polarized-form bound as in (VH8) and (UG7) imply

$$
|q(W_Nh)-q(h)|<\frac1{80}
 \left(\frac{49}{20}+\frac1{80}\right)=\frac{197}{6400},
\qquad q(W_Nh)<-\frac3{6400}<-2^{-19},
$$

contradicting (UG8). Constants reduce the actual operator separately.
The original spectral theorem therefore gives

$$
D(h)\ge\frac{15}{32}\operatorname{Var}_\nu(h)
\qquad(h\in\mathcal F_{\min,\mathrm{even}}).
\tag{UG9}
$$

This is a conditional paper deduction under the inherited actual
form/domain and accepted scalar-supplier premises, plus the checked
finite inequality (UG6). The accompanying rational application records
the same input commit and all fixed budget comparisons. The literal
windowed (FF7)/(VH1) choices retain their own unpaid conditions.
No cofinal family is supplied; the fixed-height separation barrier
remains. The one-half bound, full Robin, RH and Lean certification
remain unresolved.

The [fixed-head remainder construction (FH1)–(FH4)](lagarias2004li.md#a-fixed-verified-head-cannot-absorb-the-absolute-smoothed-remainder)
also excludes absorbing the whole absolute paired tail into this fixed
head with a vanishing ambient-norm error uniformly on the entire original
form remainder, even after these same unwindowed maps. It uses actual
real zero duals and exact finite head annihilation, independently of the
shifted-tail separation estimate. The constructed inputs have not been
placed in the strict-subhalf spectral class used above; no signed-tail
obstruction or change to (UG9) follows.


## Split the prime index before taking a high-frequency minimum

Retain the original minimal even form, (WF1), the original pole probability,
and every prime power. The following is a paper application of the existing
Fourier leakage argument, theta coefficient bounds and classical Chebyshev
partial summation. It supplies an alternative high-block allowance and its
inverse consumer, with no new general-method, originality or Lean claim.
It does not identify a low-block sign or establish the endpoint half-bound.

Write the full prime off-diagonal operator in (WF1) as $\mathcal B_p$,
distinct from the negative-edge metric $C_-^*C_-$, and put
$S_M=\sum_{2\le n\le M}\Lambda(n)/\sqrt n$ for an integer $M\ge2$.
Since $b_n(x)=w_ns(x)s(x+\log n)$, its complete finite part is exactly

$$
 \mathcal B_{p,\le M}
 =M_s\sum_{2\le n\le M}w_n(\tau_n+\tau_n^*)M_s,
 \qquad
 |\langle \mathcal B_{p,\le M}v,v\rangle|
 \le2S_M\|sv\|_2^2. \tag{PS1}
$$

This uses the same $sv$ at both ends of every translation and keeps the
shifted adjoint. The [existing full theta coefficient bound](lenz2010compactness.md#full-prime-off-diagonal-tail)
with $C_\Phi=144/5$ gives
$\|b_n\|_\infty\le(C_\Phi/2)w_ne^{-3n/2}$.
Reuse $w_n\le n$ and the geometric tail, and set $\vartheta=e^{-3/2}$:

$$
 \|\mathcal B_p-\mathcal B_{p,\le M}\|\le\beta_M,\qquad
 \beta_M=\frac{144}{5}\,\vartheta^{M+1}
       \frac{M+1-M\vartheta}{(1-\vartheta)^2}. \tag{PS2}
$$

The original operator is not truncated: (PS2) pays for all omitted
prime powers in operator norm.

The [existing theta derivative bounds (WC2)–(WC3)](../Analytic/romik2021orthogonal.md)
supply $s\in H^3(\mathbb R)$ and permit one additional derivative in the Fourier-tail argument of (WF5). For $N\ge2$ and
$\widehat v=0$ on $|\xi|<N$, the same convolution support and Young
inequality, now followed by Cauchy--Schwarz with $|\omega|^{-3}$, give

$$
 \begin{aligned}
 \|\mathbf1_{|\mathsf D|<N/2}sv\|_2
 &\le \eta_{N,3}\|v\|_2,\\
 \eta_{N,3}^2&=\frac{32}{5\pi}\|s'''\|_2^2N^{-5}.
 \end{aligned} \tag{PS3}
$$

Indeed $(2\pi)^{-1}\int_{|\omega|>N/2}|\omega|^{-6}d\omega
=32/(5\pi N^5)$ in the existing unitary Fourier convention.
With $m_N=m(N/2)$, define

$$
 a_{N,M}=m_N-8-2S_M,\qquad
 \Delta_{N,M}=m_N\eta_{N,3}^2+\beta_M. \tag{PS4}
$$

The high-frequency part of $sv$ contributes at least
$m_N(\|sv\|_2^2-\eta_{N,3}^2\|v\|_2^2)$ to the flat energy.
Combine this with (WF1), $c_\Gamma>-8$ and (PS1)--(PS2). Every
$v$ in the actual minimal high form domain satisfies

$$
 \widetilde D(v)\ge
 \left(\tfrac12-\Delta_{N,M}\right)\|v\|_2^2
       +a_{N,M}\|sv\|_2^2. \tag{PS5}
$$

All terms other than the flat energy are bounded on $L^2$; its existing
closed Fourier realization and the same minimal-domain passage as (WF1)
justify the inequality on that domain. This uses no maximal-domain
identification. If $a_{N,M}\ge0$, the first term alone is a complete
high-block lower bound.

### A sufficient algebraic bandwidth near the endpoint

Fix a classical constant $C_\psi\ge1$ with
$\Psi(t)\le C_\psi t$ for $t\ge1$. Reuse the inclusive
[half-weighted Chebyshev allowance](desogus2026threegates.md),
$S_M\le2C_\psi\sqrt M$; no PNT remainder or RH is required.
For all sufficiently large $N$, take the single analytic choice

$$
 M_N=\left\lfloor\left(\frac{m_N-8}{8C_\psi}\right)^2\right\rfloor\ge2.
 \tag{PS6}
$$

Then $a_{N,M_N}\ge(m_N-8)/2>0$. The existing symbol bounds give
$m_N\asymp\log N$, so $M_N\asymp(\log N)^2$. Consequently (PS2)
is $o(N^{-A})$ for every fixed $A>0$, whereas (PS3) gives

$$
 \Delta_{N,M_N}=O\!\left(\frac{1+\log N}{N^5}\right).
 \tag{PS7}
$$

The constants depend on the original theta derivative supplier and the
fixed Chebyshev constant. They are not numerically evaluated here.
For all sufficiently small $\varepsilon>0$, a sufficient bandwidth can
therefore be chosen of order
$O((\varepsilon^{-1}\log(1/\varepsilon))^{1/5})$ to have
$\Delta_{N,M_N}\le\varepsilon/2$. This is an alternative sufficient
asymptotic schedule, not a claim that it improves every previously used
fixed bandwidth or that any saved matrix is positive at these parameters.

### Use the same constrained inverse and ground term

For $0<\varepsilon\le1/2$, set $c=1/2-\varepsilon$ and retain the actual
high restriction of $\widetilde A-cI+c|v_0\rangle\langle v_0|$.
Choose $N,M$ with $a_{N,M}\ge0$ and
$\Delta_{N,M}\le\varepsilon/2$. Equation (PS5) gives, on its actual
high form domain,

$$
 C[q]\ge\int V(x)|q(x)|^2dx+c|\langle v_0,q\rangle|^2,
 \qquad
 V(x)=\varepsilon-\Delta_{N,M}+a_{N,M}s(x)^2\ge\varepsilon/2.
 \tag{PS8}
$$

Thus the existing variational inverse, projection shorting and rank-one
ground correction in (WH4), (WH6)--(WH8) apply in place of
(WH1)--(WH3). Substitute $\delta_{\rm PS}=\varepsilon-\Delta_{N,M}$,
$a_{N,M}$, $V=\delta_{\rm PS}+a_{N,M}s^2$ and $w=V^{-1}$ throughout
the multiplier-dependent definitions; in particular
$V_{\max}=\delta_{\rm PS}+9a_{N,M}/5$. The same sharp high projection
and original closed domain are used; no projection is commuted through
a multiplier. This is the original-form consumer of the estimate.
It supplies neither the same-band low Schur sign nor a cofinal full-form
certificate. The one-half variance bound, the projected signed comparison,
Robin and RH remain unresolved; no numerical experiment or new Lean
verification is claimed.
