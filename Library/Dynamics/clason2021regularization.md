---
bibkey: clason2021regularization
authors: Christian Clason
year: 2021
title: Regularization of Inverse Problems
doi: null
url: https://arxiv.org/abs/2001.00617v2
claim: The linear Tikhonov normal equation applies to the actual compact theta-translation map in the negative-edge metric. Fitted-source convergence is distinct from coefficient convergence and from a uniform projection error rate.
strata_touched: []
license: citation-only
triage: anchor
---

# Regularization of Inverse Problems

## Source contract

The inspected [arXiv v2 lecture notes](https://arxiv.org/pdf/2001.00617v2)
identify the version on the title page. Section 6, printed pp.58–60,
Lemma 6.3 and equation (6.1), give the normal equation for arbitrary
Hilbert-space data $y$ and positive $\alpha$:

$$(L^*L+\alpha I)x_\alpha=L^*y.$$

The section uses the filter $1/(\lambda+\alpha)$ and residual
$\alpha/(\lambda+\alpha)$. Theorem 5.6, printed p.48, asserts
coefficient convergence only for data in the pseudoinverse domain;
Corollaries 6.1–6.2, printed p.59, require source conditions for rates.
Neither supplies an unconditional coefficient limit or a rate for the
project's theta inputs. The inspected PDF SHA-256 is
`696b4f580464ec0e1da6a1863b91d9142aa58b8b841b8ea437b5944152cd649e`.
The generic normal equation, filters and resolvent identity are reused.

The following is a conditional paper application under the
[actual theta form, critical-family and negative-edge metric premises](../Weil/lagarias2004li.md).
Use its $c_*=11/2500$ on the centered even space $\mathcal H_0$,
$B=C_-^*C_-$ and closed critical source $N$. The source supplies no
arithmetic half-bound, original-operator spectral estimate or Lean
certification. This application preserves the original $\nu$ and both
edge maps. It constructs a regularized coefficient problem, without
claiming a certified finite numerical solution.

## Actual theta translations generate the critical source

Take r=1/16, I=[-r,r] with Lebesgue measure, and define

$$w_t(x)=\frac{\Phi(x+t)+\Phi(x-t)}{2\Phi(x)}-\cosh(t/2).\tag{R1}$$

For real t in I, w_t is even and nu-centered: shift the two integrals against cosh(x/2). On the complex box |Re z|,|Im z|<1/8, the inherited theta series and positive real first-term lower bound give a common squared-ratio majorant on either tail,

$$C e^{5|x|}\exp\{-\pi[2e^{-1/4}\cos(1/4)-1]e^{2|x|}\}.$$

The bracket is positive (e^-1/4>=3/4 and cos(1/4)>=31/32). On compact x intervals Phi has a positive minimum. Thus z->w_z is an H_0-valued holomorphic function on a neighborhood of I, and

$$w_t=\sum_{k\ge1}\frac{t^{2k}}{(2k)!}v_k,\qquad\overline{\operatorname{span}\{w_t:t\in I\}}=N.\tag{R2}$$

The first inclusion uses norm convergence of the Taylor series; the reverse uses Hilbert-valued difference quotients at zero. This does not use all real translations or a characterization by the complete zero set.

Define F:L2(I)->H_0 by Fq=integral_I w_t q(t)dt. It is Hilbert–Schmidt, its range closure is N, and every actual Fq lies in N and hence in the accepted form domain. Its adjoint is F*g(t)=<w_t,g> with the usual inner product antilinear in the first variable. The positive compact coefficient Gram K=F*BF has the actual kernel

$$\kappa(s,t)=\langle C_-w_s,C_-w_t\rangle
=\frac14\iint a(x,y)\overline{\Delta w_s(x,y)}\Delta w_t(x,y)d\nu(x)d\nu(y).\tag{R3}$$

## An explicit regularized common-source correction

For epsilon>0 and h in the actual form domain, h_0=h-nu(h)1, solve the bounded-window Fredholm normal equation

$$(K+\varepsilon I)q_\varepsilon=F^*Bh_0,\qquad n_\varepsilon=Fq_\varepsilon.\tag{R4}$$

The coefficient inverse has norm<=1/epsilon and involves no exact P_N. It is the standard Tikhonov fit for L=B^(1/2)F and datum g=B^(1/2)h_0. Its fitted signal, not necessarily its coefficient vector, converges to P_M g, M=B^(1/2)N (closed because B>=c_*I on H_0). Thus n_epsilon converges in H_0 and in both critical edge norms to the same n_h=G^-1 P_N Bh_0 from G4. Coefficients q_epsilon need not converge: g's projection may lie only in the closure of Ran L. Each n_epsilon belongs to N, so q(h-n_epsilon)=q(h) exactly.

For A=L L*, with spectral measure E_A, its remaining paired-edge error is exactly

$$\|C_\pm(n_h-n_\varepsilon)\|^2
=\int_{(0,\|A\|]}\left(\frac\varepsilon{\lambda+\varepsilon}\right)^2d\langle E_A(\lambda)g,g\rangle.\tag{R5}$$

The zero eigencomponent is excluded. Since M is infinite dimensional while A is compact, eigenvalues on M tend to zero. The fitted-filter error has operator norm 1 on M for every epsilon>0. Strong convergence therefore provides no uniform rate over all unit inputs, and no actual source condition or small-spectral-value mass bound has been proved for the required input class. The source's Theorem 5.6 applies only on the pseudoinverse domain; it is not used to infer bounded convergence of these coefficient vectors.

## A finite-epsilon approximation bound with the same source

Suppose F_m maps L2(I) into a finite span of actual w_t, ||F-F_m||<=delta, and ||F||<=M_F. Define K_m=F_m* B F_m and n_epsilon,m=F_m(K_m+epsilon I)^-1 F_m*Bh_0. The usual resolvent identity for A and A_m=B^(1/2)F_mF_m*B^(1/2) gives

$$\|C_\pm(n_\varepsilon-n_{\varepsilon,m})\|
\le\frac{\delta(2M_F+\delta)}{2\sqrt2\,\varepsilon}\|h_0\|.\tag{R6}$$

Both differences lie in N, so this is a common paired edge norm bound; the source norm bound is R6 divided by sqrt(c_*). With m equal cells of I and midpoint w_t samples, one may take delta<=L_w(2r)^(3/2)/(sqrt(12)m), where L_w is an independently validated upper bound for sup_I||w'_t||. The [directed small-window bounds](../../docs/reports/theta-mixed-matrix/theta-translation-bounds.md) supply numerical M_F and L_w for this interface. No finite Fredholm matrix has been certified here. R6 controls discretization for fixed epsilon; it does not pay the regularization error R5.

## Finite epsilon does not erase the old exact raw Schur obstruction

Let P_epsilon=F(K+epsilon I)^-1 F*B on H_0. The classical Woodbury identity gives

$$(I-P_\varepsilon)^{-1}=I+\varepsilon^{-1}FF^*B.\tag{R7}$$

Extend $P_\varepsilon$ by zero on constants, equivalently $P_\varepsilon h=P_\varepsilon(h-\nu(h)1)$; the inverse in (R7) extends by identity on constants. This agrees with the ambient formula because $B1=0$. Both operators preserve the actual form domain because their correction has range in $N$ and is bounded into its form norm. Suppose an ordinary measurable kernel $S$ has a finite, strictly positive weighted absolute Schur certificate of product at most one and exactly reconstructs $C_-(I-P_\varepsilon)h$ from $C_+(I-P_\varepsilon)h$ for every original core input. Schur supplies boundedness of $S$, so core density first extends that identity to the actual form domain. Equation (R7) then gives exact reconstruction of the original raw $C_\pm$ there. The already accepted theta-Schur obstruction excludes this certificate. This is reuse of that obstruction, not another fiber proof. Approximate reconstruction, absolute products>1 tending to1 and better actual norm estimates remain distinct possibilities.

The concrete new interface is R1–R4: it replaces an unspecified P_N primitive by a small-window integral kernel and a regularized normal equation, with the separately controlled discretization error R6. The outstanding estimate is the actual input's small-spectral-value error R5, or a directly certified complementary residual B(h-n)-w with w in N-perp, followed by a jointly reconstructed and norm-bounded projected transfer. No half-bound, RH/Robin proof, complete zero-set characterization or executable full-space approximation algorithm is claimed.


## Numerical inputs for the fixed-parameter discretization bound

The [actual-theta translation norm computation](../../docs/reports/theta-mixed-matrix/theta-translation-bounds.md)
uses the existing derivative supplier and the full original probability
measure, including both spatial tails. Its outward interval bounds give

$$L_w<9/2,\qquad \|F\|\le\|F\|_{\mathrm{HS}}<3/50,\qquad
\|F-F_m\|\le\frac{3}{50m}.$$

Substitution into R6 yields, for every positive epsilon and m equal
midpoint cells, the same-source bound

$$\|C_\pm(n_\varepsilon-n_{\varepsilon,m})\|
\le\frac{9}{5000\sqrt2\,\varepsilon}
\left(\frac2m+\frac1{m^2}\right)\|h_0\|.$$

At epsilon=1/100 and m=256, its coefficient is strictly below 1/1000.
This pays the fixed-parameter discretization term only. The actual-input
regularization error R5, kernel-entry quadrature, a uniform complementary
residual on the required input class and the projected reconstruction/norm estimate
remain unresolved. No new original-energy lower bound or Lean
certification is supplied.

## One fixed quadratic-input complementary residual

The [direct actual-operator enclosure](../../docs/reports/theta-mixed-matrix/theta-common-residual-bounds.md)
uses seven finite critical directions and eight individual certified real
Xi-zero witnesses for h=x^2. Under the inherited actual-model and
numerical-supplier premises it supplies
||B(h-n)-w||<9/8000, with n in N and w in N-perp. The accepted inverse
constant c*=11/2500 converts this to ||n_h-n||<=45/176 and paired edge
errors <=9/(160 sqrt(11)). The 512 retained point rows are reused;
derivative transport, all theta series and full spatial tails are paid.
This is a bounded-B input calculation, without asserting original
form-domain membership of x^2. Its upper enclosure does not reach 1e-4
and is not a lower bound on attainable residuals. It supplies neither
R5 on the required input class nor the projected transfer/norm comparison,
original half-bound, Robin or RH, and has no new Lean certification.

## The real translation boundary retains fixed sharp-low mass

This is a conditional paper application of the
[original theta tail](../Analytic/romik2021orthogonal.md#reusable-theta-tail-and-its-local-scale),
(R1)–(R5), and the accepted actual-model premises above. It keeps the
small-window generated space $N$ and the original measure. The theta
asymptotic, analytic identity principle, weak translation convergence
and Fourier projection tools are reused; no new generic regularization
theorem, numerical producer, Lean certification or originality claim
is supplied.

Put $v_0(x)=\sqrt{2\Phi(x)\cosh(x/2)}$, $Uh=v_0h$ and $N_c=UN$.
The complex theta series is normally convergent on $|\Im z|<\pi/4$.
For the translation parameter define

$$
t_c=\frac{\log2}{2},\qquad
\mathcal D=\{z:|\Im z|<\pi/4,\
2e^{-2|\Re z|}\cos(2\Im z)>1\}.
$$

This domain is connected, contains $I$ and has real section
$(-t_c,t_c)$. For each compact $E\subset\mathcal D$, the normally
convergent series and the positive real first-term denominator give
on either spatial tail

$$
|Uw_z(x)|^2\le C_Ee^{5|x|}
 e^{-\pi k_Ee^{2|x|}}+C_Ev_0(x)^2,\qquad
k_E=\min_{z\in E}(2e^{-2|\Re z|}\cos(2\Im z)-1)>0.
$$

On compact spatial intervals use the positive minimum of $\Phi$.
This common integrable majorant makes $z\mapsto w_z$ Hilbert-valued
holomorphic. Its projection onto $N^\perp$ vanishes on $I$ by (R2),
so the analytic identity principle makes it vanish on $\mathcal D$.
Centering and evenness extend as well. Consequently $w_t\in N$ for
every real $|t|<t_c$, without enlarging the original $N$.

For $0<t<t_c$ set

$$
\begin{gathered}
\eta_t=2e^{-2t}-1,\qquad R_t=\tfrac12\log(1/\eta_t),\\
G(y)=e^{5y/2-(\pi/2)e^{2y}},\qquad
A_t=\pi e^{-9t/2}\eta_t^{-5/4}.
\end{gathered}
$$

The actual two-tail profile, as $t\uparrow t_c$, is

$$
\left\|A_t^{-1}Uw_t-G(\cdot-R_t)-G(-\cdot-R_t)\right\|_2
\longrightarrow0. \tag{E1}
$$

To pay both tails, fix $A>t_c+1$ and $t\ge t_c/2$. On $x\ge A$,
the dominant numerator is $\Phi(x-t)$. The source tail comparison
gives

$$
\frac{v_0(x)\Phi(x-t)}{2\Phi(x)}
\le Ce^{5x/2}e^{-(\pi/2)\eta_te^{2x}}.
$$

After $x=R_t+y$ and division by $A_t$, this is bounded by $CG(y)$
on $y\ge A-R_t$. For each fixed $y$, the original first-term relative
asymptotic and $2\cosh(x/2)\sim e^{x/2}$ give convergence to $G(y)$.
Extend the term by zero below $A-R_t$ and apply $L^2$ dominated
convergence. On this right tail the other numerator has an
$\eta_t$-independent integrable envelope, because $2e^{2t}-1$ is
bounded away from zero. Its divided norm tends to zero, as does that
of $\cosh(t/2)v_0$. The compact interval $[-A,A]$ contributes a
bounded numerator divided by $A_t\to\infty$. Evenness supplies the
left tail, where $\Phi(x+t)$ is dominant. The wrong-half profile
tails vanish since $G\in L^2$; neither shifted numerator is asserted
globally bounded.

The two full profiles have overlap tending to zero. Thus

$$
\begin{gathered}
n_t:=\frac{Uw_t}{\|Uw_t\|_2}\in N_c,\qquad
\|Uw_t\|_2\sim\sqrt2A_t\|G\|_2,\\
\left\|n_t-\frac{G(\cdot-R_t)+G(-\cdot-R_t)}
 {\sqrt2\|G\|_2}\right\|_2\longrightarrow0,\qquad
n_t\rightharpoonup0. \tag{E2}
\end{gathered}
$$

At real $|t|\ge t_c$, use $w_t=w_{|t|}$ and put
$\eta_{|t|}=2e^{-2|t|}-1\le0$. The same leading ratio has an
$e^{5x/2}$ prefactor and exponent $-(\pi/2)\eta_{|t|}e^{2x}$,
so $w_t\notin L^2(\nu)$. The bounded centering
subtraction cannot cancel it. This is a real translation-integrability
boundary, not a zero ordinate or an eigenvalue.

For any fixed bandwidth $\Lambda>0$ let
$P_\Lambda=\mathbf1_{|\mathsf D|<\Lambda}$ on the even physical
space. Compute the projection of $G$ in the full physical space,
since $G$ itself is not even. Plancherel and Riemann–Lebesgue give

$$
\|P_\Lambda n_t\|_2^2\longrightarrow
\gamma_\Lambda:=
\frac{\|\mathbf1_{|\mathsf D|<\Lambda}G\|_2^2}{\|G\|_2^2}>0.
\tag{E3}
$$

The two projected translated profiles have equal norms and an
oscillatory cross integral with an $L^1$ frequency density. Positivity
uses $G\in L^1$, $G>0$ and its Fourier transform nonzero near zero.
Also $\gamma_\Lambda\uparrow1$ as $\Lambda\to\infty$. Hence the
fixed-band restriction of the actual critical space is noncompact;
this is a restricted-class interface to (R5).

## A compact fit has a fixed error on the whole sharp-low sphere

Use the family (E2), the actual negative-edge metric (G2) and its
already supplied positive coercivity. No inverse-constant computation
is repeated. In physical coordinates,

$$
\widetilde B=UBU^{-1}=M_d-\mathcal K,\qquad
d(x)=\tfrac12\int a(x,y)d\nu(y),\qquad
\mathcal K(x,y)=\tfrac12v_0(x)v_0(y)a(x,y),
$$

with the same $a(x,y)$ as (G2); assign its null diagonal value zero.
Since $0\le a\le1$ and $\nu$ is a probability, $\mathcal K$ is
Hilbert–Schmidt. For each fixed $y$, $a(x,y)\to1$ as
$|x|\to\infty$, so $d(x)\to1/2$. Compactness makes
$\mathcal K n_t\to0$, and (E2) makes the mass on every fixed
compact interval tend to zero. Therefore

$$
\|(\widetilde B-\tfrac12I)n_t\|_2\longrightarrow0. \tag{E4}
$$

Remove the original ground state exactly. With first-slot-linear
pairings, put $p_0=P_\Lambda v_0\ne0$ and

$$
b_t=P_\Lambda n_t-
 \frac{\langle P_\Lambda n_t,p_0\rangle}{\|p_0\|^2}p_0,
\qquad p_t=b_t/\|b_t\|.
$$

Here $p_0\ne0$ because $v_0$ is positive, belongs to $L^1$ and has
Fourier transform nonzero at zero. Weak escape makes the removed
coefficient tend to zero. For $t$ sufficiently close to $t_c$ the
normalization is nonzero, and $p_t$ is an even sharp-low unit input,
$\langle p_t,v_0\rangle=0$, $p_t\rightharpoonup0$,
$\|b_t\|\to\sqrt{\gamma_\Lambda}$ and
$\langle p_t,n_t\rangle\to\sqrt{\gamma_\Lambda}$.
The existing [sharp-center (SC1)](../../docs/reports/theta-mixed-matrix/sharp-center.md#operator-domain-and-complete-block)
places every physical finite-band input in the original minimal
operator domain; in $L^2(\nu)$ the corresponding input is $U^{-1}p_t$.

Let $\mathcal R p=Un_{U^{-1}p}$ be the exact common critical
correction from (G4). It is bounded on the centered ambient space
and has range in $N_c$. Its defining metric projection gives

$$
\langle\mathcal R p,\widetilde Bz\rangle
=\langle p,\widetilde Bz\rangle\qquad(z\in N_c).
$$

With $z=n_t$, boundedness and (E4) give
$\langle\mathcal R p_t,n_t\rangle\to\sqrt{\gamma_\Lambda}$.
For every fixed $\varepsilon>0$ the original (R4) correction
$\mathcal R_\varepsilon=UP_\varepsilon U^{-1}$ is compact, so
$\mathcal R_\varepsilon p_t\to0$. Consequently

$$
\begin{gathered}
\liminf_{t\uparrow t_c}
 \|(\mathcal R-\mathcal R_\varepsilon)p_t\|_2
 \ge\sqrt{\gamma_\Lambda},\\
\sup_{\substack{p\in P_\Lambda L^2_{\rm even},\ \|p\|_2=1\\
                 \langle p,v_0\rangle=0}}
 \|(\mathcal R-\mathcal R_\varepsilon)p\|_2
 \ge\sqrt{\gamma_\Lambda}. \tag{E5}
\end{gathered}
$$

The paired-edge statement retains the same source. Set
$z_t=(\mathcal R-\mathcal R_\varepsilon)p_t\in N_c$.
Then $\langle z_t,\widetilde Bn_t\rangle\to
\sqrt{\gamma_\Lambda}/2$ and
$\langle n_t,\widetilde Bn_t\rangle\to1/2$.
Cauchy–Schwarz in the $B$ metric, with mixed critical nullity, gives

$$
\liminf_{t\uparrow t_c}\|C_\pm U^{-1}z_t\|
\ge\sqrt{\gamma_\Lambda/2}. \tag{E6}
$$

This applies to the whole fixed infinite-dimensional sharp-low
centered sphere for each positive regularization parameter. The source
norm argument also tests any fixed compact source approximation into
the ambient space. Extending the paired-edge conclusion requires the
approximation's range in $N_c$ with the inherited form-domain
membership, as satisfied by $\mathcal R_\varepsilon$.
It does not contradict strong convergence on each individual input,
or give this lower bound on a finite frame or a spatially restricted
source class. Uniform accuracy on the stated sphere needs a
noncompact approximation mechanism or a source restriction excluding
this escaped family. This interface determines a boundary of the
bounded-window fit; it supplies no divergence result for the actual
projected inverse, no original all-input half-bound, and no signs on
a common cofinal sequence. Full Robin and RH remain unresolved.

## A bounded synthesis from the actual endpoint translations

This conditional paper interface retains the original $N$, $\nu$,
unitary $U$, domain and common correction from (R1)–(R6), (E1)–(E6)
and (G1)–(G4). The original theta tail supplies the additional
quantitative step below. Gamma, convolution, Hilbert–Schmidt and
compact-class convergence facts are reused. No new generic theorem,
numerical producer, Lean certification or originality claim is made.

For sufficiently large $R_0$ and $R\ge R_0$ put

$$
t(R)=\tfrac12\log\frac2{1+e^{-2R}},\qquad
n_R=n_{t(R)},\qquad
E_R(x)=\frac{G(x-R)+G(-x-R)}{\sqrt2\|G\|_2}.
$$

The original two-term theta tail improves (E2) to

$$
\|n_R-E_R\|_2\le C e^{-R}\qquad(R\ge R_0). \tag{NC1}
$$

To verify the rate, fix $A>t_c+1$. Write on the positive tail
$\Phi(x)=4\pi^2e^{9x/2-\pi e^{2x}}\ell(x)$, where the supplied
two-term expansion gives $\ell(x)=1+O(e^{-2x})$. Uniformly for
$t_c/2\le t<t_c$ and $x\ge A$, the dominant physical ratio equals

$$
\frac{v_0(x)\Phi(x-t)}{2\Phi(x)}
=\pi e^{-9t/2}e^{5x/2-(\pi/2)\eta_te^{2x}}
 \frac{\sqrt{1+e^{-x}}\ell(x-t)}{\sqrt{\ell(x)}}.
$$

The last factor is $1+O(e^{-x})$. After $x=R+y$ and division by
$A_{t(R)}$, its error is at most $Ce^{-R}G(y)e^{-y}$, whose
$L^2(dy)$ norm is finite. The compact-region, centering and
wrong-shift terms in (E1) have divided norm $O(e^{-5R/2})$; the
wrong-half ideal profile has that bound as well. Evenness pays the
other spatial tail. The overlap integrand of the two ideal profiles is

$$
e^{-5R}\exp\{-\tfrac\pi2(e^{2(x-R)}+e^{-2(x+R)})\}.
$$

Its integral is $O((1+R)e^{-5R})$: on $x\ge0$ drop the second
positive exponential and split $x-R$ at zero, then reflect.
Normalization therefore preserves the $O(e^{-R})$ error. This uses
the actual original-series remainder, without differentiating an
asymptotic or inferring a rate from (E2) alone.

For compactly supported coefficients in $L^2((R_0,\infty),dR)$
define $S_nh=\int_{R_0}^\infty n_Rh(R)dR$, and define $S_E$ with
the $E_R$ columns. Extending $h$ by zero, Young's convolution bound
and reflection make $S_E$ bounded. Equation (NC1) gives

$$
\|S_n-S_E\|_{\rm HS}^2
\le\int_{R_0}^\infty C^2e^{-2R}dR
=\tfrac12C^2e^{-2R_0}. \tag{NC2}
$$

Thus $S_n$ extends boundedly to all such $L^2$ coefficients. Finite
coefficient truncations have range in the closed $N_c$, so its full
range is in $N_c$. The infinite integral means this bounded extension;
pointwise absolute integrability for every coefficient is not assumed.
No lower frame bound or completeness for all of $N_c$ is asserted.

Use the unitary angular-frequency convention
$\widehat f(\xi)=(2\pi)^{-1/2}\int f(x)e^{-i\xi x}dx$.
The Euler substitution $v=(\pi/2)e^{2y}$ gives

$$
\widehat G(\xi)=\frac1{2\sqrt{2\pi}}
 (\pi/2)^{-(5/4-i\xi/2)}\Gamma(5/4-i\xi/2). \tag{NC3}
$$

The classical Gamma nonvanishing theorem gives a positive minimum
of $|\widehat G|$ on each fixed compact band. Define the bounded
coefficient map $W_\Lambda$ on sharp-low inputs by
$\widehat{W_\Lambda p}=\widehat p/(\sqrt{2\pi}\widehat G)$.
Then $G*(W_\Lambda p)=p$. The coefficient map need not preserve
evenness, and its norm is not asserted uniformly bounded as
$\Lambda$ grows. These are applications of the existing Gamma and
Fourier tools, not a new Wiener theorem.

## The actual low residual is Hilbert–Schmidt

Let $J_+$ restrict the coefficient line to $(R_0,\infty)$. Define
on the whole even sharp-low space

$$
\mathcal L_\Lambda p=\sqrt2\|G\|_2S_nJ_+W_\Lambda p,
\qquad K_\Lambda p=p-\mathcal L_\Lambda p. \tag{NC4}
$$

The principal map is bounded and has range in the original $N_c$.
For $h=W_\Lambda p$, compare its ideal version on $x>0$ with
$p(x)=\int_{\mathbb R}G(x-R)h(R)dR$. The residual has a missing
coefficient kernel $G(x-R)$ for $R<R_0$, and a reflected-tail kernel
$G(-x-R)$ for $R>R_0$. Their full squared kernel integrals are

$$
\begin{aligned}
\int_{x>0,\ R<R_0}|G(x-R)|^2dx\,dR
 &=\int_{y>-R_0}(y+R_0)|G(y)|^2dy<\infty,\\
\int_{x>0,\ R>R_0}|G(-x-R)|^2dx\,dR
 &=\int_{y<-R_0}(-y-R_0)|G(y)|^2dy<\infty.
\end{aligned}
$$

Evenness transports this residual to the negative half-line. The
actual-minus-ideal synthesis is Hilbert–Schmidt by (NC2). Composing
these maps with bounded $W_\Lambda$ proves that $K_\Lambda$ is
Hilbert–Schmidt on the entire even sharp-low space. This supplies
the original-theta interface; a generic compactness theorem alone
does not supply these kernels or their range in $N_c$.

For the actual centered class set
$\mathcal E_\Lambda=P_\Lambda L^2_{\rm even}\cap v_0^\perp$.
Each $\mathcal L_\Lambda p$ is exactly ground-orthogonal, since
each $n_R$ is. For $p\in\mathcal E_\Lambda$, $K_\Lambda p$ is
centered and lies in the original form domain: (SC1) admits $p$,
and the accepted critical-domain premise admits
$\mathcal L_\Lambda p\in N_c$ after transport by $U^{-1}$.

## A corrected fit converges uniformly at each fixed band

The actual correction $\mathcal R$ fixes $N_c$. Clason's normal
equation accepts arbitrary Hilbert data; its $B$-metric contraction
and the existing $cI\le B\le I/2$ on the centered space give
$\sup_{\varepsilon>0}\|\mathcal R_\varepsilon\|\le(2c)^{-1/2}$.
The known strong convergence consequently extends from the dense
form domain to all centered ambient inputs. Reuse that convergence
on the compact image of the $K_\Lambda$ unit ball, rather than
on the entire original unit ball.

Define the corrected common-source fit on $\mathcal E_\Lambda$ by

$$
\begin{aligned}
\mathcal R_{\Lambda,\varepsilon}p
 &=\mathcal L_\Lambda p+
    \mathcal R_\varepsilon K_\Lambda p,\\
\mathcal Rp-\mathcal R_{\Lambda,\varepsilon}p
 &=(\mathcal R-\mathcal R_\varepsilon)K_\Lambda p.
\end{aligned} \tag{NC5}
$$

For each fixed $\Lambda>0$, the right side tends to zero in
operator norm as $\varepsilon\downarrow0$. It also tends to zero
in Hilbert–Schmidt norm by the standard strong-times-Hilbert–Schmidt
convergence fact. Both terms of the fit lie in the same $N_c$.
The existing common critical-edge bound therefore gives

$$
\sup_{\substack{p\in\mathcal E_\Lambda\\\|p\|_2=1}}
 \|C_\pm U^{-1}(\mathcal Rp-\mathcal R_{\Lambda,\varepsilon}p)\|
\le\frac1{\sqrt2}
 \|\mathcal R-\mathcal R_{\Lambda,\varepsilon}\|_{
       \mathcal E_\Lambda\to L^2}
\longrightarrow0. \tag{NC6}
$$

The principal map is noncompact, consistently with (E5). Replacing
its synthesis by any fixed finite $R$ interval makes it compact
and cannot preserve this full-sphere uniform conclusion. The
construction is an infinite-source representation, without an
all-input finite acquisition algorithm or an effective regularization
rate. Constants depend on the band; no growing-band or common
cofinal error estimate is supplied. The full residual comparison,
original all-input half-bound, actual joint cofinal signs, full Robin
and RH remain unresolved. This is conditional paper analysis with
no new Lean certification or originality claim.


## Actual endpoint jets in the original form

Under the same original-theta, whole-critical-space minimal-domain,
mixed-nullity and coercive negative-edge premises as (NC1)–(NC6),
the original series supplies spatial and parameter jets of the
normalized endpoint columns. This is a conditional paper application
of that series and the existing
[global form comparison (WF2)](../Weil/fukushima2011dirichlet.md#transformed-form-and-a-global-derivative-comparison),
without a new generic regularization theorem, numerical producer,
Lean certification or originality claim.

Retain $t(R)$, $n_R$, $E_R$ and sufficiently large $R_0>0$. For
$j,\ell\in\{0,1\}$ there are finite original-series constants
$C_{j,\ell}$ such that

$$
\|\partial_x^j\partial_R^\ell(n_R-E_R)\|_2
\le C_{j,\ell}e^{-R},\qquad R\ge R_0. \tag{J1}
$$

To pay the derivatives, fix $A>t_c+1$ and write
$\Phi(x)=4\pi^2e^{9x/2-\pi e^{2x}}\ell_\theta(x)$ on
$x\ge A-t_c$. The first theta term gives
$\ell_\theta(x)=1-(3/(2\pi))e^{-2x}$ plus the terms with
$n\ge2$. Apply the supplied derivative polynomials to these terms
before removing the first exponential. Their normally convergent
series gives, for $0\le m\le2$,

$$
|\ell_\theta^{(m)}(x)-\mathbf1_{m=0}|
\le D_m e^{-2x},\qquad \inf_{x\ge A-t_c}\ell_\theta(x)>0.
$$

The polynomial factors $e^{2mx}$ in the remaining terms are absorbed
by $e^{-3\pi e^{2x}}$. This differentiates the original series,
rather than an asymptotic remainder.

Put $A_R=\pi e^{-9t(R)/2}e^{5R/2}$,
$d_R=A_R^{-1}Uw_{t(R)}$ and
$p_R=G(\cdot-R)+G(-\cdot-R)$. On the positive tail the dominant
term of $d_R$ is exactly $G(x-R)b(x,t(R))$, where

$$
b(x,t)=\frac{\sqrt{1+e^{-x}}\ell_\theta(x-t)}
              {\sqrt{\ell_\theta(x)}},\qquad
 t'(R)=\frac{e^{-2R}}{1+e^{-2R}}.
$$

For $j=0,1$ the same series bounds give
$|\partial_x^j(b-1)|\le De^{-x}$ and
$|\partial_x^j\partial_R b(x,t(R))|\le De^{-2R-2x}$.
After $y=x-R$, the errors are bounded by $e^{-R}$ times finite
linear combinations of $e^{-y}G(y)$, $e^{-y}G'(y)$ and
$e^{-y}G''(y)$, all in $L^2$. The compact-region, centering,
wrong-shift and wrong-half ideal jets are $O(e^{-5R/2})$:
$A_R'/A_R$ is bounded, and the wrong shift retains a uniform
positive tail exponent, including its differentiated series.
Reflection pays the other spatial tail. These facts prove (J1)
first with $d_R-p_R$ in place of $n_R-E_R$.

The ideal overlap and its $R$ derivative are
$O((1+R)e^{-5R})$, by differentiating the overlap integrand in
(NC1) and using the same two-half-line split. Set
$a_0=\sqrt2\|G\|_2$ and $a_R=\|d_R\|_2$. The preceding jet bounds
therefore give $a_R\ge a_0/2$ after increasing $R_0$,
$|a_R-a_0|=O(e^{-R})$ and $|a_R'|=O(e^{-R})$, using
$a_R'=\operatorname{Re}\langle d_R,d_R'\rangle/a_R$.
Spatial derivatives commute with this scalar normalization.
Substitute $n_R=d_R/a_R$ and $E_R=p_R/a_0$ to obtain (J1),
including the mixed spatial–parameter derivative.

Use $\|v\|_{\mathcal F_c}=\|U^{-1}v\|_{\mathcal F}$ for the
original minimal form norm in physical coordinates. The existing
(WF2) comparison supplies

$$
\|v\|_{\mathcal F_c}^2
\le c_0\|v\|_2^2+c_1\|v'\|_2^2,
\quad
c_0=\tfrac32+\|B_{\rm prime}\|
       +2M_2\|s'\|_\infty^2,
\quad c_1=2M_2\|s\|_\infty^2.
$$

Here $B_{\rm prime}$ is the complete prime operator in (WF1),
distinct from the negative-edge metric $B$ in (R3)–(R5).
Every prime power remains. The $C_{j,\ell}$ are unevaluated
original-series constants, rather than numerical certificates.
Ordinary spatial smoothness does not assert a source condition
for the actual small-window Gram.


## Truncate and sample only the actual compact residual

For $x>0$ define a kernel on the whole coefficient line by

$$
k_R(x)=\mathbf1_{R<R_0}G(x-R)
-\mathbf1_{R>R_0}G(-x-R)
-a_0\mathbf1_{R>R_0}(n_R-E_R)(x).
$$

Let $Hh$ be its integral against $h(R)$ on $x>0$, reflected evenly.
The missing and reflected squared kernel integrals are those in
(NC4), with $G$ replaced by $G^{(j)}$ for $j=0,1$; (J1) pays the
actual-error kernel. Even reflection preserves $H^1$, so $H$ is
Hilbert–Schmidt into $H^1$ and hence into the original
$\mathcal F_c$ by (WF2). The separate reflected columns need not
have zero derivative trace at zero; they are not declared $H^2$.

For $p\in\mathcal E_\Lambda$, the same $W_\Lambda$ gives

$$
K_\Lambda p=HW_\Lambda p=H_0W_\Lambda p,
\qquad H_0=Q_0H,
\quad Q_0=I-|v_0\rangle\langle v_0|. \tag{J2}
$$

The second equality uses the exact centering of $K_\Lambda p$.
It does not make $Hh$ centered for arbitrary coefficients.
Since the original constant has zero energy, $Q_0$ is contractive
in $\mathcal F_c$.

For $T>R_0$, restrict the coefficient kernel to $[-T,T]$, giving
$H_T$ and $H_{0,T}=Q_0H_T$. The same actual kernels imply

$$
\begin{aligned}
\|H_0-H_{0,T}\|_{\rm HS(L^2\to\mathcal F_c)}&\le d(T),\\
d(T)&=left[
2\sum_{j=0}^1c_j\int_{y>T}(y-T)|G^{(j)}(y)|^2dy
\right]^{1/2}\\
&\quad+left[
2\sum_{j=0}^1c_j\int_{y<-T}(-y-T)|G^{(j)}(y)|^2dy
\right]^{1/2}\\
&\quad+\|G\|_2 e^{-T}
    (c_0C_{0,0}^2+c_1C_{1,0}^2)^{1/2}.
\end{aligned} \tag{J3}
$$

The first integral comes from $R<-T$, the second from $R>T$,
and the last term truncates the actual-minus-ideal columns.
Their respective orders are super-exponential,
$O(e^{-5T/2})$ and $O(e^{-T})$. This truncates the
Hilbert–Schmidt residual, not the noncompact principal $S_n$.

Split $[-T,T]$ exactly at $R_0$. On its two open pieces the
kernel columns are continuously differentiable in $R$ with values
in $\mathcal F_c$. Equation (J1) supplies the uniform bounds

$$
\begin{aligned}
M_-&=[2(c_0\|G'\|_2^2+c_1\|G''\|_2^2)]^{1/2},\\
M_+&=M_-+a_0e^{-R_0}
       (c_0C_{0,1}^2+c_1C_{1,1}^2)^{1/2},\qquad
M=\max(M_-,M_+).
\end{aligned}
$$

For cells $I_i$ in these pieces, lengths $\Delta_i$ and midpoints
$R_i$, put $r_i=Q_0k_{R_i}^{\rm even}$ and define

$$
\begin{aligned}
D_{\Lambda,T,\mathcal I}p
 &=\sum_i r_i\int_{I_i}(W_\Lambda p)(R)dR,\\
\|K_\Lambda-D_{\Lambda,T,\mathcal I}\|_{
       \mathcal E_\Lambda\to\mathcal F_c}
 &\le Q_\Lambda
   [d(T)+M\Delta_{\max}\sqrt{T/6}],\qquad
Q_\Lambda=\|W_\Lambda\|.
\end{aligned} \tag{J4}
$$

The columns are centered and in the original minimal form domain
by (WF2). Reuse the midpoint mean-square column estimate:
its Hilbert–Schmidt sampling error is at most
$(\sum_iM_i^2\Delta_i^3/12)^{1/2}$, bounded by the displayed
mesh term because the total coefficient length is $2T$.
The split at $R_0$ avoids an across-jump derivative estimate.
All complex coefficients retain one actual $W_\Lambda$.

Equation (J4) is a joint parameter inequality in the original
jet constants, band inverse norm, tail cutoff and mesh.
It gives no band-independent constant. Column evaluation and
integration certification remain acquisitions to perform;
no sampled values or numerical producer are supplied here.
If finite coefficient-functional representations are required,
reuse the repository's
[finite Fourier-window supplier](../../Blueprint/D5/S3/Quantum/Analysis/FourierWindowFiniteRank.md).
The infinite principal synthesis remains present.


## Pay the finite remainder with the existing common-source certificate

The new kernel columns in (J4) can be used by the existing
[actual primal/dual residual certificate](../../docs/reports/theta-mixed-matrix/theta-common-residual-bounds.md),
conditionally on acquiring their simultaneous residual Gram.
This reuses (G4)'s metric inverse and the common coefficient estimate;
it is not a new generic Gram or projection theorem.

Write $\mathcal B=UBU^{-1}$ for the negative-edge metric on the
centered physical space, with $b_0I\le\mathcal B\le I/2$.
Retain the same $\mathcal R$ and $N_c$. Normalize the cells by

$$
e_i=\sqrt{\Delta_i}r_i,
\qquad z_i(p)=\Delta_i^{-1/2}\int_{I_i}(W_\Lambda p)(R)dR,
\qquad D_{\Lambda,T,\mathcal I}p=\sum_i e_i z_i(p).
$$

The normalized cell indicators are orthonormal in coefficient
$L^2$, so $\|z(p)\|_{\ell^2}\le Q_\Lambda\|p\|_2$.
There is no dimension factor or independent column optimization.
For each of these same $e_i$, choose an actual critical
$\eta_i\in N_c$ and an exact dual $\omega_i\in N_c^\perp$, and put

$$
b_i=\mathcal B(e_i-\eta_i)-\omega_i.
$$

A positive Hermitian upper Gram $G_b$ must certify
$\|\sum_i z_i b_i\|_2^2\le z^*G_bz$ for all complex coefficients.
Individual samples and the previously acquired quadratic-input rows
do not certify this different family. Each dual needs a legitimate
orthogonality witness; no completeness of a real-zero family or RH
is assumed.

The existing inverse $G_N=P_{N_c}\mathcal B|_{N_c}$ satisfies
$G_N(\mathcal R e_i-\eta_i)=P_{N_c}b_i$ and
$\|G_N^{-1}\|\le b_0^{-1}$. Retain the infinite principal map and set

$$
\begin{aligned}
\mathcal F_{\Lambda,T,\mathcal I}p
 &=\mathcal L_\Lambda p+\sum_i\eta_i z_i(p),\\
\sup_{\substack{p\in\mathcal E_\Lambda\\\|p\|_2=1}}
\|\mathcal Rp-\mathcal F_{\Lambda,T,\mathcal I}p\|_2
 &\le (2b_0)^{-1/2}\delta_\Lambda
       +\frac{Q_\Lambda}{b_0}\sqrt{\|G_b\|},
\end{aligned} \tag{J5}
$$

Here $\delta_\Lambda$ is any valid (J4) upper allowance.
Use the existing $\|\mathcal R\|\le(2b_0)^{-1/2}$ on
$K_\Lambda-D_{\Lambda,T,\mathcal I}$, then the same metric inverse
on its finite columns. The difference is critical, so both original
edge errors are bounded by the (J5) right side divided by $\sqrt2$.
They use one source family, coefficient map and simultaneous Gram.
Only the compact residual is finitely acquired.

For a growing band, sufficient conditions for the explicit (J5)
upper allowance to vanish are that $\delta_\Lambda\to0$ and
$Q_\Lambda\sqrt{\|G_b\|}\to0$ on the required common sequence.
These are not asserted necessary conditions for actual approximation. No numerical $G_b$, selected $\eta_i,\omega_i$,
effective regularization rate or finite all-input algorithm is
supplied. Equation (J5) does not say that an arbitrary finite dual
family can attain those residuals. The old quadratic-input experiment
is not rerun, and its values are not reassigned to these columns.

Under the inherited mixed-nullity premise,
$p-K_\Lambda p=\mathcal L_\Lambda p$ is critical, so the exact
original half-slack
$\mathfrak q(v)=D(U^{-1}v)-\|Q_0v\|_2^2/2$ satisfies
$\mathfrak q(p)=\mathfrak q(K_\Lambda p)$.
The usual bounded-form estimate gives, for $p\in\mathcal E_\Lambda$,

$$
|\mathfrak q(p)-\mathfrak q(D_{\Lambda,T,\mathcal I}p)|
\le\delta_\Lambda
 (2\|K_\Lambda\|_{\mathcal E_\Lambda\to\mathcal F_c}
   +\delta_\Lambda)\|p\|_2^2.
$$

This is an error bound, not positivity: a finite-rank approximation
has an infinite-dimensional low kernel, and its absolute error alone
cannot certify the entire low-space sign.

Equations (J1)–(J5) supply original-form residual, tail, mesh and
conditional acquisition interfaces. They give no small-eigenvalue
mass bound for the actual $\mathcal B^{1/2}UFF^*U^{-1}
\mathcal B^{1/2}$, hence no effective rate for the old
$(\mathcal R-\mathcal R_\varepsilon)K_\Lambda$.
Actual residual certification, source and archimedean costs,
low and complementary-low signs on one common cofinal sequence,
the full half-bound, Robin, RH and Lean certification remain
unresolved. Unevaluated series constants and paper reviews do not
supply numerical certificates or a runtime guarantee.
