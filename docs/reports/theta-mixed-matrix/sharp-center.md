# Actual sharp-band center and residual interface

This paper interface reuses the [inverse-residual comparison and polynomial
approximation source](../../../Library/Weil/liu2026tailcompensation.md),
the [actual transformed form](../../../Library/Weil/fukushima2011dirichlet.md)
(WF1)–(WF3), and the [original-series bounds](../../../Library/Analytic/romik2021orthogonal.md)
(WC1)–(WC5). These general methods are existing tools. The new question is whether the actual
sharp-band center has a prescribed finite approximation with a payable
complete remainder, on the even minimal realization.

Complex pairings, rank-one operators and coefficient Grams follow the
[first-slot-linear matrix convention](README.md#complex-inner-products-for-matrix-reports).

## Operator domain and complete block

Fix $c=3/8$, $N=64$, $\alpha=1/2-c=1/8$ and
$T=\widetilde A-cI+c|v_0\rangle\langle v_0|$, where
$v_0=\sqrt\rho$ and $\|v_0\|_2=1$.
Let $P=\mathbf1_{|\mathsf D|<N}$ on the even space and $Q=I-P$.
For even $u\in H^1$, bounded $s,s'$ put $su\in H^1$; (WF3) puts
$m(\mathsf D)su\in L^2$. Consequently

$$
Tu=\alpha u+s\,m(\mathsf D)(su)+c_\Gamma s^2u-Bu
       +c\langle u,v_0\rangle v_0. \tag{SC1}
$$

Every term is $L^2$. First (WF2) and its compact-core approximation
place every even $H^1$ vector in the actual minimal form domain.
Pairing (SC1) with the compact smooth even core gives the existing closed
form (WF1); form continuity extends that pairing to the form domain.
Its representation theorem therefore gives $H^1_{\rm even}\subset D(T)$
and (SC1), without a maximal-domain identification. In particular $P$ maps all even $L^2$
into $D(T)$ and $TP$ is bounded.

The [complete high restriction](joint-high-floor.md) has associated operator $C\ge\delta I$,
where the approved joint bound permits
$\delta=0.0383682545007734$. Put $K=QTP$ and

$$
S=PTP-K^*C^{-1}K. \tag{SC2}
$$

$K$ is bounded. This is a bounded Schur operator on the entire
infinite-dimensional center $PL^2_{\rm even}$, rather than a finite
compression. Completing the high-form square gives $T\succeq0$
if and only if $S\succeq0$. The high minimizer is $-C^{-1}Kp$
in the high operator domain. This invokes the standard positive
block elimination, retaining the original domain and all terms.

## Explicit cosine columns and localized prime tails

Use the isometric even Fourier coordinates $z(\eta)=\sqrt2\widehat p(\eta)$
on $[0,N]$, so

$$
p(x)=\frac1{\sqrt\pi}\int_0^N\cos(\eta x)z(\eta)d\eta.
$$

Define $H=T-\alpha I$ only on its domain. Its center-input map has
$L^2(dx)$-valued columns

$$
\begin{aligned}
h_\eta(x)=\frac1{\sqrt\pi}\bigg[&
s(x)m(\mathsf D)(s\cos(\eta\,\cdot))(x)
+c_\Gamma s(x)^2\cos(\eta x)\\
&-\sum_{n\ge2}w_ns(x)\{
s(x+t_n)\cos(\eta(x+t_n))
+s(x-t_n)\cos(\eta(x-t_n))\}\\
&+c\,v_0(x)\int_{\mathbb R}v_0(y)\cos(\eta y)dy\bigg],
\quad t_n=\log n,\quad w_n=\Lambda(n)/\sqrt n.
\end{aligned} \tag{SC3}
$$

The bare cosine is not asserted to belong to $D(T)$; (SC3) defines
columns after cancellation of the nonlocalized $\alpha$ term.
Both shifted directions and every prime power occur. Differentiation
in $\eta$ replaces each cosine by minus its own physical argument
times the sine, including $x+t_n$, $x-t_n$ and the mean integral.

Here are explicit, finite complete majorants. Write
$a_j=\|s^{(j)}\|_2$ for $j=0,1$, $X_j=\|x s^{(j)}\|_2$,
$s_\infty=\|s\|_\infty$, $V_j=\||x|^jv_0\|_1$ for $j=0,1$.
All exist by (WC2), $v_0=2\cosh(x/2)s$, and its superexponential tails.
The existing derivative data can supply $a_j$ without rerunning its grid.

Termwise differentiation of the positive symbol series gives
$|m'|\le(9/(4\sqrt3))\sum_{k\ge0}a_k^{-2}<7$,
where here $a_k=2k+1/2$; the sum is at most $4+1=5$.
Thus a modulation of $f\in H^1$ by any $|\eta|\le N$ satisfies
$\|m(\mathsf D)(fe^{i\eta x})\|_2
\le m(N)\|f\|_2+7\|f'\|_2$.

Let $b=3/8$, $r=e^{-b}$ and use the existing $K_0$ from (WC2).
Since $|t|\le e^{2|t|}/2$ and $8/(3e)<1$,
$|t|s(t)\le K_0e^{-(b/2)e^{2|t|}}$.
Also $e^{2|x|}+e^{2|x\pm\log n|}\ge2n$.
Allocate half the exponential to the pair and half to the $x$ tail.
With $q(x)=e^{-(b/2)e^{2|x|}}$, every unweighted or argument-weighted
shifted product is bounded by $K_0^2e^{-bn}q(x)$.
Consequently the two-direction prime column and its $\eta$ derivative
have $L^2$ norm at most

$$
J=2K_0^2\sqrt{e^{-b}/b}\left(\frac r{(1-r)^2}-r\right). \tag{SC4}
$$

This uses $w_n\le n$ and all integers $n\ge2$, hence pays every prime
power. The tail beyond an integer $L\ge1$ has the same prefactor times
$r^{L+1}((L+1)-Lr)/(1-r)^2$. This is an actual full-column error bound,
not just an energy tail or a bound at the retained modes.

Triangle and modulation bounds give

$$
\begin{aligned}
\sup_{0\le\eta\le N}\|h_\eta\|_2&\le M_0
:=\frac{s_\infty[(m(N)+|c_\Gamma|)a_0+7a_1]+J+cV_0}{\sqrt\pi},\\
\sup_{0\le\eta\le N}\|\partial_\eta h_\eta\|_2&\le M_1
:=\frac{s_\infty[(m(N)+|c_\Gamma|)X_0+7(a_0+X_1)]+J+cV_1}{\sqrt\pi}.
\end{aligned} \tag{SC5}
$$

Dominated differentiation gives $h\in H^1([0,N];L^2(dx))$.
Bochner integration of (SC3), followed by the existing form identity,
establishes $Hp=\int h_\eta z(\eta)d\eta$. Therefore $HP$ is
Hilbert–Schmidt and $\|K\|\le\|HP\|\le\sqrt N M_0$.

## Prescribed center remainder and exact ground-state removal

Let $E_M$ be the Fourier-side orthogonal projection onto constants on
the $M$ equal cells of $[0,N]$. The standard mean-zero interval Poincare
bound, applied to the Hilbert-space-valued columns, gives

$$
\|HP(I-E_M)\|\le\|HP(I-E_M)\|_{\rm HS}
\le\varepsilon_M:=\frac{N\sqrt N}{\pi M}M_1. \tag{SC6}
$$

All projections in this display act inside the sharp even center.
The compact remainder $L=S-\alpha I$ therefore satisfies

$$
\|L(I-E_M)\|\le d_M:=(1+\delta^{-1}\sqrt N M_0)\varepsilon_M.
\tag{SC7}
$$

This proves $S=\alpha I+\text{compact}$ by a prescribed approximation,
and bounds the discarded center. No unknown eigenbasis is involved.
The constants are deliberately coarse; no practical rank is asserted.

Let $p_0=Pv_0\ne0$. From the exact known $Tv_0=0$,
$Qv_0=-C^{-1}Kp_0$ and $Sp_0=0$.
Augment the cell space by this exact vector, writing $F_M$ for the
orthogonal projection onto $\operatorname{ran}E_M+\mathbb Cp_0$.
The (SC6) bound remains valid for $I-F_M$ since its range is contained
in $\ker E_M$. Self-adjointness then gives

$$
\|L-F_MLF_M\|\le2d_M. \tag{SC8}
$$

The approximant $\alpha I+F_MLF_M$ has the same exact ground nullvector.
On $p_0^\perp$, its finite retained block is $F_MSF_M$ and its remaining
block is $\alpha I$. A directed generalized-eigenvalue lower bound
$\lambda_M$ for the retained block on
$\operatorname{ran}F_M\cap p_0^\perp$ proves the sufficient condition

$$
2d_M<\min\{\alpha,\lambda_M\}\quad\Longrightarrow\quad S\succeq0.
\tag{SC9}
$$

Basis vectors may be defined by exact subtraction of their $p_0$ component.
Their Gram, overlaps and enclosure errors must be paid in $\lambda_M$;
a floating-point zero eigenvalue is not nullspace removal.

## Analytic columns give a smaller prescribed rank

The cell rate is a baseline, not a computational requirement. On the
Bernstein ellipse for $[0,N]$ of radius $\varrho=3/2$, put

$$
t=\frac N4(\varrho-\varrho^{-1})=40/3,
\qquad R_\eta=\frac N2+\frac N4(\varrho+\varrho^{-1})=200/3.
$$

The real-theta (WC2) bound gives, for $j=0,1$,

$$
A_j(t):=\|e^{t|x|}s^{(j)}\|_2
\le K_j\sqrt{\Gamma(t)/(2b)^t},\qquad
V(t):=\|e^{t|x|}v_0\|_1
\le2K_0\Gamma((t+1/2)/2)b^{-(t+1/2)/2}.
$$

These follow by $u=e^{2|x|}$ and enlarging the positive integrals from
$[1,\infty)$ to $[0,\infty)$. The Euler Gamma function here bounds
coefficient moments; it does not replace the original Gamma jump term.
For complex $\eta$ in that ellipse, $|\cos(\eta x)|,|\sin(\eta x)|
\le e^{t|x|}$. The original multiplier satisfies
$\|m(\mathsf D)f\|_2\le16(\|f\|_2+\|f'\|_2)$ by (WF3).
For shifted prime columns maximize
$u^{t/2}e^{-(b/2)u}$ over $u\ge1$; its upper bound is
$L(t)=(t/b)^{t/2}e^{-t/2}$. The same pair allocation as (SC4)
therefore bounds the entire complex prime column by $JL(t)$.
Thus the even cosine columns are entire as $L^2$-valued functions and
on this ellipse have the explicit norm bound

$$
M_\varrho=\frac{
16s_\infty[(1+R_\eta)A_0(t)+A_1(t)]
+|c_\Gamma|s_\infty A_0(t)+JL(t)+cV(t)}{\sqrt\pi}. \tag{SC11}
$$

Uniform exponential moments on a neighborhood justify the claimed
analyticity of the kinetic, full prime and mean terms. No complex
evaluation of the theta square root is required.

Let $E_d$ be the orthogonal projection onto polynomials in $\eta$ of
degree at most $d$ on $[0,N]$. Reuse the standard Bernstein-ellipse
Chebyshev tail bound, extending the scalar statement by Hilbert-space
duality. A degree-$d$ column polynomial has uniform error at most
$2M_\varrho\varrho^{-d}/(\varrho-1)$, so best $L^2$ approximation gives

$$
\|HP(I-E_d)\|\le\varepsilon_d
:=\sqrt N\frac{2M_\varrho}{\varrho-1}\varrho^{-d}.
$$

Augment the polynomial space by the exact $p_0$ as before. Its rank is
at most $d+2$, and the complete Schur remainder obeys

$$
e_d:=2(1+\delta^{-1}\sqrt N M_0)\varepsilon_d,
\qquad\|L-F_dLF_d\|\le e_d. \tag{SC12}
$$

Only the actual column bound is new model input; polynomial approximation,
Schur elimination and residual identities are reused tools.
The directed coefficient supplier, reusing the original derivative data
without its grid, gives $M_\varrho<1.910085\cdot10^9$ and
$e_{94}<0.04383817677622261<1/16$.
Hence a prescribed center of rank at most 96 suffices for this tail
accuracy. The uniform-cell baseline supplies the chosen sufficient count
5,206,493,707 for the same accuracy under its coarse first-derivative
majorants. This count is not claimed minimal.
Neither rank statement supplies the retained matrix sign, high residuals
or a total runtime estimate. A sufficient finite lower bound remains
$\lambda_{94}>e_{94}$ in addition to the already satisfied
$\alpha>e_{94}$.

## Complete inverse-coupling residuals

For one common retained family $p_i$, put $k_i=Kp_i$ and choose one common
high trial family $q_i=Q\psi_i$ with even $\psi_i\in H^1$.
(SC1) gives $q_i\in D(C)$ and $Cq_i=QTq_i$.
Thus the full $L^2$ residual is
$r_i=k_i-Cq_i=QT(p_i-q_i)$, evaluable through (SC1) and the original
theta callbacks. It includes the Gamma multiplier, all prime powers
and the full rank-one term, rather than a finite energy residual.
Reuse the positive inverse-residual comparison to obtain the Loewner
upper matrix $U$ defined, with common coefficients, by

$$
z^*Uz=2\Re\langle k(z),q(z)\rangle
-\langle Cq(z),q(z)\rangle+\delta^{-1}\|r(z)\|_2^2
\ge\langle k(z),C^{-1}k(z)\rangle. \tag{SC10}
$$

The finite lower Schur matrix is $[T(p_j,p_i)]-U$.
All cross terms and the residual Gram must use the same trials.
Complete numerical operator residuals, useful evaluated constants,
the retained matrix sign and cofinal $c\uparrow1/2$ remain missing.
These are paper model interfaces, with no new Lean or RH/Robin certificate.


## Directed suppliers and reproduction

The [coefficient program](sharp_center.py) reuses the
[approved derivative data](derivative-bandwidth-result.json) and loads the
canonical derivative program's AST prefix, stopping before its grid.
The [saved result](sharp-center-result.json) includes exact dyadic upper
endpoints, the input data hash, and both sufficient approximation sizes.
No derivative, deficit, joint-row or scalar grid is rerun.

For $u_R=e^6$ the supplied whole-line moments use

$$
X_j^2\le9a_j^2+\frac{K_j^2e^{-2bu_R}}{8b},\quad
s_\infty\le\sqrt{a_0a_1},\quad
V_0\le\sqrt6+\frac{2K_0u_R^{-3/4}e^{-bu_R}}b,\quad
V_1\le\sqrt{18}+\frac{K_0u_R^{-1/4}e^{-bu_R}}b.
$$

The first inequality uses $x^2\le e^{2|x|}/4$ on the two exterior tails;
the interior uses $|x|\le3$. The infinity bound is the standard
one-dimensional $H^1$ inequality. Interior mean moments use
$\|v_0\|_2=1$ and Cauchy–Schwarz; exterior moments use
$v_0=2\cosh(x/2)s$ and (WC2). The program uses $|c_\Gamma|<8$
and the 1024-term symbol sum with its decreasing integral tail.

The declared runtime is Python 3.13.12, python-flint 0.9.0 and 128-bit
ball arithmetic. From the repository root run

```sh
uv run --no-project --python 3.13.12 --with python-flint==0.9.0 python docs/reports/theta-mixed-matrix/sharp_center.py
```

This project-authored coefficient program uses the existing FLINT arithmetic;
dependency licensing is supplied by python-flint/FLINT. Its successful
coefficient comparisons supply the displayed remainder bounds. They do
not compute the retained Schur matrix or high correctors, provide a total
runtime bound, establish cofinal positivity, or certify RH/Robin in Lean.


## Retain this spatial weight in the complete inverse residual

For this section replace the fixed $c=3/8$, $N=64$ above by
$0<\varepsilon\le1/2$, $c=1/2-\varepsilon$ and
$N\ge N_w(\varepsilon)$ from the
[original weighted high estimate](../../../Library/Weil/fukushima2011dirichlet.md#spatially-weighted-high-inverse-at-every-subcritical-parameter).
Keep its actual $T_c,P,Q,C$, $\delta=\varepsilon/4$,
$w_{\varepsilon,N}=(\delta+a_Ns^2)^{-1}$ and
$b_{\varepsilon,N}>0$. This is a conditional paper allowance on the
original domain, with no new generic inverse theorem or Lean result.

For any finite common low family $p_i\in PL^2_{\rm even}$ and common
high trials $q_i\in D(C)$, put

$$
k_i=QT_cp_i,\qquad r_i=k_i-Cq_i,
\qquad p(z)=\sum_i z_ip_i,\quad q(z)=\sum_i z_iq_i,
\quad k(z)=\sum_i z_ik_i,\quad r(z)=\sum_i z_ir_i.
\tag{SC13}
$$

All are actual full operator residuals. The sharp low projection puts
$p_i$ in the original operator domain. The Gamma action, every prime
power, both shifted adjoints and the exact variance term remain in
$T_c$. A high projected residual is not assigned the unprojected
source's support or localization.

Reuse the inverse-residual identity already used in (SC10), whose
published supplier is [the source proof of Theorem B, section 4](../../../Library/Weil/liu2026tailcompensation.md#a-common-256-mode-consumer).
Apply (WH4) to the same residual and define the Hermitian allowance
$U_w$ by

$$
z^*U_wz=2\Re\langle k(z),q(z)\rangle-C[q(z)]
 +\int w_{\varepsilon,N}|r(z)|^2dx
\ge\langle k(z),C^{-1}k(z)\rangle.
\tag{SC14}
$$

Let $U_{\rm scalar}$ be the same expression with
$\delta^{-1}\|r(z)\|_2^2$ in place of the integral, and let
$G_s$ be the actual common residual Gram specified by
$z^*G_sz=\|sr(z)\|_2^2$. Equation (WH5) gives

$$
U_{\rm scalar}-U_w\succeq b_{\varepsilon,N}G_s\succeq0.
\tag{SC15}
$$

Thus the full finite Schur lower matrix
$[T_c(p_j,p_i)]-U_w$ dominates the existing scalar-residual comparison
by this explicit nonnegative source Gram. The saving is strict on any
coefficient direction with nonzero full residual; residual null
directions are retained. This comparison uses identical sources,
trials, parameter, bandwidth and high operator on both sides.

It also preserves an exact ground column. With $p_0=Pv_0$ and
$q_0=-Qv_0$, the known $T_cv_0=0$ gives
$k_0=Cq_0$ and $r_0=0$. Hence both residual-cost terms and all their residual cross entries
vanish on that column. The exact trial contribution
$2\Re\langle k_0,q_0\rangle-C[q_0]=C[q_0]$ remains; neither full
inverse allowance is claimed to vanish. No rounded ground vector or
independent source correction is substituted.

The weight has been established for every subcritical parameter, but
its full weighted residual entries have not been evaluated here.
Directed enclosures of those entries and all source errors are still
required for a numerical consumer. Actual low and complementary-low
signs remain necessary at every chosen $c_j\uparrow1/2$; (SC15) alone
proves neither sign, the endpoint half-bound, RH or full Robin.
The saved $N=64$ matrices and residuals are not data for these other
bands, and no old producer or new numerical target is executed.


## Keep the projection and ground corrections on the same residual

Use precisely the (SC13) common family and the same subcritical parameter,
bandwidth, full $T_c$ and high $C$ as (WH1). Reuse $J$ from the
[constrained weighted comparison](../../../Library/Weil/fukushima2011dirichlet.md#keep-the-high-constraint-and-the-exact-ground-term),
with its $A,R,g=Qv_0$ and $\beta$. Define the Hermitian allowance
$U_{\rm cw}$ by its value on every common coefficient vector:

$$
z^*U_{\rm cw}z=2\Re\langle k(z),q(z)\rangle-C[q(z)]+J(r(z))
\ge\langle k(z),C^{-1}k(z)\rangle.
\tag{SC16}
$$

The inverse-residual identity and (WH8) supply the inequality. Relative
to the identical weighted allowance (SC14), the exact saving is

$$
\begin{aligned}
z^*(U_w-U_{\rm cw})z
&=\langle P(wr(z)),A^{-1}P(wr(z))\rangle
  +\beta|\langle Rg,r(z)\rangle|^2\\
&\ge\delta\|P(wr(z))\|_2^2.
\end{aligned}
\tag{SC17}
$$

These are common-source Grams, retaining all cross entries. The ground
correction must use the same constrained $R$; independent full-space
projection and ground optima cannot be added. No support or localization
is assigned to the projected full residual.

A simpler admissible consumer defines
$z^*G_Pz=\|P(wr(z))\|_2^2$ and
$U_{\rm proj}=U_w-\delta G_P$. Then
$U_{\rm cw}\preceq U_{\rm proj}\preceq U_w$, and each remains above
the actual inverse-coupling matrix. This directly usable projection
credit requires no inverse computation on the infinite-dimensional
$PH$ and no new high trial family. Its Fourier projection entries and
all source errors still require directed enclosures.

For the exact ground column (SC13)--(SC15), $r_0=0$, so both new
correction matrices have zero ground row and column. The exact trial
contribution $C[q_0]$ remains. The corrections can vanish on other
directions, and the rank-one correction vanishes when $c=0$.
No uniform fractional saving or evaluated matrix is supplied. This
conditional paper interface reuses block and rank-one inversion;
actual low and complementary-low signs on one common cofinal sequence,
the endpoint half-bound, RH, full Robin and Lean certification remain
unresolved. Saved fixed-band matrices do not supply these entries.


## Pay weighted action errors with one common dual source

Keep exactly (SC13)'s actual WH1 parameter, bandwidth and full residual,
with high trials chosen in $H^2_{\rm even}\cap QH$. This extra trial
regularity pays (WA4); it does not replace the domain of the high form.
Low-band sources and these high trials are in the original operator
domain. Include the exact ground trial $(p_0,q_0)=(Pv_0,-Qv_0)$.
Reuse its existing [ground-complement construction](ground-residual.md#one-residual-map-on-the-exact-ground-complement),
not a rounded ground column. For the same coefficient vector $z$ set

$$
\begin{aligned}
t(z)&=\langle p(z),p_0\rangle/\|p_0\|^2,\\
q_\perp(z)&=q(z)+t(z)Qv_0,\\
u_\perp(z)&=p(z)-q(z)-t(z)v_0.
\end{aligned}
\tag{SC18}
$$

The known $T_cv_0=0$ gives $QT_cu_\perp(z)=r(z)$.
The ground vector has $u_\perp=q_\perp=0$. All these maps share the
same coefficients; $su_\perp\in H^2$ follows from the selected trials,
the sharp low band, and the existing theta derivative bounds.
For a complex multiple $p=\zeta p_0$, $q=-\zeta Qv_0$, the declared
convention gives $t=\zeta$ and $u_\perp=q_\perp=0$, including
$\zeta=i$.

Let $F=M_V+c|v_0\rangle\langle v_0|$ on the full even space.
The standard shorting and rank-one inversion used in (WH6)--(WH8)
give, with $\eta=c/(1+c\langle v_0,M_wv_0\rangle)$,

$$
\begin{aligned}
J(r)&=\min_{h\in PH}\langle r+h,F^{-1}(r+h)\rangle,\\
F^{-1}&=M_w-\eta|wv_0\rangle\langle wv_0|.
\end{aligned}
\tag{SC19}
$$

This is a reuse of the bounded positive block formula, not a new
inverse theorem. The low compressed inverse of $F^{-1}$ exists since
$\delta I\preceq F\preceq(V_{\max}+c)I$. The variational comparison
with the actual high form remains that of (WH7); no maximal domain or
commutation of $Q$ with a multiplier is assumed.

Choose the common low trial $h(z)=PH_cu_\perp(z)$. Since
$Qu_\perp=-q_\perp$,

$$
r(z)+h(z)=H_cu_\perp(z)-\varepsilon q_\perp(z)=:a(z).
\tag{SC20}
$$

Thus this trial recovers an unprojected full action rather than assigning
localization to $r$. It need not be the minimizing trial in (SC19).
Set $a_{J,L}=H_{c,J,L}u_\perp-\varepsilon q_\perp$ using the full
retained action from (WA4). Define actual common Hermitian Grams by

$$
\begin{aligned}
z^*G_0z&=\|u_\perp(z)\|_2^2,&
z^*G_2z&=\|(su_\perp(z))''\|_2^2,\\
z^*G_{J,L}z&=\int w|a_{J,L}(z)|^2dx
 -\eta|\langle wv_0,a_{J,L}(z)\rangle|^2.
\end{aligned}
\tag{SC21}
$$

For any fixed $\theta,\tau>0$ and the complete (WA1)--(WA3)
budgets on that same source, put

$$
G_E=(1+\theta)b_\Gamma^2G_2
 +(1+\theta^{-1})b_{\rm p}^2G_0.
$$

The weighted action error obeys
$\|\sqrt w(a-a_{J,L})\|_2^2\le z^*G_Ez$.
Since $0\preceq F^{-1}\preceq M_w$, the usual squared-norm
inequality and (SC19)--(SC20) yield

$$
\begin{aligned}
\langle r(z),C^{-1}r(z)\rangle
&\le J(r(z))\le\langle a(z),F^{-1}a(z)\rangle\\
&\le z^*[(1+\tau)G_{J,L}+(1+\tau^{-1})G_E]z.
\end{aligned}
\tag{SC22}
$$

Use this last expression in place of the residual cost in (SC16) to
obtain an upper Hermitian inverse-coupling allowance. This pays the
omitted-action component of the same weighted input without solving
$A^{-1}$ or taking $Q$ through the weight. The ground and low dual
trial are evaluated jointly through $F^{-1}$, rather than summing
independently optimized corrections.

Every displayed Gram has exact zero ground row and column, because
$u_\perp=q_\perp=a_{J,L}=0$ there. The full trial contribution
$2\Re\langle k_0,q_0\rangle-C[q_0]=C[q_0]$ remains. Directed upper
Gram enclosures must preserve that exact null column. The derivative
and norm Grams belong to the common complement maps, not to
independently optimized columns or a scalar error charged on the ground.

The selected dual trial can cost more than the minimizing (SC19) trial;
no domination of $U_w$, evaluated saving or matrix sign is supplied.
The actual retained actions, derivative/source Grams and their directed
quadrature and input-error enclosures remain unevaluated. Growing
$a_N$ alone does not control the bandwidth-dependent derivative Gram.
This conditional paper consumer reuses the published inverse tools and
existing action envelopes. The common cofinal low/complementary-low
signs, endpoint half-bound, RH, full Robin and Lean certification
remain unresolved; the saved $N=64$ data are not transported here.


At the original $N=64,c=3/8$, the
[direct saved-joint-field input](joint-weighted-input.md) supplies a
different positive weight from the already retained pointwise high
floors, together with an evaluated common ground-complement action-tail
budget. It reuses this dual-source algebra with that separately justified
high weight, rather than assigning (WH1) to the old band. The differing
old low/high action cutoffs keep the fixed trial $Z$ unchanged. Weighted
retained-action Grams and their step-boundary integration errors still
require directed enclosures.
