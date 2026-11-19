# Original finite-record acquisition of bounded local-energy pairings

> Reference theory with ordinary conditional proofs. The cited source and
> endpoint results are premises, not freshly verified Lean statements.
> No kernel verification or worldwide novelty is asserted.
> After incorporation, corrections and further results belong after the final
> append anchor; existing text remains unchanged.

## 1. The unchanged source, target and finite information

**Definition 1.1 (original source and target).** Use precisely
[W, Assumption 1.1 and Definition 1.2][W], including its source suppliers
[E, §§109–112][E] and [S, §§115–117, 120][S]. Thus

$$
\begin{gathered}
G=H^1\times\mathbb R,\quad e=(0,0,0,0),\quad
pp'=(x+x',y+y',z+z',w+w'+xy'),\quad d\mu=dx\,dy\,dz\,dw,\\
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\quad L=-\sum_{j=1}^3X_j^2,\quad
L\Gamma=\delta_e,\quad \Gamma\circ\delta_s=s^{-3}\Gamma,\\
\delta_s(x,y,z,w)=(sx,sy,sz,s^2w),\qquad a,\eta,d>0.
\end{gathered}
\tag{1.1}
$$

The minimal expression is
$aL-\eta\partial_w^2-16\sqrt{a\eta}\Gamma$ on the punctured smooth
compact core. Retain its adjoint $S^*$, original coefficient maps $A,C$,
coefficient-positive unit zero state $h$, and full complex endpoint

$$
\begin{gathered}
D(H)=\{u\in D(S^*):A(u)=\rho C(u)\}
       =D(\overline S)\dotplus\mathbb Ch,\quad
\rho=A(h)/C(h),\quad H\ge0,\quad\ker H=\mathbb Ch,\\
D(F)=\{u\in D(S^*):C(u)=0\},\quad F\ne H,\quad
m=h^2\mu,\quad \|h\|_2=1,\quad m(G)=1,\\
J_hv=hv,\quad K=J_h^{-1}HJ_h,\quad T_t=e^{-tK},\quad
b=g_d,\quad P=T_d,\quad
c=\frac1{4(1+\|g_d\|_\infty)}.
\end{gathered}
\tag{1.2}
$$

The positive smooth representative of $h$ is used only off $e$.
The actual source starts at $e$, the first read is at $2d$, subsequent
gaps are $d$, and the four emissions remain

$$
f_3=cb,\qquad f_B=\tfrac14,\qquad
f_0=f_1=\tfrac38-\tfrac12 f_3.
\tag{1.3}
$$

All permitted null repairs remain permitted. Conditional on the same
undisturbed path the read noises are fresh and independent. Write
$F_\varnothing=1$, $F_{yu}=f_yPF_u$ and
$p(u)=\langle Pb,F_u\rangle_m$. Inner products are antilinear in the
first slot. Put $\mathcal W=\{3,B\}^*$ as in [W, §2]. The declared
finite menu consists of triples $(u,v,\theta)$ with $u,v\in\mathcal W$
and positive rational $\theta$. Its target is

$$
\begin{gathered}
v_u=c^{-1/2}P^{1/2}F_{u3},\qquad
\gamma=d\left(a\sum_{j=1}^3(X_jb)^2+
                         \eta(\partial_wb)^2\right),\\
Q(u,v,\theta)=\langle v_u,M_{(1+\theta\gamma)^{-1}}v_v\rangle_m.
\end{gathered}
\tag{1.4}
$$

This is exactly the off-source energy field in [W, (12.2)]; its value
at the $m$-null point $e$ is immaterial. The marked identity [W, (2.8)]
gives $\|v_u\|_m^2=p(u^Ru3)\le1$. Positivity preservation gives
$v_u\ge0$, hence $0\le Q\le1$. An inconclusive computation therefore
always has the valid enclosure $[0,1]$. No word probability replaces
the energy-sensitive target (1.4).

**Definition 1.2 (allowed finite packet).** Retain [W, Definition 9.1].
A preselected $\ell\ge0$ fixes $T=2\ell+3$ and $K_T=4^T$. From
$N+T$ actual labels, through physical time $(N+T+1)d$, retain the full
$4^{T+1}$ counters and use

$$
\begin{gathered}
Z=\sum_{v\in\mathcal L^T}A(3v),\quad
\widehat\nu(v)=\frac{A(3v)+1}{Z+K_T},\quad \widehat c=Z/N,\\
0<D_0^-\le d_{1/(4d)},\quad 0<D_N^-\le d_{1/(Nd)},\quad
D_0^-,D_N^-\le1,\quad t>0,\\
\overline V=\frac{2T+1}{4N}+2\frac{1-D_N^-}{D_N^-},\quad
\alpha=\min\left(1,\frac{4^{T+1}}t
                       \sqrt{\overline V/D_0^-}\right),\quad
e_p=\min\left(1,\frac{Nt+K_T}{Z+K_T}\right).
\end{gathered}
\tag{1.5}
$$

Nonrational upper bounds are enclosed upward rationally. The defects
are legally supplied, validated and charged as in that contract;
labels do not supply them. No numerical original coefficients or
physical clock are added. Packet choices and failure allowances
precede consultation of that packet's record. The single supplied
event $\mathcal E$ satisfies

$$
\begin{gathered}
\mathbb P_e(\mathcal E)\ge1-\alpha,\quad
\sum_v|A(3v)/N-cp(v)|\le t,\quad
|\widehat p(w)-p(w)|\le e_p\quad(|w|\le T),\\
c\in[c_-,c_+],\quad c_-=[\widehat c-t]_+,\quad
c_+=[\widehat c+t]_{[0,1]}.
\end{gathered}
\tag{1.6}
$$

The last interval is [W, Definition 10.1], on this same event. The
present consumer uses only it and $\widehat p(3)\pm e_p$ from the
record. One may predeclare $\ell=0,T=3$, using 256 counters even for
long query words; their extra cost is deterministic computation.
A previously supplied larger legal packet can also be used.

[W]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_WORD_GEOMETRY_RECOVERY.md
[R]: RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md
[E]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md
[S]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md

## 2. Reference reduction and finite calibration

**Theorem 2.1 (the invariant target and a bracketed reference time).**
Every requested $Q$ equals its counterpart in the original reference
member $a=\eta=1$ at time $\tau=a^2d/\eta$, with that member's
normalized $h,m$ and full non-Friedrichs endpoint. No numerical name
of the actual $a,\eta,d$ is required. On $\mathcal E$, when $c_->0$,
put

$$
\begin{gathered}
p_-=[\widehat p(3)-e_p]_+,\quad
p_+=[\widehat p(3)+e_p]_{[0,1]},\quad
I_-=p_-/c_+,\quad I_+=p_+/c_-,\\
\Phi(t)=\|g^{\rm ref}_{3t/2}\|_{m_{\rm ref}}^2.
\end{gathered}
\tag{2.1}
$$

Positive rational $L<U$ certify $L<\tau<U$ whenever outward reference
evaluations prove

$$
\Phi(L)>I_+,\qquad \Phi(U)<I_-.
\tag{2.2}
$$

For a fixed source, packet errors $t,e_p\to0$ permit successful
brackets of every positive width at sufficient deterministic precision.

*Proof.* Reuse the entire-domain transport in [W, Theorem 5.2]. For
$a'=\kappa a/s^2$, $\eta'=\kappa\eta/s^4$, $d'=d/\kappa$,
the unitary $\mathcal W_sf=f\circ\delta_s$ transports $m,K$, the
trace, entrance, prescribed $c$, four emissions and words. Its raw
counterpart transports $D(S^*)$ and the full complex selector,
including $A'(\mathcal U_su)=s(A(u)-\log(s)C(u))$ and
$C'(\mathcal U_su)=sC(u)$. Thus it selects the actual full endpoint.
The first epoch $2d'$ maps to $2d$ and each later gap $d'$ to $d$.
On the punctured smooth source,
$X_j\mathcal W_sb=s\mathcal W_sX_jb$ and
$\partial_w\mathcal W_sb=s^2\mathcal W_s\partial_wb$.
Substitution gives $\gamma'=\mathcal W_s\gamma$ and
$v'_u=\mathcal W_sv_u$, proving invariance of (1.4).
Choose $s^2=\eta/a$, $\kappa=\eta/a^2$ to obtain $(1,1,\tau)$.
This is a mathematical model correspondence, not a change of the
running source or a numerical evaluation of physical parameters.

[W, Theorem 5.3] gives $p(3)/c=\Phi(\tau)$ and continuous strict
decrease of $\Phi$ on $(0,\infty)$. This proves (2.2). The reference
services below compute $w_t=hg_t$ globally, hence
$\Phi(t)=\|w_{3t/2}\|_2^2$. A raw error $\varepsilon$ on $U$
gives squared-norm error at most
$\varepsilon(2\|U\|+\varepsilon)$. No supremum calibration enters.
Since $c>0$, shrinking marker intervals and probability errors give
$I_-,I_+\to\Phi(\tau)$. For fixed rational $L<\tau<U$ the two
strict gaps are positive, and sufficiently accurate evaluations
recognize them. Choose rational endpoints arbitrarily close to
$\tau$ to prove the width assertion. No inverse derivative bound
for $\Phi$ is used. A finite bracket search that has not certified
both inequalities returns inconclusive; it does not wait forever
for a loose packet to yield a bracket. $\square$

## 3. Computed raw graph data and local gradient certificates

In §§3–7 unprimed operators and raw vectors refer to the reference
member. The unknown $\tau$ remains in its certified bracket.

**Definition 3.1 (existing services and computed graph data).** A raw
name returns rational complex box steps with certified global
$L^2(\mu)$ errors at requested precisions. Reuse [R, §11 and
Theorems 12.2–12.4][R], which construct $h$, the full resolvent
$R_H=(H+1)^{-1}$ and the raw source vector $z$ satisfying

$$
w_t=hg_t=(H+1)e^{-tH}z,\qquad S_t=e^{-tH}.
\tag{3.1}
$$

Here $z$ names a vector, separately from the third coordinate.
Generate a rational $Z_0\ge\|z\|_2$ from a finite approximant and
its error. The fixed reference coefficients are rational; this
calculation uses the precise-family prior, not original coefficient
measurements. In particular $z\in D(H)$ is not presumed.

The same resolvent service computes $Hw_t$. For $0<x\le1$, set

$$
q_{0,t}(x)=x^{-1}e^{-t(x^{-1}-1)},\quad
q_{1,t}(x)=(x^{-2}-x^{-1})e^{-t(x^{-1}-1)},\quad q_{j,t}(0)=0.
\tag{3.2}
$$

Then $w_t=q_{0,t}(R_H)z$, $Hw_t=q_{1,t}(R_H)z$. Both zero
extensions are continuous. For rational $t>0$ and rational $E>e^t$,
valid Lipschitz bounds in $x$ for these two functions are

$$
E(4/t^2+27/t^2),\qquad
E(54/t^3+4/t^2+256/t^3+27/t^2),
\tag{3.3}
$$

respectively. Indeed, with $y=1/x$, their derivative magnitudes are
bounded by $E(y^2+ty^3)e^{-ty}$ and
$E(2y^3+y^2+ty^4+ty^3)e^{-ty}$, and
$\sup_{y\ge0}y^ke^{-ty}\le(k/t)^k$. Bernstein approximation of
degree $n$ has uniform error at most its Lipschitz bound divided by
$2\sqrt n$, plus coefficient rounding. Expand the rational polynomial
as $\sum a_jx^j$. Initial vector error $e$ and resolvent-action errors
$\beta_i$ give the explicit output bound

$$
Z_0\varepsilon_{\rm scalar}
 +\sum_j|a_j|\left(e+\sum_{i=1}^j\beta_i\right)
 +\varepsilon_{\rm arith}.
\tag{3.4}
$$

This follows from $\|R_H\|\le1$ and spectral calculus, exactly the
construction of [R, Theorem 12.4] applied to (3.2). Every term is
computed or requested; no spectral floor is needed at $x=0$.

Put $B_0(L)=1$, $B_j(L)=(j/L)^j$ for $j\ge1$, and

$$
G_0=Z_0(1+B_1(L)),\quad C_0=Z_0(B_1(L)+B_2(L)),\quad
C_1=Z_0(B_2(L)+B_3(L)).
\tag{3.5}
$$

Smoothing before powers of $H$ and the spectral theorem give, for
$s,t\ge L$,

$$
\begin{gathered}
\|w_t\|_2\le G_0,\quad \|w_t-w_s\|_2\le C_0|t-s|,\quad
\|Hw_t-Hw_s\|_2\le C_1|t-s|,\\
\|S_t-S_s\|\le |t-s|/L,\quad
\|S_{t/2}-S_{s/2}\|\le |t-s|/L.
\end{gathered}
\tag{3.6}
$$

For example $\partial_tw_t=-H(1+H)e^{-tH}z$ gives $C_0$;
applying $H$ gives $C_1$. The heat bounds follow from
$\sup\lambda e^{-L\lambda}\le1/L$, including the half-time scaling.

**Definition 3.2 (evaluated punctured geometry).** Let $K$ be a finite
union of closed rational boxes with disjoint interiors, and choose a
bounded finite union of open rational boxes $\Omega$ such that
$K\subset\Omega$ and $\overline\Omega\subset G\setminus\{e\}$.
Write $V_K=\mu(K)>0$. Choose an explicit $C^1$ cutoff $0\le\chi\le1$,
equal to one on $K$, compactly supported in $\Omega$, with rational
$B_\chi\ge\|\nabla\chi\|_\infty$. Coordinate transition factors
$3r^2-2r^3$ on $[0,1]$, constant outside, have derivative at most
$2$. Products give box cutoffs; $1-\prod_i(1-\chi_i)$ gives their
union cutoff. Sum their coordinate derivative bounds
$2/\text{transition width}$ to obtain $B_\chi$.

If $|x|\le M_x$ on $\Omega$, take rational bounds

$$
\begin{gathered}
\Lambda=2+M_x^2,\quad\lambda=1/\Lambda,\quad
A_{\rm raw}=\begin{pmatrix}
1&0&0&0\\0&1&0&x\\0&0&1&0\\0&x&0&1+x^2
\end{pmatrix},\quad \lambda I\le A_{\rm raw}\le\Lambda I,\\
H_{\rm loc}=-\operatorname{div}(A_{\rm raw}\nabla)-V,\quad V=16\Gamma,
\quad \mathcal Df=(\partial_xf,\partial_yf+x\partial_wf,
                                      \partial_zf,\partial_wf).
\end{gathered}
\tag{3.7}
$$

The $y,w$ block has determinant one and trace $2+x^2$, proving these
ellipticity bounds. Also $|\mathcal Df|^2\le\Lambda|\nabla f|^2$.
The column divergences vanish, so the actual expression is
$-\partial_{xx}-\partial_{yy}-\partial_{zz}
 -(1+x^2)\partial_{ww}-2x\partial_{yw}-V$; no first-order shear
term is omitted.

Generate rational $r_*>0$ with
$\varrho=(|(x,y,z)|^4+(w-xy/2)^2)^{1/4}\ge r_*$ on
$\overline\Omega$ by interval subdivision. The polynomial under
the root vanishes only at $e$, so this terminates. [R, (10.12)]
gives $0\le V\le V_*:=512r_*^{-3}$. Uniform names of $V$ on
$\overline\Omega$ are already constructed in [R, §11.2,
(11.10)–(11.11)]. Its real-contour charts cover positive lower
bounds for $|(x,y,z)|^2$; shifted-contour charts cover either sign
of $w-xy/2$ bounded away from zero. Thus central-axis boxes are
included. Only the published value estimates are used, without
differentiating their infinite tails.

**Theorem 3.3 (generated source gradient certificates).** Let $u=h$
or $u=w_s$ for rational $s>0$, and let $f=Hu$ with its constructed
raw name ($f=0$ for $h$).
For a real rational polynomial $P_{\rm loc}$ compute upper bounds

$$
a\ge\|u-P_{\rm loc}\|_{L^2(\Omega)},\qquad
b\ge\|f-H_{\rm loc}P_{\rm loc}\|_{L^2(\Omega)}.
\tag{3.8}
$$

With outward square roots define

$$
\mathcal C(a,b)=\left[\frac{2ab}{\lambda}
 +\left(\frac{2V_*}{\lambda}
       +\frac{4\Lambda^2B_\chi^2}{\lambda^2}\right)a^2\right]^{1/2}.
\tag{3.9}
$$

Then $\|\mathcal D(u-P_{\rm loc})\|_{L^2(K)}
\le\sqrt\Lambda\mathcal C(a,b)$. A total search from the stated
reference services finds such polynomials with both this bound and
$a$ below any prescribed positive rational. If a polynomial was
tested at rational $t_0\in[L,U]$ for $w_{t_0}$ with bounds $a_0,b_0$,
then for every $\tau\in[L,U]$ it suffices to use

$$
a=a_0+C_0\Delta,\quad b=b_0+C_1\Delta,\quad\Delta=U-L.
\tag{3.10}
$$

*Proof.* [S, (120.5)–(120.7)] and positive-time smoothing give smooth
representatives of $h,w_s$ on punctured neighborhoods. Multiplication
by smooth positive $h$ transports the cited weak equation to the
actual raw expression (3.7). Thus these vectors are local $H^1$
solutions of $H_{\rm loc}u=f$. No boundary condition on $\Omega$
is imposed. Put $v=u-P_{\rm loc}$ and test with $\chi^2v$.
Compactly supported $H^1$ test approximation justifies the $C^1$
cutoff. Taking real parts and writing $X=\|\chi\nabla v\|_2$ gives

$$
\lambda X^2\le ab+V_*a^2+2\Lambda B_\chi aX
\le ab+V_*a^2+\tfrac\lambda2X^2
                    +\frac{2\Lambda^2B_\chi^2}{\lambda}a^2.
\tag{3.11}
$$

Rearrangement proves (3.9); (3.7) converts Euclidean gradients to
the four source fields. This is the elementary Caccioppoli test
inside the source-specific certificate, with every constant shown.

To evaluate (3.8), restrict the global names of $u,f$ to $\Omega$.
Polynomial norms on rational box unions are computable by finite
partition and integration. A uniform $V$ error $\epsilon$ changes
$H_{\rm loc}P_{\rm loc}$ in local $L^2$ by at most
$\epsilon\|P_{\rm loc}\|_{L^2(\Omega)}$. Thus norms of its
differences from raw steps have arbitrarily accurate enclosures.
Add the raw input errors by the triangle inequality. These are
evaluated strong residual norms, without differentiating a raw step.

Enumerate rational polynomials and precisions and accept strict
tests on evaluated $a$ and $\sqrt\Lambda\mathcal C(a,b)$.
For termination only, extend the smooth $u$ from a neighborhood of
$\overline\Omega$ by a cutoff to a compactly supported smooth
function on $\mathbb R^4$. On an enclosing box, tensor Bernstein
polynomials approximate it with derivatives through order two.
Indeed their differentiated formulas are Bernstein averages of
scaled first and second forward differences; the integral formulas
for these differences and uniform continuity of the derivatives
give uniform convergence. Rational approximation of the finitely
many coefficients preserves it. Hence polynomials in the enumeration
make both $P_{\rm loc}\to u$ and $H_{\rm loc}P_{\rm loc}\to f$
uniform on $\overline\Omega$. Their measured residuals and (3.9)
tend to zero, so a strict test eventually passes.

Smoothness supplies a termination argument, not an unevaluated
numerical supplier: every accepted derivative radius is the explicit
(3.9) with computed residuals. There is no unnamed $C_K$, modulus,
derivative supremum or local-solution input. Equation (3.10) follows
from (3.6) before applying the same energy test. The full-domain
vectors are retained and no estimate crosses $e$. $\square$

## 4. Removing division and large-gradient oracles

**Definition 4.1 (a computed small-denominator allowance).** On $K$,
for rational $\delta>0$ define the bounded $1/\delta$-Lipschitz function

$$
\phi_\delta(r)=\begin{cases}
1&r\le\delta,\\2-r/\delta&\delta<r<2\delta,\\0&r\ge2\delta.
\end{cases}
\tag{4.1}
$$

For a real raw step $H_e$ with $\|h-H_e\|_2\le e$, compute

$$
J_\delta=\min\left\{V_K,
\int_K\phi_\delta(H_e)\,d\mu+\sqrt{V_K}\,e/\delta\right\}.
\tag{4.2}
$$

Use outward rational bounds. The integral is a finite exact step sum;
Lipschitz continuity gives $\mu(K\cap\{h<\delta\})\le J_\delta$.
A total search makes $J_\delta$ smaller than any positive rational:
since $h>0$ a.e., dominated convergence gives
$\int_K\phi_\delta(h)\to0$; take $\delta=2^{-n}$ and raw error
$e\le2^{-2n}$, refining if needed. No numerical $\inf_Kh$ is supplied.

**Theorem 4.2 (acquisition of the actual bounded energy multiplier).**
Fix rational $0<L<U$, $t_0\in[L,U]$, $\theta>0$ and a localization.
Choose real rational polynomials $P_h,W$ with evaluated bounds
$a_h,b_h$ for $h$ and $a_0,b_0$ for $w_{t_0}$ as in (3.8). Put

$$
\begin{gathered}
a_w=a_0+C_0\Delta,\quad b_w=b_0+C_1\Delta,\quad
\eta_h=\sqrt\Lambda\mathcal C(a_h,b_h),\quad
\eta_w=\sqrt\Lambda\mathcal C(a_w,b_w),\\
d_h=\|\mathcal DP_h\|_{L^2(K)},\quad
d_w=\|\mathcal DW\|_{L^2(K)},\quad
\widehat N=P_h\mathcal DW-W\mathcal DP_h,\\
E_N=\eta_w+a_hd_w+G_0\eta_h+a_wd_h,\quad
B_N\ge\sup_K|\widehat N|,\\
\widehat g_\delta=\widehat N/\max(P_h,\delta)^2,\quad
\widetilde k=(1+\theta t_0|\widehat g_\delta|^2)^{-1},\quad
E_g=\delta^{-2}E_N+2\delta^{-3}B_N\sqrt{V_K}\,a_h.
\end{gathered}
\tag{4.3}
$$

Norms and polynomial bounds are enclosed upward. For any rational
$j>0$, a rational box step $k$ on $K$ can be computed with
$0\le k\le1$ and $\|k-\widetilde k\|_{\infty,K}\le j$.
For every $\tau\in[L,U]$ the true reference field obeys

$$
\begin{gathered}
\gamma_\tau=\tau|\mathcal D(w_\tau/h)|^2,\quad
k_{\theta,\tau}=(1+\theta\gamma_\tau)^{-1},\\
\|k_{\theta,\tau}-k\|_{L^1(K)}\le E_k,
\quad E_k=J_\delta+\sqrt{\theta t_0}\,E_g
                     +V_K\Delta/(4L)+V_Kj.
\end{gathered}
\tag{4.4}
$$

All terms are generated from allowed data. At fixed source, positive
time and compact, these certificates attain every positive error
by joint refinement of bracket, residuals, denominator allowance and
mesh; no uniform local jet service is required.

*Proof.* Write $w=w_\tau$, $N=h\mathcal Dw-w\mathcal Dh$.
The quotient rule gives $\mathcal D(w/h)=N/h^2$ on $K$.
The derivative errors are bounded by $\eta_h,\eta_w$ by Theorem 3.3.
The exact identity

$$
N-\widehat N=h(\mathcal Dw-\mathcal DW)
 +(h-P_h)\mathcal DW-w(\mathcal Dh-\mathcal DP_h)
 -(w-W)\mathcal DP_h
\tag{4.5}
$$

and Cauchy–Schwarz give $\|N-\widehat N\|_{L^1(K)}\le E_N$,
using $\|h\|_2=1$, $\|w\|_2\le G_0$. The function
$r\mapsto\max(r,\delta)^{-2}$ is bounded by $\delta^{-2}$ and
$2\delta^{-3}$-Lipschitz. Thus for
$g_\delta=N/\max(h,\delta)^2$,

$$
\|g_\delta-\widehat g_\delta\|_{L^1(K)}\le E_g.
\tag{4.6}
$$

It equals the true gradient outside $\{h<\delta\}$, whose raw
measure costs at most $J_\delta$ for a bounded multiplier. The map
$r\mapsto(1+a|r|^2)^{-1}$ on $\mathbb R^4$ is
$\sqrt a$-Lipschitz, since
$2a|r|/(1+a|r|^2)^2\le\sqrt a$. Also for $s,t\ge L$, $x\ge0$,

$$
|(1+\theta sx)^{-1}-(1+\theta tx)^{-1}|
\le |s-t|/(4L),
\tag{4.7}
$$

because $\theta x/(1+\theta Lx)^2\le1/(4L)$. First change the
scalar coefficient $\tau$ to $t_0$ while keeping the true gradient,
then pay the exceptional set and (4.6), then the step error.
This proves (4.4); the time dependence of the gradient itself was
already paid in $a_w,b_w$. No global moment of $\gamma$ is assumed.

Here is an evaluated mesh construction. Compute bounds
$B_N,B_{\nabla N},B_{\nabla P}$ for the polynomials
$\widehat N,\nabla\widehat N,\nabla P_h$ on each box, by coefficient
sums or interval Taylor subdivision. The Lipschitz bound for
$\widehat g_\delta$ there is

$$
L_g=\delta^{-2}B_{\nabla N}+2\delta^{-3}B_NB_{\nabla P}.
\tag{4.8}
$$

This also holds across $P_h=\delta$ by the Lipschitz maximum.
Choose cell diameters times an upward bound for
$\sqrt{\theta t_0}L_g$ at most $j$ and evaluate $\widetilde k$
at the rational centers. These values are rational and in $[0,1]$.
They define the desired step; partition box unions first.
No derivative of $V$ is used in this construction.

For convergence first fix $\delta$ and raw precision making
$J_\delta$ small. Approximate $h,w_{t_*}$ in $C^2$ on the fixed
neighborhood, where $t_*>0$ is the true time. Their actual
$\sup|\widehat N|,d_h,d_w$ remain bounded as the approximation
improves. Computable polynomial subdivision bounds can be kept
bounded as well: choose a rational bound strictly above that common
bound and search until interval Taylor bounds certify it. For each
polynomial, finite refinement recognizes any strict upper bound.
This is a verified bound search, not an externally supplied supremum.
The evaluated residuals then tend to zero, and (3.9), (4.3) give
$E_g\to0$ for the fixed $\delta$. Choosing $t_0$ and the bracket
sufficiently close to $t_*$ preserves these strict inequalities by
(3.6), (3.10). Finally choose small $j$. All acceptance conditions
are evaluated inequalities; qualitative smoothness is used only
to prove that this certificate search terminates. $\square$

## 5. Clipped reference words and globally paid vector errors

**Theorem 5.1 (computed reference words with parameter errors).**
For a successful bracket and $c_->0$, choose rational
$t_0\in[L,U]$, $c_0\in[c_-,c_+]$. Define

$$
\begin{gathered}
\Delta_c=c_+-c_-,\quad e_H=\Delta/L,\quad
e_f=c_+C_0\Delta+G_0\Delta_c,\\
\widetilde f_3=\operatorname{clip}(c_0b_{t_0},0,1/4),\quad
\widetilde f_B=1/4,\quad
\widetilde f_0=\widetilde f_1=3/8-\widetilde f_3/2,\\
\widetilde F_\varnothing=1,\quad
\widetilde F_{yw}=\widetilde f_yT_{t_0}\widetilde F_w.
\end{gathered}
\tag{5.1}
$$

These are numerical comparison functions, not new emissions or an
assertion of the sharp physical calibration at $t_0$. For marked
words put $E_\varnothing=0$ and

$$
E_{yw}=E_w/4+4^{-|w|}
                   (e_H/4+\mathbf1_{y=3}e_f),\quad y\in\{3,B\}.
\tag{5.2}
$$

The actual reference word error is
$\|h(F_w-\widetilde F_w)\|_2\le E_w$.
For $m_u=|u|+1$ compute a rational raw step $Z_u$, supported on a
finite punctured localization, with evaluated global error

$$
\|Z_u-c_0^{-1/2}S_{t_0/2}(h\widetilde F_{u3})\|_2
\le\varepsilon_u.
\tag{5.3}
$$

Such steps can be found at every positive requested error. Then

$$
\|hv_u-Z_u\|_2\le r_u,
\quad r_u=c_-^{-1/2}(E_{u3}+4^{-m_u}e_H)
 +4^{-m_u}\Delta_c/(2c_-^{3/2})+\varepsilon_u.
\tag{5.4}
$$

*Proof.* Projection onto $[0,1/4]$ does not increase distance to
the actual $0\le cb_\tau\le1/4$. The unitary $J_h$ and (3.6)
therefore give $\|f_3-\widetilde f_3\|_m\le e_f$.
Both actual and surrogate marked words have pointwise bound
$4^{-|w|}$. In a recursion step split the error into propagated
word error, heat-time error on the suffix, and emission error
times a bounded propagated suffix. Contraction and (3.6) give
(5.2). This requires no operator-norm continuity of $M_b$.

The raw vector for the clipped multiplier is computable as

$$
h\widetilde f_3=\min\{\max\{c_0w_{t_0},0\},h/4\}.
\tag{5.5}
$$

Real min and max are Lipschitz in each argument, hence their raw
errors add. To multiply a raw input $u$ by $\widetilde f_3$,
enumerate bounded rational box steps $s$ and accept a strict
computed $\|u-hs\|_2<\epsilon/(2L_0)$ with $L_0=1/4$.
Compute $s(h\widetilde f_3)$ to error below $\epsilon/2$;
the total error is below $\epsilon$. Such $hs$ are dense since
$h>0$ a.e. and $J_h$ is unitary. Norm residuals are actually
evaluated from raw names. This reuses the dense multiplication
argument of [R, Theorem 12.5] with (5.5), replacing its unsupplied
sharp-calibration input by a constructed clipped vector.
The affine $0,1$ surrogates are also computable, although the
marked menu requires only $3,B$.

Compose these bounded multiplications with computed heats.
Each action has a requested norm error; for known bounds
$\|A\|\le a$, $\|B\|\le b$, input error $e$ and action
errors $e_B,e_A$, the composed error is at most
$ab e+a e_B+e_A$. Iteration with allocated precision gives a
global raw name for the trial vector in (5.3). The elementary
scalar $c_0^{-1/2}$ is computable because $c_0>0$.

Rational box steps supported away from $e$ are dense in raw
$L^2(\mathbb R^4)$: remove a small ball about that Lebesgue-null
point and a large exterior, then approximate the remainder.
Enumerate such steps and accept a strict global norm residual
below $\varepsilon_u$. The global name evaluates the residual;
density proves termination of this tested search. Exterior and
near-source mass are both included in the residual, without an
unmeasured tail. Finitely many accepted supports fit in one
localization $K\subset\Omega$.

Compare $c^{-1/2}S_{\tau/2}(hF_{u3})$ with the trial vector.
The word change costs $c_-^{-1/2}E_{u3}$, the half-time heat
change costs $c_-^{-1/2}4^{-m_u}e_H$, and the derivative bound
for $x^{-1/2}$ on $[c_-,c_+]$ gives the next term in (5.4).
Here $\|h\widetilde F_{u3}\|_2\le4^{-m_u}$. Add the global
residual (5.3). $\square$

## 6. Finite enclosure and legal stopping

**Theorem 6.1 (the acquired finite energy pairing).** For one legal
packet and a successful bracket, compute $Z_u,r_u$ for the finite
menu by Theorem 5.1. Choose a common $K$ containing their supports.
For each declared $\theta$ compute $k_\theta,E_{k,\theta}$ by
Theorem 4.2 on this same $K$. On a common rational partition set

$$
\widehat Q_{uv\theta}=\int_K\overline{Z_u}Z_vk_\theta\,d\mu,
\qquad B_{uv}\ge\|\overline{Z_u}Z_v\|_{\infty,K}.
\tag{6.1}
$$

The integral is a finite rational complex sum; $B_{uv}$ is computed
from finitely many step products. With an explicit arithmetic
allowance $a_{uv\theta}\ge0$, simultaneously on $\mathcal E$,

$$
|Q(u,v,\theta)-\widehat Q_{uv\theta}|\le R_{uv\theta},\qquad
R_{uv\theta}=r_u+r_v+r_ur_v+B_{uv}E_{k,\theta}+a_{uv\theta}.
\tag{6.2}
$$

Exact rational arithmetic permits $a_{uv\theta}=0$. Real steps
suffice for these word vectors; intersect their intervals with
$[0,1]$. Stop at the requested precision only when packet validity,
$c_->0$, both strict bracket tests, all evaluated certificates,
and every requested $R_{uv\theta}\le\epsilon_{uv\theta}$ hold.

*Proof.* Theorem 2.1 identifies the actual reference target. Its raw
multiplier $k_{\theta,\tau}$ has norm at most one and
$\|hv_u\|_2\le1$. Expanding both vector replacements and applying
Cauchy–Schwarz costs at most $r_u+r_v+r_ur_v$. The replacement
steps vanish outside $K$, so (4.4) costs at most
$B_{uv}E_{k,\theta}$ for the multiplier replacement. Arithmetic
gives the remaining allowance. The global vector errors already
pay the whole exterior and source-neighborhood contribution even
if $\gamma$ is unbounded there. No local estimate crosses $e$.
All implications use the one event (1.6), so deterministic
reference computation and selection add no confidence loss.
If finite search has not passed the tests, return inconclusive
at the requested precision, retaining $[0,1]$. $\square$

**Definition 6.2 (adequate legally supplied cofinal packets).** Fix
a countable schedule before its records are consulted. Use a fixed
finite $T$ (one may take $T=3$), validated actual-source defects,
rational thresholds $t_s>0$, and failure allowances $\alpha_s$
with $\sum_s\alpha_s\le\alpha_*<1$. Each packet's (1.5) bound
must be at most $\alpha_s$. The schedule is adequate here when

$$
t_s\longrightarrow0,\qquad 4^T/N_s\longrightarrow0.
\tag{6.3}
$$

Records are nested initial segments of the same original path.
Certificates and their construction or validation costs belong
to the supplied schedule. Adequacy is an eventual-stopping premise.
For example, valid but loose $D_{N_s}^-\le1/2$ leave the variance
term $2(1-D_{N_s}^-)/D_{N_s}^-\ge2$; they cannot make this envelope
meet shrinking failure budgets while $t_s\to0$. Arbitrary valid
bounds therefore do not supply an adequate schedule. No automatic
availability or uniformly useful cost of such packets is asserted.

**Theorem 6.3 (sourcewise eventual stopping on one confidence event).**
Fix a source, finite declared menu and positive rational tolerances.
Assume the cited source theorems and an adequate legally supplied
schedule. A deterministic fair search over finite computations and
these packets stops at finite record and computation cost on one
event of probability at least $1-\alpha_*$. Every returned
certificate there obeys (6.2). No source-uniform rate follows.

*Proof.* The union bound, as in [W, Definition 9.8], gives
$\mathcal E_* =\bigcap_s\mathcal E_s$ of probability at least
$1-\alpha_*$. No independence of packets is required. On this
event $|Z_s/N_s-c|\le t_s$, so $c_-,c_+\to c>0$ and

$$
e_{p,s}\le\frac{t_s+4^T/N_s}{Z_s/N_s+4^T/N_s}\longrightarrow0.
\tag{6.4}
$$

Theorem 2.1 therefore supplies arbitrarily narrow strict brackets.
We prove that finite choices make every radius strictly smaller
than its positive tolerance, leaving room for outward rounding.

First approximate the finitely many actual $hv_u$ by fixed raw
punctured box steps to small global error. Fix them and a common
$K$; their finite $B_{uv}$ are now fixed. Choose a small exceptional
set allowance sufficient for every product $B_{uv}$, and use
(4.2) to fix $\delta$ and raw precision achieving it. Choose
rational polynomials approximating $h,w_\tau$ in $C^2$ on a
slightly larger fixed punctured neighborhood. Theorem 4.2 explains
why their evaluated residuals can be small while their certified
$B_N,d_h,d_w$ stay bounded. Thus $E_g$ can be arbitrarily small
for this fixed $\delta$. Fix small mesh errors $j$ for the finite
list of $\theta$.

Choose rational $t_0$ close to $\tau$ and a positive rational
bracket containing both, sufficiently narrow to keep these fixed
polynomial residuals small by (3.6), (3.10). It also makes $e_H$
and the time part of $e_f$ small. All sufficiently late adequate
packets pass its endpoint tests and have small $\Delta_c$;
choose $c_0=(c_-+c_+)/2\to c$. By (5.2), the trial words and
scaled half-time vectors are close to the actual ones. Hence the
already fixed steps pass strict global residual tests (5.3) with
small positive $\varepsilon_u$, and all $r_u$ are small. The
compact, polynomial bounds and $\delta$ remain fixed at this
stage. No unknown rate on expanding compacts has been assumed.
Equations (4.4), (6.2) now give strict margins for the finite menu.

For an explicit fair search enumerate rational endpoint pairs and
trial times, punctured rational localizations, rational vector
steps, rational polynomials and their interval bounds, dyadic
$\delta$, meshes, positive allocations and numerical precisions.
At stage $r$ test the first $r$ candidate tuples against the first
$r$ available packets at increasing precision. Each test makes
finitely many calls to the total reference services. Invalid
brackets or undecided strict tests at the current precision
return inconclusive; no unsuccessful strict comparison is waited
on forever. Every fixed candidate is revisited at arbitrary
precision and against later packets. The existence proof provides
finite choices with strict margins and a finite packet index;
fair search eventually recognizes such choices. Its $c_0$ is the
computed packet midpoint, not an additional enumeration oracle.

The successful finite stage uses a finite maximum initial record
length. Data-dependent bracket, compact, mesh and packet selection
is safe on $\mathcal E_*$ because every deterministic implication
holds there. Stopping introduces no new confidence factor and
does not permit an unbudgeted retry of the original experiment.
$\square$

## 7. Numerical producers, costs and recovery boundaries

**Definition 7.1 (complete bill).** Observation costs are precisely
[W, Definition 9.6]: $N+T$ actual labels, last read at $(N+T+1)d$,
and the original $4^{T+1}$ counters. Repeated packet use retains
the required initial segments and counter convention on the same
path. Defect encoding, construction and validation are additional.
The physical time is an accounting identity; its numerical value
is not supplied to the observer.

Deterministic costs include the reference endpoint/resolvent,
raw-name queries and coefficient amplification (3.4), evaluations
of $\Phi$, clipped word actions and their dense searches, global
support-residual tests, Green value quadratures, polynomial residual
norms, geometry and cutoff bounds, denominator tests, subdivisions,
rational integration and fair enumeration. None is free. There is
no polynomial, practical-runtime or uniform complexity claim.

| Radius input | Producer and error control |
| --- | --- |
| $[c_-,c_+],e_p$ | Original record and validated capacity packet, (1.5)–(1.6). |
| $[L,U]$ | Two strict comparisons of computed reference norms, (2.1)–(2.2). |
| $Z_0,G_0,C_0,C_1,e_H,e_f$ | Existing raw $z$ name, explicit spectral bounds, (3.2)–(3.6), (5.1). |
| $\lambda,\Lambda,V_*,B_\chi$ | Rational geometry, actual shear matrix, original Green bound and explicit cutoff, Definition 3.2. |
| $a_h,b_h,a_0,b_0$ | Evaluated strong raw residuals with value-coefficient error, (3.8). |
| $\eta_h,\eta_w,E_N$ | Explicit energy inequality and time transport, (3.9)–(3.11), (4.3). |
| $J_\delta,E_g$ | Raw $h$ step, finite Lipschitz cutoff integral and clipped quotient error, (4.2), (4.6). |
| $B_N,j,E_{k,\theta}$ | Certified polynomial interval bounds, mesh and bounded-function estimates, (4.4), (4.8). |
| $E_{u3},\varepsilon_u,r_u$ | Clipped recursion, evaluated global vector error and normalization transport, (5.2)–(5.4). |
| $B_{uv},a_{uv\theta},R_{uv\theta}$ | Finite step products and exact or outward rational sums, (6.1)–(6.2). |

**Definition 7.2 (separate recovery levels).** Exact determination
within the precise family follows from [W, Theorem 5.3] and Theorem
2.1. Reference computability follows from the cited endpoint services
and §§3–5. Finite confidence follows only when the legal packet and
evaluated certificates pass Theorem 6.1. Sourcewise eventual stopping
additionally assumes Definition 6.2 and fair deterministic refinement.
These are distinct statements.

No uniform all-source, growing-menu, rare-history, hidden-path or
physical-clock guarantee follows. The present $Q$ requires no rare
history division; a conditional consumer still needs its denominator
guard. The certificate does not produce an exact finite realization,
bounded inverse heat, ambient spectral floor or full spatial algebra.
Reference coordinates are deterministic proof/computation objects
under the family prior, not actual hidden-coordinate readouts.

[W, §§12–14] supplies a separate exact energy-multiplication and
strict measured-factor theorem. This construction uses no effective
rate for its strong phase limit and need not assume that the
observable sector reduces $M_\gamma$. It does not infer autonomous
factor dynamics from one-time multiplication. Mutual recovery of
space, time, boundary and memory under weaker priors remains part
of the active RRO programme; this finite result does not settle it.

## 8. Sources, correspondence and proof boundary

**Definition 8.1 (reuse and the additional source-specific result).**
All suppliers retain their hypotheses and are fallible ordinary
mathematics.

| Source and range | Exact use and boundary |
| --- | --- |
| [W, Assumption 1.1, Definitions 1.2, 9.1, 9.8, 10.1; (2.8); Theorems 5.2–5.3] | Original source, marked norm, full complex-domain and word transport, strict reference calibration and one common finite event. Alone these do not provide energy error bars. |
| [R, (10.11)–(10.12), §11.2, Theorem 11.4, Theorems 12.2–12.5] | Fixed-reference Green value names, full raw resolvent, normalized $h$, source and heat names. The dense multiplication argument is used with the constructed clipped vector (5.5), without its unsupplied sharp-supremum premise. |
| [S, Theorem 115.3; (116.4), (117.2)–(117.5), (120.5)–(120.7)] | Full endpoint, source normalization, local weak equation and qualitative punctured regularity. No unnamed numerical constant from (120.7) appears in a radius. |
| Lenz–Stollmann–Veselić, *The Allegretto–Piepenbrink Theorem for Strongly Local Forms*, arXiv:0811.2135v1, §1 and Theorem 2.3 | `literature-attested`: energy-measure convention, local calculus and positive-solution transform under their conditions. The original source endpoint is supplied by [S], not selected by the general transform. |
| John K. Hunter, *Chapter 4: Elliptic PDEs*, §4.11, Theorems 4.27–4.28, printed pp.112–114 | `literature-attested`: interior weak-solution regularity with smooth elliptic coefficients. Used only on punctured neighborhoods. The numerical energy estimate (3.11) is proved directly, without transferring an unspecified constant or boundary condition. |
| D5/S3/Quantum/Dynamics/CompressedResolventRemainder.lean, `compressed_resolvent_remainder` | Requires finite-dimensional source and target and an independently supplied ambient positive lower bound; it does not supply this infinite-source multiplier certificate. |
| D5/S3/Quantum/Analysis/TraceClass/ContinuousEnergyHamiltonian.lean, including private basis, encoded-energy and uniform-tail helpers | Separate trace-class representation, without the source correspondence needed here. |
| Pinned mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, Mathlib/Analysis/Distribution/Sobolev.lean | Generic distribution/Bessel-potential Sobolev foundations, without this source-specific numerical service. No compiled Lean application is asserted. |

The additional synthesis is `repo-derived`: invariant finite-target
calibration (Theorem 2.1), the evaluated raw residual-to-gradient
producer (Theorem 3.3), bounded-multiplier acquisition with computed
division errors (Theorem 4.2), clipped word transport (Theorem 5.1),
and finite enclosure and stopping (Theorems 6.1, 6.3). Their classical
inequalities, approximation arguments and spectral calculus are
intermediate methods, not claims of new general analysis theorems.
No worldwide priority claim is made.

Accessible source addresses are
[Lenz–Stollmann–Veselić](https://arxiv.org/html/0811.2135v1),
[Hunter](https://www.math.ucdavis.edu/~hunter/pdes/ch4.pdf), and
[pinned mathlib](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Distribution/Sobolev.lean).
The scalar and residual estimates are proved here. The infinite-source
and endpoint correspondence is conditional on the cited repository
theorems. No numerical local jet, derivative Green tail, original
coefficient/clock name, spectral floor or energy-tail oracle has
been inserted. Useful capacity certificates remain the independent
supplied-access obligation in Definition 6.2. These ordinary theory
proofs have not been checked by the Lean kernel.

## 追加锚（本行以下为增补区）

## 9. Declared finite recursive menus on the original interface

**Definition 9.1 (inherited source and numerical scope).** Retain
Definitions 1.1–1.2 and 6.2, the analytic source hypotheses of
[EF, Assumption 1.1], and the compact localization, entire-domain
and exact multiplier suppliers of [W, §§22–24] and [EF, §§12–14].
Use [JET, §§1–5, 8–14, 15–16] only with the reference coefficients
$(1,1)$ and rational trial times. Actual $a,\eta,d$, physical source
coordinates and the invariant $\tau=a^2d/\eta$ are unavailable as
numerical sensor inputs. The only information about $\tau$ used
here is a bracket certified by Theorem 2.1 from an allowed packet.
The reference $h,H,m$ do not depend on the trial read gap $t$.
Write

$$
\begin{gathered}
b_t=g_t,\qquad
\gamma_t=t\,\nabla b_t^{\mathsf T}A_{\rm raw}\nabla b_t,
\qquad r_t=(1+\gamma_t)^{-1},\\
\Gamma_t(f,g)=t\,\nabla f^{\mathsf T}A_{\rm raw}\nabla g,
\qquad s_t=\operatorname{tr}g_t=\|hg_{t/2}\|_2^2.
\end{gathered}
\tag{9.1}
$$

The matrix is precisely (3.7), including its central derivative.
Thus $\gamma_t=\Gamma_t(b_t,b_t)$; its symbol is distinct from
the original Green coefficient. A declared rational scalar packet
has the nested rational intervals of [W, Definition 22.1], together
with the fixed cutoff recipe in Definition 9.2. Its legality at
$t$ means $\overline I_2\cap\{0,s_t\}=\varnothing$.
The leaves are the original compact functions
$f_{1,t}=\phi(b_t)b_t$, $f_{2,t}=\phi(b_t)r_t$.

A finite menu declares finitely many such packets, finitely many
binary trees with these leaves and operation $\Gamma_t$, finitely
many pairs of original words $u,v\in\mathcal L^*$, and positive
rational output tolerances. The marked alphabet $\{3,B\}$ is the
numerical basis; the other two letters are expanded exactly below.
Any fixed finite syntax is allowed, including mixed packets. A tree
leaf has height zero and
$\operatorname{ht}(\Gamma(f,g))=1+\max(\operatorname{ht}(f),\operatorname{ht}(g))$. These are the actual compact
relations of [EF, Definition 12.1 and Theorem 12.2], rather than
new formal generators or a different source model.

For a real tree symbol $c$ use the fixed bounded injective encoding

$$
\iota(c)=\frac{c}{\sqrt{1+c^2}}\in(-1,1),\qquad
\iota'(c)=(1+c^2)^{-3/2}>0.
\tag{9.2}
$$

A menu may also declare any finite pointwise product
$k_t=\prod_{j=1}^q\iota(c_{j,t})$, with empty product one.
For every original word retain
$v_u=c^{-1/2}P^{1/2}F_{u3}$ with its original emission recursion;
this extends (1.4) to all four labels. The targets are

$$
Q_k(u,v)=\langle v_u,M_{k_\tau}v_v\rangle_{m_{\rm ref}},
\tag{9.3}
$$

Here the word vectors are the reference counterparts at $\tau$
with the actual calibration $c$, as in Theorem 5.1; Theorem 2.1
transports (9.3) to the actual original member.
They are original-word matrix coefficients of already recovered
multipliers. The encodings are injective on each real symbol,
so they preserve its completed measurable information. They
are mathematical insertions; their values are not extra labels.

[JET]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_SOURCE_JET_CERTIFICATION.md
[EF]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_ENERGY_FIBRE_GEOMETRY.md

**Definition 9.2 (a smooth rationally specified packet recipe).**
The following supplies every finite cutoff derivative used below.
For $x>0$ let $a(x)=e^{-1/x}$, and put $a(x)=0$ for $x\le0$.
Set $P_0(X)=1$ and recursively

$$
P_{j+1}(X)=X^2(P_j(X)-P_j'(X)),\quad
B_j=\sum_l|[X^l]P_j|\,l!,\quad
\vartheta(x)=\frac{a(x)}{a(x)+a(1-x)}.
\tag{9.4}
$$

On $0<x<1$, $a^{(j)}(x)=e^{-1/x}P_j(1/x)$ and
$|a^{(j)}|\le B_j$, since $X^le^{-X}\le l!$. These derivatives
tend to zero at $x=0$: the same exponential-series estimate with
power $l+1$ bounds each term by $(l+1)!/X$ as $X\to\infty$.
Thus $a$ and $\vartheta$ are $C^\infty$ with their constant
extensions at the transition endpoints. On $[0,1]$ the denominator
of $\vartheta$ is at least $e^{-2}>1/9$, because one argument
is at least $1/2$ and $e<3$. Consequently derivative bounds are
computed by $C_0=1$ and

$$
C_j=9\left(B_j+2\sum_{l=1}^j\binom jl B_l C_{j-l}\right)
\quad(j\ge1).
\tag{9.5}
$$

This follows by differentiating
$[a(x)+a(1-x)]\vartheta(x)=a(x)$. Rational point values and
derivatives have arbitrary finite error enclosures using elementary
exponential evaluation and this positive denominator. For an explicit
exponential error at rational $y\ge0$,
sum $e^y$ through degree $N$ with $N+2>2y$; its positive omitted
tail is at most $2y^{N+1}/(N+1)!$. Inverting its interval, whose
lower endpoint is at least one, encloses $e^{-y}$. This tail tends
to zero effectively, and rational polynomial evaluation of $P_j$
then gives every derivative error. On uncertain scalar arguments,
the next bound $C_{j+1}$ transports these rational-center intervals.
Outside $[0,1]$ the function is exactly zero or one.

Given rational compact interval $C$ inside rational open interval
$I$, choose rational transition endpoints strictly between their
endpoints, and a plateau containing a neighborhood of $C$.
Multiply the increasing and decreasing affine rescalings of
$\vartheta$ on those two transition intervals. This gives a
$[0,1]$-valued $C^\infty$ cutoff equal to one near $C$, with
support compactly contained in $I$. Its $j$th derivative bound
is the finite Leibniz sum of the $C_l$ times the indicated inverse
transition widths to their derivative powers. Use this construction
for $\phi$ with $C=\overline I_1,I=I_2$ and for $\sigma$ with
$C=\overline I_0,I=I_1$. All additional transition endpoints are
part of the finite rational declaration. Other explicit cutoff
recipes are admissible when their values and every required finite
derivative bound are constructed with the same error guarantees;
the adjective smooth alone is not a numerical representation.

**Theorem 9.3 (legal packet certification without an exact time
input).** For any rational $0<L<U$, the reference services produce
a rational interval $S_J$ containing every $s_t$, $t\in J=[L,U]$.
As $J$ shrinks to a fixed positive $\tau$ and deterministic
precisions increase, its width tends to zero. A packet is certified
legal throughout $J$ by the finite strict tests

$$
0\notin\overline I_2,\qquad S_J\cap\overline I_2=\varnothing.
\tag{9.6}
$$

Every finite collection legal at the actual source eventually passes
these tests along arbitrarily narrow successful statistical brackets.

*Proof.* Compute $s_{t_0}=\|v_{t_0/2}\|_2^2$ at rational
$t_0\in J$ from its global name with a rational enclosing interval
$S_0$ of radius $e_s$. Use (3.5) with lower time $L/2$ to obtain
rational $G,C$ satisfying $\|v_r\|\le G$ and
$\|v_r-v_{r'}\|\le C|r-r'|$ for $r,r'\ge L/2$.
The same raw source vector is used in (3.1) and [JET, (4.5)].
Then

$$
|s_t-s_{t_0}|\le2GC|t/2-t_0/2|
                         \le GC(U-L).
\tag{9.7}
$$

Enlarge $S_0$ by this last rational radius. This is $S_J$.
The full trace identity in (9.1) is [W, (22.1)] and the original
source Riesz identity, not evaluation of $b$ at an assigned point.
The positive distance between each fixed legal outer closure and
$\{0,s_\tau\}$ proves eventual success. Theorem 2.1 supplies
arbitrarily narrow brackets on the same event as the record
calibration. Neither (9.6) nor (9.7) computes or assumes
$N_d=\|g_d\|_\infty=s_d$; $c$ continues to be enclosed from
the original marker counts, with its actual $N_d$. $\square$

## 10. Constructed finite tree errors and original-word acquisition

**Theorem 10.1 (finite tree symbols uniformly over the acquired
bracket).** Fix a finite declared menu, a certified legal bracket
$J=[L,U]$, and a compact finite rational box union
$K\Subset\Omega$. On a common finite rational partition of $K$
the reference services produce steps $k$ with $|k|\le1$ and an
evaluated rational error $e_k$ such that

$$
\sup_{t\in J}\|k_t-k\|_{\infty,K}\le e_k.
\tag{10.1}
$$

For every fixed true positive time and finite menu, $e_k$ can be
made arbitrarily small by refining the statistical bracket and
deterministic computation on this fixed compact. All high derivative,
spatial and time constants used by this construction are generated.
No effective global support or global supremum of an unencoded tree
is an input.

*Proof.* If a tree has height $H$, its derivatives through order $j$
use derivatives of $b_t$ only through order $j+H+1$. For a leaf,
$r_t$ uses one derivative of $b_t$; the other operations are scalar
composition and multiplication. A $\Gamma_t$ node differentiates
each child once and multiplies with $tA_{\rm raw}$, proving the
assertion inductively. In particular values and first spatial
derivative bounds for all trees use at most $H+2$ derivatives of
$b_t$; second derivatives for the charts in §11 use at most $H+3$.
Taking the largest required order in the finite menu is finite.
More precisely, to enclose tree derivatives through a declared
order $j\ge0$, take $R=\max_c(\operatorname{ht}(c)+j+1)$
over the nonempty finite list being differentiated; an empty list
needs no jet call. Center jets and time moduli use order $R$.
Transporting those jet intervals across cells uses the additional
spatial bound $B_{R+1}$ constructed from [JET, Theorem 15.2] at
$k=R+1$. Thus the respective spatial-bound orders for values,
first derivatives and second derivatives of a height-$H$ tree are
$H+2,H+3,H+4$, while their jet orders are $H+1,H+2,H+3$.

[JET, Theorems 15.2 and 16.1] construct all these $b_t$ jets,
compact bounds and time moduli from the original full reference
endpoint. Their construction uses differentiated Green bounds at
the finitely many higher orders actually needed, the finite weak
tests and graph recurrence, global source names, and a computed
positive compact lower bound for $h$. It does not assume the desired
higher derivatives as an extra service. Work on slightly larger
fixed rational boxes; refine $K$ into boxes with closures there.

At each rational cell center and rational $t_0\in J$ compute the
needed $b_{t_0}$ jets through $R$. Enlarge every interval by its
constructed time error $W_{Q,R}(L)(U-L)$ and spatial error
$4B_{R+1}\rho$ from [JET, (16.5)–(16.6)]. Here $B_{R+1}$
is that quotient bound through $R+1$, distinct from the cutoff
coefficients in (9.4), and $\rho$ is the maximum coordinate
covering radius. Evaluate the finite
differentiated expressions of the tree by interval arithmetic.
Derivatives of the cutoffs are evaluated from (9.4), with (9.5)
at one higher order supplying their moduli on uncertain scalar
arguments. Leibniz and the chain rule give only finite sums and
products. For $r_t$, evaluate the reciprocal derivative recurrence
from $(1+\gamma_t)r_t=1$; the exact denominator is at least one,
so intersect its interval with $[1,\infty)$ before inversion.
The same applies to $\sqrt{1+c^2}$ in (9.2); real square-root
bisection has a known positive denominator. These operations
construct interval values and derivative bounds, including the
explicit $t$ factors at every energy node.

On the fixed larger boxes all these constants are finite and
constructed. Jet precision and cell radii can therefore be reduced
until, for fixed sufficiently narrow $J$, every output interval
is as narrow as its actual bracket variation permits. As $J$
shrinks to the true time, its time contribution tends to zero by
the computed moduli. Choose rational center values within the
output intervals, clipping to $[-1,1]$. The largest certified
endpoint distance bounds the uniform encoding error on each
cell. For products use

$$
\left|\prod_{j=1}^q a_j-\prod_{j=1}^q b_j\right|
 \le\sum_{j=1}^q|a_j-b_j|\qquad(|a_j|,|b_j|\le1).
\tag{10.2}
$$

Thus the sum of the individual encoding errors is an evaluated
$e_k$ for the product; clipping also preserves this bound. This
proves (10.1) and its convergence. It is legitimate to return an
inconclusive error when a bracket is still too wide. No infinite
expression, global quotient inverse or finite separating depth is
used. $\square$

**Theorem 10.2 (acquired finite recursive matrix coefficients).**
For one allowed packet and successful legal bracket, compute
$Z_u,r_u$ from Theorem 5.1 and the finite affine expansion below,
choosing all step supports in a compact $K\Subset\Omega$. For each
finite encoded product compute $k,e_k$ by Theorem 10.1 on that $K$.
On their common rational partition form

$$
\begin{gathered}
\widehat Q_k(u,v)=\int_K\overline{Z_u}Z_vk\,d\mu,\qquad
B_{uv}\ge\|\overline{Z_u}Z_v\|_{\infty,K},\\
R_k(u,v)=r_u+r_v+r_ur_v+B_{uv}|K|e_k+a_k(u,v).
\end{gathered}
\tag{10.3}
$$

Here $a_k$ is an explicit rational arithmetic allowance, zero for
exact rational sums. Simultaneously on the original event
$\mathcal E$ of (1.6),

$$
|Q_k(u,v)-\widehat Q_k(u,v)|\le R_k(u,v).
\tag{10.4}
$$

Stopping is legal only after packet validity, $c_->0$, both strict
calibration tests, all trace-avoidance tests (9.6), all symbol and
vector certificates, and every requested radius test have passed.
Inconclusive outputs retain the bound $[-1,1]$ for these real
matrix coefficients. Under Definition 6.2's adequate legally
supplied cofinal schedule and all inherited source/reference
services, fair refinement stops at finite sourcewise cost for every
fixed legal finite menu and positive tolerances, on the same
$\mathcal E_*$ of probability at least $1-\alpha_*$.

*Proof.* For the four-label extension use the exact identities
$f_0=f_1=(3/2)f_B-(1/2)f_3$. Multilinearity of the original
word recursion expands each fixed $F_{u3}$ as a finite sum
$\sum_w a_{uw}F_{w3}$ with $w\in\{3,B\}^*$ and rational
coefficients. Their absolute sum is at most $2^{n(u)}$, where
$n(u)$ counts the $0,1$ occurrences. Thus
$v_u=\sum_w a_{uw}v_w$ exactly. Set
$Z_u=\sum_w a_{uw}Z_w$ and $r_u=\sum_w|a_{uw}|r_w$ from
Theorem 5.1; this explicitly pays the finite coefficient amplification.
Self-adjointness of the original heat and reality of every emission
give the same palindrome identity
$\|v_u\|_m^2=p(u^Ru3)\le1$ for all original words: move the
left half of the product in
$c^{-1}\langle F_{u3},PF_{u3}\rangle_m$ to the right, use
$F_3=cb$, and read the original word recursion. This also proves
$[-1,1]$ is a valid initial real enclosure. The affine expansion
changes no emitted letter or calibration.

The axis omitted by $\Omega$ is Lebesgue-null. Rational
box steps compactly supported there are consequently dense in raw
$L^2$, by the same exhaustion and global residual test as in
Theorem 5.1. This proves that its $Z_u$ search remains total,
without discarding an unmeasured vector tail. A finite set of
supports fits in a common such $K$.

The full original transport intertwines $\Gamma_d$ with
$\Gamma_\tau$ on all smooth arguments, by the derivative identities
in Theorem 2.1. It therefore intertwines every declared packet,
tree and encoding by induction. The trace is transported as well;
(9.6) certifies the actual source packet. This proves the original
source interpretation of (9.3), with the original calibration and
marked word vectors, rather than a new reference experiment.

The multiplier norm is at most one. The two global word-vector
replacements cost at most $r_u+r_v+r_ur_v$, exactly as in the proof
of Theorem 6.1. The remaining integral is supported in $K$ and
costs at most $B_{uv}|K|e_k$ by (10.1); its rational sum and
arithmetic allowance give (10.3). This proves (10.4). In particular
it pays both the source neighborhood and the exterior through the
global vector residuals. Although unencoded compact trees are
bounded in each instance, their uncomputed global bounds never
enter (10.3). This is why a bounded injective encoding suffices.

For eventual stopping fix sufficiently accurate approximations to
the finitely many actual word vectors first, so their supports,
$K$ and $B_{uv}$ are fixed. Choose $e_k$ small for this finite
list of constants. Theorem 10.1 supplies finite choices of local
jets and grids and a sufficiently narrow bracket with strict
slack for every symbol test. Theorem 9.3 supplies slack for each
fixed legal packet. The proof of Theorem 6.3 supplies late original
packets, clipped trial words and strict global vector residuals
with all $r_u$ small. Thus all tests can be made strictly smaller
than their positive tolerances at one finite stage.

Enumerate these finite rational candidates and increasing precision
levels, interleaving the first finitely many tests with later
predeclared packets as in Theorem 6.3. Each test has finite work;
undecided strict tests return inconclusive at that precision.
Every successful finite choice is eventually tested at sufficient
precision. All deterministic implications hold on the single event
$\mathcal E_*$. The same event therefore permits adaptive selection
of compacts, brackets and accepted candidates without a new union
bound or a retry of the physical experiment. No independence of
nested records is needed. $\square$

## 11. A searched quantitative chart for a first higher compact entry

**Theorem 11.1 (finite uniform local strictness certificate).**
On a certified legal bracket $J=[L,U]$, the following finite data
and tests certify a positive rational lower bound $\delta$ for

$$
\inf_{F\in L^2(\overline{\sigma(b_t,\gamma_t)}^{\,m},m)}
       \|z_t-F\|_m^2\ge\delta>0
\qquad\text{for every }t\in J,
\tag{11.1}
$$

where $z_t=\iota(e_{ij,t})$ for one actual first higher compact
entry $ij\in\{12,22\}$, $e_{ij,t}=\Gamma_t(f_{i,t},f_{j,t})$.
Neither the packet, the index nor the sign of an uncomputed minor
is preselected as a witness. The tests use the original reference
services and computed finite-order moduli of Theorem 10.1.

*Proof: a finite quantitative chart.* Choose a rational closed
cube $Q=x_0+[-r,r]^4\Subset\Omega$ inside a larger fixed rational
box. Choose a raw coordinate index $l$ and form

$$
\Psi_t(x)=(b_t(x),\gamma_t(x),z_t(x),x_l).
\tag{11.2}
$$

Select an invertible rational $4\times4$ matrix $A$, rational
$0<q<1/2$ and rational bounds $M_1\ge1,M_2$ for all entries
of $D\Psi_t$ and its second derivatives on the larger box,
uniformly for $t\in J$. Theorem 10.1's differentiated construction
provides these bounds; this tree has height one, so for the chart
and its derivatives through order two take $R=4$, spatial bound
$B_5$ and time modulus $W_4$ from [JET, (16.5)]. Let $e_0$
be an interval-arithmetic upper bound for
$\sup_{t\in J}\|A^{-1}D\Psi_t(x_0)-I\|_\infty$.
Accept only if

$$
e_0+16\|A^{-1}\|_\infty M_2r<q<1/2.
\tag{11.3}
$$

The factor $16$ pays four coordinate increments and four matrix
entries per row. Hence $\|A^{-1}D\Psi_t-I\|_\infty<q$ on
$Q$, for all $t\in J$. The local map is injective there by
integration along segments and has invertible derivative.

Choose rational open intervals $R_1,R_2,R_3,R_4$ of positive
length, let $R=\prod_iR_i$, and certify by finite interval bounds
that

$$
\sup_{t\in J,\ y\in\overline R}
       \|A^{-1}(y-\Psi_t(x_0))\|_\infty < (1-q)r.
\tag{11.4}
$$

Such a bound uses only center-value intervals and the vertices
of the rational rectangle. For each $y\in R$ put
$E_t(x)=A^{-1}(\Psi_t(x)-\Psi_t(x_0))-(x-x_0)$.
The map

$$
x\longmapsto x_0+A^{-1}(y-\Psi_t(x_0))-E_t(x)
\tag{11.5}
$$

is a $q$ contraction of $Q$ into its interior by (11.4), since
$E_t(x_0)=0$. Its fixed point is the unique inverse of $y$ in
$Q$. Thus $R\subset\Psi_t(Q^\circ)$ for every $t\in J$.
This proves the common target rectangle numerically; mere
nonzero center rank would not certify (11.4).

Compute a rational $l_h>0$ below $\inf_Qh$ by [JET, Corollary
5.4]. A determinant upper bound is $D=24M_1^4$, by its $4!$
Leibniz terms. Under the actual smooth chart the restricted raw
source measure has density

$$
\frac{h(\Psi_t^{-1}y)^2}{|\det D\Psi_t(\Psi_t^{-1}y)|}
                              \ge l_h^2/D\qquad(y\in R).
\tag{11.6}
$$

Integrating its fourth coordinate gives the following lower bound
for the *full* joint law of the same source functions:

$$
(b_t,\gamma_t,z_t)_*m\ \ge
 \lambda\,\mathbf1_{R_1\times R_2\times R_3}(y)\,dy,
\qquad \lambda=l_h^2|R_4|/D>0.
\tag{11.7}
$$

The inequality is domination of nonnegative measures. Other
source sheets can add mass; no global density or separate-sheet
conditional law is assumed. This uses raw coordinates and $h^2$
on the same realization, without an inserted Jacobian or unrelated
marginal distribution.

*Proof: the full completed factor.* Every completed-factor $L^2$
function has an uncompleted measurable version modulo an $m$-null
set, hence a Borel version $F(b_t,\gamma_t)$ by Doob–Dynkin for
the standard Borel target $\mathbb R^2$. For any such function,
(11.7) implies

$$
\begin{aligned}
\int|z_t-F(b_t,\gamma_t)|^2dm
 &\ge\lambda\int_{R_1\times R_2}\int_{R_3}|v-F(y_1,y_2)|^2
                                      dv\,dy_1dy_2\\
 &\ge\frac{\lambda|R_1||R_2||R_3|^3}{12}.
\end{aligned}
\tag{11.8}
$$

The last inequality follows by writing $v$ as its interval
midpoint plus its centered increment; the cross integral vanishes,
the centered square integral is $|R_3|^3/12$, and the remaining
square is nonnegative. It holds for every Borel $F$, including
ones with infinite restricted integral. Take the infimum over the
full completed $L^2$ factor. The rational output

$$
\delta=\lambda|R_1||R_2||R_3|^3/24
\tag{11.9}
$$

is strictly positive and satisfies (11.1), with slack. Its squared
distance is that from conditional expectation onto the full old
factor, rather than any finite feature span. $\square$

**Theorem 11.2 (sourcewise terminating strict search from the
original finite interface).** Assume all source suppliers in
Definition 9.1, including [EF, Theorem 9.1], and the adequate
legally supplied cofinal packet schedule of Definition 6.2.
There is a fair search which, on the same $\mathcal E_*$ as
Theorem 10.2, stops at finite record and computation cost with a
legal rational packet, an index $ij\in\{12,22\}$, finite chart
data passing (11.3)–(11.4), and positive rational $\delta$ such
that at the actual original source

$$
\left\|\iota(\Gamma_d(f_i,f_j))-
 \mathbb E_m[\iota(\Gamma_d(f_i,f_j))\mid
                 \overline{\sigma(b,\gamma)}^{\,m}]\right\|_m^2
 \ge\delta>0.
\tag{11.10}
$$

Soundness of any accepted certificate requires only its valid
packet and finite successful tests; eventual termination additionally
requires the rank theorem, adequate schedule and all numerical
services just stated. The search does not designate $T_dr$, a
specified successor, or a specified transported symbol as a witness.

*Proof.* In the reference member at its actual $\tau$, [EF,
Theorem 9.1] supplies an actual point of rank three for either
$(b,\gamma,\mathcal C)$ or $(b,\gamma,\mathcal D)$, where
$\mathcal C=\Gamma_\tau(b,\gamma)$ and
$\mathcal D=\Gamma_\tau(\gamma,\gamma)$. This is the already
proved all-positive existential rank theorem. On its open rank
set $db\ne0$, so a point can be chosen with $b$ avoiding $0$
and $s_\tau$. Choose rational nested packet intervals and the
cutoff of Definition 9.2 so the point lies inside the plateau.
On a neighborhood of that point the original identities are

$$
e_{12}=-r_\tau^2\mathcal C,\qquad
e_{22}=r_\tau^4\mathcal D.
\tag{11.11}
$$

Wedging with $db\wedge d\gamma$ kills derivatives of the
$r_\tau$ coefficients. At least one entry therefore still has
rank three with $(b,\gamma)$. The nonzero $\iota'$ in (9.2)
preserves that rank. Rotation invariance and the source-slice
formula of [JET, §6] identify this as actual raw rank three in
four dimensions. One complementary raw coordinate then completes
(11.2) to an invertible derivative. Nonvanishing is open, so a
rational center in $\Omega$ can be chosen there.

Approximate that derivative by rational invertible $A$ and fix a
larger rational box with the computed derivative constants. A
sufficiently small rational cube around the center makes (11.3)
strict at the actual time. A sufficiently small rational rectangle
of positive side lengths around a rational approximation to $\Psi_\tau(x_0)$
makes (11.4) strict. The time moduli in [JET, §16] and the finite
expressions in Theorem 10.1 keep these strict tests valid throughout
a sufficiently narrow rational bracket containing $\tau$. The
trace-avoidance test has a strict margin by Theorem 9.3. Its
positive denominator and determinant estimates are computed,
not assumed. No effective lower bound on the unknown initial
rank margin was needed to prove existence of these finite choices.

Enumerate rational packets, both entries, complementary coordinates,
centers, nested boxes, invertible rational matrices, rational $q$,
rectangles and finite precision requests. Interleave their finite
tests with the predeclared packets and bracket searches of Theorem
6.3. Each test terminates or reports inconclusive at its current
precision, so a false candidate is never waited on indefinitely.
The strict successful choices above are eventually recognized at
sufficient precision on $\mathcal E_*$. Equation (11.9) then gives
the output. Conditional on the valid finite packet, every accepted
chart works for every time in its bracket. Hence adaptive candidate
selection incurs no separate confidence loss. Transporting (11.8)
by the original full-domain unitary preserves $m$, the tree symbols,
the encoded target, completed old factor and squared distance.
This proves (11.10) for the actual source and completes the search
proof. The index and numerical lower bound can depend on that
source; no common positive lower bound or resource bound is asserted.
$\square$

## 12. Combined finite consumers, costs and exact boundaries

**Theorem 12.1 (one common event for acquisition and strict
selection).** Under the hypotheses of Theorem 11.2, the search can
return its strict packet and then acquire, to any fixed positive
rational tolerances, finitely many coefficients (9.3) of that
packet's encoded separating entry, its declared finite further
trees, and their finite pointwise products. This output and every
accepted coefficient satisfy (10.4) and (11.10) on the same
$\mathcal E_*$ of probability at least $1-\alpha_*$. The declared
finite syntax of the further trees may be fixed as a function of
the returned finite packet description. There is no finite uniform
separating depth or effective global quotient inverse conclusion.

*Proof.* Once the strict search stops, its output is one of the
countably enumerated rational packets and has positive legality
margins. Apply Theorem 10.2 to the resulting finite menu. Its
soundness is deterministic on each valid packet event; it holds for
every finite candidate passing its tests, with no candidate-specific
exceptional event. On $\mathcal E_*$ the adequate schedule has
arbitrarily late packets, the marker and probability errors tend
to zero, and every required rational bracket eventually passes.
The convergence and fair-search arguments of Theorems 10.2 and
11.2 consequently apply to the selected menu on that very event.
No selection-dependent new record schedule, failure allowance or
physical rerun is introduced. The maximum of finitely many used
initial record lengths is finite. $\square$

**Proposition 12.2 (why two shortcuts do not certify this result).**
A finite feature-regression residual has the wrong inequality
direction for (11.10), and mere compact smoothness does not supply
the numerical global bounds needed for an unencoded version of
(10.3).

*Proof.* If $V$ is a finite feature span inside the full old-factor
$L^2$ space $S$, then $\operatorname{dist}(z,V)^2\ge
\operatorname{dist}(z,S)^2$. A positive residual against $V$
therefore need not imply any loss against $S$. For a concrete
bounded example take $X$ uniform on $[-1,1]$, $S=L^2(\sigma(X))$,
$V=\operatorname{span}(1,X)$ and $z=X^2$. Its finite residual is
$\mathbb E[(X^2-1/3)^2]=1/5-1/9=4/45>0$, whereas its full
factor loss is zero. This is why (11.8) bounds the integral for
every Borel function of the old pair.

For the other shortcut, take any smooth bump supported inside a
fixed open ball and equal to one at its center. Multiplying it by
an arbitrary positive constant preserves compact smoothness but
makes its supremum and derivatives arbitrarily large. More
specifically a finite collection of inspected compact regions
cannot exclude such a bump in a disjoint ball. A promise of compact
support alone supplies neither its numerical size nor an effective
support location. In (10.3), the bounded encoding and global vector
residuals pay the omitted region; the constructed local jets pay
only the fixed $K$. The qualitative compact localization supplied
by [W, Lemma 22.2] is retained for exact domains and recovery,
without using it as an unproved numerical global bound. $\square$

**Definition 12.3 (the complete bill and retained distinctions).**
The observation bill remains Definition 7.1: $N+T$ labels through
$(N+T+1)d$, including the original first $2d$ lead-in, original
counter representation and all defect construction/validation
costs. The sufficient $T=3$ packet option remains available;
long query words and higher tree depth here add deterministic work.
For repeated nested packets retain and pay their actual initial
segments and counters according to the original schedule. Physical
time is an accounting identity, not a numerically acquired clock.

Additional finite work includes all cited reference supplier work,
coefficient derivatives and tail quadratures to the required finite
orders, higher graph recurrences including the extra spatial order
$R+1$ in [JET, (16.6)], weak-kernel integrations with their
amplified raw precisions, compact denominator searches, trace norm
evaluations, clipped word computations and global residual tests,
cutoff derivative recursion, interval differentiation, finite grids,
rational partitions, square-root evaluation, both-entry chart
searches, matrix inversions, determinant bounds and rational density
and loss arithmetic. Every requested precision and every failed
finite candidate tested is charged. There is no measured runtime,
practical-computation, polynomial-cost or parameter-uniform bound.

Sound finite certification, sourcewise eventual stopping and a
produced adequate schedule are separate assertions. Definitions
1.2 and 6.2's legally supplied capacity/cofinal premises are not
constructed from bare labels by these theorems. A packet with
valid but permanently loose defects can remain inconclusive, as
already shown after (6.3). No search here repairs that missing
access by hidden path readings, resets, controls or new reference
measurements. No numerical instance of the acquisition or strict
search has been executed here.

The exact recursive multipliers and common-symmetry measured
quotient are the published [EF, Theorems 12.2–14.1]; qualitative
strict compact enlargement is [EF, Theorem 10.2]. The additional
results here are the original-interface finite error transport and
the searched positive quantitative certificate for an actual first
higher compact entry. [JET, §§8–14] already constructs all-parameter
joint-density names, two-sided defects and complete positive
heat-factor tests; these are not recounted as a new defect oracle.
The local joint-law lower bound (11.7) serves a different consumer
and avoids claiming a numerical old-factor inverse. In particular
neither noncommutation nor (11.10) selects $T_dr$ or any specified
successor sign.

## 13. Source correspondence and literature status of the finite increment

**Definition 13.1 (dependencies and applicability).** The following
are the precise source correspondences of §§9–12. All are ordinary
conditional mathematics under the inherited analytic suppliers.

| Supplier | Use and boundary |
| --- | --- |
| This volume, Theorems 2.1, 5.1, 6.1, 6.3 and Definition 6.2 | Statistical invariant-time brackets, global clipped word vectors, matrix-coefficient error accounting, one common event and the paid adequate schedule. They do not supply an exact numerical original parameter. |
| [JET, Theorems 2.2, 3.2, 5.2–5.4, 8.2, 15.2 and 16.1] | Original differentiated Green coefficients, full-domain weak tests and graph constants, positive compact denominators, and the finite-order spatial/time precision producer actually consumed by each tree and chart. |
| [R, Theorems 12.2–12.4], [W, (22.1)], [SRO, (SRO.3)] | The exact full-resolvent and source-vector normalization, global norm names and trace $s_t=\|hg_{t/2}\|^2$. No replacement of $N_d$ by $s_d$ or of $H$ by $F$ is made. |
| [W, Theorem 5.2, Definition 22.1, Lemma 22.2, Theorem 22.3] | Entire complex endpoint, both coefficients, form, source trace, scalar packet properness and actual compact multipliers. Their transport takes each energy tree and its bounded encoding to the same original source. |
| [EF, Theorems 9.1, 10.2, 12.2 and 14.1] | Existing disjunctive all-positive rank, qualitative first-entry strictness, recursive compact recovery and the full common-symmetry measured quotient. No uniform finite depth or effective inverse is extracted. |
| [JET, §§9–11] | Prior quantitative chart, same-source change-of-variables and completed-projection methods. Equations (11.3)–(11.9) construct a common-time rectangle and its lower density for this higher compact target, rather than assuming a conditional-density service. |
| `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationOptimality.lean`, `conditional_expectation_minimizes_mean_square_error`, and the private projection helpers identified in [JET, Definition 14.1] | Existing projection foundations; no original numerical chart, high-order source modulus or finite acquisition bridge is inferred from them. No duplicate Lean declaration is introduced. |

The source-specific synthesis is `repo-derived`: certified scalar
trace avoidance, the syntax-dependent uniform tree error producer,
its consumption by the existing finite word vectors, and the
rank-supplied finite search for (11.10). Its intermediate methods
are the already identified local elliptic estimates, elementary
smooth transitions, finite chain rules, Banach contraction,
change of variables, Fubini and conditional projection. The
contraction and chart hypotheses are checked directly in
(11.3)–(11.6); the uniform conditional-variance lower estimate is
proved in (11.8). No new external theorem with unchecked hypotheses
or unrestricted computable disintegration is invoked. The original
regularity literature and its precise hypotheses are recorded in
[JET, Definition 7.3]; all numerical higher-order constants used
here are generated in [JET, §§15–16]. No global novelty or fresh
Lean/kernel verification is claimed.

The actual $e$-start, complete original endpoint/domain/form/trace,
source measure, calibration, four labels, first $2d$ read and later
$d$ reads, and their conditional fresh noise are preserved on the
same path. The neighboring seminorm-to-quantum geometry theory
supplies no automatic common-source identification for these
objects, and none is used. This finite acquisition theorem supplies
neither physical controls nor pointwise observation of the acquired
symbols. Full economical mutual recovery of space, time or lawful
continuation, boundary and memory remains the active RRO goal;
these finite syntax and strictness results do not complete it.

[SRO]: RECURSIVE_RELATIONAL_OBSERVATION_SOURCE_RELATIVE_ORDER.md

## 追加锚（本行以下为增补区）

## 14. Acquired bounded coordinates of the original regular quotient

**Theorem 14.1 (one prebudgeted original-record event).** Retain
Definitions 1.1, 9.1–9.2, [EF, Definition 15.1], all their original
analytic and numerical suppliers, and precisely [SRO, Definition
21.1]'s paid computation, retention and overrun premises. Fix a
rational total failure budget $0<\alpha<1$. There is a single event
$\mathcal G_\tau$ of original-source probability at least $1-\alpha$
on which all the following can be used together: sourcewise finite
startup; convergent calibration intervals for the actual $c>0$;
arbitrarily narrow strict positive reference-time brackets; the
mass, regular-frame, finite-menu, cross-time separation and decoder
certificates of [EF, Theorem 15.2]; and every returned coefficient
in Theorem 14.2 below. Adaptive deterministic choices of compacts,
frames, tree menus, prototypes, polynomials and accepted finite
precision tests introduce no further confidence loss.

*Proof.* Choose positive rational budgets
$\alpha_{\rm st}+\alpha_{\rm acq}\le\alpha$. Use exactly [SRO,
Theorems 21.2–22.1]. Its possible startup outputs $r_j>0$ are
deterministic. For each branch $j$, predefine the $T=3$ adequate
packet schedule using reference defects $D_v(r_j)$ and summable
budgets, for instance $\beta_{j,s}=\alpha_{\rm acq}2^{-j-s}$.
All packet lengths, thresholds and defect construction are fixed
before consulting that packet's record. The strict rational test
[SRO, (SRO.152)] produces these schedules from the existing
fixed-reference names. It does not assume an adequate schedule
or a numerical original clock as free input.

For clarity, let $q_{\rm stat}(w)=\langle1,F_w\rangle_m$ denote
only the stationary mathematical comparison word law, using the
same original heat and emissions. The actual acquired law is
$p(w)=\langle Pb,F_w\rangle_m$ from the $e$-start. Their exact
marked relation is

$$
q_{\rm stat}(3v)=\langle1,cbPF_v\rangle_m
 =c\langle Pb,F_v\rangle_m=c\,p(v).
\tag{14.1}
$$

The first equality uses the original word recursion, and the second
uses self-adjointness of $P$. Thus the full original counters
$A(3v)$ and the supplied dependence estimate control
$\sum_v|A(3v)/N-cp(v)|$, precisely (1.6) and [W, (9.5)].
Raw unmarked word frequencies are not substituted for $p$.
No stationary preparation, independent windows, reset or second
path occurs in (14.1).

On every valid branch $r_j\le\tau$, its predeclared packet event
$\mathcal E_{j,s}$ has unconditional original failure probability
at most $\beta_{j,s}$. Write $\mathcal A_\tau$ for the startup
validity event of [SRO, (SRO.149)] and intersect also its
probability-one termination event. The joint event is

$$
\mathcal G_\tau=\mathcal A_\tau\cap
 \bigcap_{j:r_j\le\tau}\ \bigcap_{s\ge1}\mathcal E_{j,s},
\qquad
\mathbb P_\tau(\mathcal G_\tau)
 \ge1-\alpha_{\rm st}-\alpha_{\rm acq}.
\tag{14.2}
$$

This is [SRO, (SRO.153)]; no conditioning on the selected startup
branch and no independence of nested records is used. Unselected
branches need not be executed. On this event startup selects a
valid branch. In its adequate schedule $t_s\to0$, $4^3/N_s\to0$,
so (6.4) gives $e_{p,s}\to0$ and $c_-,c_+\to c>0$.
Theorem 2.1 supplies arbitrarily narrow strict brackets for
$\tau=a^2d/\eta$ from $p(3)/c$ and fixed-reference evaluations.
Neither $N_d=\|g_d\|_\infty$ nor the trace $s_d$ is numerically
supplied, and they are not equated.

Every further certificate is a deterministic implication on each
valid packet event, valid for every finite candidate passing its
tests. It remains valid after selection on this intersection. In
particular countably many possible rational finite descriptions
of geometry and polynomial syntax require no candidate-specific
statistical event. Their total deterministic services and strict
slack prove sourcewise finite stopping for each fixed finite task,
as in Theorem 10.2 and [EF, Theorem 15.2]. Finitely many reached
finite computations and prefixes have finite total bill on this
event. Off it no finite stopping or correct selected inverse is
asserted here. $\square$

**Definition 14.2 (concrete coordinate consumers and finite inputs).**
For the reference quotient $q=(u,S,Z)\in Q_+$ of [EF, (15.2)] use

$$
F_1(q)=\frac{u}{1+u},\qquad
F_2(q)=\frac{S}{1+S},\qquad F_3(q)=\frac{Z}{1+Z}.
\tag{14.3}
$$

These are globally $[0,1]$-valued, have exact rational values at
rational points and satisfy
$|F_i(q)-F_i(q')|\le\|q-q'\|_\infty$. On the original source
their meaning is $F_i\circ q_*$, where $q_*$ is exactly [EF,
(15.3)], not an unknown physical point passed as an input.
Extend across the omitted null sets in any bounded Borel manner.
Each multiplier reduces the already identified common invariant
sector [EF, Theorem 14.1]. The actual finite-word targets are

$$
\begin{gathered}
\mathcal Q_F(u,v)=\langle v_u,M_{F\circ q_*}v_v\rangle_m,
\qquad v_u=c^{-1/2}P^{1/2}F_{u3},\qquad u,v\in\mathcal L^*.
\end{gathered}
\tag{14.4}
$$

Here $u,v$ in (14.4) are words, distinct from the reference radial
coordinate. The targets may be specified for any finite list of
word pairs and positive rational coefficient tolerances. They are
multiplier matrix coefficients on the original source, not new
emission probabilities or observations of a hidden coordinate.

An optional function $F:Q_+\to[-1,1]$ may be substituted only with
its actual representation: rational-point evaluation to each rational
error, and for every rational compact enclosing box in $Q_+$ a
supplied effective uniform-continuity modulus there. Concretely,
given a rational $e>0$ that modulus returns rational $r>0$ such
that distance less than $r$ implies oscillation at most $e$ on
that box. These are finite numerical suppliers, not a bare assertion
of Borel measurability or continuity. For a finite family take the
minimum of its returned moduli. No extra supplier is needed for
(14.3), whose displayed Lipschitz bound is its modulus. The global
bound $|F|\le1$ is required also outside the selected compact.

**Theorem 14.2 (finite inverse with actual acquired coordinate
consumers).** Under Theorem 14.1, for every unchanged finite positive
original $a,\eta,d$, rational $\epsilon>0$, rational
$0<\delta<1$, the three functions (14.3), finitely many declared
word pairs and positive rational tolerances, the finite inverse
of [EF, Theorem 15.2] can be returned together with rational
enclosures for every requested (14.4), of radius smaller than its
tolerance. The same holds for a finite family with the representation
in Definition 14.2. All conclusions and finite stopping hold on
$\mathcal G_\tau$. No numerical original parameter, exact law,
feature point value or unproved global gap is an input.

More precisely, let $\beta>0$ be rational, at most one and at most
all requested coefficient tolerances. Freeze any certified rational
$0<c_*\le c$ from a positive marker interval, and choose rational

$$
0<\kappa\le\min\{\delta/2,\ \beta c_*/16\}.
\tag{14.5}
$$

The returned regular compact may be required to satisfy
$\nu(K)>1-\kappa$. A finite rational polynomial in its encoded
compact trees can then be constructed with

$$
\begin{gathered}
P_F(y)=\sum_{l=1}^{M_F}a_l\prod_{i=1}^m y_i^{n_{li}},
\quad a_l\in\mathbb Q,\ n_{li}\in\mathbb Z_{\ge0},\\
\sup_{y\in[-1,1]^m}|P_F(y)|\le1,\qquad
\sup_{q\in K,t\in J}|F(q)-P_F(z_t(q))|\le\beta/4.
\end{gathered}
\tag{14.6}
$$

At the true time this entails the compact/global integral bounds

$$
\begin{gathered}
\|F-P_F(z_\tau)\|_{L^1(\nu)}\le\beta/4+2\kappa,\qquad
\|F-P_F(z_\tau)\|_{L^2(\nu)}^2\le\beta^2/16+4\kappa,\\
|\mathcal Q_F(u,v)-\mathcal Q_{P_F}(u,v)|
 \le\beta/4+2\kappa/c_*.
\end{gathered}
\tag{14.7}
$$

For each monomial $k_{l,t}=\prod_i\iota(c_{i,t})^{n_{li}}$,
compute $\widehat Q_{k_l}$ and the evaluated radius $R_{k_l}$
of (10.3), retaining all its word and symbol errors. Stop only
when, for every requested pair and function,

$$
\sum_l|a_l|R_{k_l}(u,v)<\beta/4.
\tag{14.8}
$$

The returned center $\widehat{\mathcal Q}_F=\sum_la_l\widehat Q_{k_l}$
then has the explicit evaluated radius

$$
\mathcal R_F(u,v)=\beta/4+2\kappa/c_*
                         +\sum_l|a_l|R_{k_l}(u,v)
 <5\beta/8<\beta.
\tag{14.9}
$$

*Proof.* Theorem 14.1 first supplies a positive $c_*$, which is
frozen and need not track later marker intervals. The compact
construction of [EF, Theorem 15.2] applies with the smaller mass
allowance (14.5), retaining its rank-three certificates. Choose a
rational enclosing compact box inside $Q_+$ containing $K$.
For each represented $F$ use its modulus there to choose a common
positive rational $r\le\epsilon$ with oscillation at most $\beta/8$
whenever two points of $K$ are at distance less than $r$. For
(14.3) one can take $r\le\min(\epsilon,\beta/8)$.
Run the finite separation and decoder construction at resolution
$r$. Its separation at $r$ implies the requested one at
$\epsilon$. It may narrow the bracket and enlarge the finite menu;
the already certified compact, mass and frame margins persist.
There is no assumption of a uniform modulus for an unrepresented
function class.

Let $q_j,a_j,t_0,\sigma$ be the resulting prototypes and set
$h_0=\sigma/16$ as in [EF, (15.9)]. Choose rational
$f_j\in[-1,1]$ with $|f_j-F(q_j)|\le\beta/16$, using the
function representation and clipping. For (14.3) these values can
be exact rational. On the entire cube $[-1,1]^m$ put

$$
\begin{gathered}
w_j(y)=\max\{0,2h_0-\|y-a_j\|_\infty\},\qquad
W(y)=\sum_{j=1}^{n_p}w_j(y),\\
V_F(y)=\sum_{j=1}^{n_p}f_jw_j(y),\qquad
G_F(y)=\frac{V_F(y)}{\max\{h_0,W(y)\}}.
\end{gathered}
\tag{14.10}
$$

At $y=z_t(q)$ with $q\in K,t\in J$, a covering prototype in
[EF, (15.9)] gives $W(y)\ge h_0$. If $w_j(y)>0$, then

$$
\|z_t(q)-z_{t_0}(q_j)\|_\infty
 <2h_0+h_0/4<\sigma.
\tag{14.11}
$$

The certified remote-pair implication at resolution $r$ gives
$\|q-q_j\|_\infty<r$. Hence $G_F(z_t(q))$ is a convex
average of numbers at distance at most $\beta/8+\beta/16$
from $F(q)$.

Globally $|V_F|\le W$, so $|G_F|\le1$, even where no prototype
represents a source point. Each $w_j$ is $1$-Lipschitz in maximum
norm. Thus both $W,V_F$ are $n_p$-Lipschitz and the denominator
is at least the known rational $h_0$. If $D(y)=\max(h_0,W(y))$,
then, using $|V_F(y')|\le D(y')$,

$$
\left|\frac{V_F(y)}{D(y)}-\frac{V_F(y')}{D(y')}\right|
 \le\frac{|V_F(y)-V_F(y')|+|D(y)-D(y')|}{h_0}
 \le C\|y-y'\|_\infty,\qquad C=2n_p/h_0.
\tag{14.12}
$$

This denominator $D(y)$ is only an approximation formula, not the
decoder of [EF, Theorem 15.2]. All values of (14.10) at rational
cube points are exact rational numbers.

Use the tensor Bernstein construction, an established approximation
method already used in (3.3), as an intermediate step:

$$
P_F(y)=\sum_{k\in\{0,\ldots,n\}^m}
 G_F(2k/n-\mathbf1)
 \prod_{i=1}^m\binom n{k_i}
 \left(\frac{1+y_i}{2}\right)^{k_i}
 \left(\frac{1-y_i}{2}\right)^{n-k_i}.
\tag{14.13}
$$

The weights are nonnegative and sum to one on the cube, giving
$|P_F|\le1$ there. To give its precise error, for fixed $y$ let
$B_i$ be independent binomial variables with parameters
$n,(1+y_i)/2$. Formula (14.13) equals
$\mathbb E G_F(2B/n-\mathbf1)$. Variance bounds and
Cauchy–Schwarz give
$\mathbb E|2B_i/n-1-y_i|\le1/\sqrt n$. Consequently (14.12)
implies

$$
\|P_F-G_F\|_{\infty,[-1,1]^m}\le Cm/\sqrt n.
\tag{14.14}
$$

Choose $n$ a positive integer square with this rational bound
less than $\beta/16$. Such an integer is found by a finite rational
comparison. Combining (14.11)–(14.14) gives the compact error
$\beta/8+\beta/16+\beta/16=\beta/4$ in (14.6), uniformly on
the entire acquired bracket. Expanding (14.13) produces finitely
many exactly rational coefficients and nonnegative integer powers.
Every monomial is an allowed finite product of encoded actual trees
in Definition 9.1, with the empty product one. The global bound
comes from the unexpanded positive weights; cancellation or large
coefficients in the expansion do not invalidate it. Neither an
unspecified effective Stone–Weierstrass theorem nor a supplied
polynomial degree is used.

At $\tau$, the compact error is at most $\beta/4$ and the error
everywhere else is at most two, because both functions are globally
bounded by one. Splitting the original reference integral over $K$
and $K^c$ gives the first two bounds of (14.7). This $L^2$ error
is an error in the reference probability measure, not an assertion
of uniformly small error on the entire quotient.

For the coefficient estimate a further source fact is essential.
All actual emissions are in $[0,1]$, so their word recursion and
the Markov property give $0\le F_{u3}\le1$ for all four-label
words. Since $P^{1/2}=T_{d/2}$ is Markov,

$$
0\le v_u\le c^{-1/2}\le c_*^{-1/2}\quad m\text{-a.e.},
\qquad \|v_u\|_m^2=p(u^Ru3)\le1.
\tag{14.15}
$$

The second identity is the actual palindrome identity proved for
all four labels in Theorem 10.2. Inside the transported compact
$q_*^{-1}(K)$, Cauchy–Schwarz bounds the coefficient error by
$\beta/4$. Outside it, the pointwise product of the two word
vectors is at most $c_*^{-1}$ and the symbol error at most two.
The full-domain transport [W, Theorem 5.2] gives
$m(q_*^{-1}(K^c))=\nu(K^c)<\kappa$. Thus

$$
\begin{aligned}
|\langle v_u,M_{F\circ q_*-P_F(z)}v_v\rangle_m|
&\le(\beta/4)\|v_u\|_m\|v_v\|_m
                         +2c_*^{-1}\nu(K^c)\\
&\le\beta/4+2\kappa/c_*.
\end{aligned}
\tag{14.16}
$$

Here $z$ on the original member is the transported $z_\tau$,
by the derivative and trace identities of Theorem 2.1 and the
induction in Theorem 10.2. Formula (14.16) pays the omitted-mass
bridge for actual word vectors. Norm bounds alone would not permit
replacing omitted reference mass by coefficient error: an arbitrary
unit vector can concentrate in that omitted set. No posterior or
conditional-density computation has been inserted.

It remains to acquire the polynomial coefficient rather than merely
integrate its reference symbol against $1$. Apply Theorem 10.2 to
the now fixed finite list of monomials and requested original word
pairs. To distinguish its raw computational support from the
quotient compact, call that support $A\Subset\Omega$ here. On its
common raw partition the actual evaluated radius is

$$
\begin{gathered}
\widehat Q_{k_l}(u,v)=\int_A\overline{Z_u}Z_vk_l\,d\mu,\\
R_{k_l}(u,v)=r_u+r_v+r_ur_v
                  +B_{uv}|A|e_{k_l,A}+a_{k_l}(u,v),
\quad B_{uv}\ge\|\overline{Z_u}Z_v\|_{\infty,A}.
\end{gathered}
\tag{14.17}
$$

The $r_u,r_v$ are global raw word-vector residuals from Theorem
5.1 and its exact four-label expansion, $e_{k_l,A}$ is the
constructed local symbol error of Theorem 10.1, and $a_{k_l}$ is
the explicit rational arithmetic allowance. In particular these
residuals pay the whole source neighborhood and exterior; the
integral is not truncated to the quotient compact $K$. No effective
global support or supremum of an unencoded tree is needed.

The exact expansion $f_0=f_1=(3/2)f_B-(1/2)f_3$ has absolute
word coefficient sum at most $2^{n(u)}$, where $n(u)$ counts its
$0,1$ letters. Theorem 10.2 includes that amplification in $r_u$.
The additional polynomial amplification is
$A_F=\sum_l|a_l|$, computed from the full finite expansion.
For example it suffices to require every monomial radius to be
less than $\beta/[4(1+A_F)]$. This implies (14.8); using the
actual weighted sum may stop earlier. Repeated factors and mixed
packets remain within the finite-menu syntax. Theorem 10.2 makes
all these radii arbitrarily small for this fixed finite syntax on
the same cofinal schedule. It proves finite stopping after all
packet validity, calibration, trace avoidance, symbol, vector and
radius tests pass. Summing the valid monomial enclosures and adding
(14.16) proves (14.9), since (14.5) gives
$2\kappa/c_*\le\beta/8$ and (14.8) is strict.

To justify the complete finite search, first freeze $c_*,\beta$
and the resulting positive mass target. The regular compact search
has a successful finite tuple with strict slack. At the finer
modulus resolution $r$ its finite menu and separation verifier have
such a tuple as well. The prototype and polynomial constructions
then have finite size, and Theorem 10.2 supplies sufficiently late
packets and finite numerical precision for all coefficient tests.
Further bracket refinements preserve the earlier certificates and
the polynomial approximation, which was uniform on the previous
bracket. If a search enumerates several candidates, each strict test
is run only to a finite precision; undecided tests return
inconclusive and are fairly revisited. The finite existence tuples
are eventually recognized. No zero test or unbounded wait on a
single unsuccessful comparison is required. Every selected object
is covered by Theorem 14.1's event. $\square$

**Definition 14.3 (finite bill and exact recovery boundary).** For
arbitrary real requested $0<\delta,\alpha<1$, these finite
theorems give the same inequalities by using positive rational
subtargets at most $\delta,\alpha$. A numerical request supplies
such rational subtargets, or a representation from which to obtain
them; an unnamed real is not a computational input. No original
source parameter is needed for choosing these tolerances.

The observation bill remains the full original one. A $T=3$
packet uses $N+3$ labels through physical time $(N+4)d$ and the
original $4^4=256$ counters. Startup blocks, all repeated initial
prefixes, rescans, counter bit lengths, retained labels, reference
defect construction and validation, and continuing-stream queueing
and completion latency retain [SRO, Definition 21.1]'s paid
premises. Computation finishing after a tested prefix consumes
retained original data, never a reinitialized source or a later
suffix relabelled as an initial prefix. The physical time formula
is an accounting identity, not an acquired physical clock.

All reached finite work is charged: full-reference endpoint,
resolvent and global-name computations, finite high-order Green
bounds and graph recurrences, compact positive denominators and
time moduli, scalar cutoff derivatives, legality and determinant
tests, mass quadrature, grids and every remote cell pair, prototype
values, all Bernstein grid values and polynomial coefficients,
exact rational bit representations and all coefficient
amplifications, failed finite candidates, raw vector residuals and
local symbol precision. Larger word length and tree depth add
deterministic work even with $T=3$. There is no uniform finite
depth, cost, memory or throughput bound, finite expected cost,
algorithm benchmark or numerical execution asserted here. Paid
finite computation and retained-prefix capacity are mathematical
premises, not a claim of an installed physical processor.

The bounded coordinates (14.3) and their acquired word insertions
retain the same full endpoint/domain/form/source trace, actual
$e$-start, first $2d$ read, subsequent $d$ gaps, four labels,
calibration, null repairs and fresh conditional noise. They add
no control, reset, sensor, exact law, derivative oracle or hidden
trajectory measurement. The finite decoder remains conditional
on supplied feature values; these acquired matrix coefficients do
not supply those values at an actual return. They do not normalize
an arbitrary rare history or prove a current-cut prediction state.
The original actual-current-return memory producer, exact hidden
path, independent physical scale and full mutual recovery remain
unresolved here. The prior exclusion of fixed finite-bit exact
all-word predictive memory is not counted as a new obstruction.

**Definition 14.4 (sources and literature scope).** The new
source-specific composite is the certified finite quotient inverse
[EF, §15] consumed by (14.3)–(14.9) through actual original word
vectors. Its original marked sampling is (14.1), its common-event
and schedule supplier is [SRO, §§21–22], and its finite local
symbols and global word errors are Theorems 9.3–10.2 with [JET,
§§15–16]. Its exact full-source reconstruction and common-symmetry
quotient are [W, §§5, 22–24] and [EF, §§12–14]. None of these
existing results is claimed again as a new rank or acquisition
theorem. The additional deduction is the generated global
far-pair certificate on a certified high-mass regular compact,
its globally bounded encoded-polynomial pullback and the paid
omitted-mass-to-original-word coefficient bridge.

Compact algebra separation is the classical Stone–Weierstrass
setting, for example J. Lebl, *Basic Analysis*, §11.7
[SW]. Its qualitative conclusion alone supplies neither the
numerical margin nor the original finite-record consumer.
Bernstein approximation, Lipschitz interpolation, binomial variance,
Cauchy–Schwarz and countable subadditivity are classical intermediate
methods; all finite bounds used here are given in (14.10)–(14.17).
No uninspected external global inverse, energy-coordinate
injectivity or computable disintegration theorem is invoked.
The source-specific composite is repo-derived conditional
mathematics, not a world-priority claim or new Lean/kernel evidence.
The neighboring C0-multiplier and central-response theories supply
no automatic interpretation of this original source, and none is
used.

[SW]: https://www.jirka.org/ra/html/sec_stoneweier.html

## 追加锚（本行以下为增补区）


## 15. Represented first-only compilation and finite scalar consumers

**Definition 15.1 (inherited record and new finite syntax).** Retain
Definitions 9.1–9.2, Theorem 14.1, Definition 14.2 and all the source,
reference, higher-jet and retained-record premises in them. Retain
[EF, Definitions 15.1 and 16.1]. A request consists of a finite legal
old mixed-packet menu, finitely many of its encoded products in
(9.3), original four-label word pairs and positive rational errors.
It may also request the finite inverse at rational resolution
$\epsilon>0$ and mass allowance $0<\delta<1$, together with the
bounded-coordinate coefficient consumers of Definition 14.2.

The new supplied source relations are only compact first-type leaves
$\phi(b_t)b_t$ and pure trees with binary operation $\Gamma_t$.
The finite output calculus is represented scalar computation and
finite rational polynomials in their encodings. It retains (9.1)'s
full principal matrix. In particular an unencoded scalar product is
not a new bare-tree node. The compiler of [EF, Theorem 16.3]
produces the finite lists and terminal maps, rather than assuming a
language closed under arbitrary smooth operations at no cost.
All numerical computations use the reference coefficients $(1,1)$
on a certified bracket for $\tau=a^2d/\eta$, never numerical
original parameters or a hidden point.

**Theorem 15.2 (constructed scalar and derivative suppliers for the
first-only menu).** A fixed finite request has the following finite
constructions on every certified common legal bracket $J=[L,U]$.
The auxiliary first-type packets in [EF, Theorem 16.2] are legal
throughout $J$. All terminal maps $F_c$ of [EF, (16.4)] and every
finite requested partial derivative have rational error evaluation,
finite compact range bounds and computable compact moduli. On a
finite rational compact box union in $\Omega$, the needed pure-tree
jets, spatial and time bounds are supplied by the existing JET
construction. In particular the ranges, $L_H$ and decoder precision
in [EF, (17.3)–(17.4)] are generated from these services.

For a compiled pure tree of height $h$, a safe invocation for spatial
derivatives through order $j$ uses $b_t$ jets through
$R=h+j+1$ and the additional spatial bound at order $R+1$,
exactly as in Theorem 10.1. For compilation of an old tree of height
$H$, one may consequently use $R\le H+j+2$ and the spatial
bound through $H+j+3$. Terminal scalar derivatives require the
base scalar functions only through order $H+j$, apart from a
further order whenever their modulus is requested. All these are
finite, explicitly charged orders, without a derivative oracle.

*Proof.* The old cutoff recipe specifies rational transition
endpoints strictly inside $I_2$. They give the compact scalar
support enclosure needed in [EF, Theorem 16.2]. Enumerating
rational nested intervals around that enclosure finds its auxiliary
packet in finite rational work. Its outer closure is inside the
old $I_2$, so (9.6) already implies its legality on $J$.
The derivative bounds and error evaluations (9.4)–(9.5) apply to
both cutoff recipes at each finitely requested order.

For $R_\psi(x)=\psi(x)/x$ in [EF, (16.2)], choose a rational
$\Delta>0$ with $\operatorname{supp}\psi$ disjoint from
$[-2\Delta,2\Delta]$. On $[-\Delta,\Delta]$ all its derivatives
are exactly zero. On $|x|\ge\Delta$, the derivative formulas for
$1/x$ have the bounds $j!\Delta^{-j-1}$. Leibniz gives finite
rational bounds for derivatives of $R_\psi$ on any compact or on
all of $\mathbb R$. Evaluating uncertain arguments uses these
bounds and one extra derivative for a modulus; it does not decide
whether a real argument equals a transition endpoint. For the
function $D$ in [EF, (16.3)], the zero branch is flat and the
nonzero branch has $1+y>1/2$. Cutoff derivative bounds and
$j!2^{j+1}$ for reciprocal derivatives give the same construction.
Near the branch join one can use its zero value and the generated
derivative modulus, avoiding a singular interval inversion.

Symbolically differentiate the finite terminal formulas [EF,
(16.6)], using product and chain rules on scalar expressions.
Their only reciprocal constituents are these protected ones;
$\iota$ has denominator $\sqrt{1+x^2}\ge1$. Thus interval
arithmetic and the explicit scalar derivative recurrences produce
finite bounds on any declared compact input box. Rational-center
evaluation to arbitrary error, with one more derivative bound for
transport, gives an effective uniform modulus. At an old parent,
terminal derivatives through order $j$ require child derivatives
through at most $j+1$. Starting from its leaf formula proves the
$H+j$ assertion by induction. This is finite differentiated syntax,
not a new numerical estimate for an unspecified smooth function.

Every pure tree is an allowed tree in Theorem 10.1. Its proof
constructs unencoded values and derivatives before encoding, so
it also supplies their local range bounds. Its safe jet order is
$h+j+1$; [EF, (16.5)] gives $h\le H+1$, and [JET, Theorems
15.2 and 16.1] supply that order and the extra spatial bound.
These calls retain their higher Green bounds, graph recurrence,
global names, weak extraction and positive compact lower bound
for $h$; none is replaced by formal differentiation of numerical
steps. The scalar map in [EF, (17.3)] uses a generated rational
$r<1$. Its inverse-encoding denominator is at least
$\sqrt{1-r^2}>0$ and its Lipschitz bound is generated there.
Finite scalar differentiation bounds on $[-B^+,B^+]^N$ therefore
give the stated $L_H$ and any requested rational evaluation error.
This completes the suppliers required for the inverse transfer.
$\square$

**Theorem 15.3 (bounded finite first-only polynomial supplier).**
Fix a finite legal old menu and a finite rational quotient compact
$K\Subset Q_+$, evaluated on its section in $\Omega$. On a
certified common legal bracket $J$, each requested product with a
declared finite number $s$ of factors

$$
k_t(q)=\prod_{j=1}^s\iota(c_{j,t}(q))
\tag{15.1}
$$

has, for each rational $e>0$, a finite pure first-type feature
vector $y_t=(\iota(C_{1,t}),\ldots,\iota(C_{N,t}))$ and an
explicit finite rational polynomial

$$
P(y)=\sum_{l=1}^{M}a_l\prod_{i=1}^Ny_i^{n_{li}},\qquad
\sup_{[-1,1]^N}|P|\le1,\qquad
\sup_{K\times J}|k_t-P(y_t)|<e.
\tag{15.2}
$$

The empty product is represented exactly by $P=1$. All degrees,
coefficients, coefficient bit lengths and approximation errors are
constructed. This is a value approximation after exact compilation;
no energy operation differentiates it.

*Proof.* Compile the finitely many $c_j$ by [EF, Theorem 16.3]
and use Theorem 15.2 to bound their pure inputs on $K\times J$.
Construct the inverse encoding and component maps $H_j$ of [EF,
(17.3)] on the whole cube. They satisfy
$H_j(y_t(q))=\iota(c_{j,t}(q))$ on this compact and are globally
bounded by one. Their generated Lipschitz constants give the
represented cube map

$$
H_k(y)=\prod_{j=1}^sH_j(y),\qquad |H_k|\le1,\qquad
\operatorname{Lip}_\infty(H_k)\le L_k:=\sum_{j=1}^sL_{H_j}.
\tag{15.3}
$$

The last inequality is the finite product estimate (10.2), so it
includes repeated factors. At each tensor grid point $2k/n-\mathbf1$
evaluate $H_k$ to rational error at most $e_0>0$ and clip to
$[-1,1]$, obtaining rational $h_k$. Form

$$
P(y)=\sum_{k\in\{0,\ldots,n\}^N}h_k
 \prod_{i=1}^N\binom n{k_i}
 \left(\frac{1+y_i}{2}\right)^{k_i}
 \left(\frac{1-y_i}{2}\right)^{n-k_i}.
\tag{15.4}
$$

This is the same classical tensor Bernstein supplier as (14.13).
Its weights are nonnegative and sum to one, giving the global
bound. The binomial variance argument (14.14), now with dimension
$N$, gives the explicit error

$$
\|P-H_k\|_{\infty,[-1,1]^N}
 \le e_0+L_kN/\sqrt n.
\tag{15.5}
$$

Choose rational $e_0<e/2$ and an integer square $n$ with
$L_kN/\sqrt n<e/2$. The strict rational comparison terminates.
Every grid evaluation uses the protected finite scalar supplier
of Theorem 15.2. Expanding (15.4) produces exact rational monomial
coefficients. Degree in each coordinate is at most $n$, total
degree at most $Nn$, and there are at most $(n+1)^N$ distinct
monomials after collection, since each exponent lies between zero
and $n$. There are precisely $(n+1)^N$ grid values before
collection. The full rational expansion, including any zero
coefficients, permits computation of all coefficient sizes and
$A_P=\sum_l|a_l|$; it is not assigned unit cost. The global
bound comes from the unexpanded positive weights, regardless of
large expanded coefficients. Substitution of the exact compact
identity (15.3) proves (15.2). $\square$

**Theorem 15.4 (simultaneous inverse and bounded-coordinate
polynomials with first-only inputs).** Under Theorem 14.1, for
rational inverse resolution $\epsilon>0$, mass allowance
$0<\delta<1$ and any finite family from Definition 14.2, the
finite inverse can use only finitely many pure first-type features.
It retains [EF, Theorem 17.1]'s generated positive separation and
point-input tolerance. For each requested bounded coordinate or
represented $F$, and each rational $e>0$, its finite menu can
also be required to have a rational polynomial $P_F$ such that

$$
\sup_{[-1,1]^N}|P_F|\le1,\qquad
\sup_{q\in K,t\in J}|F(q)-P_F(y_t(q))|<e.
\tag{15.6}
$$

It may be combined with the finitely many polynomials of Theorem
15.3 on the same $K,J$ and a concatenated pure first-type menu.
All claims are deterministic on the single event $\mathcal G_\tau$
of (14.2); a coefficient request still does not reveal point features.

*Proof.* Choose a rational enclosing compact box in $Q_+$ for the
certified regular compact. Use the supplied finite family moduli
to choose a positive rational resolution $r\le\epsilon$ at which
each $F$ oscillates by at most $e/4$ on that box. For the three
coordinates (14.3) their stated Lipschitz constants supply this
choice. Keep this $K$ and its frame certificates fixed. Reuse the
finite separation and prototype construction in the proof of [EF, Theorem
15.2] at resolution $r$ on this same compact, and transfer its
finite menu by [EF, Theorem 17.1]. The regular mass certificate
is retained. Narrow the bracket and refine the spatial cover to produce prototypes $q_j$ and rational first-feature
approximants $a_j$ with (15.9) of [EF], now for $y_t$, separation
$\sigma_1$ and $h_1=\sigma_1/16$. The constructed pure-tree
spatial/time bounds of Theorem 15.2 certify this cover. Adding
more pure coordinates before this construction is harmless;
the transferred gap still holds in the maximum norm.

Use the represented scalar formula (14.10) with these prototypes,
$h_1$, and rational $f_j\in[-1,1]$ approximating $F(q_j)$ to
error less than $e/4$. Its whole-cube bound is one and its
Lipschitz constant is at most $2n_p/h_1$. At an actual compact
feature image there is a covering prototype of weight at least
$h_1$. Every prototype of positive weight is within feature
distance less than $2h_1+h_1/4<\sigma_1$ from that image.
The cross-time separation in [EF, (17.1)] puts its point within
$r$. Thus the weighted average has error less than $e/2$
from $F(q)$, uniformly on $K\times J$. This is precisely the
finite interpolation implication used in (14.10)–(14.12), with
a generated first-only separation in place of the old one.

Apply the existing rational Bernstein formula (14.13) to this
scalar map with dimension $N$, choosing square degree $n$ such
that $(2n_p/h_1)N/\sqrt n<e/4$. Its rational grid values are
exact once the $f_j,a_j,h_1$ are rational. The polynomial then
has compact error less than $3e/4<e$ and global bound one,
as in (14.14). All degrees, expansions and amplification constants
are finite and computed. This reuses the coordinate polynomial
supplier of Theorem 14.2, rather than claiming a new qualitative
density theorem. Theorem 15.3 supplies old product polynomials
on the same compact. Enlarging the feature list is just adjoining
unused variables to each earlier polynomial; subsequent bracket
narrowing preserves all its uniform certificates. The common event
is Theorem 14.1's, since all these implications are deterministic
for every accepted finite candidate. $\square$

## 16. Original-word errors, one event and the complete finite bill

**Theorem 16.1 (acquired original-word transfer through first-only
menus).** Retain the request and all premises of Definition 15.1,
and Theorem 14.1's common event and paid services.
For any fixed original finite positive $a,\eta,d$, any finite such
request has, on $\mathcal G_\tau$, a sourcewise finite construction
of the following coherent unit: the first-only finite inverse when
requested, and enclosures for every original four-label word
coefficient of its declared old encoded products and bounded
coordinates. All returned enclosures have radius smaller than
their requested positive rational tolerances.

Concretely take rational $0<\beta\le1$ no larger than all requested
coefficient tolerances, and freeze a certified $0<c_*\le c$.
Choose rational

$$
0<\kappa<\min(\delta,\beta c_*/16),\qquad \nu(K)>1-\kappa.
\tag{16.1}
$$

When no inverse mass tolerance is requested, any fixed rational
$0<\delta<1$ can be used internally. Apply Theorems 15.3–15.4
with compact errors $e_{\rm app}\le\beta/4$ to obtain, for each
target $k$, a globally bounded polynomial in pure encodings
$P_k=\sum_la_l k_l$, where $k_l=\prod_i\iota(C_i)^{n_{li}}$.
Acquire each monomial for the same actual word pair by Theorem
10.2. On its common raw computational support $A\Subset\Omega$
the evaluated radii retain the full formula

$$
\begin{gathered}
R_l(u,v)=r_u+r_v+r_ur_v+B_{uv}|A|e_{l,A}+a_l^{\rm arith}(u,v),\\
r_u=\sum_w|b_{uw}|r_w,\qquad
\sum_w|b_{uw}|\le2^{n(u)}.
\end{gathered}
\tag{16.2}
$$

Here $b_{uw}$ are the exact marked-word expansion coefficients
of Theorem 10.2, $n(u)$ counts its $0,1$ labels, and $r_w$ are
its global word-vector residuals. The polynomial $a_l$ and the
arithmetic allowance $a_l^{\rm arith}$ are different quantities.
Return center $\widehat Q_k=\sum_la_l\widehat Q_{k_l}$ and
radius

$$
\mathcal R_k(u,v)=e_{\rm app}+2\kappa/c_*
          +\sum_l|a_l|R_l(u,v)+a_{\rm sum}(u,v).
\tag{16.3}
$$

The final sum has explicit rational arithmetic allowance
$a_{\rm sum}$, zero if exact rational sums are used. Require
strict tests

$$
\sum_l|a_l|R_l(u,v)<\beta/4,\qquad
 a_{\rm sum}(u,v)<\beta/8.
\tag{16.4}
$$

Then $\mathcal R_k<3\beta/4<\beta$. This includes scalar
approximation and evaluation errors, omitted reference mass,
original word tails, local pure-tree errors, both coefficient
amplifications and arithmetic. The same actual joint source, law
and word pair occur in every term.

*Proof.* The positive marker interval and the convergent brackets
are supplied on $\mathcal G_\tau$ by Theorem 14.1. The high-mass
regular compact of [EF, Theorem 15.2] can use the smaller target
$\kappa$ in (16.1). Add all finitely requested old packets and
narrow the bracket until each is certified legal. Every one was
legal at the true time, so Theorem 9.3 gives finite strict slack.
The first-only replacements then add only legal auxiliary packets
whose outer closures lie inside those old intervals. Theorems
15.2–15.4 produce one common finite menu, the inverse if requested,
and the polynomials, all uniformly on a common bracket. This
construction uses the original marked record only through its
already certified intervals and finite tests.

For a requested old product set $k(p)=k_\tau(q_*(p))$ in the
original source representation; for a coordinate set
$k(p)=F(q_*(p))$. Both are bounded in absolute value by one.
The polynomial is also bounded by one on the entire source,
since every actual encoded first-tree value lies in $[-1,1]$.
Theorem 14.2's actual word estimate (14.15) gives, for every
original four-label word pair,

$$
\|v_u\|_m,\|v_v\|_m\le1,\qquad
0\le v_u,v_v\le c_*^{-1/2}.
\tag{16.5}
$$

The exact full-domain source transport sends the reference compact
to $q_*^{-1}(K)$ and its complement has actual mass less than
$\kappa$. On this compact the error is at most $e_{\rm app}$;
on its complement it is at most two. Cauchy–Schwarz inside and
the actual pointwise word bounds outside therefore give

$$
|Q_k(u,v)-Q_{P_k}(u,v)|
 \le e_{\rm app}\|v_u\|_m\|v_v\|_m
                  +2c_*^{-1}\nu(K^c)
 \le e_{\rm app}+2\kappa/c_*.
\tag{16.6}
$$

This uses the same actual vectors, rather than separately optimal
bounds from unrelated laws. It is the paid omitted-mass bridge
of (14.16); a bare unit-vector norm bound would not pay it.
It also avoids an assumption of uniform approximation over the
noncompact whole source or a global supremum of unencoded trees.

Every monomial is an allowed encoded product from Definition 9.1
with only first-type leaves. Its source interpretation follows
from the exact compiler and the original transport in Theorem
10.2, so $Q_{P_k}=\sum_la_lQ_{k_l}$ for the same words.
Theorem 10.2 gives (16.2) and the enclosure for each monomial
on the same event. Its global residuals pay both source-neighborhood
and exterior word tails, independently of the geometric compact.
The raw reference support $A$ need not lie inside the reference
quotient pullback of $K$: these are distinct approximations with
distinct paid errors.
The triangle inequality gives (16.3). For example, with the
computed $A_{P_k}=\sum_l|a_l|$, requiring every monomial radius
less than $\beta/[4(1+A_{P_k})]$ is sufficient for (16.4).
Original $0,1$ expansion amplification remains in $r_u,r_v$,
and polynomial amplification remains outside $R_l$. Nothing is
charged only after a cancellation has been presumed. Equations
(16.1) and (16.4) give the displayed strict final bound.

For finite stopping, first freeze $c_*,\beta,\kappa$. The existing
compact/frame/separation search has a finite successful tuple with
strict margins. Compilation adds a finite number of rational packet
choices, finite trees and finite scalar formulas. On the accepted
compact/bracket their finite bounds are produced by Theorem 15.2.
The positive approximation targets in Theorems 15.3–15.4 give a
finite degree and finitely many scalar evaluations. Freeze those
polynomials after certification. There is no circular request for
word accuracy before their amplification constants are known.
The finitely many now fixed pure monomials are exactly within
Theorem 10.2, which makes their radii arbitrarily small under
SRO's original cofinal schedule. Further bracket refinement does
not spoil any earlier uniform certificate. Exact rational summation
can set $a_{\rm sum}=0$.

Every candidate strict test is run to a finite precision and returns
inconclusive when unresolved; fair interleaving revisits candidates
without waiting indefinitely on equality. The successful finite
choices have strict slack, so they are recognized at one finite
stage. Only finitely many reached finite tests precede that stage.
All deterministic implications hold for every passing candidate on
(14.2), including adaptively chosen compacts and polynomials.
Consequently no further statistical event, independence assumption
or confidence loss is introduced. This proves the claimed finite
stopping and original-word errors. $\square$

**Definition 16.2 (paid resource correspondence and unresolved
return interface).** The reference suppliers in Theorems 15.2–16.1
are the existing full-endpoint, resolvent, global-name, higher-jet
and weak-extraction services. The source sampling supplier remains
[SRO, Definition 21.1 and Theorems 21.2–22.1], with the original
prebudgeted schedules and event (14.2). In particular the identity
used for marker counters remains exactly

$$
q_{\rm stat}(3v)=c\,p(v),
\qquad p(v)=\langle Pb,F_v\rangle_m,
\tag{16.7}
$$

with $q_{\rm stat}$ only the stationary mathematical comparison
law. Unmarked transient frequencies are not substituted for it.
The actual source remains the undisturbed $e$-start, first read
$2d$ and subsequent gaps $d$, four original labels, actual
calibration, permitted null repairs and fresh conditional noise.
No source restart, extra sensor or hidden point value enters the
compiler, inverse or coefficient estimates.

The finite bill includes every old cost in Definition 14.3 and,
in addition, the explicit auxiliary packets and legality tests,
the expanded tree sizes bounded in [EF, (16.5)], all terminal
formula sizes and symbolic partial differentiations, the jet and
extra spatial orders in Theorem 15.2, scalar denominator/range
certificates and every scalar evaluation precision and modulus,
raw feature bounds, inverse-encoding margins, $L_H$, decoder
precision and prototype covers. It includes each Bernstein degree,
all $(n+1)^N$ grid evaluations, rational expansions, coefficient
numerator/denominator bit lengths and amplification constants,
all local symbol errors, global word residuals and arithmetic.
All unsuccessful finite legality, frame, mass, separation,
polynomial and coefficient tests are charged too. Counts and
sizes here describe actual finite syntax, not unit-cost scalar
or real-number operations. The inequalities give no cost advantage
for removing a leaf template.

The physical record bill can retain $T=3$: $N+3$ labels through
$(N+4)d$ and all $4^4=256$ original counters per such packet.
Startup blocks, repeated original prefixes, rescans, counter bit
lengths, reference defect certification, retained labels and working
bits remain charged. When computation proceeds while the stream
continues, buffering, every intervening label and completion latency
remain under [SRO, Definition 21.1]'s paid premises. All later
computation uses retained initial data, without calling a later
suffix an initial prefix. Sourcewise finiteness on the common
event gives no source-uniform or expected resource bound, installed
throughput, fixed memory limit or free retention service.

The full complex $A=\rho C$ endpoint, distinct $C=0$ selector,
normalized $h$, full original operator and form domains and nonpolar
source trace persist under the same reference transport. No physical
units or numerical original $a,\eta,d$ have been obtained. The
completed information equality is [EF, Theorem 16.4], and the
retained seed/operation account is [EF, Definition 16.5]. The new
source-specific deduction is the finite compiler consumed by the
existing inverse and word estimates, not a new general chain rule,
quotient classification, rank theorem or qualitative density result.
The literature scope is that definition's `repo-derived` composite,
with Bernstein and finite interpolation reused from §14.

The decoder still requires legitimately supplied features at its
point. A finite list of original-word insertion coefficients does
not provide such features at an actual return. This static supplier
change supplies no new ready or throughput service, no producer
assimilating every label between certified record endpoint $S$ and
actual return $C$, and no all-history predictive state. Those
interfaces and the full mutual-recovery goal remain unresolved.
This statement does not count the previously settled stale-prefix
or fixed-bit obstructions as new results. All results here remain
conditional on the stated original analytic source, numerical
reference and paid resource suppliers.

## 追加锚（本行以下为增补区）


## 17. A finite certificate against every depth of a represented bank

**Definition 17.1 (bank request and unchanged numerical suppliers).**
Retain Definitions 9.1–9.2 and 15.1, Theorem 14.1's single event
$\mathcal G_\tau$ in (14.2), and precisely the full-endpoint
reference and paid record services of [JET, §§12–13, 15–16] and
[SRO, §§21–22]. The finite input is a bank $\mathcal P$ of
represented scalar packets legal at the actual unknown reference
time $\tau=a^2d/\eta$. Empty banks are allowed. A legality
promise is not a passed numerical test: every bank packet used
in a returned certificate must pass (9.6) on its returned bracket.
Only the reference coefficients $(1,1)$, rational trial times and
rational reference coordinates enter deterministic computation.
Original parameters and values at a hidden physical point are not
numerical inputs.

For each time $t>0$ at which the bank is legal, let
$\mathcal T_t(\mathcal P)$ and $\Sigma_{\mathcal P,t}$ have
exactly [EF, Definition 18.1]'s meaning with $b_t,r_t,\Gamma_t$.
All finite depths and arbitrary measurable terminal processing are
included; global $b_t,r_t$ are retained observations and are not
pure-tree inputs. For a new represented packet $\psi$ write

$$
\begin{gathered}
U_t=\psi(b_t)b_t,\qquad W_t=\Gamma_t(U_t,U_t),\\
c_{1,t}=\Gamma_t(U_t,W_t),\qquad
c_{2,t}=\Gamma_t(W_t,W_t),\qquad z_{i,t}=\iota(c_{i,t}).
\end{gathered}
\tag{17.1}
$$

A finite coefficient request may specify original four-label word
pairs, positive rational tolerances, and finite expression templates
in the bank leaves and the newly selected leaf. Only finitely many
pure trees and finite products of their encodings may be requested
at a time. No coefficient of the infinite bank factor, conditional
expectation oracle, or exact hidden-point feature is assumed.

**Theorem 17.2 (generated, uniform, full-factor gap certificate).**
Under Definition 17.1, the following finite data and strict tests
certify a positive rational $\Delta$ such that, simultaneously
for every $t$ in the returned bracket $J=[L,U]\Subset(0,\infty)$,

$$
\inf_{F\in L^2(\Sigma_{\mathcal P,t},m)}
       \|z_{i,t}-F\|_m^2\ge\Delta>0.
\tag{17.2}
$$

The same certificate proves noncommutation of conditional
expectation onto this factor with the full reference $T_t$.
Soundness requires valid finite input intervals and the successful
finite tests below; it does not assume a preselected rank witness,
a uniform unknown margin, or termination of a failed search.

*Proof: finite legal-support data.* Require all bank trace-avoidance
conditions (9.6), and generate rational $\beta>0$ satisfying

$$
\beta<\inf S_J,\qquad
[0,\beta]\cap\overline I_{2,B}=\varnothing\quad(B\in\mathcal P).
\tag{17.3}
$$

Here $S_J$ is the computed enclosure of all $s_t$, not a supplied
exact trace. Choose a new rational nested packet with
$\overline I_{2,\psi}\Subset(0,\beta)$, with all transition
endpoints represented as in Definition 9.2. It passes (9.6) by
(17.3). Its outer closure is disjoint from every bank outer
closure. On a raw rational closed cube
$Q=x_0+[-\rho,\rho]^4\Subset\Omega$ inside a larger rational
box $Q^+\Subset\Omega$, require the computed strict enclosure

$$
b_t(Q)\Subset I_{0,\psi}\qquad(t\in J).
\tag{17.4}
$$

All endpoints and containment margins in (17.3)–(17.4) are
rational comparisons of certified intervals. In particular
$Q\subset A_{\beta,t}:=\{0<b_t<\beta\}$ for every $t\in J$.
Induction by locality [EF, (18.5)] makes every tree of
$\mathcal T_t(\mathcal P)$ zero on this open set at **all**
finite depths. No test enumerates that infinite family and no
uniform spatial support bound for its members is assumed.

*Proof: construction of every finite differential bound.* Select
$i\in\{1,2\}$ and one raw coordinate $x_l$, and put

$$
\Psi_t=(b_t,\gamma_t,z_{i,t},x_l).
\tag{17.5}
$$

The finite jet order needed for this chart follows directly from
its actual syntax. A first-type leaf $f(b_t)$ with
$f(x)=x\psi(x)$ uses $b_t$ derivatives through order $j$ for
its derivatives through $j$. Differentiating
$\Gamma_t(f,g)=t\nabla f^{\mathsf T}A_{\rm raw}\nabla g$
through order $j$ uses child derivatives through at most $j+1$;
all coefficient derivatives are of the known polynomial matrix
$A_{\rm raw}$ of (3.7). Hence a pure first-type tree of height
$h$ uses $b_t$ derivatives through $j+h$. In (17.1), $W_t$
has height one and each $c_{i,t}$ height two. Values, first and
second derivatives of the $c_{i,t}$ therefore use orders two,
three and four respectively. The same chain rule for $\iota$
adds no $b_t$ derivative order. The $\gamma_t$ component uses
only orders through three for its Hessian. Thus $R=4$ suffices
for all center jets and chart derivatives through order two.
Transporting order-four jet intervals across cells additionally
requires the constructed spatial bound $B_5$; time transport uses
$W_{Q^+,4}(L)$. This is the first-only specialization of Theorem
10.1's construction, rather than a new derivative service.

For clarity, [JET, Theorems 15.2 and 16.1] construct these orders
with $k=R+1=5$, $p=k+2=7$, $n=2k+4=14$ for the spatial
instance. Their graph cutoffs require derivatives through $14$
and their differentiated Green bounds through $n-2=12$.
The time instance uses $k=4,p=6,n=12$. All are finite instances
of the existing recurrence, with the actual full-domain graph
vectors and a computed compact positive lower bound for $h$.
The weak extraction kernel [JET, (16.2)] has exponent $R+2=6$.
Its center error for $|\alpha|\le4$ is bounded by
$4\epsilon M+L_{4,\alpha}\epsilon^{-2-|\alpha|}\delta$;
choose $\epsilon$ first and the raw norm error $\delta$ second
to meet each requested jet precision. There is no derivative
of a numerical step approximation.

At a cell of maximum coordinate radius $r_0$ about a rational
center at a rational $t_0\in J$, enlarge every center jet interval
by

$$
4B_5r_0+W_{Q^+,4}(L)(U-L).
\tag{17.6}
$$

This is [JET, (16.6)], on fixed surrounding nested boxes. Cutoff
bounds through order five, from (9.4)–(9.5), enclose derivatives
of $f$ through four and their scalar moduli on uncertain $b_t$
arguments; $f^{(j)}(x)=x\psi^{(j)}(x)+j\psi^{(j-1)}(x)$
for $j\ge1$. All scalar ranges used here are bounded by the
computed local $b_t$ range. Differentiating $\iota$ uses the
protected denominator $\sqrt{1+c^2}\ge1$ and finite rational
square-root enclosures. The explicit $t$ factors at both tree
levels are included in interval evaluation. Thus finite product,
chain and sum expressions give bounds for $\Psi_t,D\Psi_t$
and its Hessian, uniformly on the stated boxes and bracket,
as well as their convergent interval values. In particular they
produce rational $M_1\ge1$ bounding every entry of $D\Psi_t$
and $M_2\ge0$ bounding every second derivative on $Q^+$.
They also certify (17.4). No global unencoded-tree supremum is
needed. Using the more conservative orders of Theorem 15.2
instead gives another valid finite certificate, with its extra
work charged.

*Proof: a certified rectangle inside the unused band.* Choose an
invertible rational $4\times4$ matrix $A$ and rational
$0<q<1/2$. From center derivative intervals compute an upper
bound $e_0$ for
$\sup_{t\in J}\|A^{-1}D\Psi_t(x_0)-I\|_\infty$, and require

$$
e_0+16\|A^{-1}\|_\infty M_2\rho<q<1/2.
\tag{17.7}
$$

The matrix norm is the maximum absolute row sum. Four source
increments and four matrix entries per row give the factor $16$.
It follows that $\|A^{-1}D\Psi_t-I\|_\infty<q$ on $Q$.
For a rational open rectangle $R=\prod_{j=1}^4R_j$ with positive
side lengths require

$$
\sup_{t\in J,\ y\in\overline R}
 \|A^{-1}(y-\Psi_t(x_0))\|_\infty<(1-q)\rho.
\tag{17.8}
$$

Center-value intervals and the finitely many rectangle vertices
give a finite rational upper bound for this supremum. The
contraction argument (11.5), applied to (17.5), now proves
$R\subset\Psi_t(Q^\circ)$ for every $t\in J$, with a unique
inverse in that cube. Indeed the normalized derivative error is
$q$-Lipschitz, zero at $x_0$ after subtracting $x-x_0$, and
(17.8) maps the closed cube into its interior. Integration along
segments also proves injectivity there. Thus this is a common
four-rectangle, not an inference from center rank alone.

Compute $l_h>0$ below $\inf_Qh$ by [JET, Corollary 5.4]. With
$D=24M_1^4>0$, the determinant has absolute value at most $D$
by its $4!$ terms. The same raw measure $m=h^2\mu$ restricted
to $\Psi_t^{-1}(R)\cap Q$ consequently has density at least
$l_h^2/D$ in these chart coordinates. By (17.4) its source
support is contained in $A_{\beta,t}$. Integrating the fourth
coordinate proves, for each $t\in J$,

$$
\begin{gathered}
(b_t,\gamma_t,z_{i,t})_*(\mathbf1_{A_{\beta,t}}m)
 \ge\lambda\,\mathbf1_{R_1\times R_2\times R_3}(y)\,dy,\\
\lambda=l_h^2|R_4|/D>0,\qquad
\Delta=\frac{l_h^2|R_1||R_2||R_3|^3|R_4|}{24D}>0.
\end{gathered}
\tag{17.9}
$$

These constants are generated rational outputs. Other sheets can
only add mass. There is no subtraction of unknown tails and no
conditioning on a separately chosen marginal law.

Every element of the full completed bank factor restricts on
$A_{\beta,t}$ to a Borel function of $(b_t,\gamma_t)$, by
[EF, Theorem 18.2]'s countable-tuple argument. The calculation
(18.8) there, with (17.9), gives a lower bound $2\Delta$ and
therefore (17.2). It applies to arbitrary complex $L^2$ terminal
functions and remains valid after completion. Finally the compact
functions $U_t,U_t^2,W_t,U_tW_t,W_t^2$ and the product identity
[EF, (19.2)] prove the asserted full-domain noncommutation.
Soundness uses the finite tests, locality and those domain
identities. The rank theorem is needed only for eventual finding
of such data. $\square$

## 18. Eventual acquisition, finite original-word consumers and their bill

**Theorem 18.1 (sourcewise finite search on the existing common
event).** For every fixed original finite $a,\eta,d>0$, every
fixed finite represented legal bank and every rational confidence
budget $0<\alpha<1$, there is a fair search under Definition 17.1
which, on the existing $\mathcal G_\tau$ of probability at least
$1-\alpha$, stops after finite charged record and computation
cost with a packet, an index $i$, the finite certificate of
Theorem 17.2 and its positive rational $\Delta$. It proves
[EF, (18.3)] and $E_{\mathcal P}T_d\ne T_dE_{\mathcal P}$
for that same original source. No numerical $a,\eta,d,\tau$
name, predetermined positive rank margin or new statistical event
is supplied to this search.

*Proof.* In the reference member at its actual $\tau$, choose
$\beta$ as in [EF, (18.4)], strictly below $s_\tau$ and below
the finitely many positive distances of bank outer closures from
zero. For an empty bank only the trace condition is needed.
Theorem 9.3 makes (17.3), all bank legality tests and legality of
a new packet with outer closure in $(0,\beta)$ pass on a
sufficiently narrow acquired bracket. No effective spatial support
for the bank or its infinite closure is requested.

[EF, Theorem 9.1] has a nontrivial analytic rank-three determinant
on its connected reduced domain. The nonempty open band
$0<b_\tau<\beta$ therefore contains a full-rank point for
$(b_\tau,\gamma_\tau,\mathcal C_\tau)$ or
$(b_\tau,\gamma_\tau,\mathcal D_\tau)$. Choose the new
packet with this value inside its plateau. On that neighborhood
(17.1) is precisely $\mathcal C_\tau$ or $\mathcal D_\tau$
at height two, by [EF, (18.6)]. The positive derivative of
$\iota$ preserves rank. One raw coordinate completes it to
(17.5). These are existence facts from the same analytic source,
not finite readings of the selected point.

Openness supplies a rational center and small rational cube
with (17.4). A rational invertible $A$ can approximate its actual
chart derivative sufficiently closely. The generated $M_2$ on a
fixed larger box is finite, so decreasing the cube radius gives
(17.7) with strict slack. A small rational target rectangle around
a sufficiently close rational approximation to
$\Psi_\tau(x_0)$ gives (17.8) with strict slack. All jets,
bounds and time moduli in (17.6) are finite and produced by the
existing total services. Narrowing $J$ and increasing finite
precision therefore preserves these strict tests uniformly on $J$.
Positivity of $h$ gives the computed $l_h>0$. This proves the
existence of a finite successful tuple, without naming its margin
before searching.

Enumerate rational $\beta$, new packet and transition endpoints,
both indices, complementary coordinates, rational centers, nested
boxes, invertible matrices, $q$, target rectangles and precision
levels. Interleave their finite tests with the predeclared startup
and packet/bracket schedules of Theorem 14.1. At each finite
precision an undecided test returns inconclusive; no equality or
false candidate is waited on indefinitely. Revisit every finite
tuple at increasing precision. On $\mathcal G_\tau$, startup,
calibration and cofinal bracket acquisition hold together. The
successful tuple with strict slack is eventually recognized, after
only finitely many reached finite tests. Every accepted tuple is
sound for every $t$ in its bracket, so adaptively selecting the
bank certificate adds neither a new union bound nor an independence
assumption for nested prefixes. This is the same deterministic
selection principle as Theorems 11.2 and 14.1.

The full original unitary of [W, Theorem 5.2] and Theorem 2.1
transports leaves, every energy node, $b,r$, the completed sigma
algebra, original measure and projection loss. Reference $T_\tau$
is the transport of original $T_d$ with its entire domains. Thus
(17.9) proves the requested original-source gap and noncommutation,
not merely a reference-family analogue. $\square$

**Theorem 18.2 (finite word coefficients of the selected new
relation).** On the same event and under the same paid premises,
after Theorem 18.1's selection one can acquire, to any requested
positive rational errors, every coefficient in any finite request
of Definition 17.1, including the encoded separating tree itself.
For a selected encoded product $k$ and original four-label word
pair $u,v$, retain exactly Theorem 10.2's certificate

$$
\begin{gathered}
Q_k(u,v)=\langle v_u,M_{k_\tau}v_v\rangle_m,\\
\widehat Q_k(u,v)=\int_A\overline{Z_u}Z_vk\,d\mu,\\
R_k(u,v)=r_u+r_v+r_ur_v+B_{uv}|A|e_k+a_k(u,v),\\
|Q_k(u,v)-\widehat Q_k(u,v)|\le R_k(u,v),
\qquad R_k(u,v)<\epsilon_{k,u,v}.
\end{gathered}
\tag{18.1}
$$

In the integrand $k$ denotes the computed rational step for the
actual encoded product, with certified local error $e_k$ on
$A\Subset\Omega$ uniformly over the acquired bracket. The
$Z$'s are raw word-vector steps, their $r$'s are global residuals,
and $a_k$ is the rational arithmetic allowance, as in (10.3).
These quantities are distinct from the retained observation $r_t$.

*Proof.* Freeze the returned finite packet description and the
requested finite expression templates. They define an ordinary
finite legal first-type menu in Theorem 10.2. The height of a
further requested tree is its actual finite height, without a
bound shared by all possible requests. Theorem 10.1, or the
first-only order recursion in Theorem 17.2, constructs its local
values, derivative/time moduli and encoded product error on the
common raw support of the finite word-vector approximants.
This support need not lie in the strictness cube $Q$, and the
certificate does not discard its exterior or source-neighborhood
tails: they are already paid by the global $r_u,r_v$.

For $0,1$ labels the exact expansions
$f_0=f_1=(3/2)f_B-(1/2)f_3$ give
$Z_u=\sum_w b_{uw}Z_w$ and
$r_u=\sum_w|b_{uw}|r_w$ with
$\sum_w|b_{uw}|\le2^{n(u)}$. The word vectors and all terms
are from the same actual law; both this amplification and the
product error in (10.2) remain in (18.1). Bounded encoding gives
$\|M_{k_\tau}\|\le1$, so exactly the three global residual
terms and the local integration term of Theorem 10.2 apply.
For a requested finite rational polynomial of encoded products,
linear combination additionally costs the computed coefficient
absolute sum and arithmetic error, exactly (16.2)–(16.4).
When an old compiled or bounded-coordinate consumer is requested,
Theorem 16.1 also retains its scalar approximation and omitted-mass
terms; they cannot be deleted on account of the new gap.

Stop only after the original finite packet validity, $c_->0$,
both strict calibration guards, all old and new legality tests,
all chart tests for the gap, all symbol and global-vector
certificates and every requested radius test have passed.
For the now fixed finite menu the convergence and strict-slack
proof of Theorem 10.2 makes all radii arbitrarily small, on
$\mathcal G_\tau$. A later bracket refinement preserves the
accepted uniform gap certificate. The selection is among rational
finite descriptions and all these implications are deterministic
on the already intersected packet events (14.2); no new failure
budget or physical rerun is used. This proves sourcewise finite
stopping of the joint finite request. It does not acquire values
of $z_{i,t}$ at a hidden realized point or all coefficients of an
infinite family. $\square$

**Definition 18.3 (complete paid resources, attribution and return
boundary).** In addition to Definitions 12.3, 14.3 and 16.2's
existing bills, charge the actual bank descriptions and transition
widths, their bit lengths, every legality and trace-norm refinement,
all enumerated finite candidates and failed or inconclusive tests,
all raw jet precisions and amplified weak-extraction norm requests,
all higher Green tails, graph cutoff derivatives and recurrences,
compact denominator/lower-density searches, spatial and time
interval arithmetic, matrix inversions and their bit lengths,
cube subdivisions, target rectangles, determinant and positive
rational gap arithmetic. The selected pure witness has finite
height two; its two alternatives and any further requested trees
are charged by their fully expanded syntax and every derivative
order actually used. A certificate of all depths is an induction
from (17.3), not a paid enumeration of infinitely many trees.
No real scalar, differentiation, reference evaluation, search step
or exact comparison receives unit or zero cost by representation.

The coefficient bill retains all clipped word computations,
original $0,1$ expansions and coefficient bit lengths, global
residual searches, raw support partitions, encoded-product errors,
reference norm names and arithmetic. Any use of §16 additionally
retains every scalar approximation, mass certificate, polynomial
degree, grid evaluation and expansion/amplification cost there.
The observation schedule may still use $T=3$: each such packet
uses $N+3$ original labels through $(N+4)d$ and all $256$
four-letter counters. Startup blocks, all reached initial prefixes,
rescans, counter widths, defect computation, retained records,
working bits and computation between packets are charged. If the
stream continues during computation, buffering every intervening
label, its storage and actual completion latency remain exactly
[SRO, Definition 21.1]'s paid premises. The successful record is
an original prefix; a later suffix is never treated as a new start.
No finite expected, uniform, practical or throughput bound follows
from sourcewise eventual finite work.

The extra mathematical relation is the finite, generated
restricted-density certificate for the **entire all-depth bank
factor**, including global $b,r$. Locality, the rank theorem,
completed factorization and full spectral-domain identities are
used with their hypotheses in [EF, §§18–19]; the quantitative
inverse-chart/density/variance construction is reused from §11,
and finite original-word acquisition from §§9–10 and 14–16.
The total precision services [JET, §§12–13] are not a new oracle
for this bank factor; their established finite reference names
and [JET, §§15–16]'s arbitrary fixed derivative orders are the
suppliers used above. This source-specific composite is
`repo-derived` conditional mathematics. It is not a new general
conditioning theorem, free-algebra interpretation, finite quotient
classification or literature-priority claim.

All statements retain the same full complex non-Friedrichs
$A=\rho C$ endpoint, distinct $C=0$ selector, normalized $h$,
full operator/form domains and source trace, $e$-start, first $2d$
read, subsequent $d$ gaps, original $0,1,3,B$ labels, actual
calibration, permitted null repairs and conditional fresh noise.
The new packet is a mathematical supplier in the recovered source,
not a new label, measurement, preparation, reset or control.
[EF, Theorems 16.4 and 17.1] continue to supply the exhaustive
first-only family and its finite inverse with their own legitimate
input requirements. Deeper pure composition of a fixed local
bank cannot replace that exhaustive family for the task (17.2);
new source observations or operations need their own correspondence
and acquisition proofs. No geometry is inferred from bare
$\alpha,\beta$ syntax, and no bridge to a different source is
obtained by common dimension, names or numerical encoding.

Existence [EF, Theorem 18.2], finite certificate soundness
(Theorem 17.2), sourcewise eventual search and finite word
acquisition (Theorems 18.1–18.2) have separate stated premises.
None supplies the actual-return feature vector or assimilates
every label arriving between certified endpoint $S$ and actual
return $C$. Actual-current-return memory and the full mutual
recovery of space, time or legal continuation, boundary and memory
remain unresolved; no stale-prefix forecast is substituted for
them. These are ordinary conditional proofs without a newly
performed numerical instance or Lean verification.

## 追加锚（本行以下为增补区）


## 19. Generated finite forward states and their actual-label successors

**Definition 19.1 (the reference state and its original-source meaning).**
Retain Definition 1.1, Theorem 14.1 and precisely its paid computation,
retention and overrun contracts. All finite steps, boxes, integrations
and raw names in this section are in the fixed reference member
$(a,\eta)=(1,1)$. Write $\bar h,\bar m,\bar H,\bar K$ for its
normalized zero state, probability measure, full endpoint and transformed
operator, and $\bar S_t=e^{-t\bar H}$, $\bar T_t=e^{-t\bar K}$.
Its time is the acquired invariant $\tau=a^2d/\eta$, not an additional
original-parameter input. Valid brackets and calibration intervals are
those of Theorem 14.1 on $\mathcal G_\tau$; denote their allocated
failure budget by $\alpha_{\rm cal}$.

For the mathematical correspondence only, put
$\sigma^2=\eta/a$, $\kappa=\eta/a^2$ and use the already proved
[W, Theorem 5.2] maps

$$
\begin{gathered}
\mathcal U_\sigma u=\sigma^{5/2}u\circ\delta_\sigma,
\qquad \mathcal W_\sigma v=v\circ\delta_\sigma,
\qquad \bar m=(\delta_{1/\sigma})_*m,\\
\bar h=\mathcal U_\sigma h,\qquad
J_{\bar h}\mathcal W_\sigma=\mathcal U_\sigma J_h,
\qquad \bar H=\kappa\mathcal U_\sigma H\mathcal U_\sigma^{-1},\\
D(\bar S_{\min}^*)=\mathcal U_\sigma D(S_{\min}^*),\quad
D(\bar H)=\mathcal U_\sigma D(H),\quad
D(\bar F)=\mathcal U_\sigma D(F),\\
\bar C(\mathcal U_\sigma u)=\sigma C(u),\qquad
\bar A(\mathcal U_\sigma u)
 =\sigma\bigl(A(u)-(\log\sigma)C(u)\bigr),\\
\bar{\mathscr V}=\mathcal W_\sigma\mathscr V,\qquad
\bar{\mathscr E}[\mathcal W_\sigma v,\mathcal W_\sigma w]
 =\kappa\mathscr E[v,w],\qquad
\overline{\operatorname{tr}}(\mathcal W_\sigma v)
 =\operatorname{tr}v .
\end{gathered}
\tag{19.1}
$$

These are the full complex domains, forms and source trace. In
particular they select the given non-Friedrichs endpoint, rather than
merely matching its expression off the source. Their entrance and
emission consequences are

$$
\begin{gathered}
\bar T_\tau\mathcal W_\sigma=\mathcal W_\sigma T_d,
\qquad \bar g_{2\tau}=\mathcal W_\sigma g_{2d},\qquad
\bar f_y=\mathcal W_\sigma f_y,\qquad \bar c=c,\\
\bar L_y=\bar T_\tau M_{\bar f_y},\qquad
\bar z_\varepsilon=\bar g_{2\tau},\qquad
\bar z_{uy}=\bar L_y\bar z_u=\mathcal W_\sigma z_{uy},\\
\bar F_v=\mathcal W_\sigma F_v,\qquad
p(uv)=\langle\bar z_u,\bar F_v\rangle_{\bar m},\qquad
p(u)=\langle\bar z_u,1\rangle_{\bar m},\\
\|\bar z_u-s\|_{\bar m}
 =\|z_u-\mathcal W_\sigma^{-1}s\|_m
 =\|\bar h\bar z_u-\bar h s\|_2 .
\end{gathered}
\tag{19.2}
$$

Here $z_u$ is the original forward density of [OPPM, Theorem 2.1],
including its $e$-start and next-read convention. To obtain (19.2),
apply the entrance statement in (19.1) at $2\tau$, the heat
intertwining at $\tau$, and multiplication by the transported emissions;
then induct on the actual word $u$. Unitarity gives both pairings and
the error identity. Thus the original first read remains $2d$ and
later gaps remain $d$. The same acquired labels and conditional fresh
noise are used. No value of $\sigma$ or $\kappa$ is computed, and
$\mathcal W_\sigma^{-1}s$ is a semantic correspondent, not an
original-coordinate box supplied to a numerical routine.

A finite step $s$ below is real, nonnegative, rational, supported on
finitely many bounded rational boxes whose closures avoid $e$; its
boxes may be partitioned into disjoint interiors. Put
$M_s=\|s\|_\infty$, an exactly known rational. The stored forward
state is $s$, a rational radius $\Delta_u$, its consumed prefix $u$
and the finite data supporting
$\|\bar z_u-s\|_{\bar m}\le\Delta_u$. It contains evaluated box
coefficients, not an unevaluated exact density. A state is
**action ready** when four computed steps $s_y$ and rational radii
$\varepsilon_y$ certify
$\|\bar L_y s-s_y\|_{\bar m}\le\varepsilon_y$.
**Readout ready at horizon $H$** additionally requires the completed
row and strict tests in Theorem 19.4. These are different requirements.

**Theorem 19.2 (generated composite-action and initialization budgets).**
For a valid $J=[L,U]$, choose rational $t_0\in J$ and
$c_0\in[c_-,c_+]$, with $c_->0$, and use Theorem 5.1's clipped
reference surrogates. Set

$$
\begin{gathered}
\Delta_J=U-L,\qquad \Delta_c=c_+-c_-,\qquad
e_H=\Delta_J/L,\qquad
e_f=c_+C_0(L)\Delta_J+G_0(L)\Delta_c,\\
\ell_3=\ell_B=1/4,\quad \ell_0=\ell_1=3/8,\quad \ell=3/8,\\
e_3=e_f,\quad e_B=0,\quad e_0=e_1=e_f/2 .
\end{gathered}
\tag{19.3}
$$

The rational $Z_0,G_0(L),C_0(L)$ are exactly (3.5), with upward
rational enclosures where necessary. All actual and surrogate emissions
are bounded by their respective $\ell_y$.

Compute a real raw step $H_*$ with
$\|H_*-\bar h\|_2\le\gamma$. For any candidate $s$, compute an
upper rational square-root enclosure $[\|H_*s\|_2]^+$ and put

$$
 Q_s=\min\{M_s,[\|H_*s\|_2]^++M_s\gamma\}.
\tag{19.4}
$$

Then $\|s\|_{\bar m}\le Q_s$. Compute raw steps $K_y$ with
$\|K_y-\bar h\widetilde f_y\|_2\le\alpha_y$ using (5.5)
and its affine $0,1,B$ formulas. For example, raw errors $a_h,a_w$
for $\bar h,w_{t_0}$ give the error
$|c_0|a_w+a_h/4$ for
$\min(\max(c_0w_{t_0},0),\bar h/4)$; subsequent affine errors
add with their absolute coefficients. Thus one can request all four
$\alpha_y\le a$ by taking
$a_h\le a/4$, $a_w\le a/[4(1+|c_0|)]$.
This is the clipped-vector construction, without a numerical supremum
of $g_{t_0}$ or an exact-calibration service.

For each $y$, apply the existing reference heat computation to the
finite raw input $sK_y$, obtaining a raw step $V_y$ with
$\|V_y-\bar S_{t_0}(sK_y)\|_2\le\beta_y$.
For a candidate successor step $s_y$, evaluate
$r_y=[\|V_y-H_*s_y\|_2]^+$ and define

$$
\begin{aligned}
\varepsilon_y^{\rm par}
 &=\ell_y e_H Q_s+M_s e_y,\\
\varepsilon_y^{\rm num}
 &=M_s\alpha_y+\beta_y+M_{s_y}\gamma+r_y,\\
\varepsilon_y&=\varepsilon_y^{\rm par}
                         +\varepsilon_y^{\rm num}.
\end{aligned}
\tag{19.5}
$$

These generated rationals certify
$\|\bar L_y s-s_y\|_{\bar m}\le\varepsilon_y$ for all four
actual labels. In particular the heat-time bound is for the required
multiplied input; it does not assume that heat commutes with emission.

For initialization, compute a raw step $W_0$ with
$\|W_0-w_{2t_0}\|_2\le\alpha_0$, choose $s_0$ and evaluate
$r_0=[\|W_0-H_*s_0\|_2]^+$. The initial radius is

$$
\varepsilon_0
 =2C_0(2L)\Delta_J+\alpha_0+M_{s_0}\gamma+r_0,
\qquad
\|\bar g_{2\tau}-s_0\|_{\bar m}\le\varepsilon_0.
\tag{19.6}
$$

Every norm here is a global norm of finite raw steps, with its stated
raw errors. Near-source and exterior errors are included.

*Proof.* Since $\bar m(G)=1$,
$\|s\|_{\bar m}\le M_s$; comparison of $\bar hs$ and $H_*s$
gives the other upper bound in (19.4). In raw coordinates split the
actual and trial actions as

$$
\begin{aligned}
&\bar S_\tau(\bar h\bar f_y s)
                    -\bar S_{t_0}(\bar h\widetilde f_y s)\\
&\quad=\bar S_\tau\bigl(\bar h(\bar f_y-\widetilde f_y)s\bigr)
       +(\bar S_\tau-\bar S_{t_0})
                                      (\bar h\widetilde f_y s).
\end{aligned}
\tag{19.7}
$$

The first term is at most $M_s e_y$ by Theorem 5.1 and the affine
identities. The second is at most
$e_H\|\bar h\widetilde f_y s\|_2\le e_H\ell_y Q_s$ by the
operator-norm heat bound (3.6). This proves the parameter part for
the composite action. The raw $K_y$ error is multiplied by $M_s$,
heat is a contraction, and comparison of $H_*s_y$ with $\bar h s_y$
costs $M_{s_y}\gamma$. Adding the evaluated residual proves (19.5).
The numerical heat acts on the explicit rational step $sK_y$ and is
therefore an authorized query at rational reference time $t_0$.

The exact initial raw vector is $w_{2\tau}$, by the source identity
(3.1), not $\bar h$ or a stationary density. On $[2L,2U]$, (3.6)
gives
$\|w_{2\tau}-w_{2t_0}\|_2\le2C_0(2L)\Delta_J$.
Adding the three displayed numerical errors proves (19.6), including
the factor $2$ for the original lead-in.

For later use, fix finitely many candidate steps and let valid brackets
shrink to $\tau$, $c$ while all requested raw and norm-enclosure
errors tend to zero. Then $L$ stays bounded away from zero,
$G_0(L),C_0(L),C_0(2L)$ stay bounded, and the parameter parts tend
to zero. The computed $Q_s$ stay bounded by the fixed $M_s$.
Moreover $r_y$ tends to
$\|\bar h(\bar L_y s-s_y)\|_2$, and $r_0$ tends to
$\|\bar h(\bar g_{2\tau}-s_0)\|_2$, by (19.7) and the triangle
inequality. This is refinement for a fixed finite tuple. It invokes
no lower Gram bound and no assertion about conditioning of changing
bases. $\square$

**Lemma 19.3 (evaluated successor on the label actually acquired).**
Suppose the state for $u$ and all four actions were computed as above.
After the original source actually returns $y$, select the already
computed $s_y$, append that original label to the retained prefix,
and set

$$
 s^{\rm new}=s_y,\qquad
 \Delta_{uy}=\ell_y\Delta_u+\varepsilon_y.
\tag{19.8}
$$

On $\mathcal G_\tau$ this is a finite numerical forward state for
the same original prefix $uy$. In a replay of
$u=y_0\cdots y_{t-1}$ with $s_{j+1}=s_{j,y_j}$, its actual
accumulated certificate is

$$
\begin{gathered}
\Delta_0=\varepsilon_0,\qquad
\Delta_{j+1}=\ell_{y_j}\Delta_j+\varepsilon_{j,y_j},\qquad
\|\bar z_{y_0\cdots y_{j-1}}-s_j\|_{\bar m}\le\Delta_j,\\
\Delta_t\le\varepsilon_0+
                    \sum_{j=0}^{t-1}\varepsilon_{j,y_j}.
\end{gathered}
\tag{19.9}
$$

*Proof.* The true action has norm at most $\ell_y$ because its
emission is bounded by $\ell_y$ and heat is a contraction. Hence

$$
\|\bar L_y\bar z_u-s_y\|_{\bar m}
 \le\ell_y\|\bar z_u-s\|_{\bar m}
          +\|\bar L_y s-s_y\|_{\bar m}.
$$

This proves (19.8) and induction proves (19.9). Only an actually
acquired label selects a child. Computing four candidate steps does
not assert that any of their labels occurred. Their certificates come
from Theorem 19.2, not from an acquired posterior row. After selection,
Theorem 19.2 applies again to the explicit retained step $s_y$ to
prepare its four outgoing actions. A requested smaller total radius
can instead trigger refinement and replay from the same original
$e$-start. All such work is charged. $\square$

**Theorem 19.4 (evaluated mass, word errors and normalized readout).**
Let the consumed prefix be $u$, with stored $s=s_t$ and radius
$\Delta_t$, and let $H\ge1$ be a finite integer. For each marked
word $w\in\{3,B\}^H$, the raw-word construction in the proof of
Theorem 5.1 produces a finite raw step $V_w$ satisfying

$$
\|V_w-\bar h\widetilde F_w\|_2\le\nu_w,
\qquad
\|\bar F_w-\widetilde F_w\|_{\bar m}\le E_w,
\tag{19.10}
$$

where $E_w$ is exactly (5.2). This is a finite composition of the
existing clipped multiplications and heat computations, not a new
word oracle. For each $v\in\mathcal L^H$, expand every $0$ or $1$
by $f_0=f_1=(3/2)f_B-(1/2)f_3$. Write the resulting finite identity
as $F_v=\sum_w a_{v,w}F_w$, with zero coefficients omitted, and set

$$
\begin{gathered}
A_v=\sum_w|a_{v,w}|=2^{k(v)},\qquad
V_v=\sum_w a_{v,w}V_w,\qquad
W_v=\sum_w|a_{v,w}|(E_w+\nu_w),\\
\|\bar h\bar F_v-V_v\|_2\le W_v,\qquad
N_v=[\|V_v\|_2]^+,\qquad
k(v)=\#\{i:v_i\in\{0,1\}\}.
\end{gathered}
\tag{19.11}
$$

No cancellation is presumed in $W_v$. For example, for
$\nu=\max_w\nu_w$,

$$
 W_v\le A_v\left[H4^{-(H-1)}(e_H/4+e_f)+\nu\right],
 \qquad \sum_{v\in\mathcal L^H}A_v=6^H.
\tag{19.12}
$$

Thus the original four-label expansion, including all its amplification,
is retained.

With $H_*,\gamma,Q_s$ as in (19.4), compute the rational integrals

$$
\begin{gathered}
\widehat a=\int sH_*^2\,d\mu,\qquad
\widehat b(v)=\int (H_*s)V_v\,d\mu,\\
\mu_s=M_s\gamma(2+\gamma),\qquad
\chi_{s,v}=Q_sW_v+M_s\gamma N_v,\\
d=\Delta_t+\mu_s,\qquad e_v=\ell^H\Delta_t+\chi_{s,v}.
\end{gathered}
\tag{19.13}
$$

Products of rational box steps have exact rational integrals; an
implementation choosing additional outward rounding adds its displayed
radii to $\mu_s,\chi_{s,v}$. In particular, the word-vector error
is multiplied by the computed state-norm bound $Q_s$.
On $\mathcal G_\tau$ the generated budgets imply

$$
 |p(u)-\widehat a|\le d,\qquad
 |p(uv)-\widehat b(v)|\le e_v.
\tag{19.14}
$$

Accept a readout only if the rational strict guards

$$
 a^-:=\widehat a-d>0,\qquad
 E^H:=\sum_{v\in\mathcal L^H}\frac{e_v+d}{a^-}<1/2
\tag{19.15}
$$

pass. Then the finite rational row

$$
 \widetilde q(v)=\widehat b(v)/\widehat a,\qquad
 \rho_u^H(v)=\frac{\max\{\widetilde q(v),0\}}
                   {\sum_{w\in\mathcal L^H}\max\{\widetilde q(w),0\}}
\tag{19.16}
$$

is defined, normalized and satisfies

$$
 \operatorname{TV}(\rho_u^H,R_u^H)\le E^H,
 \qquad R_u^H(v)=p(uv)/p(u).
\tag{19.17}
$$

*Proof.* Multilinearity of the word recursion gives the expansion in
(19.11); a $0$ or $1$ contributes absolute coefficient sum $2$.
Induction in (5.2) gives
$E_w\le H4^{-(H-1)}(e_H/4+e_f)$, proving (19.12).
All raw linear combinations are evaluated with their absolute error
sums. Their supports and coefficients are finite.

For the mass, $\|\bar h\|_2=1$ and
$\|H_*\|_2\le1+\gamma$ give

$$
\left|\int s(\bar h^2-H_*^2)\,d\mu\right|
 \le M_s\|\bar h-H_*\|_2\|\bar h+H_*\|_2
 \le\mu_s.
$$

For the numerator, split its error at $\langle\bar hs,V_v\rangle$:

$$
\begin{aligned}
|\langle s,\bar F_v\rangle_{\bar m}-\widehat b(v)|
 &\le\|\bar hs\|_2\|\bar h\bar F_v-V_v\|_2
       +\|\bar hs-H_*s\|_2\|V_v\|_2\\
 &\le Q_sW_v+M_s\gamma N_v=\chi_{s,v}.
\end{aligned}
$$

Since $\|1\|_{\bar m}=1$ and
$0\le\bar F_v\le\ell^H$, (19.2) and the state radius give
(19.14). There is no unknown norm of the exact state in these budgets.

Put $a=p(u)>0$, $b=p(uv)$ and $q=b/a\in[0,1]$. The guards give
$\widehat a\ge a^->0$, and

$$
 \left|q-\frac{\widehat b(v)}{\widehat a}\right|
 =\frac{|q(\widehat a-a)+(b-\widehat b(v))|}{\widehat a}
 \le\frac{d+e_v}{a^-}.
$$

Summing gives $\|q-\widetilde q\|_1\le E^H$. Positive-part
clipping cannot increase distance to the nonnegative $q$. Its sum
$s_+=\sum_v\widetilde q(v)^+$ obeys $|s_+-1|\le E^H<1/2$,
so it is strictly positive. Normalization adds at most $|s_+-1|$
to the $\ell^1$ error. Dividing by two proves (19.17). No likelihood
floor uniform in $u$ has been inserted. $\square$

**Theorem 19.5 (finite generation for every acquired finite task).**
Fix a finite actually acquired original prefix $u$, an integer $H\ge1$
and a positive rational $\delta$. Under precisely the paid contracts
of Theorem 14.1, on $\mathcal G_\tau$ there is a terminating
numerical construction with the following outputs: a replayed finite
state for that exact $u$, its actual accumulated certificate (19.9)
with $\Delta_{|u|}<\delta$, four generated outgoing action
certificates with $\varepsilon_y<\delta$, and a completed normalized horizon-$H$ row with
$E^H<\min\{\delta,1/2\}$. Every state, action and readout has
its finite reference-coordinate representation, parameter error and
global numerical residual. The construction takes no reached-history
row, exact law, finite successful catalogue or supplied success
certificate as input.

*Proof.* Here is a total finite-precision search, followed by a separate
proof of a successful finite tuple. Put $t=|u|$. For $k=1,2,\ldots$
set $q_k=2^{-k}$. At each search level $n$ for this $k$, use Theorem
14.1's prebudgeted schedule to obtain valid intervals with
$\Delta_J,\Delta_c<2^{-n}$ and $c_->0$. Inconclusive packet or
bracket attempts are retained in the bill. Their sourcewise finite
success on $\mathcal G_\tau$ is the already proved Theorem 14.1.
Choose rational interior $t_0,c_0$.

Enumerate all well-formed finite step tuples of total binary description
length at most $n$ consisting of $s_0$ and $s_{j,y}$ for
$0\le j\le t$, $y\in\mathcal L$. Their main path is defined by
$s_{j+1}=s_{j,y_j}$ for $j<t$. Nonnegative coefficients, rational
box bounds and separation from $e$ are finite rational tests. There
are at most $2^{n+1}$ binary descriptions to inspect. For each tuple,
compute every budget in (19.3)--(19.13), with all requested raw errors
and outward norm-enclosure widths at most $2^{-n}$; the raw $K_y$
subrequests use the explicit allocations in Theorem 19.2.
Each trial is finite: total reference names are queried only at
positive rational times and errors. Every comparison is made on the
returned rational upper bounds, and an unresolved strict test is
inconclusive. No trial waits on equality.

At this $k$, accept the first tuple satisfying

$$
 \varepsilon_0<q_k,\qquad
 \varepsilon_{j,y}<q_k\ (0\le j\le t,\ y\in\mathcal L),
 \qquad \mu_{s_t}<q_k,\qquad
 \chi_{s_t,v}<q_k\ (v\in\mathcal L^H).
\tag{19.18}
$$

Compute (19.9) and (19.15). Stop the entire task only if
$q_k<\delta$, $\Delta_t<\delta$ and (19.15) holds with
$E^H<\min\{\delta,1/2\}$. Otherwise increase $k$ and repeat.
The archive is always the same source record. If the calibration
refinement consumes later original labels, all of them are retained
and charged; the computed result still has tag $u$.

To prove finite success of (19.18), fix $k$. Nonnegative rational
punctured box steps are dense in the nonnegative cone of
$L^2(\bar m)$. Indeed, $\bar m=\bar h^2\mu$ is a finite Borel
measure, the exceptional point is null, and truncation of the support
and value followed by rational simple-step approximation is dense;
positive-part clipping preserves the error bound. Equivalently use
the dense $\bar hs$ search in Theorem 5.1 and clip $s$ at zero.
The raw residual to a named vector is evaluated from the existing
names, so no effective tail or pointwise lower bound for $\bar h$
is presumed by this density statement.

Choose once, for this proof, steps $s_j$ satisfying
$\|\bar z_{y_0\cdots y_{j-1}}-s_j\|_{\bar m}<q_k/16$
for $0\le j\le t$. For each $j<t$, set its actual-label child
to this chosen $s_{j+1}$. Contraction gives

$$
 \|\bar L_{y_j}s_j-s_{j+1}\|_{\bar m}
 <(1+\ell)q_k/16<q_k/8.
\tag{19.19}
$$

Choose every other child, including all four children at $j=t$,
to approximate the nonnegative vector $\bar L_y s_j$ within
$q_k/8$. These are finitely many fixed vectors and finitely many
fixed approximants. No child of a terminal child is required in this
finite replay. All their $M_s$ are finite constants for this fixed
tuple. There is no common-basis closure requirement.

Keep this tuple fixed. By Theorem 19.2, as brackets and numerical
errors shrink, its computed initialization radius tends to a number
less than $q_k/16$ and each computed action radius tends to a number
less than $q_k/8$. Each $Q_s$ remains bounded. For the fixed finite
$H$, (19.11)--(19.12) give $W_v\to0$ with all affine amplification
included. The finitely many $N_v$ stay bounded, so
$\mu_{s_t},\chi_{s_t,v}\to0$. Consequently (19.18) holds with
strict slack at sufficiently large $n$. The description of this fixed
tuple is eventually included. The finite-precision search therefore
recognizes a successful tuple at a finite level. This proves existence
before using search fairness; no assertion is made that shrinking
unweighted residuals controls coefficients of a changing basis.

Every accepted tuple, regardless of its amplitudes or dimension,
satisfies $\Delta_t<(t+1)q_k$ by the actual recurrence (19.9).
Equations (19.13) and (19.18) imply
$d<(t+2)q_k$ and $e_v<(t+2)q_k$. For the fixed positive number
$a=p(u)$, (19.14) gives
$a^-\ge a-2d>a/2$ as soon as $(t+2)q_k<a/4$.
Then

$$
 E^H<4^{H+1}(t+2)q_k/a .
\tag{19.20}
$$

Thus for sufficiently large finite $k$, the state and readout guards
all pass with strict slack. The proof uses $a>0$ only to establish
termination; neither $a$ nor a lower bound for it is an input.
Each earlier $k$ has only finitely many trials by the preceding
argument. This proves finite generation of the actual accumulated
certificate and of the normalized readout.

The same construction applies after any finite actually acquired
extension of $u$, with the new full prefix and desired tolerance.
A previously action-ready state advances by (19.8) without a new row
query; generating further actions or sharpening its radius uses the
explicit reference computations, or replay if necessary. More precisely,
to prepare a successor with state error below a positive rational $\beta$
before knowing the next label, run this theorem at a rational
$\delta'<\beta/(1+\ell)$. Both the parent radius and its four
local action radii are then below $\delta'$, so (19.8) gives
$\Delta_{uy}<(1+\ell)\delta'<\beta$ for whichever label is
actually acquired. This is a generated four-action successor guarantee.
A normalized child readout still needs its own completed tests; for
any reached child they terminate by the theorem just proved. An increasing
sequence of finite tasks need not have bounded total work, bounded
state size or a finite time at which all tasks are complete. $\square$

**Definition 19.6 (finite representations and cost coordinates).**
Use exactly the bit/service model of [W, Definition 21.1 and
Proposition 21.2]. In particular source reads, arithmetic, storage,
numerical-service work and completion latency remain distinct.
An explicit representation of a real rational $p/q$, $q>0$, contains
its sign and self-delimiting binary integers $|p|,q-1$; write
$\lambda(p/q)$ for that length. If
$g(n)=2\lfloor\log_2(n+1)\rfloor+1$ is the length of the
positive gamma code of $n+1$, one choice is
$\lambda(p/q)=1+g(|p|)+g(q-1)$. Reduction is optional.
For a step $s=\sum_{i=1}^r a_i1_{B_i}$ in four coordinates, its
finite representation length is

$$
 \mathsf b(s)=g(r)+\sum_{i=1}^r
 \left[\lambda(a_i)+\sum_{j=1}^4
       \bigl(\lambda(l_{ij})+\lambda(u_{ij})\bigr)\right],
 \qquad B_i=\prod_{j=1}^4[l_{ij},u_{ij}].
\tag{19.21}
$$

Overlapping raw-step lists are allowed, with the same formula. A box
intersection and its volume use finitely many rational comparisons,
subtractions and multiplications. A raw squared norm of a list of
$r$ boxes is the $r^2$-term pair-intersection sum. An integral of
$h\le3$ step factors has at most the product of their list lengths
terms. Thus (19.4)--(19.18) specify actual finite-dimensional
representations and arithmetic, without a Gram matrix or solve.

The accepted replay can retain $1+4(t+1)$ step slots with main-path
slots shared, their scalar budgets, the four final successor slots
and the $4^H$ rational readout entries. The current state itself has
$r_{s_t}$ rational box coefficients; its four successor slots have
$\sum_y r_{s_{t,y}}$ coefficients. All box endpoints, precisions,
errors and reference-query replies are included in their storage.
Names retain their total-query meaning; an infinite name is not
charged as a finite string. Count each genuinely shared backing once
and each distinct retained copy separately.

**Theorem 19.7 (generated finite work and storage accounting).**
The finite task of Theorem 19.5 has a finite work certificate in the
inherited bit/service model. The following explicit accounting is one
such certificate; it is not a bound on a processor rate or on expected
work.

Index every reached tuple trial by $a$, including trials at rejected
$k,n$ and failed strict tests. Also include each arithmetic block of a
composite routine outside its original paid query boundaries, including
each dense multiplication search trial and calibration guard. For a
block without replay or readout take $t=H=0$ in the cost formulas.
Each block is charged once. For each block let $L_a$ be the total
length of its finite input descriptions and numerical replies, and
let $r(F)$ be the actual box-list length of each finite raw or weighted
step $F$ used in it. All the following finite collections are determined
by the displayed formulas, their list lengths and reached loop limits:
$\mathcal N_a$, the norm computations;
$\mathcal I_a$, the step-product integrations;
$\mathcal P_a$, the raw step products;
$\mathcal C_a$, the pointwise min/max partitions;
and $\mathcal A_a$, the affine word combinations. Include syntax,
nonnegativity, disjointness and puncture tests for every candidate.
For a norm of $r$ terms use the pair sum above. For a min/max of a
total of $r$ box terms, sort all coordinate endpoints, partition their
bounded enclosing box into at most $(2r+1)^4$ cells, and evaluate its
finite rational value on each cell. Quadratic sorting is sufficient.
No spatial quadrature oracle is used.

For a square root of a nonnegative rational $x$ to upper-enclosure
width $\epsilon$, bisection of $[0,1+x]$ uses at most

$$
 j(x,\epsilon)=\min\{j\ge0:(1+x)2^{-j}<\epsilon\}+1
\tag{19.22}
$$

rational tests and updates, up to a fixed factor. Include the integer
doubling search computing this $j$. A sufficiently generous explicit
upper bound for the non-service rational/list operations in trial $a$
is

$$
\begin{aligned}
D_a=2^{16}\biggl[&1+t+4^H+L_a+\sum_F(1+r(F))^2
 +\sum_{N\in\mathcal N_a}(1+r(N))^2\\
 &+\sum_{I\in\mathcal I_a}\prod_{F\text{ in }I}(1+r(F))
 +\sum_{(F,G)\in\mathcal P_a}(1+r(F))(1+r(G))\\
 &+\sum_{C\in\mathcal C_a}(1+r(C))(2r(C)+1)^4
 +\sum_{A\in\mathcal A_a}(1+\#A)\\
 &+\sum_{(x,\epsilon)\text{ in norm enclosures}}
                         (1+j(x,\epsilon))\biggr].
\end{aligned}
\tag{19.23}
$$

Here $r(N)$ is the length of the list whose norm is requested;
for example, the initial residual has
$r(W_0)+r(H_*)r(s_0)$ terms and an action residual has
$r(V_{j,y})+r(H_*)r(s_{j,y})$ terms. The mass integral has at
most $r(s_t)r(H_*)^2$ terms; readout $v$ has at most
$r(s_t)r(H_*)r(V_v)$ terms. An unmerged affine output has
$r(V_v)\le\sum_{w:a_{v,w}\ne0}r(V_w)$ terms. In particular it
has at most $2^{k(v)}\max_w r(V_w)$ terms and the sum of these
bounds over all $v$ is $6^H\max_w r(V_w)$.
These are bounds using reached dimensions, not a fixed-dimensional
or coefficient-norm proxy for work.

Let $b_a$ bound numerator and denominator bit lengths of the rational
subexpressions in this finite evaluation, and $w_a$ bound its integer
indices. Such integers are generated structurally from actual input
and reply lengths: addition of two rationals replaces the two length
bounds by their sum plus two, multiplication or nonzero division by
their sum plus one; take maxima over branches and iterate these rules
for the reached finite loop limits. This also counts the errors,
parameter budgets, norm bisections, residuals, denominators and final
normalization. No trace-retention or execution-recording service is
required. Schoolbook integer arithmetic then bounds all of these
non-service operations by
$2^{16}D_a(b_a+w_a+1)^2$ bit operations. Encoding the certificate
by the same finite integer/rational operations is included, with
unused slack in this bound.

At level $(k,n)$ let $T_{k,n}$ be the number of well-formed tuples
actually tested; $T_{k,n}\le2^{n+1}$. Enumerating and parsing all
binary descriptions through length $n$ costs at most
$2^{16}(n+1)^2 2^{n+1}$ bit operations in addition to trial work.
All levels through the successful one are included in the finite set
$\mathcal L$. A replay reads $t$ archive labels per trial, paying at
most $2^{16}(t+1)(\lceil\log_2(t+2)\rceil+1)^2$ bit work; include
this even if some reads could be shared.

For calibration, let $\mathcal B$ be all reached startup or packet
scans of Theorem 14.1, including unsuccessful ones. Scan $s$ has
actual prefix length $R_s$, counter count $K_s$, maximum window
length $T_s+1$ and counter width
$b_s=\lceil\log_2(R_s+2)\rceil$. A direct retained-prefix scan
that updates every declared counter costs at most
$2^{16}K_s(T_s+1)(R_s+1)b_s^2$ bit operations and uses at most
$K_s b_s+2(T_s+1)+2^{16}b_s$ counting bits, in addition to the
retained prefix. For the adequate $T=3$ packets $K_s=4^4=256$;
startup marker blocks have their actual smaller counters. Include
rational packet guards and every failed bracket comparison among
the same finite arithmetic blocks as (19.23).

Finally expand composite raw-word and calibration computations into
the original paid raw-name, heat, resolvent, source and defect queries
$q\in\mathcal Q$ and the arithmetic blocks just specified. Their
internal dense-search trials, polynomial degrees, resolvent powers,
precision queries and failed tests are therefore included. One may
instead charge an existing composite's full bill once, omitting its
subcalls and arithmetic blocks from the separate sums. For each reached
query its input/precision description and reply length are finite data.
For example, an unshared full tuple trial uses one $w_{2t_0}$
computation, the $\bar h$ precision queries, four clipped-vector
computations and $4(t+1)$ forward heat computations. Computing the
$2^H$ marked words separately uses at most $H2^H$ further heats and
$H2^H$ bounded multiplications, with every internal multiplication
search charged as above. The $4^H$ affine outputs and their integrals
are ordinary finite arithmetic. Reused queries are counted once only
when their actual input and certified precision suffice; refined or
repeated calls remain separate charges.
Write $C_q,M_q,B_q$ for precisely its inherited bit-work, scratch-space
and retained-representation charges. These are the service coordinates
of [W, Definition 21.1], not an assumed uniform bound or a new cost
oracle. The finite work certificate is the reached integer/list data
above together with the finite sum of these existing charges. One
valid upper bound for numerical and archive work is

$$
\begin{aligned}
\mathsf C_{\rm task}\le{}&\sum_{q\in\mathcal Q}C_q
 +2^{16}\sum_aD_a(b_a+w_a+1)^2\\
 &+2^{16}\sum_{(k,n)\in\mathcal L}(n+1)^2 2^{n+1}
 +2^{16}\sum_{s\in\mathcal B}
                  K_s(T_s+1)(R_s+1)b_s^2\\
 &+2^{16}\sum_a(t+1)(\lceil\log_2(t+2)\rceil+1)^2 .
\end{aligned}
\tag{19.24}
$$

Service terms stay in their original charged units; a symbolic finite
sum of opaque service charges is not reported as a numerical runtime
prediction for those services. All non-service terms are generated
finite integers. No finite name-answer cost is inferred from label
counts or from the magnitude of a state coefficient.

Let $R_*$ be the greatest original prefix acquired for this task,
including calibration, and let $J\ge0$ additional labels have arrived
by the actual declared completion cut. There are $R_*+J$ physical
reads from the same $e$-start, with last indexed read at
$(R_*+J+1)d$. Archive payload is exactly $2(R_*+J)$ bits for one
backing; every additional complete copy of length $r$ adds $2r$.
Each pending arrival is included even if not yet assimilated. Capture
and indexing add at most
$2^{16}(R_*+J+1)(\lceil\log_2(R_*+J+2)\rceil+1)^2$ bit work
under the inherited lawful-capture contract. Any later replay of those
labels is a further trial/update charge, not free assimilation.
Writing $B_{\rm out}$ for the actual encoded row and tag length,
copying $B_{\rm copies}$ additional archive/buffer bits and serializing
that row add at most

$$
 2^{16}(B_{\rm copies}+B_{\rm out}+1)
 \bigl(\lceil\log_2(R_*+J+B_{\rm copies}+B_{\rm out}+2)\rceil+1\bigr)^2
$$

bit work by direct bit copying and indexing, in addition to the
capture term and (19.24). Here $B_{\rm copies}$ counts distinct label
backings beyond the shared archive. Any separately charged lawful
output-port service retains its original charge. These terms together
give the total work accounting for a delivered row, conditional on
those existing capture and output contracts.

For a sequential evaluation, a finite peak-space bound is

$$
\begin{aligned}
\mathsf M_{\rm task}\le{}&2(R_*+J)+B_{\rm copies}+B_{\rm old}
 +B_{\rm kept}+\sum_{q\text{ retained}}B_q\\
 &+\max_a\bigl[2^{16}(L_a+D_a)(b_a+w_a+1)
                                      +\max_{q\text{ used in }a}M_q\bigr]\\
 &+\max_{s\in\mathcal B}
       [K_s b_s+2(T_s+1)+2^{16}b_s+M_{{\rm ref},s}] .
\end{aligned}
\tag{19.25}
$$

Here $B_{\rm old}$ retains every previously acquired menu, row,
permission and record; $B_{\rm copies}$ counts distinct label buffers
and copies beyond the shared archive; $B_{\rm kept}$ is the sum of
(19.21) for retained steps, the actual encoded scalar certificates,
all $4^H$ output entries and their tags. Reference scratch in packet
$s$ is $M_{{\rm ref},s}$. Failed trial scratch can be released after
its charge is included. If more replies or trials are retained, add
their actual representation lengths. Actual serialization adds its
encoded output length and ordinary bit-copy work, unless an already
accepted backed-representation contract supplies that output instead.

*Proof.* Pairwise box intersections compute each raw squared norm;
triple intersections compute the mass integrals. Endpoint sorting and
cell evaluation give the stated min/max partition bound. The finite
sum of their rational operations, list operations, bisections and
strict tests is bounded by (19.23); each intersection involves four
coordinates and a fixed number of scalar operations, below the
chosen constant. Rational comparison uses cross multiplication, and
schoolbook multiplication and division on the generated bit bounds
cost at most a fixed quadratic multiple. Parsing, enumeration and
archive scans have the stated explicit loop lengths. Counter values
are at most $R_s$, giving the displayed widths and packet scan bound.
These observations prove (19.24) by adding every reached block,
including failures, and its original service bill once. The algorithms
for reference names have finite executed degrees and searches at each
reached precision by their owning theorems; their costs are included
in $\mathcal Q$, without presuming a response-time rate.

Theorem 19.5 makes the numbers of levels and trials finite, each
representation and query finite, and each inherited service bill
finite on the stated event. The retained representation and maximum
scratch accounting proves (19.25). Overrun payload and read indexing
are exactly the original chronological contract of [W, §21]. If an
actual finite completion cut is supplied, its $J$ is finite; no rate
relative to $d$ is required for this conditional accounting. Conversely
these sums do not prove that a physical device catches up or that
such a cut occurs. The state tag in Theorem 19.5 is still $u$ even
when $R_*+J>|u|$. $\square$

**Corollary 19.8 (the ready same-cut input for the existing OPPM consumer).**
Retain [OPPM, Corollary 9.4 and Definition 9.5], including its
predeclared descriptions and dynamic failure budgets
$\delta_\kappa$. Let its original acquisition validity event have
failure at most $\alpha_{\rm old}$. Incorporate the calibration
packets of Theorem 14.1 into that acquisition event, with total
failure allocation $\alpha_{\rm acq}$: one can use the same
prebudgeted packets if they already supply both contracts, or use
the intersection with
$\alpha_{\rm acq}=\alpha_{\rm old}+\alpha_{\rm cal}$.
Then the common original-law event

$$
 \mathcal G^{\rm all}=\mathcal A_{\rm old}\cap\mathcal G_\tau
      \cap\bigcap_{\kappa\text{ deterministically valid}}\mathcal D_\kappa,
 \qquad
 \mathbb P_e(\mathcal G^{\rm all})
 \ge1-\alpha_{\rm acq}-\sum_\kappa\delta_\kappa
\tag{19.26}
$$

supports both this numerical supplier and OPPM9's all-later-cut
comparison. No independence of packets, calibration, stopping or
comparison events is assumed.

Suppose the existing lawful executor conditions actually hold at a
finite causal cut $C\ge T_\kappa$: all labels through $C$ have
been captured, retained and assimilated, the calibration used has
actually become available, and the completed state and horizon-$H$
readout of Theorems 19.2--19.5 for exactly $u=Y_{<C}$ are actually
available there. Include its four outgoing action certificates if
further continuation is requested. Readout readiness requires the
$4^H$ entries, normalization and guards; action readiness alone is
insufficient. Suppose also that lawful output is completed at that
cut, with any serialization/rounding error at most $\omega_C$ in TV.
On $\mathcal G^{\rm all}$ the supplied row then obeys

$$
\begin{gathered}
\operatorname{TV}(\rho_C^{\rm out},{\bf R}_C^H)
                          \le E_C^H+\omega_C,\\
\operatorname{TV}(\rho_C^{\rm out},
                    Q_{W_{\kappa,C-T_\kappa}}^H)
               \le E_C^H+\epsilon_\kappa+\omega_C .
\end{gathered}
\tag{19.27}
$$

Consequently it earns an actual numerical instance of [OPPM, (9.24)]
with $\zeta_C=E_C^H$ and
$\xi_C=\epsilon_\kappa+\omega_C$, independently of any
suffix-row catalogue. Using the old consumer verbatim gives the
conservative bound

$$
 \operatorname{TV}({\bf R}_C^H,\rho_C^{\rm out})
        \le 2\epsilon_\kappa+E_C^H+\omega_C .
\tag{19.28}
$$

The stronger first inequality of (19.27) is available directly.
The extra comparison error in (19.28) is explicit.

*Proof.* Include the calibration event before applying the countable
union bound in [OPPM, (9.26)]. Deterministic numerical tests add no
further random event, but do require that calibration event. This
proves (19.26). At the actually ready cut, (19.17) and output error
give the first bound in (19.27). OPPM9 supplies
$\operatorname{TV}({\bf R}_C^H,
Q_{W_{\kappa,C-T_\kappa}}^H)\le\epsilon_\kappa$ on this same
event, so the triangle inequality gives its second bound and then
(19.28) by the old consumer. A deterministic calculation for a fixed
consumed prefix can finish later; it remains a row for that prefix.
If labels arrive during its calculation or output, obtaining a row
current at the later completion cut requires their lawful capture,
retention, assimilation and a completed corresponding readout.
The theorem asserts no coincidence of these cuts from numerical
termination alone. $\square$

**Definition 19.9 (scope, reuse and literature boundary).** The new
supplier is the evaluated reference step state, generated four-action
residuals (19.5), finite successful replay for their actual accumulated
certificate (19.18)--(19.20), and the generated readout/work/consumer
interface (19.13)--(19.28). Its source-specific composite estimate
uses the earned $\tau,c$ intervals and bounded clipped source
vectors, including heat after multiplication. FEA5/14 already supply
the calibration event, clipped finite reference words and total raw
computations; [OPPM, §§2 and 7] already supply exact filtering and
finite acquired catalogues. Those results are reused, not counted
as new. Neither finite-word computability nor exact Bayes recursion
alone supplies the generated finite state and its action-residual
refinement proof above. No exact finite invariant span, uniform lower
Gram bound or uniform likelihood floor is assumed.

The source correspondence uses the full endpoint, forms and entrance
in [W, Theorem 5.2], and the exact-source raw identity in
[R, Theorems 12.2--12.4]. Real finite steps do not replace the full
complex endpoint. The retained source is the same original diffusion,
with all four labels, the original full history and all acquired
menus, references, permissions and costs. Reference coordinates
supply no original hidden point, original box mass, physical clock,
reset, control, new sensor or parameter name.

The argument is `repo-derived` for these source contracts and this
consumer. Dense simple-step approximation, contraction residual
estimates, spectral heat continuity, positive-part normalization and
schoolbook arithmetic are established methods used inside its proof.
For the numerical-name convention see Klaus Weihrauch, *Computable
Analysis*, DOI [10.1007/978-3-642-56999-9](https://doi.org/10.1007/978-3-642-56999-9);
for elementary integer arithmetic see Richard P. Brent and Paul
Zimmermann, *Modern Computer Arithmetic*, §§1.1--1.4,
DOI [10.1017/CBO9780511921698](https://doi.org/10.1017/CBO9780511921698).
No general theorem from these references is asserted to install an
original-source service. The estimates used here are proved above;
worldwide novelty and new Lean verification are not claimed.

Theorem 19.5 is sourcewise finite mathematics for each fixed acquired
finite prefix, horizon and positive tolerance under the existing paid
contracts. It is not confined to prefixes from a supplied finite
catalogue. Its tolerance quantifier concerns these fixed-prefix numerical
tasks with paid calibration refinement; it does not assert that every
tolerance can be delivered as a current forecast on a fixed running
source. It gives no uniform dimension, likelihood floor, runtime,
throughput, deadline, finite expected bill, or fixed finite memory.
Capture, retention, assimilation of every arriving label, completed
readout, lawful output and actual finite executor completion retain
their distinct inherited conditions. A past-prefix row never becomes
current merely by finishing later. No native/diffusion/AURIC bridge,
full mutual recovery or termination of the persistent objective
follows from this supplier.

[OPPM]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_PASSIVE_PREDICTIVE_MEMORY.md

## 追加锚（本行以下为增补区）
