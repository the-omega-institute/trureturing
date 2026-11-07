# Original finite-record acquisition of bounded local-energy pairings

> Reference theory with ordinary conditional proofs. The cited source and
> endpoint results are premises, not freshly verified Lean statements. This
> volume uses the `consensus-rnd:sshx` context and an independent `codex-cli`
> implementation carrier. Independent review and publication belong to the
> calling workflow. No kernel verification or worldwide novelty is asserted.
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
mathematics. Formal-code references report source lookup, not fresh
compiled application. This volume adds no Lean, Blueprint or
digestion artifact.

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
