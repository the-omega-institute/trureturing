# Original source energy and positive-measure fibre geometry

## 1. The original endpoint, source and clock

**Assumption 1.1 (the full original analytic source).** Fix arbitrary
finite $a,\eta,d>0$. Retain the entire original analytic source of
[original word geometry, Assumption 1.1][W], with its hypotheses and
suppliers [E, §§109–112] and [S, §§115–117, 120, 122, 133]. In particular,
use the group, identity and raw Haar measure

$$
\begin{gathered}
G=H^1\times\mathbb R,\qquad e=(0,0,0,0),\qquad
pp'=(x+x',y+y',z+z',w+w'+xy'),\\
d\mu=dx\,dy\,dz\,dw,\qquad
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\qquad L=-\sum_{j=1}^3X_j^2,\\
L\Gamma=\delta_e,\qquad
\Gamma\circ\delta_q=q^{-3}\Gamma,\qquad
\delta_q(x,y,z,w)=(qx,qy,qz,q^2w).
\end{gathered}
\tag{1.1}
$$

The potential is the original unit-source Green field $\Gamma$. With
$\mathcal D_0=C_c^\infty(G\setminus\{e\};\mathbb C)$, put

$$
\begin{gathered}
S=(aL-\eta\partial_w^2-16\sqrt{a\eta}\,\Gamma)|_{\mathcal D_0},
\qquad \ker S^*=\mathbb Cw_*,\qquad C(w_*)=1,\\
h=\frac{w_*}{\|w_*\|_{L^2(\mu)}},\qquad c_h=C(h)>0,
\qquad \rho=\frac{A(h)}{C(h)},\\
D(H)=\{u\in D(S^*):A(u)=\rho C(u)\}
     =D(\overline S)\dotplus\mathbb Ch,\qquad Hu=S^*u,\\
H\ge0,\qquad \ker H=\mathbb Ch,\qquad
D(F)=\{u\in D(S^*):C(u)=0\},\qquad F\ge0,\quad F\ne H.
\end{gathered}
\tag{1.2}
$$

Here $A,C$ are exactly the parameter-dependent maximal-domain
coefficients of [E, (109.1)–(109.3), (112.2)–(112.5)]. The endpoint in
(1.2) is imposed on the entire complex maximal domain. The supplied
representative of $h$ is real, smooth and strictly positive on
$M=G\setminus\{e\}$. Keep

$$
\begin{gathered}
m=h^2\mu,\qquad m(G)=1,\qquad m(\{e\})=0,\qquad
J_hv=hv,\qquad K=J_h^{-1}HJ_h,\qquad T_t=e^{-tK},\\
\mathscr V=D(K^{1/2})=\mathscr V_0\dotplus\mathbb C1,
\qquad \operatorname{tr}(v_0+q1)=q,\\
\mathscr E[v,u]=\int_Gh^2\left(
 a\sum_{j=1}^3\overline{X_jv}X_ju+
 \eta\overline{\partial_wv}\partial_wu\right)d\mu.
\end{gathered}
\tag{1.3}
$$

The subspace $\mathscr V_0$ is the form-norm closure of
$\mathcal D_0$ in $L^2(m)$, and $\operatorname{tr}$ is the original
continuous source trace. The actual conservative continuous-path
process starts at $e$. Its deterministic positive-time laws satisfy

$$
\begin{gathered}
\mathbb P_e(Z_t\in dp)=g_t(p)m(dp),\qquad
g_t\in L^2(m)\cap L^\infty(m),\qquad
g_t>0\quad m\text{-a.e.},\qquad \int_Gg_t\,dm=1,\\
g_{t+u}=T_ug_t\quad(t>0,u\ge0),\qquad T_u1=1,\qquad
\operatorname{tr}(T_tv)=\langle g_t,v\rangle_m.
\end{gathered}
\tag{1.4}
$$

The inner product is antilinear in its first argument. No value of
$h$ at $e$ is part of these definitions.

**Definition 1.2 (the original observation and the source energy).**
Use the unique smooth representative of the class $g_d$ on $M$ and
write it as $b$ there. For the spatial differential use
$\mathrm d_{\rm sp}$, to distinguish it from the fixed sampling
interval $d$. Define

$$
E=a\sum_{j=1}^3(X_jb)^2+\eta(\partial_wb)^2,
\qquad \gamma=dE\quad\text{on }M.
\tag{1.5}
$$

Assign any finite values at $e$ when taking laws; they have zero
$m$-measure. The actual readout may use any permitted bounded Borel
representative $\widetilde b$ of $g_d$, including its prescribed
null repairs. Retain exactly

$$
\begin{gathered}
P=T_d,\qquad c=\frac1{4(1+\|g_d\|_{L^\infty(m)})},\qquad
f_3=c\widetilde b,\qquad f_B=\frac14,\\
f_0=f_1=\frac{3/4-f_3}{2},\qquad
\mathcal L=\{0,1,3,B\},\qquad
\mathsf X_j=Z_{(j+2)d}\quad(j\ge0).
\end{gathered}
\tag{1.6}
$$

Conditional on the path, the labels use these emissions with fresh
independent read noise. Thus the first read is at $2d$ and subsequent
gaps are $d$. All coordinate curves below are mathematical curves
in this fixed source.

[W]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_WORD_GEOMETRY_RECOVERY.md
[R]: RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md
[E]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md
[S]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md
[C]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md

## 2. Source regularity and the principal metric

**Definition 2.1 (symmetric coordinates and the local source suppliers).**
Put

$$
s=w-xy/2,\qquad r=(x^2+y^2)^{1/2},\qquad
\Omega=\{r>0\},\qquad x=r\cos\theta,\quad y=r\sin\theta.
\tag{2.1}
$$

The change to $(x,y,z,s)$ has Jacobian one. The set $\Omega$ is
connected and has full $m$-measure. The original local estimates
[S, (120.6)–(120.8)] make $T_tu$ smooth on $M$ for $u\in L^2(m)$,
$t>0$, with real evaluation vectors $k_{t,p}\in L^2(m)$ satisfying

$$
(T_tu)(p)=\langle k_{t,p},u\rangle_m\quad(p\in M).
\tag{2.2}
$$

The actual analyticity supplier [S, (122.6)–(122.11)] makes
$\Gamma,h,T_tu$ real analytic on $\Omega$; in particular $b$ is
analytic there. Its hypotheses are the analytic original local
coefficients, compact local ellipticity for $a,\eta>0$ and the spectral
iterate bounds for the actual full $K$. This supplier asserts no
analyticity on the omitted axis. The actual quotient decay theorem
[R, Theorem 14.3] gives

$$
\lim_{R\to\infty}\sup_{\varrho(p)\ge R}b(p)=0,
\qquad
\varrho(p)=\bigl((x^2+y^2+z^2)^2+s^2\bigr)^{1/4}.
\tag{2.3}
$$

This is a value estimate for the same $g_d$, without a derivative
estimate or a monotonicity assertion. The full-source rotations of
[S, §120] fix $(z,s)$ and rotate $(x,y)$. The full-source reflection
of [C, Proposition 141.1] changes $z$ to $-z$. Both preserve $h,m$,
the full endpoint, the trace and every $g_t$.

**Definition 2.2 (the unchanged principal metric).** The positive
principal symbol in (1.5) is the inverse of the smooth analytic
Riemannian metric

$$
\mathsf g=\frac{dx^2+dy^2+dz^2}{a}
 +\frac1\eta\left(ds+\frac{y\,dx-x\,dy}{2}\right)^2.
\tag{2.4}
$$

Consequently $E=|\nabla_{\mathsf g}b|_{\mathsf g}^2$. In cylindrical
coordinates the geodesic Hamiltonian is

$$
\mathcal H_{\rm geo}=\frac12\left[
 a p_r^2+a p_z^2+
 a\left(\frac{p_\theta}{r}+\frac r2p_s\right)^2+
 \eta p_s^2\right].
\tag{2.5}
$$

The cyclic variables conserve $p_\theta,p_s,p_z$. In particular, a
geodesic with $p_\theta=0$ and $p_s=\nu$ satisfies, before its first
axis crossing,

$$
\ddot r+\frac{a^2\nu^2}{4}r=0,\qquad
\dot\theta=\frac{a\nu}{2},\qquad
\dot s=\nu\left(\eta+\frac{ar^2}{4}\right),\qquad
\ddot z=0.
\tag{2.6}
$$

These are Hamilton's equations for (2.5), in the original units.
The general two-step nilpotent geodesic equations and central first
integrals are the classical intermediates of Eberlein,
[*Geometry of 2-step nilpotent groups with a left invariant metric*,
§3, Propositions 3.1–3.2 and Corollary 3.4, pp. 625–627][EB].
Equations (2.5)–(2.6) give their direct specialization to this metric,
including the independent $z$ direction. No metric classification is
needed.

[EB]: https://www.numdam.org/item/10.24033/asens.1702.pdf

## 3. The actual derivative obstruction through critical times

**Theorem 3.1 (a nonzero actual energy minor for every positive triple).**
Under Assumption 1.1, for every original finite $a,\eta,d>0$ there
exists $p\in\Omega$ such that

$$
\bigl(\mathrm d_{\rm sp}b\wedge\mathrm d_{\rm sp}\gamma\bigr)_p
 \ne0.
\tag{3.1}
$$

In particular $p$ is a regular point of $b$, and the actual map
$(b,\gamma)$ has rank two on a nonempty open subset of $\Omega$.
The quantifier includes all original positive parameter triples;
there is no small-time or asymptotic parameter restriction.

*Proof.* First the canonical smooth representative is strictly
positive at every point of $M$. Fix $p\in M$ and $t>0$. Positivity
preservation makes $T_tu\ge0$ almost everywhere for every nonnegative
real $u\in L^2(m)$. Its smooth representative is therefore nonnegative
at every point of $M$: otherwise continuity and the strictly positive
local density of $m$ would give a negative set of positive measure.
Equation (2.2), tested against all such $u$, gives $k_{t,p}\ge0$
almost everywhere. Conservation and (2.2), with $1\in L^2(m)$, give
$\langle k_{t,p},1\rangle_m=1$. In (1.4) use $t=d/2$ and
$g_{d/2}>0$ almost everywhere. Thus

$$
b(p)=\langle k_{d/2,p},g_{d/2}\rangle_m>0.
\tag{3.2}
$$

The pairing is finite by Cauchy–Schwarz. This proves positivity of
the smooth representative itself.

We also need central evenness for the actual source. In symmetric
coordinates let

$$
J_s(x,y,z,s)=(x,-y,z,-s).
\tag{3.3}
$$

In the original coordinates this is $(x,y,z,w)\mapsto(x,-y,z,-w)$,
a raw-Haar-preserving group automorphism fixing $e$. Pullback fixes
$X_1,X_3$ and reverses $X_2,\partial_w$, so preserves $L$ and
$\partial_w^2$. The original representation
$\Gamma=\int_0^\infty h_t^L\,dt$, used in [S, §120], makes $\Gamma$
invariant: the free $L$ semigroup commutes with $J_s$ and its identity
source is fixed. Hence $J_s$ preserves $S$, $S^*$ and $\overline S$.
Its pullback sends $h$ into the supplied line $\ker S^*=\mathbb Ch$.
Reality, positivity and unit norm force $J_sh=h$. Therefore it
preserves the entire domain
$D(H)=D(\overline S)\dotplus\mathbb Ch$ and commutes with $H$.
Conjugation by $J_h$ gives invariance of $m$ and commutation with the
actual $K,T_t$. Pullback preserves $\mathscr V_0$, fixes $1$, and
therefore preserves $\operatorname{tr}$. Apply (1.4) to a pulled-back
input; Riesz uniqueness gives $J_sg_t=g_t$. The smooth representatives
have this symmetry pointwise. Together with rotations and the
$z$ reflection in Definition 2.1, this gives

$$
b=b(r,z,s),\qquad b(r,z,s)=b(r,z,-s)=b(r,-z,s),
\qquad b_s(r,0,0)=b_z(r,0,0)=0.
\tag{3.4}
$$

Thus the symmetry includes the full complex endpoint and the original
source law, rather than only its punctured differential expression.

Suppose, seeking a contradiction, that
$W=\mathrm d_{\rm sp}b\wedge\mathrm d_{\rm sp}E$ vanishes identically
on $\Omega$. By (3.2) and (2.3), the positive radial function
$r\mapsto b(r,0,0)$ tends to zero. The mean value theorem supplies
$r_0>0$ with

$$
q_0=(r_0,0,0,0),\qquad B_0=b_r(q_0)<0,\qquad
c_0=b(q_0),\qquad E_0=E(q_0)=aB_0^2>0,
\tag{3.5}
$$

where the tuple for $q_0$ uses $(r,\theta,z,s)$. Near $q_0$, analytic
submersion coordinates $(b,y_1,y_2,y_3)$ and $W=0$ show that $E$ is
independent of the $y$ coordinates. On a smaller neighborhood,

$$
E=\beta(b),\qquad \beta\text{ analytic},\qquad \beta(c_0)=E_0>0.
\tag{3.6}
$$

Let $\Lambda$ be a connected small piece of $\{b=c_0\}$ containing
$q_0$ inside this neighborhood. On it $E=E_0$. In the local regular
tube the descending unit normal
$n=-\nabla_{\mathsf g}b/\sqrt E$ has geodesic integral curves. Indeed,
writing $v=\nabla_{\mathsf g}b$, symmetry of the Riemannian Hessian gives

$$
\nabla_vv=\tfrac12\nabla E=\tfrac12\beta'(b)v,
\qquad \nabla_nn=0.
\tag{3.7}
$$

The second equality follows by differentiating $E^{-1/2}$ and using
$v(E)=\beta'(b)E$. This is only a local regular-level calculation.
The familiar normal-geodesic relation for transnormal functions is
an intermediate here; global critical-level theorems, such as
Alexandrino–Alves–Dehkordi, [*On Finsler transnormal functions*,
Theorem 1.3][TR], require additional hypotheses and are not used.

The geodesic starting at $q_0$ with velocity $n(q_0)$ is the outward
radial ray

$$
C_0(t)=(r_0+\sqrt a\,t,0,0,0),\qquad
f(t)=b(C_0(t)),\qquad f'(0)=-\sqrt{E_0}<0.
\tag{3.8}
$$

It remains in $\Omega$ for all $t\ge0$. The function $f$ is real
analytic on $(-r_0/\sqrt a,\infty)$.

The restriction $b_s|_\Lambda$ is a nonzero analytic germ at $q_0$.
To prove this, first $b_s$ is not identically zero on $\Omega$:
for fixed $r>0,z=0$, (3.2) and (2.3) make
$s\mapsto b(r,0,s)$ positive and tending to zero at both ends, hence
nonconstant. If $b_s$ vanished on a neighborhood of $q_0$ in
$\Lambda$, the initial covector of each normal geodesic there would
have $p_s=-b_s/\sqrt{E_0}=0$. Conservation of $p_s$ in (2.5) and the
normal-flow identity on a sufficiently short regular tube would give

$$
0=p_s=\mathsf g(n,\partial_s)=-b_s/\sqrt E
\tag{3.9}
$$

throughout that tube. The normal flow from an open leaf piece is a
local diffeomorphism onto an open subset of the four-dimensional
$\Omega$. Thus $b_s$ would vanish on an open subset, and analytic
uniqueness on connected $\Omega$ would make it identically zero, a
contradiction.

Since $b_r(q_0)\ne0$, the leaf has analytic coordinates
$(\theta,z,s)$ near $q_0$. Rotational invariance makes $b_s|_\Lambda$
independent of $\theta$. A direction on which its first nonzero
homogeneous Taylor term is nonzero supplies an analytic curve
$q(u)\in\Lambda$, with $q(0)=q_0$, $\theta(q(u))=0$, and, after
shrinking $\epsilon>0$,

$$
\begin{gathered}
R(u)=r(q(u))>0,\qquad B(u)=b_r(q(u))<0,\\
S(u)=b_s(q(u))\ne0\quad(0<u<\epsilon),\qquad
S(u)\longrightarrow0,\qquad E(q(u))=E_0.
\end{gathered}
\tag{3.10}
$$

Let $C_u$ be the unit-speed geodesic with initial covector
$-\mathrm d_{\rm sp}b(q(u))/\sqrt{E_0}$. Rotation invariance gives
$p_\theta=0$, and

$$
\nu(u)=p_s=-\frac{S(u)}{\sqrt{E_0}},\qquad
\omega(u)=\frac{a|S(u)|}{2\sqrt{E_0}}>0.
\tag{3.11}
$$

Equation (2.6), with $\dot r(0)=-aB(u)/\sqrt{E_0}$, yields

$$
\begin{gathered}
r(C_u(t))=R(u)\cos(\omega(u)t)
        -\frac{2B(u)}{|S(u)|}\sin(\omega(u)t),\qquad 0\le t<T(u),\\
\alpha(u)=\pi-\arctan\frac{R(u)|S(u)|}{-2B(u)}\in(\pi/2,\pi),\qquad
T(u)=\frac{2\sqrt{E_0}\,\alpha(u)}{a|S(u)|}.
\end{gathered}
\tag{3.12}
$$

Here $T(u)$ is the first positive axis-crossing time. The radius
stays positive before $T(u)$ and has a simple zero there, since
$R(u)>0$ and $-2B(u)/|S(u)|>0$. Thus the horizontal Cartesian
velocity at $T(u)$ is nonzero. The function $T$ is continuous on
$(0,\epsilon)$ and tends to infinity as $u\downarrow0$.

Every crossing endpoint used here is off the source. In fact, (2.6)
gives $\dot s=\nu(u)(\eta+ar^2/4)$ with constant nonzero sign, whence

$$
\begin{aligned}
|s(C_u(T(u)))-s(q(u))|
 &\ge\eta|\nu(u)|T(u)
   =\frac{2\eta\alpha(u)}a>\frac{\pi\eta}a.
\end{aligned}
\tag{3.13}
$$

Shrink $\epsilon$ so that $|s(q(u))|<\pi\eta/(2a)$. Then
$|s(C_u(T(u)))|>\pi\eta/(2a)>0$. In Cartesian coordinates the
geodesic and its velocity extend smoothly to this endpoint: in
(3.12) write $x+iy=r\exp(i\theta)$, use
$\theta(t)=\theta(0)+a\nu(u)t/2$, and integrate (2.6) for $s,z$.
All quantities have finite limits at each finite $T(u)$.

Initially all the $C_u$ are normal-flow curves from $b=c_0$ in the
regular tube of (3.6). Their scalar profiles solve the same ordinary
differential equation $y'=-\sqrt{\beta(y)}$, $y(0)=c_0$. Local
uniqueness and (3.8) therefore give both identities

$$
b(C_u(t))=f(t),\qquad
\nabla_{\mathsf g}b(C_u(t))=f'(t)\dot C_u(t)
\tag{3.14}
$$

for sufficiently small positive $t$. For each fixed $u$, both sides
of each identity are real analytic on the connected interval
$(0,T(u))$: $C_u(t)\in\Omega$ there, $b$ and the inverse metric are
analytic there, the geodesic is analytic, and $f$ is analytic on
its whole positive ray. Express the vector identity in symmetric
Cartesian components and apply the one-variable analytic identity
theorem to every component. Equation (3.14) holds for all
$0<t<T(u)$, including every intervening critical time of $b$.
This continues identities along predefined geodesics; it does not
continue the normalized vector field $n$ or the local scalar
$\beta$ through a critical point.

At $t=T(u)$, the endpoint is in $M$. Smoothness of $b$ and the
metric there allow passage to the limit in the vector identity of
(3.14). A smooth rotation-invariant function has $b_x=b_y=0$ on
$x=y=0$. At that axis the metric (2.4) has no horizontal-central
cross term. Hence $\nabla_{\mathsf g}b$ has zero horizontal component
at the endpoint. The horizontal component of $\dot C_u(T(u))$ is
nonzero, so

$$
f'(T(u))=0\quad(0<u<\epsilon).
\tag{3.15}
$$

Fix $u_*\in(0,\epsilon)$. By continuity of $T$, its divergence as
$u\downarrow0$, and the intermediate value theorem, every
$t>T(u_*)$ equals $T(u)$ for some $0<u<u_*$. Thus $f'$ vanishes on
a whole tail interval. Analytic uniqueness on the domain of $f$
forces $f'\equiv0$, contradicting (3.8). Therefore $W$ is not
identically zero. Since $d>0$ and
$\mathrm d_{\rm sp}b\wedge\mathrm d_{\rm sp}\gamma=dW$, (3.1)
follows. Nonvanishing is open and implies rank two. $\square$

[TR]: https://arxiv.org/html/1807.08398v1

## 4. The original joint measure and completed observation fibres

**Theorem 4.1 (absolute continuity and strict completed-sigma separation).**
Under Assumption 1.1, for every original finite $a,\eta,d>0$, the
joint probability law

$$
\nu=(b,\gamma)_*m
\tag{4.1}
$$

is absolutely continuous with respect to two-dimensional Lebesgue
measure. There are nonempty bounded open intervals $I,J$, a Borel
set $U\Subset\Omega$ of positive original $m$-measure, and a
strictly positive smooth function $q$ on $I\times J$, such that

$$
(b,\gamma)_*(\mathbf1_Um)=q(u,v)\,du\,dv
\quad\text{on }I\times J,
\tag{4.2}
$$

with the restricted law supported there. In particular, for every
$u\in I$ there are regular points in $U$ with the same value $b=u$
and different values of $\gamma$. The failure of dependence has a
positive original-measure consequence:

$$
\gamma\notin L^0\!\left(\overline{\sigma(b)}^{,m};\mathbb R\right),
\qquad
\overline{\sigma(b)}^{,m}
 \subsetneq\overline{\sigma(b,\gamma)}^{,m}
\quad\text{modulo }m.
\tag{4.3}
$$

Indeed, for every Borel $F:\mathbb R\to\mathbb R$,
$m\{\gamma=F(b)\}=0$. All statements are unchanged when the original
readout uses any permitted null-repaired $\widetilde b$.

*Proof.* The coefficients of
$\mathrm d_{\rm sp}b\wedge\mathrm d_{\rm sp}\gamma$ in symmetric
Cartesian coordinates are analytic on connected $\Omega$.
Theorem 3.1 makes at least one coefficient nontrivial. The real
analytic zero-set theorem, Mityagin, [*The Zero Set of a Real Analytic
Function*, Proposition 0][M], makes that coefficient's zero set
Lebesgue-null. Thus the rank-deficient set is null for raw Haar
measure and for the original $m=h^2\mu$. The omitted axis is also
null. Hence $(b,\gamma)$ has rank two $m$-almost everywhere.

At any rank-two point the submersion theorem supplies smooth
coordinates $(u,v,y_1,y_2)$ with $u=b$ and $v=\gamma$. Choose an
open coordinate rectangle $I\times J\times Q$ with compact closure
in such a chart, where $Q\subset\mathbb R^2$ is a bounded open
rectangle. Let $U$ be its inverse image. The original $m$ has smooth
strictly positive density $j(u,v,y)$ in this chart, because $h>0$
and the coordinate Jacobian is nonzero. Its restricted pushforward
has density

$$
q(u,v)=\int_Qj(u,v,y)\,dy>0\qquad((u,v)\in I\times J).
\tag{4.4}
$$

Compact containment justifies differentiating under the integral,
so $q$ is smooth, proving (4.2). This gives an interval of equal
readout values, each supporting a nondegenerate interval of energy
values. The conditional energy law for this restricted measure,
given $b=u$, has density $q(u,v)/\int_Jq(u,v')\,dv'$ on $J$.
In particular the consequence is not confined to a single null
level or to two isolated points.

Countably many submersion charts cover the full-rank set. Within
each chart, the inverse image of a planar Lebesgue-null Borel set
has zero $m$-measure by Fubini and the local smooth density.
The rank-deficient complement has zero $m$-measure as already
proved. Thus the entire law (4.1) is absolutely continuous.
A Borel graph $\{(u,F(u)):u\in\mathbb R\}$ is planar-null by Fubini,
giving $m\{\gamma=F(b)\}=0$.

For clarity, completion causes no gap in this conclusion. A finite
real variable measurable for the $m$-completion of $\sigma(b)$ has
a $\sigma(b)$-measurable version: approximate it by simple functions
and replace their completed-measurable level sets by equal-modulo-null
$\sigma(b)$ sets, using their countable union of null exceptions.
The usual real-valued Doob–Dynkin factorization then makes this
version $F(b)$ for a Borel $F$. Such a version of $\gamma$ would
contradict the graph calculation. This proves (4.3). Since
$\widetilde b=b$ $m$-almost everywhere, their generated sigma
algebras agree modulo null sets. Their joint laws with the fixed
smooth-source energy also agree. $\square$

[M]: https://arxiv.org/html/1512.07276v1

## 5. Conditional scope and the separate recovery relation

**Definition 5.1 (mathematical attribution and hypothesis correspondence).**
The source-specific derivative obstruction (3.1), the analytic
synchronization through critical times in (3.14), and the original
joint-measure consequences in Theorem 4.1 are `repo-derived`
conditional deductions from Assumption 1.1. The positive-time source,
full-domain symmetries, local analytic heat images and value tails
are the cited source suppliers, applied to the same original
$\Gamma,H,h,m,g_d$ and deterministic time $d$. They are not statements
about a product replacement of the interacting source. The constants
$r_0,E_0,\epsilon$ and the witnessing chart may depend on the entire
fixed positive triple. Every original finite positive triple remains
in the conditional scope of Theorems 3.1 and 4.1.

The classical geodesic and normal-flow calculations, analytic
identity and zero-set principles, the submersion theorem, Fubini
and Doob–Dynkin are `literature-attested` intermediates inside these
source-specific proofs. They are not separate new general theorems.
The local transnormal relation (3.6) is used only at a regular leaf;
no scalar energy profile is assumed smooth at critical values. The
argument requires neither a critical-free exterior nor derivative
asymptotics or analyticity on the axis. It excludes global energy
dependence despite possible intervening wholly critical levels;
it does not classify individual critical fibres.

**Definition 5.2 (the distinct word-law recovery question).** For the
original passive law let $F_\varnothing=1$,
$F_{yu}=M_{f_y}PF_u$, and $p(u)=\langle Pg_d,F_u\rangle_m$, as in
[W, Definition 1.2]. Let $\mathcal O$ be that source's closed
observable word sector of [W, Definition 2.1]. The separate question
is to determine whether the entire exact original function
$p:\mathcal L^*\to[0,1]$ determines the actual energy multiplication
operator $M_\gamma$ on its appropriate observable domain, and under
which source-bound correspondence it does so. Equations (3.1) and
(4.3) distinguish spatial functions in the original measure. They
do not themselves construct that operator from $p$, locate a
numerical derivative witness, or provide a finite-record procedure.
The coordinates and geodesics in Theorem 3.1 specify no reset,
stationary preparation, selectable outcome, additional readout or
physical control. Full spatial-algebra recovery and mutual recovery
of space, time, boundary and memory require their own corresponding
relations.

## 追加锚（本行以下为增补区）

## 6. Higher energies on the unchanged source

**Definition 6.1 (the source map and its reduced principal metric).**
Retain Assumption 1.1 and the actual regularity, symmetry and decay
suppliers of Definition 2.1 and Theorem 3.1. To distinguish the
cylindrical radius in (2.1) from the recovered resolvent symbol of
[W, §12], write

$$
\begin{gathered}
v=(x^2+y^2)^{1/2},\qquad
\mathcal U=\{v>0\}=\Omega\text{ of (2.1)},\qquad
r=(1+\gamma)^{-1},\\
\Gamma_d(f,g)=d\left(a\sum_{j=1}^3X_jfX_jg
                         +\eta f_wg_w\right),\\
\mathcal C=\Gamma_d(b,\gamma),\qquad
\mathcal D=\Gamma_d(\gamma,\gamma),\qquad
\mathcal F=(b,\gamma).
\end{gathered}
\tag{6.1}
$$

The higher energies $\mathcal C,\mathcal D$ are the quantities
called $C,D$ in the higher-energy factorization question; neither
denotes the endpoint coefficient $C$ of (1.2). They are finite
smooth real functions on $M$, analytic on $\mathcal U$. No global
boundedness, global generator domain or multiplication action on
$\mathcal O$ is assumed for either of them.

For rotation-invariant functions, the symmetric-coordinate fields
are $X_1=\partial_x-(y/2)\partial_s$ and
$X_2=\partial_y+(x/2)\partial_s$. Substitution, with cancellation
of the mixed radial-central terms, gives the exact identity

$$
\frac1d\Gamma_d(f,g)
 =a(f_vg_v+f_zg_z)
       +\left(\eta+\frac{av^2}{4}\right)f_sg_s.
\tag{6.2}
$$

Set

$$
u=v/\sqrt a,\qquad \zeta=z/\sqrt a,\qquad
\lambda=a^2/4>0,\qquad k(u)=\eta+\lambda u^2,
\qquad
\overline{\mathsf g}=du^2+\frac{ds^2}{k(u)}+d\zeta^2.
\tag{6.3}
$$

Thus (6.2) is exactly the cotangent metric of
$\overline{\mathsf g}$. This metric expresses the original
principal energy on invariant functions. It is not the induced
metric on a constant-angle surface, and no quotient diffusion,
replacement heat kernel or new endpoint is introduced. All source
functions below are still the original $b=g_d$ and its energies.
The full source drift and the singular domain are retained through
Assumption 1.1; they are not inferred from (6.3).

The reflection in $z$ makes $b$ and $\gamma$ even in $\zeta$.
Consequently $\partial_\zeta\mathcal F(u,s,0)=0$. Write
$\mathcal F_0=\mathcal F|_{\zeta=0}$. The next lemma locates
rank two on this particular slice, rather than merely somewhere
in the full source.

## 7. Rank two on the original reflection slice

**Lemma 7.1 (a regular two-variable source section).** For every
finite $a,\eta,d>0$ under Assumption 1.1 there is a point with
$v>0,z=0$ at which

$$
\det D_{(v,s)}\bigl(b(v,0,s),\gamma(v,0,s)\bigr)\ne0.
\tag{7.1}
$$

In particular $\mathcal F_0$ is an analytic local diffeomorphism
at some point of the actual reflection slice.

*Proof.* Put $\beta(v,s)=b(v,0,s)$ on
$\Sigma=(0,\infty)\times\mathbb R$ and use the metric

$$
\mathsf g_\Sigma=\frac{dv^2}{a}
       +\frac{ds^2}{\eta+av^2/4},\qquad
E_\Sigma=|\nabla_\Sigma\beta|^2
       =a\beta_v^2+(\eta+av^2/4)\beta_s^2.
\tag{7.2}
$$

By the actual $z$ reflection, $b_z(v,0,s)=0$, so
$\gamma(v,0,s)=dE_\Sigma(v,s)$. Suppose that
$\mathrm d\beta\wedge\mathrm dE_\Sigma$ vanished identically
on $\Sigma$. Positivity (3.2) and decay (2.3) give $v_0>0$ with
$\beta_v(v_0,0)<0$. The central reflection (3.4) gives
$\beta_s(v_0,0)=0$. Write

$$
q_0=(v_0,0),\quad c_0=\beta(q_0),\quad
E_0=a\beta_v(q_0)^2>0.
\tag{7.3}
$$

Analytic submersion coordinates near $q_0$ give
$E_\Sigma=F(\beta)$ for an analytic $F$, positive on a smaller
neighborhood. Exactly the local Hessian calculation (3.7), now
for $\mathsf g_\Sigma$, shows that
$n=-\nabla_\Sigma\beta/\sqrt{E_\Sigma}$ has unit-speed geodesic
integral curves in the regular tube. The small level curve
$\Lambda=\{\beta=c_0\}$ is an analytic graph $v=V(s)$ through
$q_0$, and its normal geodesics all have the same initial scalar
profile, solving $y'=-\sqrt{F(y)}$, $y(0)=c_0$.

The analytic germ $\beta_s|_\Lambda$ is nonzero. Indeed,
$\beta_s$ cannot vanish identically on $\Sigma$: at any fixed
$v>0$, the actual positive function $\beta(v,s)$ tends to zero
as $|s|\to\infty$. If $\beta_s$ vanished on a level-curve
neighborhood, each normal geodesic there would start with
$p_s=-\beta_s/\sqrt{E_0}=0$. The metric in (7.2) is independent
of $s$, so $p_s$ is conserved. On the short regular normal tube
this gives $p_s=-\beta_s/\sqrt{E_\Sigma}=0$. That tube is open
in $\Sigma$, by the local normal-flow diffeomorphism. Analytic
uniqueness on connected $\Sigma$ would make $\beta_s$ vanish
everywhere, a contradiction.

The nonzero one-variable analytic germ on $v=V(s)$ is nonzero
for all sufficiently small $s=\epsilon>0$. Thus, shrinking the
interval of $\epsilon$, the points
$q_\epsilon=(V(\epsilon),\epsilon)$ satisfy

$$
\begin{gathered}
R_\epsilon=V(\epsilon)>0,\qquad
B_\epsilon=\beta_v(q_\epsilon)<0,\qquad
S_\epsilon=\beta_s(q_\epsilon)\ne0,\\
E_\Sigma(q_\epsilon)=E_0,\qquad
q_\epsilon\longrightarrow q_0,\quad S_\epsilon\longrightarrow0.
\end{gathered}
\tag{7.4}
$$

Let $c_\epsilon(t)$ be the geodesic of (7.2) with initial
velocity $n(q_\epsilon)$. Its conserved central momentum and
radial equation are

$$
\nu_\epsilon=-S_\epsilon/\sqrt{E_0},\qquad
\ddot v+\frac{a^2\nu_\epsilon^2}{4}v=0,
\qquad \dot s=\nu_\epsilon(\eta+av^2/4).
\tag{7.5}
$$

These follow directly from the Hamiltonian of (7.2), and are the
same radial-central equations as (2.6). With
$\omega_\epsilon=a|S_\epsilon|/(2\sqrt{E_0})$, their solution
up to the first crossing of $v=0$ is

$$
\begin{gathered}
v(c_\epsilon(t))=R_\epsilon\cos(\omega_\epsilon t)
       -\frac{2B_\epsilon}{|S_\epsilon|}\sin(\omega_\epsilon t),\\
\alpha_\epsilon
 =\pi-\arctan\frac{R_\epsilon|S_\epsilon|}{-2B_\epsilon}
 \in(\pi/2,\pi),\qquad
T_\epsilon=\frac{2\sqrt{E_0}\alpha_\epsilon}
                         {a|S_\epsilon|}.
\end{gathered}
\tag{7.6}
$$

The radius is positive before $T_\epsilon$ and has a simple zero
there. The times $T_\epsilon$ are continuous in $\epsilon>0$
and tend to infinity as $\epsilon\downarrow0$. Moreover

$$
|s(c_\epsilon(T_\epsilon))-\epsilon|
 \ge\eta|\nu_\epsilon|T_\epsilon
 =2\eta\alpha_\epsilon/a>\pi\eta/a.
\tag{7.7}
$$

For sufficiently small $\epsilon$, the crossing therefore has
$|s|>\pi\eta/(2a)$ and is off the original singular source.
The radius and central coordinate have finite limits at each
such finite crossing time.

The reference geodesic from $q_0$ is the outward radial ray.
Define the analytic function

$$
f(t)=\beta(v_0+\sqrt a\,t,0),\qquad
t>-v_0/\sqrt a,\qquad f'(0)=-\sqrt{E_0}<0.
\tag{7.8}
$$

Initially the common normal scalar profile and gradient identity
give

$$
\beta(c_\epsilon(t))=f(t),\qquad
\nabla_\Sigma\beta(c_\epsilon(t))
                    =f'(t)\dot c_\epsilon(t).
\tag{7.9}
$$

For each fixed $\epsilon$, these are identities between analytic
functions on $0<t<T_\epsilon$. The one-variable identity theorem,
applied also to the two coordinate components of the vector
identity, extends them over that whole interval. This is the
analytic synchronization used in (3.14); it continues identities
along fixed geodesics, including critical times, without assuming
that $F$ or the normalized gradient field extends through critical
levels.

At the off-source crossing, actual smooth rotational invariance
gives $\beta_v(0,s)=0$, as a one-sided radial derivative of the
original smooth $b$. The $v$ component of
$\nabla_\Sigma\beta$ therefore tends to zero. Passing to the
limit in the $v$ component of (7.9), and using the simple radial
zero in (7.6), gives $f'(T_\epsilon)=0$. For any fixed small
$\epsilon_*>0$, continuity and divergence of $T_\epsilon$ imply
that its values on $(0,\epsilon_*)$ include every
$t>T_{\epsilon_*}$. Hence $f'$ vanishes on a tail interval.
Analytic uniqueness contradicts (7.8).

Thus $\mathrm d\beta\wedge\mathrm dE_\Sigma$ is nonzero
somewhere. Since $d>0$, this proves (7.1). The proof used only
the original slice, smooth off-source axis limits and the actual
value decay; no global transnormal-foliation theorem or derivative
tail estimate was used. $\square$

## 8. Analytic rigidity of a local metric retraction

**Lemma 8.1 (the quadratic-central metric admits no bending
retraction).** Let $\eta,\lambda>0$,
$k(u)=\eta+\lambda u^2$, and let $V$ be an open rectangle in
$(0,\infty)\times\mathbb R$. Suppose that an analytic map
$\pi=(X,Y)$, defined on a neighborhood of $V\times\{0\}$, obeys

$$
\pi(u,s,0)=(u,s),\qquad \pi_\zeta(u,s,0)=0
\tag{8.1}
$$

and the cotangent isometry equations from
$du^2+ds^2/k(u)+d\zeta^2$ to $dX^2+dY^2/k(X)$:

$$
\begin{aligned}
X_u^2+k(u)X_s^2+X_\zeta^2&=1,\\
X_uY_u+k(u)X_sY_s+X_\zeta Y_\zeta&=0,\\
Y_u^2+k(u)Y_s^2+Y_\zeta^2&=k(X).
\end{aligned}
\tag{8.2}
$$

Then $\pi(u,s,\zeta)=(u,s)$ locally along $V\times\{0\}$.
The equations already imply submersion; no harmonicity, diffusion
drift condition or global fibre hypothesis is part of the lemma.

*Proof.* First write

$$
X=u+\tfrac12\zeta^2p(u,s)+O(\zeta^3),\qquad
Y=s+\tfrac12\zeta^2q(u,s)+O(\zeta^3).
$$

The coefficients of $\zeta^2$ in (8.2) are exactly

$$
p_u=-p^2,\qquad q_u+kp_s=-2pq,\qquad
kq_s-\lambda u p=-q^2.
\tag{8.3}
$$

If $p$ were nonzero at any point, restrict to a smaller rectangle
where $p\ne0$. The first equation gives
$p=1/(u+c(s))$ with analytic $c$. Put
$J(u)=\eta u+\lambda u^3/3$, so $J'=k$. The second equation
then integrates to

$$
q=\frac{c'(s)J(u)+j(s)}{(u+c(s))^2}
\tag{8.4}
$$

for an analytic $j$. Substitute in the third equation and
multiply by $(u+c)^4$. The resulting polynomial identity in $u$
is

$$
\begin{aligned}
0={}&k\left[(c''J+j')(u+c)^2
             -2c'(c'J+j)(u+c)\right]\\
   &-\lambda u(u+c)^3+(c'J+j)^2.
\end{aligned}
\tag{8.5}
$$

An identity on an open $u$ interval is a polynomial identity,
even though the interval need not contain zero or infinity.
Its degree-seven coefficient is $\lambda^2c''/3$, so $c''=0$.
With this relation imposed, the degree-six coefficient is
$-5\lambda^2(c')^2/9$, so $c'=0$. Equation (8.5) reduces to

$$
k j'(u+c)^2-\lambda u(u+c)^3+j^2=0.
\tag{8.6}
$$

Its degree-four coefficient gives $j'=1$, and its degree-three
coefficient then gives $c=0$. The degree-two coefficient is now
$\eta$, contrary to $\eta>0$. This excludes every nonzero point
of $p$. Hence $p=0$. Equations (8.3) give $q_u=0$ and
$kq_s=-q^2$. Varying $u$ on an open interval, where $k$ is
nonconstant, first gives $q_s=0$ and then $q=0$. The entire
quadratic coefficient vanishes.

For completeness, higher analytic orders cannot evade this
quadratic obstruction. If $\pi$ were not the identity as a germ,
let $n>2$ be the least order with a nonzero coefficient function:

$$
X=u+\zeta^n p_n+\cdots,\qquad
Y=s+\zeta^n q_n+\cdots.
\tag{8.7}
$$

For every order $j$ from $n$ through $2n-3$, products of
perturbations in the $u,s$ derivatives have order at least $2n$,
and products of $\zeta$ derivatives have order at least $2n-2$.
Thus its coefficient pair $(p_j,q_j)$ satisfies the homogeneous
linear equations

$$
(p_j)_u=0,\qquad (q_j)_u+k(p_j)_s=0,\qquad
k(q_j)_s-\lambda u p_j=0.
\tag{8.8}
$$

Every solution of these equations is $(0,c_j)$ for a constant
$c_j$. Indeed, the first two equations give
$p_j=p_j(s)$ and $q_j=-p_j'(s)J(u)+j_j(s)$. The third becomes

$$
k(-p_j''J+j_j')-\lambda u p_j=0.
\tag{8.9}
$$

The coefficients of degrees five, two and one, in that order,
give $p_j''=0$, $j_j'=0$ and $p_j=0$. Thus $q_j$ is constant.
In particular $(p_n,q_n)=(0,c)$ with $c\ne0$.

At order $2n-2$ the only nonlinear contribution is
$n^2c^2\zeta^{2n-2}$ from $Y_\zeta^2$ in the last equation
of (8.2). Earlier coefficient pairs are constant translations
in $Y$, so they contribute no $u,s$ derivatives, and only the
pair of order $n$ can contribute at this order through
$\zeta$ derivatives. If $(p_*,q_*)$ is the coefficient pair
of order $2n-2$, it therefore satisfies

$$
(p_*)_u=0,\qquad (q_*)_u+k(p_*)_s=0,\qquad
k(q_*)_s-\lambda u p_*=-n^2c^2/2.
\tag{8.10}
$$

As before, write $q_*=-p_*'J+j_*$. The degree-five, degree-two
and degree-one coefficients force $p_*''=0$, $j_*'=0$ and
$p_*=0$. The left side of the last equation is then zero;
its constant term forces $c=0$, a contradiction. There is no
first nonzero Taylor coefficient. Analyticity implies the
asserted local identity. Both $\lambda>0$ and $\eta>0$ have
been used explicitly. $\square$

## 9. Actual third rank and completed-measure separation

**Theorem 9.1 (a higher original energy separates every positive
parameter source).** Under Assumption 1.1, for every original
finite $a,\eta,d>0$, at least one of

$$
\mathrm d_{\rm sp}b\wedge\mathrm d_{\rm sp}\gamma
                         \wedge\mathrm d_{\rm sp}\mathcal C,
\qquad
\mathrm d_{\rm sp}b\wedge\mathrm d_{\rm sp}\gamma
                         \wedge\mathrm d_{\rm sp}\mathcal D
\tag{9.1}
$$

is nonzero at an actual source point in $\mathcal U$. For at
least one fixed choice $\kappa\in\{\mathcal C,\mathcal D\}$,
depending on the positive triple, the law
$ (b,\gamma,\kappa)_*m$ is absolutely continuous with respect
to three-dimensional Lebesgue measure. In particular

$$
\kappa\notin L^0\!\left(\overline{\sigma(b,\gamma)}^{\,m};
                                      \mathbb R\right),
\qquad
m\{\kappa=H(b,\gamma)\}=0
\quad\text{for every Borel }H:\mathbb R^2\to\mathbb R.
\tag{9.2}
$$

*Proof.* Suppose that both three-forms in (9.1) vanished
identically on $\mathcal U$. Work in the reduced coordinates
of (6.3). Lemma 7.1 supplies a point on $\zeta=0$ where
$\mathcal F_0$ is an analytic local diffeomorphism. Near that
point, $(\mathcal F,\zeta)$ is an analytic coordinate system.
The vanishing three-forms say that the derivatives of
$\mathcal C,\mathcal D$ in the remaining coordinate at fixed
$\mathcal F$ are zero. After restricting to a product coordinate
neighborhood, there are analytic functions $c_*,d_*$ with

$$
\mathcal C=c_*(\mathcal F),\qquad
\mathcal D=d_*(\mathcal F).
\tag{9.3}
$$

This is local differential descent. It assumes no agreement
between disconnected pieces of a distant fibre.

The energy matrix of $\mathcal F$ for
$\overline{\mathsf g}$ is

$$
\left(\langle\mathrm d\mathcal F_i,
                 \mathrm d\mathcal F_j\rangle_{
                        \overline{\mathsf g}^{-1}}\right)_{ij}
 =\frac1d
   \begin{pmatrix}\gamma&\mathcal C\\\mathcal C&\mathcal D\end{pmatrix}.
\tag{9.4}
$$

It is positive definite on a smaller neighborhood because
$\mathcal F$ has rank two there. By (9.3), (9.4) depends only
on the target value $\mathcal F$. It defines a positive target
cometric. On $\zeta=0$, the normal derivatives of both
components of $\mathcal F$ vanish. Thus (9.4) restricted to
that slice is exactly the pushforward under $\mathcal F_0$
of the cometric of $du^2+ds^2/k(u)$.

Shrink so that the image of $\mathcal F$ lies in the inverse
chart of $\mathcal F_0$, and put
$\pi=\mathcal F_0^{-1}\circ\mathcal F=(X,Y)$. The chain rule
for this target cometric gives precisely (8.2): the squared
cotangent norms and cross product of $\mathrm dX,\mathrm dY$ are
$1,k(X),0$. Also $\pi(u,s,0)=(u,s)$ and
$\pi_\zeta(u,s,0)=0$. Lemma 8.1 applies with
$\lambda=a^2/4$ and the original $\eta$. It forces
$\mathcal F(u,s,\zeta)=\mathcal F_0(u,s)$ locally.
In particular $b_z=0$ on an open subset of the actual reduced
source. Analytic uniqueness on connected
$(0,\infty)\times\mathbb R^2$ gives $b_z=0$ everywhere there.
For fixed $v>0,s$, this contradicts the actual positivity of
$b(v,z,s)$ and its decay to zero as $|z|\to\infty$ in (2.3).
Consequently at least one of (9.1) is nonzero somewhere.

Choose the corresponding $\kappa$. Rotation invariance makes

$$
J_\kappa(v,z,s)=\det D_{(v,z,s)}(b,\gamma,\kappa)
\tag{9.5}
$$

a nontrivial analytic function on the connected reduced domain.
Mityagin's Proposition 0 [M] applies: this is a real analytic
function on a connected open subset of $\mathbb R^3$, and it
is not identically zero. Its zero set is Lebesgue-null there.
In original cylindrical coordinates
$d\mu=v\,dv\,d\theta\,dz\,ds$, and the original $h^2$ is
smooth and strictly positive on $\mathcal U$. Fubini transfers
this null set to $m$; the omitted axis is also $m$-null. Thus
$(b,\gamma,\kappa)$ has rank three $m$-almost everywhere.

Countably many submersion charts cover that full-rank set.
Their coordinates can be written $(b,\gamma,\kappa,y)$,
and $m$ has a positive smooth local density in each chart.
Fubini in these coordinates shows that the inverse image of
any three-dimensional Lebesgue-null Borel set is $m$-null.
The rank-deficient complement is already null, proving the
asserted absolute continuity. More locally, a compactly contained
coordinate rectangle $I\times J\times L\times Q$ gives a
positive smooth restricted density
$q(t_1,t_2,t_3)=\int_Q j(t_1,t_2,t_3,y)\,dy$ on
$I\times J\times L$, exactly as in (4.4).

Every Borel graph $\{(t_1,t_2,H(t_1,t_2))\}$ is
three-dimensional Lebesgue-null. Absolute continuity proves the
second assertion of (9.2). The completion and Doob–Dynkin
argument in Theorem 4.1 applies to the real-valued pair
$(b,\gamma)$ just as to $b$: completed measurability would give
a Borel version $H(b,\gamma)$ almost everywhere, contrary to
that graph calculation. This proves (9.2). Arbitrary finite
assignments at $e$ and permitted null repairs of the original
readout do not affect any conclusion. $\square$

## 10. Strict recovered energy enlargement and failure of old heat closure

**Definition 10.1 (the exact-law and packet correspondence).**
For the operator conclusions additionally retain the original
word-law recovery hypotheses of [W, §§1–4, 12–13, 22–23],
including the same-source all-angle limit and compact-domain
suppliers of [W, Definition 22.1 and Lemma 22.2]. Under their
source unitary $U$ the marked data obey

$$
\begin{gathered}
U\Omega=1,\qquad U\mathsf B U^{-1}=M_b|_{\mathcal O},\qquad
U\mathsf R U^{-1}=M_r|_{\mathcal O},\\
\widehat P=e^{-\Lambda},\qquad
U\widehat P U^{-1}=T_d|_{\mathcal O},\qquad
U\Lambda U^{-1}=dK|_{\mathcal O},\\
\mathcal A_{\rm rel}=W^*(\mathsf B,\mathsf R),\qquad
H_{\rm rel}=L^2\!\left(\overline{\sigma(b,\gamma)}^{\,m},m\right)
           =U\overline{\mathcal A_{\rm rel}\Omega}
           \subseteq\mathcal O.
\end{gathered}
\tag{10.1}
$$

Here $\Omega$ is the marked reference vector, not the cylindrical
set called $\Omega$ in (2.1). For a scalar packet of [W,
Definition 22.1], its outer interval avoids both $0$ and

$$
s_d=\|\widehat P^{-1/2}b_o\|^2=\operatorname{tr}b>0.
\tag{10.2}
$$

This is the source trace, distinct from the calibration
$N_d=\|g_d\|_\infty$. The packet functions are
$f_1=\phi(b)b$, $f_2=\phi(b)r$. By [W, Theorem 22.3] the
intrinsically determined bounded operators

$$
\mathsf E_{ij}
 =\overline{-\tfrac12[[\Lambda,\mathsf F_i],\mathsf F_j]},
\qquad e_{ij}=\Gamma_d(f_i,f_j),\qquad
U\mathsf E_{ij}U^{-1}=M_{e_{ij}}|_{\mathcal O}
\tag{10.3}
$$

are actual multipliers on all $\mathcal O$, with
$e_{ij}\in C_c^\infty(M)$. These are reused recovery, reduction
and domain statements, not new conclusions from the rank proof.

**Theorem 10.2 (strict compact-energy information gain).** Under
the source and recovery hypotheses just stated, for every original
finite positive triple there is a scalar packet for which at
least one of $e_{12},e_{22}$ is not measurable for
$\overline{\sigma(b,\gamma)}^{\,m}$. For that packet,

$$
\mathcal A_{\rm rel}
 \subsetneq W^*(\mathsf B,\mathsf R,\mathsf E_{12},\mathsf E_{22}),
\qquad H_{\rm rel}\subsetneq\mathcal O.
\tag{10.4}
$$

All displayed operators act in the same exact-law realization;
the enlargement is a commutative multiplication algebra on that
sector.

*Proof.* Take a rank-three point from Theorem 9.1 for its chosen
$\kappa$. Within its open rank-three set, $\mathrm d b\ne0$,
so $b$ takes an open interval of values. Choose a point there
whose value avoids $0$ and $s_d$, and choose nested packet
intervals around that value as in [W, Definition 22.1]. On a
neighborhood of the point, $\phi(b)=1$. Hence the chain rule
and $r=(1+\gamma)^{-1}$ give

$$
e_{12}=-r^2\mathcal C,\qquad e_{22}=r^4\mathcal D,
\tag{10.5}
$$

and therefore

$$
\begin{aligned}
\mathrm d b\wedge\mathrm d\gamma\wedge\mathrm d e_{12}
   &=-r^2\mathrm d b\wedge\mathrm d\gamma\wedge\mathrm d\mathcal C,\\
\mathrm d b\wedge\mathrm d\gamma\wedge\mathrm d e_{22}
   &=r^4\mathrm d b\wedge\mathrm d\gamma\wedge\mathrm d\mathcal D.
\end{aligned}
\tag{10.6}
$$

All differentials in (10.6) are spatial. Since $r>0$, the
corresponding packet symbol has a rank-three chart of positive
original $m$-measure. The restricted positive-density argument in
Theorem 9.1 excludes $e_{ij}=H(b,\gamma)$ almost everywhere on
that chart for every Borel $H$. The completion argument then
excludes old-factor measurability. Only a local chart is needed
here: the global joint law of a compact packet symbol need not
be absolutely continuous, since the symbol vanishes off its
compact support.

For this separating entry, (10.3) gives
$U\mathsf E_{ij}\Omega=e_{ij}\in\mathcal O$. If
$\mathsf E_{ij}\in\mathcal A_{\rm rel}$, this vector would lie
in $H_{\rm rel}$ by (10.1), contrary to nonmeasurability.
This proves both strict inclusions in (10.4). The operators
commute because they are restrictions of reducing actual
multipliers on the full source. $\square$

**Corollary 10.3 (the old factor is not an autonomous heat
factor).** Let $E_{\rm rel}$ be the conditional-expectation
orthogonal projection from $L^2(m)$ onto $H_{\rm rel}$. Under
the hypotheses of Theorem 10.2,

$$
E_{\rm rel}T_d\ne T_dE_{\rm rel}.
\tag{10.7}
$$

Equivalently, the corresponding projection in the marked space
does not commute with $\widehat P$. Thus the old factor does
not reduce the original full heat semigroup or its generator.

*Proof.* Suppose instead that the projection commuted with
$T_d=e^{-dK}$. The injective spectral calculus for
$x\mapsto e^{-dx}$ on $[0,\infty)$ makes it commute with every
spectral projection of $K$. In particular $H_{\rm rel}$ would
reduce $K$: its domain intersection would be preserved by $K$.
For the packet in Theorem 10.2, each $f_i$ and $f_if_j$ is
bounded, old-factor measurable and in the actual $D(K)$.
Indeed they are compact smooth on $M$ by [W, Lemma 22.2];
their $h$-multiples are in $\mathcal D_0\subset D(H)$.
Therefore $Kf_i$ and $K(f_if_j)$ would belong to $H_{\rm rel}$.
Multiplication by the bounded old-factor functions $f_i$
preserves that subspace. The actual product identity on $M$
then gives, as an $L^2(m)$ identity,

$$
e_{ij}=\frac d2\left(f_iKf_j+f_jKf_i-K(f_if_j)\right)
       \in H_{\rm rel}.
\tag{10.8}
$$

This contradicts the separating entry in Theorem 10.2. The
generator and compact domains here are the full original ones;
no replacement Friedrichs operator or factor generator was used.
Finally $\mathcal O$ reduces $T_d$ by [W, Theorem 3.2] and
$H_{\rm rel}\subseteq\mathcal O$. The full projection is zero
on $\mathcal O^\perp$, so its commutation on the full source
is equivalent to commutation on $\mathcal O$, and then under
$U$ to the marked-space statement. $\square$

**Proposition 10.4 (lawful finite products on the original
observable sector).** The additional operators in Theorem 10.2
are determined from the same entire exact word law through the
marked tuple and (10.3). They require no extra observer input.
For any finite ordered list of packet entries $\iota_j$ and
numbers $\tau_j\ge0$,

$$
U\left(\mathsf E_{\iota_1}\widehat P^{\tau_1}\cdots
          \mathsf E_{\iota_n}\widehat P^{\tau_n}\right)U^{-1}
 =\left(M_{e_{\iota_1}}T_{d\tau_1}\cdots
          M_{e_{\iota_n}}T_{d\tau_n}\right)|_{\mathcal O}.
\tag{10.9}
$$

The same composition is valid with any finite set of the
already-recovered bounded multipliers and transports of [W,
§§22–23], in the written order. Their matrix coefficients,
including those with original word vectors, are consequently
determined as exact mathematical quantities.

*Proof.* Full-source reduction of every $M_{e_{ij}}$ is already
part of [W, Theorem 22.3]; full heat reduction is [W, Theorem
3.2]. Thus every intermediate vector in (10.9) stays in
$\mathcal O$. All factors are bounded, and conjugating each
one by $U$ proves the ordered product. The same argument uses
the actual transport correspondence of [W, Theorem 23.1] when
transports are included. No commutation with heat or between
distinct transport groups is asserted. Compact multiplier
domains retain the original endpoint: [W, Lemma 22.2] gives
$he_{ij}u\in D(\overline S)$ and
$A(he_{ij}u)=C(he_{ij}u)=0$ for $u\in D(K)$. The transport
factors retain the full domain, form domain and source trace
as specified in [W, (22.12)]. These are the existing domain
suppliers; neither the composition nor strictness proof changes
them. $\square$

## 11. Attribution, access and the remaining recovery boundaries

**Definition 11.1 (the precise conditional increment).** Lemma
7.1 strengthens the location of the source rank-two result to
the actual $z=0$ slice. Lemma 8.1 proves the needed local
analytic rigidity directly from the exact quadratic-central
metric. Their composition in Theorem 9.1 excludes simultaneous
local descent of both higher energies everywhere on the source,
and proves an actual original-measure distinction. Theorem 10.2
consumes that distinction through already-recovered compact
energy multipliers. Corollary 10.3 settles the noncommutation
of the old conditional-expectation factor with the full original
heat step, under the same stated source and recovery suppliers.

These are `repo-derived` ordinary mathematical deductions
conditional on the published source theory, not fresh
Lean/kernel-verified results. The positivity, analyticity,
symmetries, off-source smoothness and value decay are the
suppliers of §§1–3. The oscillator and critical-time
synchronization mechanism are those of Theorem 3.1, restricted
and justified on the actual slice in Lemma 7.1. The analytic
zero-set, submersion, Fubini and completion intermediates are
the ones used in Theorem 4.1. In particular [M, Proposition 0]
has exactly the connected-open-domain and nontrivial-analytic
function hypotheses checked in (9.5). The compact localization,
signed energy recovery, full-source reduction and finite ordered
multiplication are supplied by [W, §§22–23]. None is recounted
as a new recovery construction.

The global transnormal theorem [TR, Theorem 1.3] assumes a
connected compact analytic Finsler manifold, connected levels
and only the two endpoint singular values. Those global
hypotheses are not supplied here. Lemma 7.1 uses only the
proved local normal identity and analytic continuation along
fixed curves. Lemma 8.1 uses the explicit cotangent equations,
not a harmonic or biharmonic submersion classification. No
worldwide novelty or exhaustive literature-search claim is made.

**Definition 11.2 (what the separation does and does not
recover).** The result is existential and disjunctive: for each
finite positive triple, some $\mathcal C$ or $\mathcal D$ and
some compact packet separate the old factor. It supplies neither
a numerical source point, a predetermined separating entry,
a uniform quantitative bound nor an effective packet-selection
rate. Its parameter scope is every $a,\eta,d>0$, hence every
$a^2d/\eta>0$; no limit substitutes for a finite source member.

The new distinctions are generated by energy and generator
operations on recovered relations. They do not add primitive
emission symbols or identify $b,\gamma$ with the two atomic
syntax generators $\alpha,\beta$ in the separate FIB theory.
The finite triangle, holonomy and radical results retain their
own objects, operations, domains and source hypotheses; no
correspondence into this singular diffusion is established by
shared terminology or a count of ranks. Nor does third rank
identify all invariant functions, a full positive module on
$\mathcal O$, or a globally injective spatial coordinate map.

Strict enlargement by these compact energies does not prove
strict enlargement by a specified transported
$q_\beta=r\circ\Theta_\beta$. The particular heat image
$T_dr$ is already the recovered vector
$U\widehat P\mathsf R\Omega$. Its old-factor membership,
reduction of its multiplication operator to $\mathcal O$,
intrinsic recovery of that multiplication and its word products
are separate questions not settled here. Noncommutation in
(10.7) does not select $r$ as a witnessing vector.

The original $e$-start, first passive read at $2d$, later gaps
$d$, labels $0,1,3,B$ and conditionally fresh noise on one
undisturbed path remain those of (1.6). The coordinates,
geodesics, local section and source density in these proofs
are representations, not freely supplied observation inputs.
Exact-law multiplication and the matrix coefficients in (10.9)
are not inserted readouts acquired on a realized path or native
physical controls. No reset, new instrument, reference,
physical clock or source is introduced. Finite noisy/passive
acquisition, control implementation and resource bounds remain
unproved. Economical mutual recovery of space, time or lawful
continuation, boundary and memory remains the full programme;
the strict relational increment here does not complete it.

## 追加锚（本行以下为增补区）

## 12. Countable compact energy relations and actual regular frames

**Definition 12.1 (the relation family and the symmetry quotient).**
Retain Assumption 1.1 and all the exact-word, all-angle source-limit
and compact-domain hypotheses of Definition 10.1. In particular the
source trace is $s_d$ in (10.2), not $N_d$. Choose the countable
rational nested scalar packets of [W, Definition 22.1, (23.4)], with
fixed smooth cutoff recipes, retaining those whose outer closures
avoid $0,s_d$. Their inner intervals $I_{0,n}$ cover
$(0,\infty)\setminus\{s_d\}$. For each packet use its two already
recovered compact seeds $f_{n,1}=\phi_n(b)b$ and
$f_{n,2}=\phi_n(b)r$. Let $\mathcal T$ consist of all finite binary
expressions with these seeds as leaves and $\Gamma_d$ as the binary
operation. Enumerate this countable family as $(c_n)_{n\ge1}$,
allowing repetitions. Set

$$
\begin{gathered}
\Sigma_\infty=\overline{\sigma(b,r,c_1,c_2,\ldots)}^{\,m},\qquad
\mathcal A_\infty=W^*(\mathsf B,\mathsf R,\mathsf C_{c_n}:n\ge1),\\
\mathcal N=(0,\infty)_u\times\mathbb R_s\times\mathbb R_\zeta,
\qquad \pi=(u,|s|,|\zeta|),\qquad \nu_\pi=\pi_*m.
\end{gathered}
\tag{12.1}
$$

Here $u=v/\sqrt a$, $\zeta=z/\sqrt a$ are exactly (6.3).
Extend $\pi$ by $(0,0,0)$ on the null axis $v=0$.
The group $\mathcal S$ is generated by the actual horizontal
rotations, $J_z$ and the full-source joint reflection $J_s$ of
(3.3). On $v>0$, the fibres of $\pi$ are precisely its orbits:
rotations remove the angle, and the two reflections independently
reverse $s,\zeta$ after that reduction. A pure $s$ reflection of
the full source is not being introduced. The operators
$\mathsf C_c$ in (12.1) are defined by the following theorem.

**Theorem 12.2 (recursive compact recovery and a conull recovered
frame set).** Every $c\in\mathcal T$ is a real
$\mathcal S$-invariant member of $C_c^\infty(M)$, and its actual
multiplier reduces $\mathcal O$. Its restriction is determined by
the exact marked tuple; recursively it is

$$
\mathsf C_{\Gamma_d(f,g)}
 =\overline{-\tfrac12[[\Lambda,\mathsf C_f],\mathsf C_g]},\qquad
U\mathsf C_cU^{-1}=M_c|_{\mathcal O}.
\tag{12.2}
$$

The closure in (12.2) is the unique bounded extension from the
entire $D(\Lambda)$. For each packet $n$ and $ij\in\{12,22\}$,
form

$$
\begin{gathered}
F^{n,ij}=(f_{n,1},f_{n,2},\Gamma_d(f_{n,i},f_{n,j})),\\
G^{n,ij}_{\alpha\beta}
   =\Gamma_d(F^{n,ij}_\alpha,F^{n,ij}_\beta),\qquad
E=\bigcup_{n,ij}\{b\in I_{0,n},\ \det G^{n,ij}>0\}.
\end{gathered}
\tag{12.3}
$$

The set $E$ is invariant, Borel, measurable for the uncompleted
relation sigma algebra and conull for the original $m$. It lies
off the axis. Every point in $E$ has one of these analytic
three-coordinate frames on a packet plateau. In particular $E$
can also be regarded as an invariant Borel subset of $\mathcal N$.

*Proof.* The compact seeds and their full-source reduction are
[W, Lemma 22.2 and Theorem 22.3]. Suppose $f,g$ are compact
smooth real symbols already recovered with reducing multipliers.
Their energy is again compact smooth and real. The same lemma
makes both multipliers preserve the entire complex $D(K)$.
The full-domain product identity [W, (22.13)] gives

$$
[[dK,M_f],M_g]=-2M_{\Gamma_d(f,g)}\quad\text{on }D(K).
\tag{12.4}
$$

The right side is bounded. The projection onto $\mathcal O$
commutes with the left side on this domain, hence with its bounded
extension on full $L^2(m)$. Restricting and conjugating by $U$
proves (12.2) and the induction. Each symbol retains the compact
multiplier-domain conclusion of [W, (22.3)], including vanishing
of both raw endpoint coefficients after multiplication. This
argument assumes no global $r,\gamma\in D(K)$, no diffusion core
of punctured tests, and no arbitrary vector multiplication.
The source symmetries preserve $\Gamma_d$ and the seeds, so they
preserve every tree.

All entries of every $G$ in (12.3) are tree symbols. Thus $E$ is
given by countably many scalar relation inequalities. At an axis
point off $e$, rotational invariance of a smooth function makes
its $x,y$ derivatives zero in symmetric coordinates. Three such
differentials have rank at most two, so their positive-symbol
Gram determinant vanishes. Assign zero to all the Gram entries
at $e$; this null convention makes $E$ disjoint from the axis.

By Theorem 9.1 and its analytic zero-set proof, one fixed
$\kappa\in\{\mathcal C,\mathcal D\}$ has
$\operatorname{rank}(b,\gamma,\kappa)=3$ almost everywhere.
Also $b-s_d$ is nontrivial analytic on connected $\mathcal N$:
positivity and decay (2.3) exclude constancy. The same analytic
zero-set argument, with the original positive cylindrical
density, makes $\{b=s_d\}$ null. Since $b>0$, almost every
remaining point admits a packet plateau. There (10.5) gives
$f_{n,1}=b$, $f_{n,2}=r$, and the third component is
$-r^2\mathcal C$ or $r^4\mathcal D$. Together with
$\mathrm dr=-r^2\mathrm d\gamma$, these identities transfer
the stated rank three to one frame in (12.3). The principal
cometric is positive definite, so its Gram determinant is
positive. This proves conullness. On that plateau the seeds and
all trees using only those seeds are analytic, although the
cutoffs need not be analytic away from their plateaus. $\square$

## 13. Global branch separation for the actual reduced metric

**Theorem 13.1 (equal recursive relations identify exactly the
common-symmetry orbit on $E$).** If two actual source points in
$E$ have the same $b,r$ and every $c_n$ value, they belong to the
same $\mathcal S$-orbit. The converse holds everywhere off the
axis. No choice of a local source branch is an input.

*Proof.* Work in the reduced source $\mathcal N$. Choose a
frame $F$ from (12.3) at the first point $p$. Equality of $b$
puts the second point $p'$ on the same packet plateau. Equality
of all tree values gives the same positive Gram matrix $G$ at
both points. Thus $F$ is an analytic local coordinate map at
both, with the same central coordinate value $F(p)=F(p')$.

In either $F$-chart, write $y=F$ and, for any tree $H$ using
only this packet's seeds, use the ordinary chain rule to obtain

$$
\partial_{y_i}H
 =\sum_j(G^{-1})_{ij}\Gamma_d(F_j,H).
\tag{13.1}
$$

Indeed $\Gamma_d(F_j,H)=\sum_kG_{jk}\partial_{y_k}H$.
Consider rational expressions in these packet-tree functions
whose denominators are powers of $\det G$. Formula (13.1),
the product rule and the reciprocal rule show that this class
is closed under every $\partial_{y_i}$. In particular every
coordinate derivative of each $G_{\alpha\beta}$ is an expression
in finitely many tree values and $(\det G)^{-1}$. Induction on
derivative order proves equality of all those derivatives at
$p,p'$. All the functions used here are analytic on the two
common plateaus. Their cometric Taylor series therefore agree
on a common small $y$-neighborhood. The two inverse $F$-charts
define an analytic local isometry $\Psi$, taking $p$ to $p'$
and preserving $b=F_1$, for

$$
\mathsf g_d=\overline{\mathsf g}/d,
\qquad
\overline{\mathsf g}=du^2+k(u)^{-1}ds^2+d\zeta^2,
\qquad k(u)=\eta+\lambda u^2,\quad\lambda=a^2/4.
\tag{13.2}
$$

The fixed positive scale $d$ means this is also an isometry of
$\overline{\mathsf g}$. The inverse Gram in (13.1) is only a
local proof of germ equality at regular points, not a globally
bounded operator or an extra observation.

We now classify this particular metric germ. For the surface
$du^2+f(u)^2ds^2$, $f=k^{-1/2}$, the curvature calculation
$\mathcal K=-f''/f$ gives

$$
\mathcal K(u)=\frac{\lambda(\eta-2\lambda u^2)}{k(u)^2},
\qquad
\mathcal K'(u)=
 -\frac{4\lambda^2u(2\eta-\lambda u^2)}{k(u)^3}.
\tag{13.3}
$$

For completeness, the surface Christoffel symbols are
$\Gamma^u_{ss}=-ff'$ and
$\Gamma^s_{us}=\Gamma^s_{su}=f'/f$; they give
$R_{usus}=-ff''$. The product with the flat $\zeta$ line
therefore has Ricci eigenvalues $\mathcal K,\mathcal K,0$.
Thus $\mathcal K$ is half its scalar curvature and is preserved
by every local isometry.
On an open set where $\mathcal K\ne0$, its unique Ricci-kernel
line is the $\zeta$ direction. An isometry preserves that line
and its orthogonal complement. Writing its coordinates as
$(U,S,Z)$ consequently gives $U_\zeta=S_\zeta=0$ and
$Z_u=Z_s=0$. The $d\zeta^2$ coefficient then gives
$Z=\epsilon_z\zeta+c_z$, $\epsilon_z\in\{-1,1\}$.

Shrink to a nonempty open subneighborhood on which also
$\mathcal K'(U)\ne0$. Such a subneighborhood exists: the
exceptional levels in (13.3) are finitely many hypersurfaces,
and a local diffeomorphism cannot map an open set into their
union. Curvature preservation gives $\mathcal K(U)=\mathcal K(u)$,
so differentiation in $s$ yields $U_s=0$. The base Jacobian
is nonzero, hence $U_uS_s\ne0$. The $du\,ds$ coefficient in
the metric identity forces $S_u=0$, and the $du^2$ coefficient
forces $U_u^2=1$. Thus locally
$U=\epsilon_u u+c_u$ and

$$
\frac{k(\epsilon_u u+c_u)}{k(u)}=S_s^2=A^2>0.
\tag{13.4}
$$

The left side depends only on $u$ and the right only on $s$,
so both are constant on a smaller product neighborhood.
Comparison of the quadratic and linear coefficients gives
$A^2=1$ and $c_u=0$. Since $u,U>0$, $\epsilon_u=1$.
Consequently $S=\epsilon_s s+c_s$ there. Analytic uniqueness
extends this affine formula for $\Psi$ to its connected original
chart domain, including any omitted curvature levels. In
particular $p'=T(p)$ for the globally defined analytic map

$$
T(u,s,\zeta)=(u,\epsilon_s s+c_s,\epsilon_z\zeta+c_z).
\tag{13.5}
$$

The local identity $b\circ T=b$ extends to all connected
$\mathcal N$ by analyticity. The actual evenness (3.4) gives
$b\circ E_0=b$ for
$E_0(u,s,\zeta)=(u,\epsilon_s s,\epsilon_z\zeta)$.
Since $T\circ E_0$ is translation by $(c_s,c_z)$, $b$ is
invariant under that translation. If this vector were nonzero,
its integer iterates at fixed $u>0$ would escape in the original
proper gauge (2.3). Decay would force their common $b$-value
to zero, contradicting strict pointwise positivity (3.2).
Thus $c_s=c_z=0$. This proves $\pi(p)=\pi(p')$, which is
exactly the actual orbit relation of Definition 12.1. Conversely
the source symmetries preserve all the trees by Theorem 12.2.
No global extension theorem for arbitrary isometries, compactness
of the source, or connectedness of remote observation fibres
has been assumed. $\square$

## 14. The full measured common-symmetry observable quotient

**Theorem 14.1 (the actual measured quotient and its lawful heat).**
Under the hypotheses of Definition 12.1, for every original finite
$a,\eta,d>0$,

$$
\begin{gathered}
\Sigma_\infty=\overline{\sigma(\pi)}^{\,m},\qquad
\mathcal O=L^2(\overline{\sigma(\pi)}^{\,m},m)
             =L^2(m)^{\mathcal S},\\
U\mathcal A_\infty U^{-1}
 =\{M_f|_{\mathcal O}:f\in
              L^\infty(\overline{\sigma(\pi)}^{\,m},m)\}.
\end{gathered}
\tag{14.1}
$$

The exact-law recovered object is this measured multiplication
algebra with reference $1$, up to pointed measured isomorphism.
Its source representation is $(\pi,\nu_\pi)$; the displayed
coordinates do not supply physical scale calibration. The
pullback $V:L^2(\nu_\pi)\to\mathcal O$, $Vf=f\circ\pi$,
is unitary. Hence $V^{-1}T_{d\tau}V$, $\tau\ge0$, is a
conservative self-adjoint Markov semigroup on this quotient.
Its sample-step generator is $V^{-1}(dK|_{\mathcal O})V$;
its form is $d\mathscr E[Vf,Vg]$ on
$V^{-1}(\mathscr V\cap\mathcal O)$, and its source trace is
$\operatorname{tr}\circ V$ on that domain.

*Proof.* Represent the sign quotient of $E\subset\mathcal N$
by its Borel section
$E_+=E\cap\{s\ge0,\zeta\ge0\}$. The countable value map

$$
J:E_+\longrightarrow\mathbb R^{\mathbb N},\qquad
J=(b,r,c_1,c_2,\ldots)
\tag{14.2}
$$

is Borel and injective by Theorem 13.1. The domain is standard
Borel and the target is Polish. Lusin–Souslin [LS] makes its
actual image Borel and the inverse on that image Borel.
Consequently $\pi$ on $E$ is a Borel function of $J$: apply
that inverse and retain the section coordinates. The set $E$
itself is relation-measurable and conull by Theorem 12.2, so
this yields the completed sigma-algebra inclusion on all of
the original probability space. The reverse inclusion follows
because every relation is invariant, hence is a Borel function
of $(u,|s|,|\zeta|)$ off the null axis. The axis is itself
the null fibre $\pi^{-1}\{(0,0,0)\}$. This proves the first
equality in (14.1), including completions. Only the image of
actual points is inverted; no arbitrary compatible thread is
declared realizable.

The countable joint multiplier calculus, as in [W, Theorem
13.1], now gives every bounded $\Sigma_\infty$-measurable
actual multiplier, reducing $\mathcal O$. Simple functions and
bounded monotone limits suffice. Its restriction is faithful:
if it kills $1\in\mathcal O$, its symbol is zero almost
everywhere on the full source. The closure of the generated
algebra applied to $1$ is therefore
$L^2(\Sigma_\infty,m)\subseteq\mathcal O$.

For the other inclusion, every original word function is fixed
by $\mathcal S$: its recursion starts with $1$, and all the
original emission multipliers and the full original heat
commute with these symmetries. Thus $\mathcal O\subseteq
L^2(m)^{\mathcal S}$. Cylindrical Fubini with density
$h^2v\,dv\,d\theta\,dz\,ds$ identifies the latter space
with $L^2(\overline{\sigma(\pi)}^{\,m},m)$: averaging over
rotations removes the angle, and invariance under the two
actual reflections makes the remaining function even in $s,z$.
The density is invariant under all these actions. This proves
both Hilbert inclusions and the remaining algebra assertion.
In particular $\Omega$ is cyclic and separating for
$\mathcal A_\infty$ on the entire recovered space.

The full original heat commutes with every symmetry and is
Markov and conservative. The proved invariant sector therefore
reduces it; pullback by $V$ preserves positivity and constants.
Spectral calculus gives the asserted quotient semigroup and
exact generator domain $V^{-1}(D(K)\cap\mathcal O)$.
Its form domain is
$V^{-1}(\mathscr V\cap\mathcal O)$, and its trace is
$\operatorname{tr}\circ V$ there. With an independently
calibrated numerical $d$, dividing the generator and form by
$d$ gives physical-time units. These are [W, Theorems
3.2 and 4.1] on the now identified space, not new boundary
conditions at a coordinate face. $\square$

**Definition 14.2 (attribution and the measured recovery boundary).**
The source-specific composition in §§12–14 is `repo-derived`:
recursive energy equality determines an analytic metric germ;
the explicit metric and the actual positive decaying $b$ remove
all branch translations; actual-image measurability then gives
(14.1). The compact-domain and energy mechanism is [W, §§22–23],
and the conull rank-three supplier is Theorem 9.1, not a new
rank calculation. Inverse-energy differentiation and its chain
rule are prior art [HIN, Theorem 3.4, (3.16), Remark 3.5].
That paper assumes a regular strongly local form, an energy-
dominant measure, finite index and its full-index coordinate
family; its coordinates need not be injective. Its theorem is
not used to supply global separation or singular-source domain
hypotheses here. The proof uses ordinary analytic coordinate
calculus on the paid principal metric. Lusin–Souslin is used
only after injectivity on the actual Borel section is proved.
No general energy-coordinate or literature-priority claim is made.

The quotient is modulo the original $m$; it retains the original
heat, full endpoint and source trace, but does not recover the
angle or the removed signs. It is the common invariant sector,
not all $L^2(m)$ or the entire rotation-invariant sector. The
actual path obstruction of [W, Theorem 6.2] remains. No pointwise
inverse on the exceptional set or at $e$, explicit coordinate-face
boundary classification, finite separating tree depth, effective
inverse, convergence modulus, packet-selection rate or uniform
parameter bound is supplied. The coordinates and inverse Gram
appear only in the proof, not as sensor ports.

Exact-law measured recovery is distinct from reading relation
values on the one passive noisy path. The existing finite-menu
acquisition and charged capacity/cofinal-schedule stopping
theorems [FEA, Theorems 4.2, 6.1 and 6.3] retain their scope;
their extension to this separating recursive family requires
an actual-menu, error, source and resource correspondence.
Nor does (14.1) decide old-factor membership of $T_dr$, select
$r$ as the witness in (10.7), or settle a specified transported
$q_\beta$. It supplies the multiplication-algebra premise for
the actual heat-image consumer of [W, §24]. The original source,
reference, $e$-start, first read $2d$, later gaps $d$, labels and
fresh conditional noise are unchanged. Full mutual recovery
of space, continuation, boundary and memory remains a further
problem.

[HIN]: https://arxiv.org/html/1212.6166v1
[LS]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Constructions/Polish/Basic.lean
[FEA]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_FINITE_ENERGY_ACQUISITION.md

## 追加锚（本行以下为增补区）
