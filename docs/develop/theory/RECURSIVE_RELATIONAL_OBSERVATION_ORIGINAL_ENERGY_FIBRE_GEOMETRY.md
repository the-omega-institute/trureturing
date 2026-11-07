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
