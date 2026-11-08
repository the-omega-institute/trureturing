# Certified local jets of the original full source

## 1. Source, domains and access

**Assumption 1.1 (the unchanged original source).** Retain the analytic
suppliers of [E, §§109–112], [S, §§115–117, 120, 122, 133],
[R, §§11–12] and [W, Assumption 1.1]. These are conditional ordinary
mathematics, not premises newly verified by a proof assistant. The
reference member is exactly $a=\eta=d=1$. In particular, put

$$
\begin{gathered}
G=H^1\times\mathbb R,\quad e=(0,0,0,0),\qquad
pp'=(x+x',y+y',z+z',w+w'+xy'),\\
d\mu=dx\,dy\,dz\,dw,\quad
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,
\quad X_3=\partial_z,\quad L=-\sum_{j=1}^3X_j^2,\\
L\Gamma=\delta_e,\quad
S_{\min}=(L-\partial_w^2-16\Gamma)
 |_{C_c^\infty(G\setminus\{e\};\mathbb C)}.
\end{gathered}
\tag{1.1}
$$

The potential is the original unit-source Green field with raw Haar
normalization. With the original maximal-domain coefficients $A,C$,
retain

$$
\begin{gathered}
C(w_*)=1,\quad h=w_*/\|w_*\|_2,\quad
c_h=C(h)>0,\quad\rho=A(h)/C(h),\\
D(H)=\{u\in D(S_{\min}^*):A(u)=\rho C(u)\}
     =D(\overline S_{\min})\dotplus\mathbb Ch,\quad
Hu=S_{\min}^*u,\\
H\ge0,\quad \ker H=\mathbb Ch,\quad
D(F)=\{u\in D(S_{\min}^*):C(u)=0\},\quad F\ne H,\\
m=h^2\mu,\quad m(G)=1,\quad m(\{e\})=0,\quad
J_hv=hv,\quad K=J_h^{-1}HJ_h,\quad T_t=e^{-tK}.
\end{gathered}
\tag{1.2}
$$

The boundary condition is on the entire complex maximal domain. The
full form domain is $\mathscr V=\mathscr V_0\dotplus\mathbb C1$ with
the original continuous trace, and punctured tests close only to
$\mathscr V_0$. The representative $h$ is real, smooth and strictly
positive off $e$. No value $h(e)$ is used. The original conservative
continuous-path process starts at $e$ and has deterministic-time
density $g_t$ with respect to $m$, where

$$
\operatorname{tr}(T_tf)=\langle g_t,f\rangle_m,
\qquad g_{t+s}=T_sg_t\quad(t>0,s\ge0).
\tag{1.3}
$$

Pairings are antilinear in the first slot. All norms without an
indicated measure are raw $L^2(\mu)$ norms.

**Definition 1.2 (numerical names and output).** A global raw name
of $u$ returns, for each positive rational $\delta$, a finite rational
complex box-step function $U$ with $\|U-u\|_2\le\delta$. All boxes
are bounded and in the original coordinates. Scalar names return
rational enclosing intervals of arbitrarily small width. The
parameter names here are the exact constants $1$; the global names
and full-resolvent action constructed in [R, §§11–12] are used with
their stated hypotheses. They are mathematical model access.

Write

$$
r^2=x^2+y^2,\qquad s=w-xy/2,\qquad \Omega=\{r>0\}.
\tag{1.4}
$$

The output sought is a rational interval of width at most a requested
rational $\varepsilon_0>0$, containing $D^\alpha h(p)$ or
$D^\alpha g_t(p)$, for rational $p\in\Omega$, $t=1,2$ and
$|\alpha|\le3$. Derivatives are initially in raw coordinates. The
restriction to the original radial slice is specified in §6.

**Definition 1.3 (the unchanged observation).** Keep $b=g_1$,
$\beta=g_2$, $P=T_1$ and

$$
\begin{gathered}
\gamma=\sum_{j=1}^3(X_jb)^2+(\partial_wb)^2,\qquad
c=\frac1{4(1+\|g_1\|_{L^\infty(m)})},\\
f_3=cb,\quad f_B=\frac14,\quad
f_0=f_1=(3/4-f_3)/2,\quad \mathcal L=\{0,1,3,B\},\\
\mathsf X_j=Z_{j+2}\quad(j\ge0).
\end{gathered}
\tag{1.5}
$$

The emissions admit exactly their original null repairs, with fresh
conditional noise on one undisturbed path. The first read remains
at time $2$ and every gap remains $1$. The exact entire word law has
the marked Hilbert tuple and the actual recovered objects of [W]:
$\widehat P$, $B=N_3/c$, $\Omega_{\rm cyc}$ and
$\mathsf R=M_{1/(1+\gamma)}$ on the visible sector $\mathcal O$.
Here $\Omega_{\rm cyc}$ is the marked constant vector, distinct from
the open coordinate set $\Omega$. The generated factor is
$\mathcal A_{\rm rel}=W^*(B,\mathsf R)$, whose cyclic space
corresponds to

$$
\mathcal H_{\rm rel}
 =L^2(\overline{\sigma(b,\gamma)}^{\,m},m)\subset\mathcal O.
\tag{1.6}
$$

No equality with $\mathcal O$, full positive cone, raw-coordinate
recovery or autonomous heat factor is assumed. The function $\gamma$
is smooth off $e$, without an assumed global bound or membership in
$D(K)$. None of the model names in Definition 1.2 is supplied by a
finite passive record merely by using this notation.

[E]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md
[S]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md
[R]: RECURSIVE_RELATIONAL_OBSERVATION_DIFFUSION_PHASE_COVER_RIGIDITY.md
[W]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_WORD_GEOMETRY_RECOVERY.md
[FQ]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_FINITE_ENERGY_ACQUISITION.md
[FG]: RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_ENERGY_FIBRE_GEOMETRY.md

## 2. Constructed coefficient bounds on raw rational boxes

**Definition 2.1 (finite coefficient data).** Let $Q\Subset
Q^+\Subset\Omega$ be nonempty open rational boxes, with compact
closures understood in every containment. For each raw coordinate
let $M_x,M_y,M_z,M_w$ be a rational upper bound for its absolute
value on $Q^+$. Choose rational $0<r_0\le1$ such that

$$
x^2+y^2\ge r_0^2\quad\hbox{on }\overline{Q^+},
\qquad L_0=4(1+M_x+M_y+M_z).
\tag{2.1}
$$

This is a finite calculation: the minimum of $x^2+y^2$ on a box
is the sum of the two one-dimensional square minima. It is positive
because the closed box is in $\Omega$. A smaller positive dyadic
$r_0$ can be found by rational comparison. For integers $n\ge0$ put

$$
\begin{aligned}
B_n&=n!2^n(n+2)!\,r_0^{-3-2n}L_0^n,\\
S_N&=\sum_{k=0}^N\binom Nk k!,\qquad
G_n=8B_nS_{n+1},\\
\mathcal T_n(T)&=8B_n2^{-T}
 \sum_{k=0}^{n+1}\binom{n+1}{k}k!
                   \sum_{j=0}^k\frac{T^j}{j!}\quad(T\in\mathbb N).
\end{aligned}
\tag{2.2}
$$

All these numbers are rational. The constants are deliberately
upper bounds; no optimization is required.

**Theorem 2.2 (effective differentiated original Green integral).**
For every multiindex $\alpha$ of length $n$, the actual original
coefficient satisfies

$$
\sup_{Q^+}|D^\alpha\Gamma|\le G_n.
\tag{2.3}
$$

Its spatially differentiated real-contour integral has absolute
tail at most $\mathcal T_n(T)$ outside $[-T,T]$. In particular,
each rational-point derivative of every fixed finite order has
arbitrarily narrow rational enclosures after finite computation,
uniformly using the box data (2.1). Derivatives through order six
give all the potential bounds needed in §3; the formula also
constructs bounds of any higher order requested for quadrature.

*Proof.* The exact original identity [S, (122.6)], in raw coordinates,
is

$$
\begin{gathered}
\Gamma(p)=\frac1{4\pi^2}\int_{\mathbb R}
 W(\tau)Z(p,\tau)^{-3/2}\,d\tau,\\
W(\tau)=\frac\tau{\sinh\tau},\qquad
q(\tau)=\tau\coth\tau,\\
Z(p,\tau)=z^2+(x^2+y^2)q(\tau)-4i\tau(w-xy/2).
\end{gathered}
\tag{2.4}
$$

The removable values of $q,W$ at zero are $1$, and the power is
principal. This is the horizontal unit-source Green field, not the
Green field of an auxiliary full Laplacian. For $v=|\tau|$,

$$
1\le q(\tau)\le1+v,\qquad q(\tau)\ge v,\qquad
0<W(\tau)\le4(1+v)e^{-v},\qquad \Re Z\ge r_0^2.
\tag{2.5}
$$

Indeed $q=v+2v/(e^{2v}-1)\le v+1$. The lower bounds follow
from $\tanh v\le\min(v,1)$. Also
$1-e^{-2v}\ge2v/(1+2v)$, so
$W\le(1+2v)e^{-v}\le4(1+v)e^{-v}$, including the limit
at zero. The only nonzero first and second spatial derivatives of
$Z$ are among

$$
\begin{gathered}
Z_x=2xq+2i\tau y,\quad Z_y=2yq+2i\tau x,\quad
Z_z=2z,\quad Z_w=-4i\tau,\\
Z_{xx}=Z_{yy}=2q,\quad Z_{zz}=2,\quad Z_{xy}=2i\tau.
\end{gathered}
\tag{2.6}
$$

Each is bounded in modulus by $L_0(1+v)$; derivatives of order
greater than two vanish. Label the $n$ differentiations in
$D^\alpha$. The chain rule for $Z^{-3/2}$ is a sum over partitions
of those labels into singletons and pairs. A partition with $k$
blocks contributes a product of $k$ derivatives of $Z$, times
$(-1)^k(3/2)_kZ^{-3/2-k}$. There are at most $n!2^n$ such
partitions, including the empty one when $n=0$: ordering labels
and placing block separators gives this elementary upper bound.
For $k\le n$, $(3/2)_k\le(n+2)!$ and
$|Z^{-3/2-k}|\le r_0^{-3-2n}$. Therefore

$$
|D^\alpha Z^{-3/2}|\le B_n(1+v)^n,\qquad
|W D^\alpha Z^{-3/2}|\le4B_n(1+v)^{n+1}e^{-v}.
\tag{2.7}
$$

These majorants hold on the entire closed box. They justify each
differentiation under the integral by dominated convergence,
including repeated and mixed raw derivatives. Since
$1/(4\pi^2)<1$, integration of (2.7) over both half-lines gives
(2.3). Expansion of $(1+v)^{n+1}$ and repeated integration by
parts give

$$
\int_T^\infty v^ke^{-v}\,dv
 =e^{-T}k!\sum_{j=0}^k\frac{T^j}{j!}.
\tag{2.8}
$$

For integer $T$, $e^{-T}\le2^{-T}$. This proves the displayed
rational tail certificate, which tends to zero effectively.

Here is also a finite compact-integral precision construction;
it does not ask for an integration service. On $[-T,T]$ write

$$
S_0(\tau)=\int_0^1\cosh(t\tau)\,dt
 =\sum_{j\ge0}\frac{\tau^{2j}}{(2j+1)!},\qquad
q=\cosh\tau/S_0,\quad W=1/S_0.
\tag{2.9}
$$

Thus $S_0\ge1$, and these expressions have no singular division
at zero. Their factorial series have explicit geometric tail
bounds after the ratio of successive absolute terms is at most
$1/2$. Such an index is found by increasing it past $2T+2$ and
checking the rational ratio. The same applies to the exponential
and hyperbolic series used below. For integer $T\ge1$ take
$E=3^{T+1}$; on this compact interval,

$$
|S_0|,|S_0'|,|\cosh\tau|,|\sinh\tau|\le E,
\quad |q'|\le E+E^2,\quad |W'|\le E,\quad W\le1.
\tag{2.10}
$$

The derivatives of $S_0$ are bounded using its integral in (2.9).
In the finite partition expression for $D^\alpha Z^{-3/2}$,
differentiate once in $\tau$. Bound each resulting product by
the triangle and product inequalities, substituting
$|Z^{-3/2-k}|\le r_0^{-3-2k}$,
$|D^\nu Z|\le L_0(1+T)$ for $1\le|\nu|\le2$, and
(2.10). For $Z_\tau$ and its spatial derivatives use the explicit
polynomial

$$
Z_\tau=(x^2+y^2)q'-4i(w-xy/2);
\tag{2.11}
$$

differentiate this polynomial and replace each coordinate by its
$M$ bound and $q'$ by $E+E^2$. A negative-power derivative
introduces only its displayed rational exponent and one additional
factor $Z_\tau/Z$. Finally use $W\le1$, $|W'|\le E$ and
$1/(4\pi^2)<1$. This finite symbolic prescription produces a
rational $L_{\alpha,T}\ge0$ bounding the $\tau$ derivative of
the complete differentiated integrand. It involves finitely many
partitions, products and sums with specified bounds for every leaf.

For completeness, evaluation of the complex powers is effective
on this same domain. If $Z=a+ib$, then

$$
\sqrt Z=u+i\frac b{2u},\qquad
u=\sqrt{\frac{\sqrt{a^2+b^2}+a}{2}}\ge r_0.
\tag{2.12}
$$

Rational bisection encloses the real square roots; the known lower
bounds justify inversion. Integer multiplication and inversion
then evaluate all the negative half-integer powers. The coefficient
$\pi$ has rational enclosures, for example from the alternating
series in $\pi=16\arctan(1/5)-4\arctan(1/239)$. Hence a
midpoint Riemann sum on a rational mesh of maximal width $h_T$
has compact-integral error at most $T L_{\alpha,T}h_T$ plus
$2T$ times the integrand evaluation error. Choose $T$ to make
the tail less than a quarter of the desired absolute error,
then choose $h_T$ and the evaluation error to make these two
compact errors each less than a quarter. If $L_{\alpha,T}=0$
there is no mesh error. Taking the real part and enlarging by
the stated errors produces a rational enclosing interval; halving
the allocated absolute error gives any prescribed interval width.
Every search here has its terminating numerical majorant. $\square$

**Definition 2.3 (the actual ellipticity data).** The raw expression
on $\Omega$ is

$$
\begin{gathered}
\mathsf A=\begin{pmatrix}
1&0&0&0\\0&1&0&x\\0&0&1&0\\0&x&0&1+x^2
\end{pmatrix},\qquad V=16\Gamma,\\
H_{\rm loc}=-\operatorname{div}(\mathsf A\nabla)-V
 =-\partial_{xx}-\partial_{yy}-\partial_{zz}
 -(1+x^2)\partial_{ww}-2x\partial_{yw}-V,\\
\Lambda=2+M_x^2,\quad\lambda=1/\Lambda,
\qquad \lambda I\le\mathsf A\le\Lambda I.
\end{gathered}
\tag{2.13}
$$

The shear block has determinant $1$ and trace $2+x^2$, proving
the last bounds. Each column divergence is zero, which proves
the nondivergence expression. For $0\le k\le6$ take

$$
\begin{gathered}
A_* = 2(1+M_x)^2+2,\qquad L_A=16A_*,\\
V_0=16G_0,\qquad V_*=16\max_{0\le n\le6}G_n.
\end{gathered}
\tag{2.14}
$$

Every entry derivative $D^\nu\mathsf A_{ij}$ of order at most
six is bounded by $A_*$: the only nonconstant entries are $x$
and $1+x^2$. The number $L_A$ bounds the operator norm of
each coordinate derivative of $\mathsf A$ and hence of each
coordinate difference quotient whose segment stays in $Q^+$.
All derivatives $D^\nu V$, $|\nu|\le6$, are bounded by $V_*$.
These are constructed bounds for the raw coefficients. No
derivative of $h$ is a coefficient input.

## 3. A rational interior constant for the full operator

**Definition 3.1 (nested boxes and cutoffs).** Set $Q_0=Q^+$,
$Q_9=Q$. If $Q$ has faces $(a_j,b_j)$ and $Q^+$ has faces
$(a_j^+,b_j^+)$, define for $0\le i\le9$

$$
a_{i,j}=a_j^++\frac i9(a_j-a_j^+),\qquad
b_{i,j}=b_j^++\frac i9(b_j-b_j^+),\qquad
Q_i=\prod_{j=1}^4(a_{i,j},b_{i,j}).
\tag{3.1}
$$

There are explicit $C^{10}$ cutoffs $\chi_i$, $1\le i\le9$,
with $0\le\chi_i\le1$, equal to $1$ on $\overline{Q_i}$ and
compactly supported in $Q_{i-1}$. The following construction fixes
all their derivative constants. Let

$$
\vartheta(t)=\frac{\int_0^t v^{10}(1-v)^{10}\,dv}
                  {\int_0^1 v^{10}(1-v)^{10}\,dv}
\quad(0\le t\le1),
\tag{3.2}
$$

continued as $0$ to the left and $1$ to the right. Its coefficients
are rational and it is $C^{10}$. Put $c_0=1$. For $1\le k\le8$
let $c_k$ be the sum of the absolute coefficients of its $k$th
derivative on $[0,1]$. These rational numbers bound those
derivatives. On each coordinate use a left transition from the
midpoint of $a_{i-1,j},a_{i,j}$ to $a_{i,j}$, and a right
transition from $b_{i,j}$ to the midpoint of $b_{i,j},b_{i-1,j}$.
Their widths are

$$
d^-_{i,j}=(a_{i,j}-a_{i-1,j})/2,\qquad
d^+_{i,j}=(b_{i-1,j}-b_{i,j})/2.
\tag{3.3}
$$

Multiply the left transition $\vartheta$ and the right transition
$1-\vartheta$, then multiply the four coordinate factors. This
defines $\chi_i$. Define rational bounds

$$
\begin{aligned}
q_{i,j,k}
 &=\sum_{l=0}^k\binom kl
       c_l(d^-_{i,j})^{-l}c_{k-l}(d^+_{i,j})^{-(k-l)},\\
K_i&=\sum_{j=1}^4q_{i,j,1},\qquad
D_\chi=\max_{|\nu|\le8}\prod_{j=1}^4q_{9,j,\nu_j},\\
J_\chi&=\binom{12}{4}2^8\max(1,D_\chi).
\end{aligned}
\tag{3.4}
$$

Thus $|\nabla\chi_i|\le K_i$ and
$\|D^\nu\chi_9\|_\infty\le D_\chi$ for $|\nu|\le8$.
The degree, integration and coefficient sums in (3.2)–(3.4)
are finite exact rational operations. Extension by the constant
pieces preserves the indicated derivatives at transition faces.

**Theorem 3.2 (constructed raw interior graph estimate).** From
Definitions 2.1, 2.3 and 3.1 one can calculate a positive rational
$C_Q$ such that every $u\in D(H^4)$ satisfies

$$
\|u\|_{C^4(\overline Q)}
 :=\max_{|\alpha|\le4}\sup_{\overline Q}|D^\alpha u|
 \le C_Q\sum_{j=0}^4\|H^ju\|_2.
\tag{3.5}
$$

The representative on the left is the continuous local Sobolev
representative. The following recurrences are one finite formula
for $C_Q$; they do not contain an unnamed elliptic or embedding
constant.

*Proof: full-domain restriction.* Put $u_j=H^ju$, $0\le j\le4$.
For $j\le3$, $u_j\in D(H)\subset D(S_{\min}^*)$. Testing
the adjoint identity against any $\phi\in C_c^\infty(\Omega)$
gives, as distributions,

$$
H_{\rm loc}u_j=u_{j+1}\quad\hbox{on }\Omega.
\tag{3.6}
$$

This follows because such a $\phi$ belongs to the original
minimal domain and $H\phi=S_{\min}\phi$; self-adjointness
moves $H$ between the two slots. It makes no assertion that
these tests are a graph core of $H$. The statement applies
to its $h$ summand, where the right side is zero.

The qualitative local maximal-domain regularity used here can
be read in Shubin, Lemma 5.1 [SH]. Its precise correspondence
is the metric $\mathsf g=\mathsf A^{-1}$, of determinant $1$,
whose volume is raw Haar and whose scalar Laplace–Beltrami
operator is $\operatorname{div}(\mathsf A\nabla)$. The magnetic
one-form is zero; the potential is $-V$, locally bounded on
$G\setminus\{e\}$. The coefficients are smooth and locally
uniformly elliptic. The maximal-domain distribution has both
$u_j$ and $H_{\rm loc}u_j$ locally $L^2$, so that lemma gives
$u_j\in H^2_{\rm loc}$ there. Only its local conclusion is
used. No completeness or essential-self-adjointness theorem
across the puncture is applied. This qualitative fact justifies
the initial weak tests below, without inserting any numerical
bound from that lemma into (3.5).

*Proof: numerical first derivative bound.* For a weak solution
$H_{\rm loc}v=f$ on $Q_{i-1}$, use $\chi_i^2v$ as test,
approximating compactly supported $H^1$ tests when necessary.
Taking real parts, and putting $U=\|v\|_{L^2(Q_{i-1})}$,
$F_0=\|f\|_{L^2(Q_{i-1})}$ and
$X=\|\chi_i\nabla v\|_2$, yields

$$
\lambda X^2\le UF_0+V_0U^2+2\Lambda K_iUX
 \le UF_0+V_0U^2+\frac\lambda2X^2
                      +\frac{2\Lambda^2K_i^2}{\lambda}U^2.
\tag{3.7}
$$

Write $N_k(v;D)^2=\sum_{|\alpha|\le k}
\|D^\alpha v\|_{L^2(D)}^2$. Since $\sqrt A\le1+A$ for
$A\ge0$, (3.7) gives the explicit estimate

$$
\begin{gathered}
N_1(v;Q_i)\le C_{1,i}(U+F_0),\\
C_{1,i}=2+\frac2\lambda+\frac{2V_0}\lambda
                      +\frac{4\Lambda^2K_i^2}{\lambda^2}.
\end{gathered}
\tag{3.8}
$$

*Proof: numerical second derivative bound.* For this step it
suffices that $v\in H^1(Q_{i-1})$ and
$-\operatorname{div}(\mathsf A\nabla v)=F$ with $F\in L^2$.
Let $D_h^k$ be a coordinate difference quotient and set
$v_h=D_h^kv$, $D=\|\nabla v\|_{L^2(Q_{i-1})}$,
$Y=\|F\|_{L^2(Q_{i-1})}$ and
$X_h=\|\chi_i\nabla v_h\|_2$. Take $|h|$ smaller than half
the distance of $\operatorname{supp}\chi_i$ from the boundary.
All shifts and their intervening segments stay in $Q_{i-1}$.
The fundamental theorem on almost every line and Jensen give
$\|v_h\|_{L^2(\operatorname{supp}\chi_i)}\le D$; the same
bound holds on the supports of its cutoff derivatives.

Use $-D_{-h}^k(\chi_i^2v_h)$ as the original weak test and
perform discrete integration by parts. The principal term has
coefficient $\mathsf A(\cdot+he_k)$. Its cutoff error is at
most $2\Lambda K_iD X_h$. The coefficient-difference term
is at most $L_AD(X_h+2K_iD)$. Finally

$$
\|D_{-h}^k(\chi_i^2v_h)\|_2
 \le\|\partial_k(\chi_i^2v_h)\|_2
 \le X_h+2K_iD.
\tag{3.9}
$$

Consequently

$$
\lambda X_h^2
 \le [Y+(2\Lambda K_i+L_A)D]X_h
                         +2K_iYD+2L_AK_iD^2.
\tag{3.10}
$$

This is the interior difference-quotient argument of Hunter,
Theorem 4.27 [HU], with the errors retained numerically. Define

$$
\begin{aligned}
B_i&=1+\lambda^{-1}
 [1+2\Lambda K_i+L_A+2K_i(1+L_A)],\\
C_{2,i}&=(2+4B_i)(1+V_0).
\end{aligned}
\tag{3.11}
$$

To see the first bound, put $Z_0=Y+D$,
$a_0=1+2\Lambda K_i+L_A$ and $b_0=2K_i(1+L_A)$.
Then (3.10) implies
$\lambda X_h^2\le a_0Z_0X_h+b_0Z_0^2$.
Since $B_i\ge1$ and $\lambda B_i\ge a_0+b_0$,
the positive root is at most $B_iZ_0$. Thus
$X_h\le B_i(Y+D)$, including $Z_0=0$ by (3.10).
Weak compactness of these difference quotients proves
$\|\nabla\partial_kv\|_{L^2(Q_i)}\le B_i(Y+D)$ for
each of the four coordinates. Summing these four bounds
and the $H^1$ norm gives an $H^2$ bound. Substituting
$F=f+Vv$ proves

$$
N_2(v;Q_i)\le C_{2,i}
 \bigl(\|f\|_{L^2(Q_{i-1})}+N_1(v;Q_{i-1})\bigr).
\tag{3.12}
$$

There is no derivative of $f$ in this step and no boundary
condition on the box. For a merely weak $H^1$ solution the
fixed-$h$ tests are justified by compact $H^1$ approximation;
boundedness followed by weak convergence supplies the
second derivatives. This also justifies the higher-order
induction without initially presuming its conclusion.

*Proof: all eight derivatives and a finite recurrence.* For
$k=0,\ldots,6$ put

$$
n_k=\binom{k+3}{3},\qquad
R_k=(2^k-1)(16A_*+V_*).
\tag{3.13}
$$

For $|\alpha|=k$ differentiate the nondivergence expression in
(2.13). For a local equation $H_{\rm loc}v=f$ this gives

$$
\begin{aligned}
H_{\rm loc}D^\alpha v={}&D^\alpha f
 +\sum_{0<\nu\le\alpha}\binom\alpha\nu
       \sum_{l,m=1}^4(D^\nu\mathsf A_{lm})
                    D^{\alpha-\nu}\partial_{lm}v\\
 &+\sum_{0<\nu\le\alpha}\binom\alpha\nu
                    (D^\nu V)D^{\alpha-\nu}v.
\end{aligned}
\tag{3.14}
$$

Every derivative of $v$ in the commutator has order at most
$k+1$. The two sums in $L^2$ are bounded by
$R_k N_{k+1}(v;Q_{i-1})$, since
$\sum_{0<\nu\le\alpha}\binom\alpha\nu=2^k-1$.
In particular $R_0=0$. If $v\in H^{k+1}$ and $f\in H^k$
on the outer box, (3.14) is a distribution identity with
$L^2$ right side. Apply (3.12) to each $D^\alpha v$.
Each derivative of order $k+2$ occurs in at least one of
these $n_k$ second derivative lists. Therefore, with $i=k+2$,

$$
\begin{aligned}
N_i(v;Q_i)\le{}&
 [1+n_{i-2}C_{2,i}(R_{i-2}+1)]
                       N_{i-1}(v;Q_{i-1})\\
 &+n_{i-2}C_{2,i}N_{i-2}(f;Q_{i-1}).
\end{aligned}
\tag{3.15}
$$

Let $S_u=\sum_{j=0}^4\|u_j\|_2$. Set $T_{j,0}=1$
for $0\le j\le4$, and $T_{j,1}=2C_{1,1}$ for
$0\le j\le3$. For $2\le i\le8$ and
$0\le j\le4-\lceil i/2\rceil$ define, in increasing $i$,

$$
\begin{aligned}
T_{j,i}={}&[1+n_{i-2}C_{2,i}(R_{i-2}+1)]T_{j,i-1}
                  +n_{i-2}C_{2,i}T_{j+1,i-2}.
\end{aligned}
\tag{3.16}
$$

All right-side indices are already defined. Equations
(3.6), (3.8), (3.15) prove inductively
$N_i(u_j;Q_i)\le T_{j,i}S_u$. In (3.15), the needed
$u_{j+1}$ norm on $Q_{i-1}$ is at most its already bounded
norm on the larger $Q_{i-2}$. In particular,
$N_8(u;Q_8)\le T_{0,8}S_u$. Only $u_4\in L^2$ is needed;
no derivative is required of the fourth graph vector.

*Proof: numerical Sobolev embedding.* Put $w=\chi_9u$, extended
by zero outside $Q_8$. The cutoff support and its $C^{10}$
regularity make $w\in H^8(\mathbb R^4)$. Leibniz' rule,
$\sum_{\nu\le\alpha}\binom\alpha\nu\le2^8$, and the
$\binom{12}{4}$ multiindices of length at most eight give

$$
N_8(w;\mathbb R^4)\le J_\chi N_8(u;Q_8).
\tag{3.17}
$$

Use the unitary Fourier convention
$\widehat w(\xi)=(2\pi)^{-2}\int e^{-ix\cdot\xi}w(x)\,dx$.
Expansion of $(1+|\xi|^2)^8$ has nonnegative coefficients
whose sum is $5^8$, so

$$
\|(1+|\xi|^2)^4\widehat w\|_2\le5^4N_8(w;\mathbb R^4).
\tag{3.18}
$$

For $|\alpha|\le4$, Cauchy–Schwarz bounds
$\|\xi^\alpha\widehat w\|_1$ by this last norm times
$[\int(1+|\xi|^2)^{-4}d\xi]^{1/2}$. In four dimensions
the integral is $\pi^2/6$, by polar integration and
$\int_0^\infty r^3(1+r^2)^{-4}dr=1/12$.
The inverse-transform factor makes
$(2\pi)^{-2}(\pi^2/6)^{1/2}<1$. Fourier inversion of these
$L^1$ derivatives supplies continuous representatives and

$$
\|w\|_{C^4(\mathbb R^4)}\le625N_8(w;\mathbb R^4).
\tag{3.19}
$$

The same inequality for arbitrary $H^8$ vectors follows by
density, or directly by inversion of their $L^1$ Fourier
derivatives. Since $\chi_9=1$ on $\overline Q$, a constructed
rational answer is

$$
\boxed{C_Q=625J_\chi T_{0,8}.}
\tag{3.20}
$$

It depends only on rational box geometry, the explicit polynomial
shear and the differentiated original Green majorants (2.2).
No graph derivative was applied to an approximation, and no
Friedrichs-domain replacement occurred. $\square$

[SH]: https://arxiv.org/html/math/0007019v1
[HU]: https://www.math.ucdavis.edu/~hunter/pdes/ch4.pdf

## 4. The full source vectors and their numerical moduli

**Theorem 4.1 (original-source correspondence and constructed local
modulus).** Under Assumption 1.1, the published coefficient and
global constructions give global raw names of $h,v_1,v_2$, where
$v_t=hg_t$, and constructed rational bounds

$$
\|h\|_{C^4(\overline Q)}\le C_Q,
\qquad \|v_t\|_{C^4(\overline Q)}\le187C_Q/\ell
\quad(t=1,2),
\tag{4.1}
$$

where $\ell>0$ is obtained by finite refinement of a scalar name.
These are bounds for the original full-endpoint vectors.

*Proof.* The suppliers [R, Theorems 11.3–11.4, 12.2–12.4]
construct $h$ and $G_1=(F+1)^{-1}$ on global raw names. They
give

$$
\begin{gathered}
n=h-G_1h,\quad D_0=\langle h,n\rangle>0,
\quad \|n\|_2\le1,\quad \xi_{\rm src}=n/D_0,\\
R_H=(H+1)^{-1}
 =G_1+\frac{|n\rangle\langle n|}{D_0},\quad0\le R_H\le I.
\end{gathered}
\tag{4.2}
$$

Refining the $D_0$ intervals eventually gives a rational positive
lower endpoint. Choose rational $0<\ell<D_0$ below it; then
$\|\xi_{\rm src}\|_2\le1/\ell$. This is a terminating
positivity search, without a supplied lower bound. Inner products
are computed from global norm names and finite box partitions.
The rank-one identity is the original boundary-pairing identity
[S, (115.5)] at discount $1$. Its imposed condition is exactly
$A=\rho C$ on the full complex domain. The auxiliary $F$ remains
distinct, and is used only in this identity.

To make the source identification explicit, the full source trace
satisfies [R, (12.9)]

$$
\operatorname{tr}(J_h^{-1}R_H\phi)
   =\langle\xi_{\rm src},\phi\rangle_\mu.
\tag{4.3}
$$

Apply it to $(H+1)e^{-tH}\phi$, a bounded operator on each
positive-time slice. Since
$R_H(H+1)e^{-tH}\phi=e^{-tH}\phi$, self-adjointness gives

$$
\begin{aligned}
\operatorname{tr}(T_tJ_h^{-1}\phi)
 &=\langle(H+1)e^{-tH}\xi_{\rm src},\phi\rangle_\mu\\
 &=\langle J_hg_t,\phi\rangle_\mu.
\end{aligned}
\tag{4.4}
$$

The second identification is the original deterministic-time Riesz
identity [S, (117.2)–(117.5)], for every input. Thus

$$
v_t=(H+1)e^{-tH}\xi_{\rm src}=hg_t
\tag{4.5}
$$

at each specified time, with the original normalization. Smoothing
occurs before the unbounded operator; $\xi_{\rm src}\in D(H)$
is neither needed nor asserted. No source delta is an $L^2$
vector. The normalization of (4.3) is the full equilibrium trace
normalization, rather than an evaluation of $h$ at $e$.

For global computation, [R, Theorem 12.4] constructs the bounded
functional calculus at $R_H$ for

$$
\psi_t(x)=x^{-1}e^{-t(x^{-1}-1)}\ (0<x\le1),\qquad
\psi_t(0)=0,\qquad v_t=\psi_t(R_H)\xi_{\rm src}.
\tag{4.6}
$$

Its uniform polynomial approximation and certified action errors
give precisely Definition 1.2's global names. Reusing that
construction introduces neither a pointwise heat service nor a
new interacting solver. For their smoothness modulus, spectral
calculus of the same nonnegative $H$ gives $v_t\in D(H^N)$
for every finite $N$, and for $0\le j\le4$, $t\ge t_->0$,

$$
\|H^jv_t\|_2\le\ell^{-1}
 \{j!t_-^{-j}+(j+1)!t_-^{-(j+1)}\}.
\tag{4.7}
$$

Indeed $\lambda^ke^{-t\lambda}\le k!t_-^{-k}$ follows
from the exponential series, including $k=0$. At $t=1,2$
choose $t_-=1$ and sum: $2+3+8+30+144=187$.
Also $h\in D(H^N)$, $\|h\|_2=1$ and $H^jh=0$ for
$j\ge1$. Theorem 3.2 now proves (4.1). These norm bounds
belong to the actual vectors, independently of which finite raw
steps are returned by their names. $\square$

## 5. A terminating rational-point jet map

**Definition 5.1 (an exact-integral local kernel).** On the real line
put

$$
\zeta(t)=\frac{315}{256}(1-t^2)^4\mathbf1_{[-1,1]}(t),
\quad \kappa(x)=\prod_{i=1}^4\zeta(x_i),\quad
\kappa_\epsilon(x)=\epsilon^{-4}\kappa(x/\epsilon).
\tag{5.1}
$$

This is a nonnegative unit-mass compact kernel, since
$\int_{-1}^1(1-t^2)^4dt=256/315$. It is $C^3$, and its
derivatives through order three are compactly supported
piecewise polynomials without distributional boundary terms.
For $0\le j\le3$ define rational

$$
b_j=\frac{315}{256}
 \sum_{l=\lceil j/2\rceil}^4\binom4l\frac{(2l)!}{(2l-j)!},
\qquad L_\alpha=4\prod_{i=1}^4b_{\alpha_i}\quad(|\alpha|\le3).
\tag{5.2}
$$

Coefficient absolute sums give $|\zeta^{(j)}|\le b_j$.
The support cube has volume $16$, so
$\|D^\alpha\kappa\|_2\le L_\alpha$. These are directly
computed derivative norms sufficient for the error certificate.

**Theorem 5.2 (finite precision map from a global name and a
constructed modulus).** Suppose $u$ is real, has a global raw name,
and has its actual local representative satisfying
$\|u\|_{C^4(\overline Q)}\le M$, with known rational $M>0$.
For every rational $p\in Q$, $|\alpha|\le3$ and rational
$\varepsilon_0>0$, a rational interval of width at most
$\varepsilon_0$ enclosing $D^\alpha u(p)$ is returned in
finitely many rational operations and one global-name request.

*Proof.* Choose rational $\epsilon>0$ such that

$$
p+[-\epsilon,\epsilon]^4\subset Q,\qquad
\epsilon<\frac{\varepsilon_0}{32M}.
\tag{5.3}
$$

For example take less than half the minimum face distance and
less than the second displayed bound. Request a finite raw step
$U$ with error

$$
\|U-u\|_2\le\delta,\qquad
0<\delta<\frac{\varepsilon_0\epsilon^{2+|\alpha|}}
                         {8L_\alpha}.
\tag{5.4}
$$

Define the finite integral

$$
I=\int_{\mathbb R^4}D^\alpha\kappa_\epsilon(p-q)U(q)\,dq.
\tag{5.5}
$$

Intersect each rational step box with
$p+[-\epsilon,\epsilon]^4$, and partition overlaps if needed.
On every resulting rational rectangle the integrand is a
polynomial with rational complex coefficients. Integrating its
monomials gives the exact rational complex number $I$. Box
faces have measure zero. Thus no unspecified quadrature error
or regularity of $U$ is involved.

Integration by parts against the actual $C^3$ representative
of $u$ on this compact cube gives
$\int D^\alpha\kappa_\epsilon(p-q)u(q)dq
=\int\kappa_\epsilon(p-q)D^\alpha u(q)dq$.
The kernel derivatives through order three have the required
vanishing boundary traces, so the identity also follows by
successive elementary integration by parts on the cube. Each
coordinate increment of $D^\alpha u$ is bounded by $M$ times
its displacement, because its first derivatives have order at
most four. Therefore

$$
\begin{aligned}
|D^\alpha u(p)-I|
 &\le4\epsilon M
     +\|D^\alpha\kappa_\epsilon\|_2\|U-u\|_2\\
 &\le4\epsilon M
          +L_\alpha\epsilon^{-2-|\alpha|}\delta
 <\varepsilon_0/4.
\end{aligned}
\tag{5.6}
$$

The exponent is the four-dimensional $L^2$ scaling. A rational
interval centered at $\Re I$ with radius $\varepsilon_0/4$
is valid and has width $\varepsilon_0/2\le\varepsilon_0$.
If a specified representation requires outward rounding, allocate
any of the unused half-width to it. Everything terminates by
the definition of a global name and finite polynomial integration.

The same estimate, with the actual $L^2$ derivative norm and
an added certified quadrature error, holds for the normalized
product of $\exp[-1/(1-t^2)]\mathbf1_{(-1,1)}$. Formula
(5.1) makes that numerical quadrature unnecessary while retaining
exactly its compact-convolution error argument. This kernel is
a mathematical functional of a global name, not an observation
of the path or a replacement physical instrument. $\square$

**Theorem 5.3 (certified jets of the original $h,g_1,g_2$).** Under
Assumption 1.1 and with only Definition 1.2's model names, the
output in Definition 1.2 exists as a terminating precision map.
It uses constructed raw elliptic constants, not an additional
pointwise, derivative, Sobolev, ground-state-lower-bound or heat
oracle.

*Proof.* A rational point in $\Omega$ has at least one nonzero
coordinate among $x,y$. Choose nested rational boxes around it
whose closure keeps that coordinate away from zero. This gives
$Q\Subset Q^+\Subset\Omega$ effectively. Construct (2.1)–(3.20),
and $\ell$ as in Theorem 4.1. Apply Theorem 5.2 to $h,v_1,v_2$
with $M=C_Q,187C_Q/\ell,187C_Q/\ell$, respectively. This
returns convergent raw derivative intervals through order three.

At $p$, refine the $h(p)$ interval until its lower endpoint is
strictly positive. This terminates because the supplied actual
$h(p)>0$. Thus a rational lower bound for the denominator is
produced, rather than given. Differentiate $v_t=hg_t$ in
increasing total order:

$$
D^\alpha g_t(p)=\frac{D^\alpha v_t(p)
 -\displaystyle\sum_{0<\nu\le\alpha}\binom\alpha\nu
                   D^\nu h(p)D^{\alpha-\nu}g_t(p)}{h(p)}.
\tag{5.7}
$$

For $\alpha=0$ the sum is empty. Each sum for larger $\alpha$
uses only lower-order quotient derivatives. Evaluate (5.7) by
rational interval arithmetic using all raw jets to width at most
$2^{-N}$. Once the denominator interval is positive, these
finitely many arithmetic expressions are continuous functions
of their finite jet inputs on a neighborhood of the actual tuple.
Their interval widths therefore tend to zero as $N\to\infty$:
addition and multiplication preserve convergence of bounded
intervals, and division does so when the limiting denominator
is nonzero. Increasing $N$ until every requested output has
width at most $\varepsilon_0$ is a total search, and yields
the required rational intervals. This is a terminating precision
map even though no uniform advance count of positivity
refinements is asserted.

Only global $L^2$ errors are attached to the finite raw steps.
The bounds (4.1) and the derivative in (5.6) apply to the actual
domain vectors. Neither $H$, $H^j$ nor a graph norm is applied
to a box step. All information about the endpoint enters through
the full resolvent and the original normalized $h$, before any
local estimate is used. $\square$

**Corollary 5.4 (a derived compact positive denominator).** For any
rational compact box $K\Subset\Omega$, a rational lower bound
$\inf_K h>l_K>0$ can be calculated from the same names.

*Proof.* Construct a larger $Q$ and its bound $C_Q$. For a
rational mesh of coordinate covering radius $\rho$, the $C^1$
bound gives $|h(p)-h(q)|\le4C_Q\rho$ between a point of $K$
and its chosen grid point in the larger box. Refine the finite
grid and the finitely many certified values until the least lower
endpoint exceeds $4C_Q\rho$. This terminates since the actual
continuous $h$ has a strictly positive minimum on $K$. Subtract
$4C_Q\rho$ and choose a smaller positive rational. No lower
bound was an input. $\square$

## 6. The actual successor certificate and its limits

**Theorem 6.1 (source-slice certificate interface).** At the same
reference member, the precision map computes certified interval
values of

$$
D(r,z,s)=\det\frac{\partial(g_1,\gamma,g_2)}{\partial(r,z,s)}
\quad(r>0)
\tag{6.1}
$$

at every rational $(r,z,s)$, to widths tending to zero. Searching
for a returned interval excluding zero is a sound semidecision
for the existence of a nonzero minor. Conditional on such an
interval being obtained, $g_2$ is not measurable for
$\overline{\sigma(g_1,\gamma)}^{\,m}$, and [W, (14.5)] fails
at the reference member.

*Proof: original slice dictionary.* The full source rotations
in [S, §120] preserve the raw operator, the entire endpoint,
the coefficient-positive $h$, the source trace and every $g_t$.
In symmetric coordinates these functions depend on $(r,z,s)$,
not the angle. On the raw slice

$$
(x,y,z,w)=(r,0,z,s),
\tag{6.2}
$$

variations of $r,z,s$ are exactly raw $x,z,w$ variations.
Thus every required derivative through order three is one
returned by Theorem 5.3, without a coordinate or source
renormalization. In particular the actual metric gives on this
slice

$$
\gamma=b_r^2+b_z^2+(1+r^2/4)b_s^2.
\tag{6.3}
$$

The derivatives needed in (6.1) use at most two derivatives of
$b$ and one of $\beta$. Rational interval arithmetic in these
jets therefore gives enclosing intervals whose widths tend
to zero. The third jets additionally serve differentiated
radial identities when separately required; they are not a
nonvanishing assumption.

*Proof: semidecision and positive measure.* Enumerate the
countable rational triples with $r>0$ and all positive integer
precision levels, by a diagonal enumeration. Each interval
calculation terminates. If an interval excludes zero, it proves
an actual nonzero value of (6.1). Conversely, if this continuous
minor is nonzero at some point, it stays nonzero in a rational
neighborhood, which contains a rational triple. Refinement
there eventually excludes zero. If $D$ vanishes identically,
the search need not halt. A search restricted to a subsidiary
radial coefficient need not halt even when $D$ is nontrivial.

For a nonzero value, the inverse function theorem gives a small
chart with coordinates $(b,\gamma,\beta,\theta)$. The original
density is $h^2r\,dr\,dz\,ds\,d\theta$, strictly positive
and smooth there. Restrict to a smaller chart rectangle and
integrate its angle variable. The resulting measure on
$(b,\gamma,\beta)$ has a strictly positive density with respect
to three-dimensional Lebesgue measure. If $\beta$ were
measurable for the completed factor, a Borel version of the
Doob–Dynkin factorization would give
$\beta=F(b,\gamma)$ $m$-almost everywhere. Indeed completion
measurability has an uncompleted measurable version modulo
a null set, and the target $\mathbb R^2$ is standard Borel.
But every Borel graph $\{(u,v,F(u,v))\}$ has three-dimensional
measure zero by Fubini, since its vertical sections are
singletons. It cannot carry the positive chart measure.
This proves actual measurable nonfactorization, conditional
on the evaluated nonzero interval, rather than a dimension
heuristic.

Under the marked unitary source correspondence,

$$
U(\widehat P B\Omega_{\rm cyc})=T_1g_1=g_2=\beta.
\tag{6.4}
$$

The vector $B\Omega_{\rm cyc}$ lies in $\mathcal H_{\rm rel}$.
Thus conditional nonfactorization gives

$$
\Delta_{\rm next}
 =\|(I-E_{\rm rel})\widehat P B\Omega_{\rm cyc}\|^2>0,
\qquad E_{\rm rel}\widehat P\ne\widehat P E_{\rm rel}.
\tag{6.5}
$$

On the unchanged path the next original label probability
conditional on the full hidden state is $c\beta(\mathsf X_j)$.
This is the same source-start experiment and gap. No inference
about its smaller one-start observed Markov property is required
for (6.5). $\square$

**Definition 6.2 (unpaid source relation).** Theorem 6.1 supplies
a terminating evaluator and a conditional semidecision, not an
evaluated nonzero interval. No rational witness, lower bound
for $\Delta_{\rm next}$ or parameter-persistence interval is
specified here. At the reference member the alternatives
$\beta=F(b,\gamma)$ almost everywhere and its negation remain
unsettled until separately established. Identical vanishing of
all local minors would still leave possible different fibre
sheets and would not prove global Borel factorization. Even
that factorization alone would not prove full heat reduction.

For all finite original $a,\eta,d>0$, the autonomous-factor
question remains the original condition
$E_{\rm rel}\widehat P=\widehat P E_{\rm rel}$, equivalent
by self-adjointness and injective time calculus to invariance
under every original $T_t$. The present quantitative construction
is at $a=\eta=d=1$, hence $a^2d/\eta=1$. It asserts neither
universality nor an exceptional parameter set. The full-domain
transport in [W, Theorems 5.2–5.3] is available only with its
actual parameter, source, normalization, clock and calibration
correspondence. No witness exists here to transport. Recovery
of mutually sufficient spatial, temporal, boundary and memory
relations retains these unresolved obligations.

## 7. Access, cost and source correspondence

**Definition 7.1 (charged mathematical operations).** The finite
precision map uses the following kinds of operations: rational
box geometry; finite differentiation and coefficient sums of
the displayed polynomials; integer factorials and finite
partition enumeration; rational comparisons and arithmetic;
certified elementary series, square-root bisection and Green
quadrature in Theorem 2.2; the already constructed coefficient,
global-vector and full-resolvent requests of [R]; scalar-name
refinement for $D_0$; bounded functional-calculus precision
requests for the global $v_t$ names; rational box intersection
and polynomial integration; interval refinements for $h(p)>0$;
and the finitely many quotient expressions (5.7).

The underlying global requests include all work charged by
[R, §§11–12], including their residual and spectral polynomial
precision searches. They are not unit-cost physical queries.
The number and sizes of returned boxes, bit lengths, spectral
degrees, Green tail cutoffs and positivity refinements depend
on the names, geometry and precision. The proof gives
termination and explicit precision choices; it supplies no
measured runtime, uniform complexity estimate, finite passive
sample bound or effective-cost improvement. Each individual
minor query terminates, while the existence search in §6 is
only a semidecision.

**Definition 7.2 (access distinction).** Mathematical coefficient
names and global raw names concern the one fixed source. Their
use entails no path intervention. Passive observation still has
only its original chronological labels with conditional fresh
noise; it has no hidden-state point sensor, derivative sensor,
reset, new clock, altered calibration or new source preparation.
The exact-law recovered multiplication operator $\mathsf R$
does not by itself provide the model names required here.
No implication from exact recovery to finite acquisition or
effective acquisition cost is included.

**Definition 7.3 (reuse, literature status and proof boundary).**
The source-specific synthesis is `repo-derived`: differentiated
original-coefficient majorants with their finite tails, the
rational constant (3.20) for the full endpoint, and their
composition with the existing global names into (5.7).
Classical interior regularity, Sobolev embedding, compact
convolution and the positive-density graph argument are
intermediate methods, not new general analysis theorems.

| Source | Correspondence and retained boundary |
| --- | --- |
| [E, (112.1)–(112.5)] and [S, §§115–117] | Full complex maximal domain, distinguished $h$, non-Friedrichs extension, full form and original trace. Local estimates do not choose an extension. |
| [S, (122.5)–(122.8)] | Exact raw/symmetric coordinate and Green normalization used in (2.4), plus the actual elliptic symbol. The derivative tail bounds are constructed in (2.7)–(2.8), rather than inferred from a value bound. |
| [R, §§11–12, especially Theorems 12.2–12.4] | Constructed coefficient and global names, actual full-resolvent identity and deterministic-time source vector. Their approximation errors are reused as global $L^2$ errors only. |
| [FQ, Definition 3.2 and Theorem 3.3] | Same raw matrix and local Caccioppoli energy method. Its gradient certificates do not supply a pointwise jet; the extra difference-quotient recurrence and Fourier constant are given in §3. |
| [W, (14.2)–(14.5)] and [FG, Theorem 4.1] | Exact recovered measured factor, remaining heat-reduction condition and positive-measure fibre argument. Strict fibre separation supplies no autonomous heat closure. |
| Shubin, *Essential self-adjointness for semi-bounded magnetic Schrödinger operators on non-compact manifolds*, arXiv:math/0007019v1, Lemma 5.1 [SH] | `literature-attested`: qualitative local $H^2$ regularity of maximal-domain distributions. Here the metric is $\mathsf A^{-1}$, raw volume has density one, magnetic one-form is zero and potential is $-16\Gamma$. No complete-manifold theorem across $e$ or numerical constant is imported. |
| Hunter, *Chapter 4: Elliptic PDEs*, §4.11, Theorems 4.27–4.28, printed pp.112–114 [HU] | `literature-attested`: local difference-quotient and higher-regularity method for weak solutions. Equations (3.7)–(3.16) expose the constants and the lower-order potential; no displayed unspecified literature constant is a numerical service. |
| Krötz–Thangavelu–Xu, *The heat kernel transform for the Heisenberg group*, arXiv:math/0401243v2, §4.1, (4.1.2) [KTX] | `literature-attested`: the horizontal heat-kernel Fourier formula underlying the already supplied (2.4), at $n=1$ with the independent $z$ Gaussian and original raw inverse-transform normalization. No full central heat factor or changed potential is substituted. |
| Pinned mathlib, revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, `Mathlib/Analysis/Distribution/Sobolev.lean` [ML] | Distribution/Bessel-potential Sobolev foundations, including `MemSobolev.fourier_memL1`. Its Fourier convention has $2\pi$ scaling; (3.18)–(3.19) use the stated unitary convention explicitly. It is not the original-source numerical elliptic certificate. |
| `D5/S3/Quantum/Dynamics/CompressedResolventRemainder.lean`, `compressed_resolvent_remainder` | A finite-dimensional compressed-resolvent theorem with an independently supplied ambient lower bound. Its hypotheses do not identify this singular infinite-dimensional source or generate the required local constant. |
| `D5/S3/Quantum/Analysis/TraceClass/ContinuousEnergyHamiltonian.lean`, including private `basis_countable`, `encoded_energy`, `encoded_heat_summable`, `uniform_tails_of_continuous_total` | Separate trace-class spectral constructions. Neither those private helpers nor the public representation supplies the raw local coefficient/endpoint correspondence used here. |
| `D5/S3/VertexAlgebra/Analysis/OriginalModeExtension.lean` and `OriginalSmearingCore.lean`, including their private mode-bound and graph-approximation declarations | Graded vertex-algebra Sobolev completions and their mode extensions, with different operators and norms. A matching word such as “Sobolev” or “core” supplies no transfer to (3.5). |

No fresh Lean compilation or kernel verification is claimed.
The literature methods remain literature-attested; the
source-specific composition is a conditional project derivation,
without a worldwide novelty claim. The source inequalities
and precision-map proofs state the resulting mathematical
interface, while Definition 6.2 states the remaining actual-source
question. A local quantitative interface does not complete the
long-term mutual-recovery programme.

[KTX]: https://arxiv.org/abs/math/0401243v2
[ML]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Distribution/Sobolev.lean

## 追加锚（本行以下为增补区）

## 8. All-parameter source correspondence and local suppliers

**Definition 8.1 (original inputs and the defects).** For §§8–14,
allow every finite original $a,\eta,d>0$ with total rational interval
names. Retain the analytic source of [FG, Assumption 1.1] and the
numerical suppliers of [R, §§11–12] and [SRO, Definitions 1.1–1.2].
These are the parameter-dependent versions of (1.1)–(1.3):

$$
\begin{gathered}
S_{a,\eta}=(aL-\eta\partial_w^2-16\sqrt{a\eta}\,\Gamma)
 |_{C_c^\infty(G\setminus\{e\};\mathbb C)},\\
C(w_*)=1,\quad h=w_*/\|w_*\|_2,\quad
D(H)=\{v\in D(S_{a,\eta}^*):A(v)=\rho C(v)\}
 =D(\overline S_{a,\eta})\dotplus\mathbb Ch,\\
H\ge0,\quad\ker H=\mathbb Ch,\quad m=h^2\mu,\quad
K=J_h^{-1}HJ_h,\quad T_t=e^{-tK},\quad P=T_d,\\
b=g_d,\quad\beta=Pb=g_{2d},\quad
\gamma=d\left[a\sum_{j=1}^3(X_jb)^2+
                         \eta(\partial_wb)^2\right],\\
u=\frac b{1+b},\quad \chi=\frac1{1+\gamma},\quad
\Phi=(u,\chi),\quad
\mathcal S=\overline{\sigma(\Phi)}^{\,m}
          =\overline{\sigma(b,\gamma)}^{\,m},\\
\mathcal H_{\rm rel}=L^2(\mathcal S,m),\quad
E=\mathbb E_m[\,\cdot\mid\mathcal S],\quad
\Delta(z)=\|(I-E)z\|_{L^2(m)}^2,\quad
\Delta_{\rm next}=\Delta(\beta).
\end{gathered}
\tag{8.1}
$$

The letter $u$ in $\Phi$ denotes the bounded scalar coordinate in
(8.1). All fields use their original smooth representatives on
$G\setminus\{e\}$; arbitrary finite assignments on omitted null
sets do not change these definitions. The inverse scalar maps
$b=u/(1-u)$ and $\gamma=\chi^{-1}-1$ prove the equality of completed
sigma algebras, since $0\le u<1$ and $0<\chi\le1$ almost everywhere.
These coordinates are mathematical functions of the original pair,
with no change to the physical emissions.

Keep the entire complex endpoint, raw Haar measure, full form
$\mathscr V_0\dotplus\mathbb C1$ and continuous source trace, the
$e$-start, first read $2d$, gaps $d$, exact calibration
$c=1/[4(1+N_d)]$, $N_d=\|g_d\|_\infty$, and four original labels
with conditionally fresh noise on one undisturbed path. In particular
$N_d=s_d=\operatorname{tr}g_d$ is not an assumption. The original
marked unitary $U$ identifies

$$
U(\widehat P B\Omega_{\rm cyc})=\beta,\qquad
\Delta_{\rm next}
 =\|(I-E_{\rm rel})\widehat P B\Omega_{\rm cyc}\|^2.
\tag{8.2}
$$

Here $E$ acts on full $L^2(m)$, whereas $E_{\rm rel}$ acts on the
recovered visible Hilbert space; their restrictions correspond under
$U$, since $\mathcal H_{\rm rel}\subset\mathcal O$. No equality
$\mathcal H_{\rm rel}=\mathcal O$ is assumed.

[SRO]: RECURSIVE_RELATIONAL_OBSERVATION_SOURCE_RELATIVE_ORDER.md

**Theorem 8.2 (transport of the entire certification problem).**
The scalar defects in (8.1), their completed factor, and the original
heat-reduction condition transport to the actual reference member
$a'=\eta'=1$ at the named time $\tau=a^2d/\eta$. The reference
local precision construction extends to this arbitrary $\tau>0$.
It gives rational-point jets through order three and computed local
$C^4$ bounds for $h,g_\tau,g_{2\tau}$ on every compact rational box
in $\Omega=\{x^2+y^2>0\}$. Consequently $\Phi$ has a computed local
$C^2$ bound. No new pointwise or derivative supplier is required.

*Proof: full-domain transport.* Use exactly [W, Theorem 5.2] and
[FQ, Theorem 2.1], with

$$
\begin{gathered}
s^2=\eta/a,\qquad \kappa=\eta/a^2,\qquad
\mathcal U_sv=s^{5/2}v\circ\delta_s,\quad
\mathcal W_sf=f\circ\delta_s,\qquad d'=d/\kappa=\tau,\\
C'(\mathcal U_sv)=sC(v),\quad
A'(\mathcal U_sv)=s\{A(v)-(\log s)C(v)\},\quad
\rho'=\rho-\log s,\\
h'=\mathcal U_sh,\quad D(H')=\mathcal U_sD(H),\quad
H'=\kappa\mathcal U_sH\mathcal U_s^{-1},\quad
m'=(\delta_{1/s})_*m,\\
K'=\kappa\mathcal W_sK\mathcal W_s^{-1},\quad
T'_{d'}\mathcal W_s=\mathcal W_sT_d,\quad
b'=\mathcal W_sb,\quad\beta'=\mathcal W_s\beta.
\end{gathered}
\tag{8.3}
$$

These identities transport maximal domains, graph closures, both
boundary coefficients and the full form and trace. The derivative
identities $X_j\mathcal W_s=s\mathcal W_sX_j$ and
$\partial_w\mathcal W_s=s^2\mathcal W_s\partial_w$ give
$\gamma'=\mathcal W_s\gamma$. Thus $\Phi'=\Phi\circ\delta_s$,
$E'\mathcal W_s=\mathcal W_sE$, and all defects are unchanged.
The same theorem transports the original entrance, clock, calibration
and words. This compares models by a proved unitary; it replaces no
physical clock or source. Positive finite parameter names compute
$s,\kappa,\tau$ by interval arithmetic with certified positive
denominators. Reference coefficient/global services are the existing
services at the exact coefficients $(1,1)$ and named time $\tau$.

*Proof: arbitrary positive reference time.* In the remainder of this
proof and in §§9–12, use the reference member, omitting primes.
Find a rational $0<L\le\tau$ from its positive name. Equations
(4.2)–(4.7) and [R, Theorem 12.4] provide the raw global names and

$$
\begin{gathered}
v_t=hg_t=(H+1)e^{-tH}\xi_{\rm src},\qquad
\|\xi_{\rm src}\|_2\le\ell^{-1},\qquad 0<\ell<D_0,\\
M_L=\ell^{-1}\sum_{j=0}^4
       \left[j!L^{-j}+(j+1)!L^{-j-1}\right],\qquad
\sum_{j=0}^4\|H^jv_t\|_2\le M_L\quad(t=\tau,2\tau).
\end{gathered}
\tag{8.4}
$$

The positive $\ell$ is obtained by the terminating refinement in
Theorem 4.1. Theorem 3.2 applies to every actual $D(H^4)$ vector;
its rational $C_Q$ is independent of $t$. Hence the local $C^4$
bounds are $C_Q$ for $h$ and $C_QM_L$ for $v_t$. Theorem 5.2
and (5.7) produce the claimed third jets. Corollary 5.4 computes a
strictly positive rational lower bound $l_Q$ for $h$ on any fixed
compact inner box. To expose also the quotient modulus, let rational
$M_h,M_v$ bound all derivatives through order four of $h,v_t$ there.
Define

$$
Q_0=M_v/l_Q,\qquad
Q_k=\max\left\{Q_{k-1},\frac{M_v+
 M_h\sum_{j=1}^k\binom kjQ_{k-j}}{l_Q}\right\}
       \quad(1\le k\le4).
\tag{8.5}
$$

Leibniz' rule in $v_t=hg_t$ proves that $Q_k$ bounds every quotient
derivative of order at most $k$. This is a bound on the actual
fourth derivatives; their point evaluation is not required. The
polynomial raw formula for $\gamma$, with a rational upper bracket
for $\tau$, and the denominators $1+b\ge1$, $1+\gamma\ge1$ give
local $C^2$ bounds and rational-point jets for $\Phi$. Every such
constant is a finite product, sum and quotient with a certified
positive denominator. Bounds on a larger fixed box supply moduli
while inner boxes are refined. At a computable, nonrational point,
rational-point evaluation plus these Lipschitz bounds gives the
same value precision by rational approximation inside the larger
box. No $H$ or derivative is applied to a raw box-step approximant.
$\square$

**Corollary 8.3 (the actual bounded successor target).** A rational
$L_\beta>0$ with $0\le\beta\le L_\beta$ almost everywhere can be
computed from the original names, without changing the calibration.
Indeed [SRO, Theorem 16.2] supplies a finite accepted global upper
certificate $U\ge N_d$ after a terminating fair search; take
$L_\beta=U+1$. Positivity and $L^\infty$ contraction of the same
original $P$ give $0\le Pb\le N_d<L_\beta$. Under (8.3) this
bound is unchanged. [SRO, Definition 17.2] additionally supplies the
exact scalar name of $N_d$, but the defect computation needs only
the accepted upper bound. Its loose $L_\beta$ is never substituted
for $1+N_d$ in an emission.

## 9. Certified original charts and effective mass exhaustion

**Lemma 9.1 (enumerated charts and a total inverse).** There is an
effective enumeration of certified rational boxes and cutoffs whose
inner boxes cover the rank-two set of $\Phi$ in $\Omega$. Each chart
has an injective coordinate map $\Psi=(\Phi,\pi):Q\to\mathbb R^4$,
where $\pi$ selects the two raw coordinates complementary to a
nonzero two-column minor of $D\Phi$. It has a computed determinant
lower bound and a total computable extension of its inverse.

*Proof.* All vector norms in this section are maximum norms and
matrix norms are induced row-sum norms. Enumerate closed rational
boxes $Q$ inside larger rational boxes compactly contained in
$\Omega$, rational invertible $4\times4$ matrices $A$, rational
$0<q_0<1/2$, the six choices of $\pi$, and finite precision requests.
Let $c_Q$ be the rational center, $r_Q$ its maximum half-side, and
let rational $M_2$ bound every second partial derivative of $\Psi$
on the larger box, using Theorem 8.2. Center derivative intervals
give a rational upper bound $\eta_Q$ for
$\|A^{-1}D\Psi(c_Q)-I\|_\infty$. Accept when

$$
\eta_Q+16\|A^{-1}\|_\infty M_2r_Q<q_0<1/2.
\tag{9.1}
$$

There are four entries per row and four coordinate increments, so
(9.1) certifies $\sup_Q\|A^{-1}D\Psi-I\|_\infty<q_0$.
Every test is finite. At any regular point choose a nonzero minor,
a rational matrix close enough to the derivative, and a sufficiently
small rational box containing that point in its interior. Bounds
from a fixed larger box stay fixed while the inner box shrinks.
Sufficient center precision then certifies (9.1). Thus accepted
boxes cover the regular set, without deciding any zero minor.

Set $R_Q(x)=A^{-1}\Psi(x)-x$ on $Q$. It is $q_0$-Lipschitz,
by integration on line segments in this convex box. Consequently
$\Psi$ is injective there. For every $x\in Q$,

$$
|\det D\Psi(x)|\ge d_Q:=|\det A|(1-q_0)^4>0.
\tag{9.2}
$$

For example, all eigenvalues of $A^{-1}D\Psi-I$ have modulus at
most $q_0$, and the determinant is their shifted product. Let
$C_Q^{\rm box}$ denote coordinatewise clamping to $Q$, and put

$$
\Lambda_Q(x)=A\{x+R_Q(C_Q^{\rm box}x)\}\quad(x\in\mathbb R^4).
\tag{9.3}
$$

For each $y$, the equation
$x=A^{-1}y-R_Q(C_Q^{\rm box}x)$ is a contraction on all
$\mathbb R^4$ with ratio $q_0$. It has a unique solution, and
$\Lambda_Q$ is a homeomorphism agreeing with $\Psi$ on $Q$.
Its inverse is Lipschitz with bound
$\|A^{-1}\|_\infty/(1-q_0)$. Starting at $x_0=0$, the exact
iterates have error at most
$q_0^n\|x_1-x_0\|_\infty/(1-q_0)$. A rational upper bound on
$\|x_1\|_\infty$ follows from one finite value enclosure.
If each evaluated update has error at most $\delta$, the additional
error is at most $\delta/(1-q_0)$, by the same contraction
recurrence. These explicit bounds give any requested inverse
precision in finite computation. Clamping is exactly computable;
the local evaluation it requests is supplied by Theorem 8.2.
The extension need not be differentiable across the clamping faces;
only its agreement with the smooth chart on the interior is used.

Within each accepted $Q$, enumerate rational inner boxes and
piecewise polynomial cutoffs $0\le\psi\le1$, equal to one on the
inner box and vanishing on a collar of $\partial Q$. The coordinate
construction (3.2) gives such $C^{10}$ cutoffs, with rational
coefficients, breakpoints and derivative bounds. Enumerating all
inner boxes makes their interiors cover each chart interior.
This proves the assertion. $\square$

**Theorem 9.2 (a terminating original mass cutoff).** The charts of
Lemma 9.1 give a sequence of rational piecewise polynomial weights
$w_j\ge0$, each supported inside its own chart, such that for any
rational $\rho>0$ one can find a finite $J$ and a rational upper
bound $\overline\rho_J<\rho$ for

$$
s_J=\sum_{j=1}^Jw_j\le1,\qquad
\rho_J=1-\int s_J\,dm.
\tag{9.4}
$$

This procedure supplies no assumed mass modulus for critical sets,
the axis, the source or infinity.

*Proof.* Enumerate the accepted chart/cutoff pairs as $\psi_j$ and
set

$$
w_j=\psi_j\prod_{i<j}(1-\psi_i),\qquad
s_J=1-\prod_{j\le J}(1-\psi_j).
\tag{9.5}
$$

All weights remain rational piecewise polynomials, with compact
support in their indicated chart. [FG, Theorem 4.1 and its proof]
gives rank $(b,\gamma)=2$ $m$-almost everywhere. The scalar
changes in (8.1) have nonzero derivatives at every finite pair,
so the same holds for $\Phi$. Also $m(\Omega)=1$. Every regular
point eventually belongs to an inner box on which some $\psi_j=1$.
Thus $s_J\uparrow1$ almost everywhere and $\rho_J\downarrow0$.
This reuses the actual-source analytic rank theorem, rather than
inferring full rank from dimensions.

The residual itself has a scalar name. If a raw approximant $H_0$
satisfies $\|H_0-h\|_2\le\delta$, then

$$
\left|\int s_J(|H_0|^2-h^2)\,d\mu\right|
 \le\delta(2+\delta),
\tag{9.6}
$$

since $0\le s_J\le1$ and $\|h\|_2=1$. Partition the finitely
many rational step boxes and polynomial pieces. The approximating
integral is exact rational polynomial integration, including complex
steps through $|H_0|^2$. A fair search over finite enumeration
prefixes and raw precisions tests whether the outward upper bound
for $1-\int s_Jh^2d\mu$ is less than $\rho$. Every finite test
terminates. Dominated convergence gives a finite successful prefix
with strict slack, and sufficient precision detects it. This proves
termination without assuming an effective rate for the qualitative
rank theorem. In particular no independently selected chart sheet
or conditional law is used. $\square$

## 10. Computed joint densities from the same original realization

**Definition 10.1 (targets used below).** A target $z$ in this section
is a real function with a computed rational bound $0\le z\le L_z$,
a raw global name of $hz$, and computed local $C^1$ bounds and value
precision maps on rational compact boxes in $\Omega$. These
conditions will be established for $z=\beta$ by §§8–9 and for the
actual bounded heat images by Theorem 12.1. They are not an extra
observation instrument or a general conditional-density oracle.

**Theorem 10.2 (total $L^1$ names of the original pair and moment
laws).** Under Definition 8.1, each target in Definition 10.1 has
jointly constructed global $L^1(\mathbb R^2,dy)$ density names
$f,q_z$ satisfying

$$
\Phi_*m=f(y)\,dy,\qquad
\Phi_*(zm)=q_z(y)\,dy,\qquad 0\le q_z\le L_z f.
\tag{10.1}
$$

The names are finite rational box steps with certified $L^1$ errors.
All contributions with the same $y$ are summed before division.

*Proof: local zero extensions and their constants.* For chart $j$
write $J_j(x)=|\det D\Psi_j(x)|$. On its closed box $Q_j$ form

$$
a_j^0(x)=\frac{w_j(x)h(x)^2}{J_j(x)},\qquad
c_j^0(x)=\frac{w_j(x)h(x)^2z(x)}{J_j(x)}.
\tag{10.2}
$$

They vanish on a collar of the boundary. Their zero extensions to
$\mathbb R^4$ are computable compactly supported Lipschitz functions
with computable rational bounds. Here are finite bounds sufficient
to make this assertion numerical. If every entry of $D\Psi_j$ is
bounded by rational $M_1\ge1$ and each second derivative by $M_2$,
Leibniz' determinant expansion gives
$|\partial_k J_j|\le96M_1^3M_2$; the determinant has constant sign
on the box. Together with (9.2),
$J_j^{-1}\le d_{Q_j}^{-1}$ and
$|\partial_k J_j^{-1}|\le96M_1^3M_2d_{Q_j}^{-2}$.

Bounds for $w_j$ and its first derivatives come from the finite
polynomial products (9.5). Bounds for $h,z$ and their first
derivatives were constructed in §8 or stipulated in Definition
10.1 and are established in Theorem 12.1 for its targets. Applying
the product rule in (10.2) now gives a rational bound $D_j$ for
each first derivative and a value bound. The zero extensions are
$4D_j$-Lipschitz in maximum norm: along any line their restriction
is absolutely continuous, with zero boundary traces, and the
interior derivative bound applies. For computation outside the box,
evaluate (10.2) at its clamped point; the boundary value is exactly
zero. This avoids an undecidable test of membership on a face.

For $Y=(y,t)\in\mathbb R^2\times\mathbb R^2$, put

$$
a_j(Y)=a_j^0(\Lambda_{Q_j}^{-1}Y),\qquad
c_j(Y)=c_j^0(\Lambda_{Q_j}^{-1}Y),
\tag{10.3}
$$

using the zero extensions. Lemma 9.1 gives total value precision
and a Lipschitz bound multiplied by
$\|A_j^{-1}\|_\infty/(1-q_{0,j})$. Support lies in the image
of the compact support of $w_j$ under the actual $\Psi_j$.
A rational product box containing that support is computed from
the original box bounds and local value bounds of $\Phi$; its
last two coordinates are the selected raw coordinates. No smooth
Jacobian for the global clamping extension is asserted or needed.
Where the density is nonzero, that extension agrees with the
original smooth chart.

*Proof: integration and sheet assembly.* Ordinary change of variables
on the interior of $Q_j$ gives

$$
f_j(y)=\int_{\mathbb R^2}a_j(y,t)\,dt,\qquad
q_{z,j}(y)=\int_{\mathbb R^2}c_j(y,t)\,dt
\tag{10.4}
$$

as densities of $\Phi_*(w_jm)$ and $\Phi_*(w_jzm)$. These
integrals have total $L^1$ names by explicit finite grid quadrature.
Indeed choose a rational support product $Y_j\times Z_j$, grid
maximum cell diameter $h_0$ and value precision $e_0$.
For a Lipschitz bound $L_0$, replacement by rational cell values
has uniform error at most $L_0h_0+e_0$ on the product. Integrating
the step function in the last two coordinates gives a finite
rational step function of $y$, with $L^1$ error at most
$|Y_j||Z_j|(L_0h_0+e_0)$. Outside the product both true and
approximating functions are zero. Choosing both mesh and precision
from this displayed bound yields any prescribed error in finitely
many operations. This constructs the integrals; it does not call
an unspecified quadrature service.

Set $f_J=\sum_{j\le J}f_j$, $q_{z,J}=\sum_{j\le J}q_{z,j}$.
Monotone limits $f=\sum_jf_j$ and $q_z=\sum_jq_{z,j}$ are the
full densities, because $s_J\uparrow1$ $m$-almost everywhere.
They concern exactly the same weighted original realization:

$$
\begin{gathered}
0\le q_{z,J}\le L_zf_J,\qquad
0\le q_z-q_{z,J}\le L_z(f-f_J),\\
\|f-f_J\|_1=\rho_J,\qquad
\|q_z-q_{z,J}\|_1\le L_z\rho_J.
\end{gathered}
\tag{10.5}
$$

Theorem 9.2 computes a sufficient $J$ for every requested tail
error; (10.4) computes the finite sums to the remaining error.
This proves total $L^1$ names. Overlapping source charts have been
weighted by (9.5), so no source mass is counted twice. Different
source sheets with equal $\Phi$ values contribute to the same
$f_J(y),q_{z,J}(y)$. They are not conditioned separately and then
averaged using an unrelated law. $\square$

## 11. Two-sided scalar certificates for the actual defect

**Theorem 11.1 (projection identity with a finite error budget).**
For every target of Definition 10.1 the scalar $\Delta(z)$ has a
total two-sided rational interval name. In particular, every
rational $\varepsilon>0$ gives a terminating construction of an
interval of width at most $\varepsilon$ containing the actual
$\Delta_{\rm next}$ for every finite positive named original
triple. This does not decide its sign.

*Proof: the completed conditional projection.* On
$\mathcal C_L=\{(f,q):f\ge0,\ 0\le q\le Lf\}$, define

$$
\mathcal P(f,q)=\begin{cases}q^2/f&f>0,\\0&f=q=0.\end{cases}
\qquad
I_z=\int_{\mathbb R^2}\mathcal P(f,q_z)\,dy.
\tag{11.1}
$$

The function $F_z=q_z/f$ where $f>0$, extended by zero elsewhere,
has a Borel version with $0\le F_z\le L_z$. For every bounded
Borel $v$ the same-source laws (10.1) give

$$
\int v(\Phi)z\,dm=\int v(y)q_z(y)\,dy
 =\int v(\Phi)F_z(\Phi)\,dm.
\tag{11.2}
$$

It follows that $Ez=F_z(\Phi)$ almost everywhere. Completion adds
only null modifications and does not change this $L^2$ class.
Orthogonal projection and the raw unitary $J_h$ give

$$
\Delta(z)=\|hz\|_2^2-I_z.
\tag{11.3}
$$

No pointwise computability of $F_z$ at zeros of $f$ is claimed.

*Proof: stability including the vertex.* On $\mathcal C_L$,

$$
|\mathcal P(f,q)-\mathcal P(g,r)|
 \le L^2|f-g|+2L|q-r|.
\tag{11.4}
$$

For positive first coordinates, integrate the derivatives
$\partial_f\mathcal P=-(q/f)^2$ and
$\partial_q\mathcal P=2q/f$ along the cone segment. Their bounds
are $L^2,2L$. If an endpoint is the vertex, take the segment limit;
$0\le\mathcal P(f,q)\le L^2f$ proves continuity there.

There is a sharper bound for the common tail (10.5):

$$
\left|I_z-\int\mathcal P(f_J,q_{z,J})\,dy\right|
 \le L_z^2\rho_J.
\tag{11.5}
$$

To verify both directions pointwise, write $(f,q)=(g,r)+(t,s)$
with $0\le r\le Lg$ and $0\le s\le Lt$. Weighted
Cauchy–Schwarz gives
$\mathcal P(g+t,r+s)\le\mathcal P(g,r)+\mathcal P(t,s)
\le\mathcal P(g,r)+L^2t$. For the other direction use
$r+s\ge r$ and, if $g>0$,

$$
\frac{r^2}{g+t}\ge\frac{r^2}{g}-L^2t.
\tag{11.6}
$$

The difference is $r^2t/[g(g+t)]\le L^2t$; if $g=0$, the
required lower bound is immediate. These arguments include zero
tails by continuity. Integrate with $\int t=\rho_J$.

*Proof: rational output and termination.* Compute finite rational
step approximants $\widehat f_0,\widehat q_0$ of $f_J,q_{z,J}$
with respective $L^1$ errors $e_f,e_q$, on a common finite rational
box partition. Put

$$
\widehat f=(\widehat f_0)_+,\qquad
\widehat q=\min\{\max(\widehat q_0,0),L_z\widehat f\},\qquad
\widehat I=\sum_C|C|\mathcal P(\widehat f_C,\widehat q_C).
\tag{11.7}
$$

This last number is rational, with zero summands when
$\widehat f_C=0$. Positive-part replacement does not increase
$e_f$. Clipping a number to $[0,L_z\widehat f]$ moves its error
relative to a point in $[0,L_zf_J]$ by at most the upper-endpoint
displacement. Thus the new moment error is at most $e_q+L_ze_f$.
Equations (11.4)–(11.5) give the explicit certificate

$$
|I_z-\widehat I|
 \le L_z^2\overline\rho_J+3L_z^2e_f+2L_ze_q=:e_I.
\tag{11.8}
$$

Every constant on the right is rational and available. For example,
choose $\overline\rho_J<\varepsilon/[24(1+L_z^2)]$,
$e_f<\varepsilon/[72(1+L_z^2)]$ and
$e_q<\varepsilon/[48(1+L_z)]$. Then $e_I<\varepsilon/8$.
The searches and finite sums producing these bounds terminate by
Theorems 9.2 and 10.2.

A raw step $V$ of error $\delta$ for $hz$ gives a rational
squared-norm enclosure centered at $\|V\|_2^2$, with radius
$\delta(2Q_V+\delta)$ for any computed rational
$Q_V\ge\|V\|_2$. Its width tends to zero as $\delta\to0$,
because the true norm is finite; rational upper bounds $Q_V$ may
be chosen within one of the computed norm. Refine until this
width is less than $\varepsilon/2$. Subtract $\widehat I$ and
enlarge both endpoints by $e_I$. The resulting interval contains
(11.3) and has width less than $\varepsilon$; intersecting with
$[0,L_z^2]$ is optional. Every test here is on finite rational
data and finitely many total-name replies.

For $z=\beta$, its raw name and local bounds are supplied by
Theorem 8.2 and its global bound by Corollary 8.3. Apply the
construction in the reference member and transport the scalar
by (8.3). This proves the stated all-parameter successor result.
No conditional density, lower bound for $f$, critical-set rate,
global bound on $\gamma$ or membership $\gamma\in D(K)$ was
supplied or assumed. $\square$

## 12. Complete positive certificates for original heat-factor failure

**Theorem 12.1 (total names for actual bounded continuation defects).**
For integers $p,q\ge0$ define, in the original member,

$$
\varphi_{p,q}=u^p\chi^q,\qquad
z_{p,q}=T_d\varphi_{p,q},\qquad
\delta_{p,q}=\Delta(z_{p,q}).
\tag{12.1}
$$

Every $\delta_{p,q}$ has a total two-sided scalar interval name
under Definition 8.1. The targets use the unchanged original heat,
and satisfy $0\le\varphi_{p,q},z_{p,q}\le1$.

*Proof.* Transport to the reference member at time $\tau$ by
(8.3). Theorem 8.2 gives local bounds and values for $\varphi$
from finite products; exponent zero means the constant one.
We first construct a global raw name for $h\varphi$, rather than
assuming multiplication by an unknown bounded field is an effective
operation on a raw name.

Use Theorem 9.2 to make $\rho_J$ as small as needed. On each of the
finitely many chart boxes supporting $s_J$, approximate
$\varphi$ uniformly by rational grid values with error at most
$\alpha$, clipping these values to $[0,1]$. The local derivative
bounds give a finite sufficient grid mesh and precision. Resolve
overlaps by a finite rational box partition; each selected grid
value approximates the same actual $\varphi$ on its cell. Call the
result $\varphi_0$ on this union. The compact piecewise polynomial
function $\theta=s_J\varphi_0$, zero elsewhere, satisfies
$0\le\theta\le1$ and

$$
\|h(\varphi-\theta)\|_2
 \le\alpha+\sqrt{\rho_J},
\tag{12.2}
$$

since $\varphi-s_J\varphi_0=s_J(\varphi-\varphi_0)
 +(1-s_J)\varphi$ and $(1-s_J)^2\le1-s_J$.
Multiplying a raw approximation $H_0$ for $h$ by $\theta$ adds
at most $\|H_0-h\|_2$. The finite product $H_0\theta$ is a
compact rational piecewise polynomial. Subdivide its rational cells
and approximate the polynomials uniformly there; their coefficient
sums on the bounded cells give finite derivative bounds. This
returns rational box steps with any desired further $L^2$ error.
Choose, for example, $\rho_J$ below the square of the allotted
error and $\alpha$, raw error and subdivision error below their
allotments. This is a total raw name of $h\varphi$.

[R, Theorem 12.4] now computes
$v=e^{-\tau H}(h\varphi)=h z_{p,q}$ globally. With
$0<L\le\tau$ as in (8.4), $\|h\varphi\|_2\le1$ gives

$$
v\in D(H^4),\qquad
\sum_{j=0}^4\|H^jv\|_2
 \le\sum_{j=0}^4j!L^{-j}.
\tag{12.3}
$$

Theorem 3.2 supplies a computed local $C^4$ bound for this actual
vector. Theorem 5.2, Corollary 5.4 and the quotient recurrence
(8.5) therefore supply local values and $C^1$ bounds for $v/h=z$.
Markov positivity and preservation of one supply its global bound
$L_z=1$. All hypotheses of Definition 10.1 have now been constructed
for these targets. Theorem 11.1 gives their scalar names, and (8.3)
returns the original defects. This argument never applies $H$ to
$h\varphi$ or to an approximant before spectral smoothing; no input
generator-domain hypothesis has been added. $\square$

**Theorem 12.2 (sound and complete positive-certificate
semidecision for OWG14.5 failure).** For each fixed original finite
positive named triple,

$$
E_{\rm rel}\widehat P\ne\widehat P E_{\rm rel}
\quad\Longleftrightarrow\quad
\exists p,q\ge0:\ \delta_{p,q}>0.
\tag{12.4}
$$

A fair enumeration of the scalar precision queries of Theorem 12.1,
accepting only an interval with strictly positive rational lower
endpoint, halts exactly when the left side holds. This is complete
for the full reference-space heat-factor condition, including a
failure for which $\Delta_{\rm next}=0$ or all local successor
minors vanish. It is a one-sided search, not a total zero decision.

*Proof.* The law $\nu=\Phi_*m$ is a probability on $[0,1]^2$.
Polynomials in its two coordinates are uniformly dense in
$C([0,1]^2)$ by Stone–Weierstrass, and continuous functions are
$L^2(\nu)$-dense for this finite Borel measure. Pullback by $\Phi$
identifies $L^2(\nu)$ with the actual completed-factor space,
modulo null sets. Thus the complex span of the monomials
$\varphi_{p,q}$ is dense in $\mathcal H_{\rm rel}$.

If every $\delta_{p,q}=0$, $P$ maps this dense span into the
closed subspace $\mathcal H_{\rm rel}$. Contractivity extends this
inclusion to all $\mathcal H_{\rm rel}$. Self-adjointness of the
original $P$ then makes its orthogonal complement invariant as
well: $\langle Px,y\rangle=\langle x,Py\rangle=0$ for
$x\perp\mathcal H_{\rm rel}$ and $y\in\mathcal H_{\rm rel}$.
Hence $EP=PE$. Conversely that commutation makes every defect
zero. Restricting to the reducing visible space gives exactly
[W, (14.5)]; since $\mathcal H_{\rm rel}\subset\mathcal O$,
invariance tested there is the same inclusion in full $L^2(m)$.
Injectivity of $\lambda\mapsto e^{-d\lambda}$ and its Borel
inverse, with the spectral domains in [W, Theorem 3.2], identifies
this condition with reduction by every original $T_t$. No inferred
local quotient generator or punctured core is used.

Enumerate all $(p,q,n)$ and compute the total interval for
$\delta_{p,q}$ with width at most $2^{-n}$. Each query terminates.
An accepted positive lower endpoint is sound. If a defect is
strictly positive, sufficiently small width forces such an endpoint,
so fair enumeration accepts. If all are zero, no interval can be
accepted and the search may continue indefinitely. A finite timeout
has no implication in either direction. $\square$

**Corollary 12.3 (intrinsic vector and necessary enlargement
consumer).** Under the published marked correspondence,

$$
Uz^o_{p,q}=z_{p,q},\qquad
z^o_{p,q}=\widehat P\left(\frac B{1+B}\right)^p
                     \mathsf R^q\Omega_{\rm cyc},\qquad
\delta_{p,q}=\|(I-E_{\rm rel})z^o_{p,q}\|^2.
\tag{12.5}
$$

The joint bounded functional calculus is legitimate because the
actual multipliers $B$ and $\mathsf R$ commute; this reuses the
published $\mathcal A_{\rm rel}=W^*(B,\mathsf R)$.
If a particular positive interval is obtained, every heat-reducing
completed sigma algebra containing $\mathcal S$ must contain the
actual $z_{p,q}$ modulo null sets, while $\mathcal S$ does not.
Indeed it contains $\varphi_{p,q}$ and must contain its original
heat image. The certified lower endpoint gives a positive rational
lower bound for its squared projection loss. This specifies a
necessary additional source relation for that certificate. It does
not supply a multiplication operator $M_{z_{p,q}}$ intrinsically
from the vector, a minimal enlargement, or a finite passive method
of acquiring that relation.

## 13. Numerical access, domains and unresolved signs

**Definition 13.1 (termination and charged operations).** The scalar
names in Theorems 11.1 and 12.1 are total relative to the original
parameter, coefficient and global norm names, including the full
resolvent/heat services constructed in [R]. Their finite work
includes all original supplier work, positive scalar refinements,
the general-time spectral polynomial degrees and action errors,
local graph constants and quotient bounds, chart precision tests,
cutoff products and rational partitions, raw mass integrations,
contraction iterations and their certified evaluation errors,
transformed density grids, common-cell assembly, clipping and the
norm and rational error arithmetic in (11.7)–(11.8).

The number of chart candidates, the size of the successful finite
cover, its mass precision, determinant bounds, inverse iterations,
box counts, bit lengths, degrees and grid sizes depend on the fixed
names and requested error. The proof gives termination separately
for each finite positive triple and precision; it gives no measured
runtime, parameter-uniform complexity, sample bound, total-resource
advantage or fixed finite memory bound. A positive-certificate
search in Theorem 12.2 has finite work only when it halts. Zero
compatible intervals never certify equality.

**Definition 13.2 (scope of the source result).** The new interface
removes a specific missing premise of a defect-based route: it
constructs same-source $L^1$ names and the two-sided scalar defect,
rather than assuming that qualitative regularity, a computable joint
law or an unevaluated local minor already computes conditional
projection. It covers all source sheets and all bounded dense-family
heat images. The calibration result supplies a target bound; the
jet result supplies local computed moduli; neither one separately
supplies this projection precision.

No scalar defect or successor minor has been numerically evaluated
here. No positive certificate, affirmative pair relation, exceptional
parameter set or actual parameter persistence interval is supplied.
Theorem 12.2 preserves both signs: if the original pair reduces heat,
all its tests are zero; if it fails, some positive test is eventually
certified relative to the stated names. Proving just
$\Delta_{\rm next}=0$ would concern $g_{2d}$ alone and would not
settle all the tests. These statements are ordinary conditional
mathematics under the inherited analytic suppliers, without fresh
Lean verification.

Every local differential estimate was restricted from the actual
full endpoint before use. Compact chart weights are integration
weights, not an asserted full graph or form core. The complete
source trace, $D(H)$, $D(K)$ and $D(K^{1/2})$ remain their original
domains; $\gamma$ need belong to none of these operator domains.
A globally bounded $\gamma$, full positive-cone recovery,
$\mathcal H_{\rm rel}=\mathcal O$, all invariant functions or raw
coordinate recovery have not been assumed. The omitted null sets
in chart integration do not remove the nonpolar source from its
form or process. No Friedrichs endpoint replaces $H$.

The exact entire word law supplies the published tuple and the
vector interpretation (12.5). It does not furnish the numerical
model names through a finite record. Chart evaluation, raw norm
requests and convolution are mathematical computations, not passive
point or derivative sensors. Every original history, memory, action,
clock, calibration and joint provenance remains unchanged, including
all four labels and the initial $2d$ lead-in. No reset, source pause,
new preparation or readout is introduced. Full source-family mutual
recovery of spatial structure, time/continuation, boundary and memory,
its lawful composition, intrinsic multiplier recovery, finite
acquisition and their costs remain unresolved.

## 14. Reused mathematics and the source-specific deduction

**Definition 14.1 (provenance and literature boundary).** The result
of §§8–12 is a `repo-derived` conditional composition: original
full-domain transport and general-time graph estimates construct
local chart data; the actual rank theorem and computed raw masses
make their exhaustion effective; summing the same-source chart
moment densities before division gives (11.8), consumed by the
successor and the complete bounded heat-test family. The projection,
contraction, change-of-variables, perspective and polynomial-density
facts are mature intermediates. No worldwide novelty is asserted.

| Reused source | Exact use and boundary |
| --- | --- |
| [W, Theorems 3.2, 5.2, 13.1 and Definition 14.2] | Original visible heat with its spectral domains, full maximal-domain/trace/clock transport, actual multiplier factor and the unpaid heat-reduction condition. The finite joint laws alone give no heat closure. |
| [FQ, Theorem 2.1], [FG, Theorem 4.1 and its proof] | Exact transport of the original $\gamma$, and rank two almost everywhere for this actual family. These facts do not name a conditional density or prove successor nonfactorization. |
| [R, Theorems 12.2–12.4], [SRO, Theorem 16.2 and Definition 17.2] | Full-resolvent, arbitrary named-time raw heat/source names, global upper certificates and exact original calibration. Neither supplies free passive access or assumes $N_d=s_d$. |
| This volume, Theorem 3.2, (4.7), Theorem 5.2 and Corollary 5.4 | A computed full-domain local graph constant, general positive-time graph bounds, finite jet extraction and a derived compact positive denominator. These are reused rather than recounted as new regularity results. |
| `D5/S3/ConceptDynamics/Prediction/ConditionalExpectationOptimality.lean`, `conditional_expectation_minimizes_mean_square_error`; `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/OriginalErasureComparison.lean`, private `norm_square_integral` and `projection_square_bound` | Existing projection optimality and squared-error foundations, including private results. They do not construct the original-source density or precision name. No duplicate Lean statement is added. |
| Pinned mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679`, `MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean` and `Basic.lean` [MLCE] | `condExpL2`, its norm contraction, self-adjoint inner-product identity and `MemLp.condExpL2_ae_eq_condExp'` are noncomputable conditional-projection foundations. Reading them supplies no executable disintegration or fresh kernel verification. |
| Ackerman–Freer–Roy, *On the computability of conditional probability*, arXiv:1005.3014v2, introduction and §8 [AFR] | `literature-attested`: a computable joint law alone need not supply computable conditional distributions. The explicit charts, $L^1$ names and bounded-cone error proof here are the additional construction; no unrestricted conditioning algorithm is invoked. |
| Boyd–Vandenberghe, *Convex Optimization*, §3.1.5 and §3.2.6 [BV] | `literature-attested`: quadratic-over-linear convexity and the perspective construction. The two-sided restricted-cone and common-tail bounds needed for this precision map are proved in (11.4)–(11.8), with every numerical error shown. |

The source-specific claim is the proved precision/certificate
interface under these hypotheses, not an end-to-end numerical
producer or a performed query. Bounded immutable-source and library
reuse checks identify the above dependencies; they establish no
external priority. The actual successor sign and the original
full heat-factor answer remain the unresolved source relations of
Definition 13.2.

[MLCE]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean
[AFR]: https://arxiv.org/html/1005.3014v2
[BV]: https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf

## 追加锚（本行以下为增补区）

## 15. Finite-order graph constants for bracketed source consumers

**Definition 15.1 (reference inputs and finite order).** Retain the
entire reference endpoint and numerical services of §§1–5 and §8,
but take a rational interval $J=[L,U]\Subset(0,\infty)$ as input,
not a name of a selected time in it. Put $v_t=hg_t$ as in (4.5).
The positive rational $\ell<D_0$ is produced by (4.2). Local boxes
are $Q\Subset Q^+\Subset\Omega=\{x^2+y^2>0\}$. The complement
of $\Omega$ is raw and $m$ null; no estimate across that complement
or across the source is intended. An integer $k\ge0$ specifies
one finite requested order. All graph vectors below are actual
full-domain vectors, never differentiated step approximations.

**Theorem 15.2 (constructed constants at every finite order).**
For each such $k,Q,Q^+$ the coefficient services and finite
rational operations produce $C_{Q,k}>0$ such that, with
$p=k+2$,

$$
\|u\|_{C^k(\overline Q)}
 \le C_{Q,k}\sum_{j=0}^{p}\|H^ju\|_2
 \qquad(u\in D(H^p)).
\tag{15.1}
$$

Consequently they produce rational bounds $M_{Q,k}(L)$ and
$D_{Q,k}(L)$ for

$$
\begin{gathered}
\|h\|_{C^k(\overline Q)}\le C_{Q,k},\qquad
\sup_{t\in J}\|v_t\|_{C^k(\overline Q)}\le M_{Q,k}(L),\\
\|v_t-v_s\|_{C^k(\overline Q)}
 \le D_{Q,k}(L)|t-s|\qquad(s,t\in J).
\end{gathered}
\tag{15.2}
$$

These include arbitrary fixed higher orders, rather than only
third point jets or the fourth-order bound of Theorem 3.2.

*Proof.* Here is an explicit extension of that theorem's numerical
recurrence. Set $n=2p=2k+4$. Replace the nine nested boxes in
Definition 3.1 by $n+1$ equally interpolated boxes, with
$Q_0=Q^+$ and $Q_{n+1}=Q$. Replace the exponent $10$ in (3.2)
by $n+2$. The resulting rational polynomial transitions are
$C^{n+2}$, compactly supported in their indicated outer boxes;
compute all derivative coefficient sums through order $n$.
Use (3.3)–(3.4) with those sums to obtain $K_i$ for
$1\le i\le n+1$ and $D_\chi$ for the last cutoff through order
$n$. Put

$$
J_\chi=\binom{n+4}{4}2^n\max(1,D_\chi),\qquad
V_*=16\max_{0\le j\le n-2}G_j.
\tag{15.3}
$$

Theorem 2.2 constructs every $G_j$ here, including its differentiated
Green tail. Keep $A_*,L_A,\lambda,\Lambda,V_0$ from (2.13)–(2.14).
The bound $A_*$ holds for derivatives of every order: entries of
$\mathsf A$ have degree at most two, so higher derivatives vanish.
Compute $C_{1,i},C_{2,i}$ by (3.8), (3.11) with the new cutoffs.
For $0\le j\le n-2$ use

$$
n_j=\binom{j+3}{3},\qquad
R_j=(2^j-1)(16A_*+V_*).
\tag{15.4}
$$

Set $T_{j,0}=1$ for $0\le j\le p$ and
$T_{j,1}=2C_{1,1}$ for $0\le j\le p-1$. For $2\le i\le n$
and $0\le j\le p-\lceil i/2\rceil$ calculate

$$
T_{j,i}=[1+n_{i-2}C_{2,i}(R_{i-2}+1)]T_{j,i-1}
                       +n_{i-2}C_{2,i}T_{j+1,i-2}.
\tag{15.5}
$$

Every right-side entry is already defined. For $u_j=H^ju$,
$H_{\rm loc}u_j=u_{j+1}$ for $j<p$, by the full-domain test
(3.6). The energy and difference-quotient tests (3.7)–(3.12)
therefore give the first two induction steps. Differentiating
that same equation $i-2$ times gives exactly (3.14): its
commutator contains derivatives of $u_j$ only through order
$i-1$, bounded by $R_{i-2}N_{i-1}(u_j)$, and at most
$n_{i-2}$ second-derivative lists are needed. Thus (3.15) proves
(15.5) and

$$
N_i(u_j;Q_i)\le T_{j,i}\sum_{a=0}^p\|u_a\|_2.
\tag{15.6}
$$

The norm of $u_{j+1}$ on $Q_{i-1}$ is bounded by its already
estimated norm on the larger $Q_{i-2}$. At the last step only
$u_p\in L^2$ is required. The qualitative local maximal-domain
regularity used to start these weak tests is precisely the one
checked in Theorem 3.2; subsequent derivatives are supplied by
the difference-quotient induction, with the displayed constants.
No extra regularity constant is imported.

For $w=\chi_{n+1}u$, Leibniz gives $N_n(w)\le J_\chi N_n(u;Q_n)$.
In the same unitary Fourier convention as (3.18),

$$
\|(1+|\xi|^2)^{n/2}\widehat w\|_2\le5^{n/2}N_n(w).
\tag{15.7}
$$

For $|\alpha|\le k$, the remaining Cauchy–Schwarz integral
is bounded by $\int(1+|\xi|^2)^{-(n-k)}d\xi$.
Here $n-k=k+4\ge4$, so it is at most $\pi^2/6$ as evaluated
in §3. After inverse Fourier normalization its square root is
less than one. Fourier inversion consequently gives (15.1) with

$$
C_{Q,k}=5^pJ_\chi T_{0,n}.
\tag{15.8}
$$

This also proves existence of the continuous derivatives in
(15.1), by the same Fourier $L^1$ argument for each derivative.
Every displayed number is rational and constructed.

Finally set

$$
\begin{aligned}
M_{Q,k}(L)&=\frac{C_{Q,k}}\ell
 \sum_{j=0}^p[j!L^{-j}+(j+1)!L^{-j-1}],\\
D_{Q,k}(L)&=\frac{C_{Q,k}}\ell
 \sum_{j=0}^p[(j+1)!L^{-j-1}+(j+2)!L^{-j-2}].
\end{aligned}
\tag{15.9}
$$

Spectral smoothing gives the first graph bounds as in (4.7).
For differences use
$H^j(v_t-v_s)=-\int_s^tH^{j+1}(H+1)e^{-rH}\xi_{\rm src}\,dr$
in $L^2$, with orientation reversed when necessary. The factorial
spectral bound on $r\ge L$ gives the second sum. Apply (15.1)
to these actual graph vectors. Also $Hh=0,\|h\|_2=1$.
This proves (15.2) without assuming any graph derivative of
$\xi_{\rm src}$. $\square$

## 16. Finite jets and quotient moduli uniform on a time bracket

**Theorem 16.1 (finite-order weak extraction and time transport).**
For every fixed integer $R\ge0$, the reference services give
rational-point jets through order $R$ of $h,g_{t_0}$ at every
rational $t_0\in J$, to any requested precision. They also
construct local spatial bounds through every fixed order and
rational constants $W_{Q,R}(L)$ such that

$$
\max_{|\alpha|\le R}\sup_{\overline Q}
 |D^\alpha(g_t-g_s)|\le W_{Q,R}(L)|t-s|
 \qquad(s,t\in J).
\tag{16.1}
$$

Thus values, derivative intervals and finite algebraic consumers
can be certified simultaneously for every $t\in J$. This result
needs neither a name of the unknown time nor original parameter
or coordinate sensors.

*Proof.* Generalize the exact weak kernel (5.1), rather than
postulating higher pointwise access. Put $a=R+2$ and

$$
\zeta_R(t)=c_R(1-t^2)^a\mathbf1_{[-1,1]}(t),\qquad
c_R=\left[2\sum_{l=0}^a\frac{(-1)^l\binom al}{2l+1}\right]^{-1}.
\tag{16.2}
$$

The denominator is the integral of a nonnegative, nonzero
polynomial on $[-1,1]$, hence positive rational. The extension
is $C^{R+1}$. Its derivatives needed for integration by parts
have zero boundary traces. For $0\le j\le R$ compute

$$
b_{R,j}=c_R\sum_{l=\lceil j/2\rceil}^{a}
               \binom al\frac{(2l)!}{(2l-j)!},\qquad
L_{R,\alpha}=4\prod_{i=1}^4b_{R,\alpha_i}.
\tag{16.3}
$$

The product kernel in four coordinates has derivative $L^2$
norm at most $L_{R,\alpha}$. Given a constructed $C^{R+1}$
bound $M$ for an actual raw vector on a surrounding box, a
raw step $U$ of error $\delta$ gives exactly as in (5.5)–(5.6)

$$
\left|D^\alpha u(x)-
 \int D^\alpha\kappa_{R,\epsilon}(x-y)U(y)d\mu(y)\right|
 \le4\epsilon M+L_{R,\alpha}\epsilon^{-2-|\alpha|}\delta.
\tag{16.4}
$$

Choose rational $\epsilon$ inside the box with the first term
below half the allotted error; then choose $\delta$ for the
second term. Each integral is an exact finite polynomial integral
on rational box intersections. Theorem 15.2 at order $R+1$
constructs $M$ for $h,v_{t_0}$. This proves the raw jet service.

A compact lower bound $l_Q>0$ for $h$ is produced by Corollary
5.4; for box unions use the minimum of finitely many such bounds.
On a fixed surrounding box let $M_h$ bound derivatives of $h$
through order $R$, and let $M_v,D_v$ be (15.9) at order $R$.
Define $B_0=M_v/l_Q$, $W_0=D_v/l_Q$, and for $1\le j\le R$

$$
\begin{aligned}
B_j&=\max\left\{B_{j-1},
 \frac{M_v+M_h\sum_{i=1}^j\binom jiB_{j-i}}{l_Q}\right\},\\
W_j&=\max\left\{W_{j-1},
 \frac{D_v+M_h\sum_{i=1}^j\binom jiW_{j-i}}{l_Q}\right\}.
\end{aligned}
\tag{16.5}
$$

Leibniz in $v_t=hg_t$ proves the $B_j$ bounds. Apply the same
identity to $v_t-v_s=h(g_t-g_s)$ and (15.2) to prove (16.1)
with $W_{Q,R}=W_R$. The multiindex coefficient sum at fixed
length $i$ is $\binom ji$, which justifies these scalar recurrences.
Point jets of the quotient are computed in increasing order by
(5.7), refining until the positive denominator and required widths
are certified. No derivative of an approximate raw step is used.

For example, if a center jet interval at $x_0,t_0$ has radius $e$,
then its value anywhere in a cell of maximum coordinate radius
$\rho$ and anywhere in $J$ has extra radius

$$
4B_{R+1}\rho+W_R(U-L)
\tag{16.6}
$$

for every derivative of length at most $R$, using bounds on a
fixed larger box. This is an explicit uniform modulus. Finite
products, reciprocal expressions with certified positive
denominators, and declared cutoff derivatives can now be evaluated
by interval arithmetic with (16.6). Bounds stay fixed on the
larger box while cells and brackets shrink. The construction is
uniform over a given rational bracket; it asserts no uniform cost
as $L\downarrow0$, the box approaches the axis, or $R\to\infty$.
$\square$

## 17. Consumers and source boundary of the higher-order supplier

**Definition 17.1 (scope and attribution).** The new source-specific
supplier is (15.8)–(16.6). Its finite-order graph recurrence extends
the numerical weak tests already proved in §3, consumes arbitrary
finite differentiated Green majorants from Theorem 2.2, and keeps
the exact source vector of [R, Theorems 12.2–12.4]. Its consumers
are finite recursive compact-energy trees and quantitative local
charts in [FQ, §§9–12]. Those consumers need higher orders depending
on their declared syntax; no single fixed third-jet service suffices.
The classical difference-quotient, Leibniz, spectral, Fourier and
convolution methods have the precedents and hypotheses checked in
Definition 7.3. Here their explicit constants and the bracket
transport are `repo-derived` deductions for this full source; no
new general elliptic theorem or worldwide priority is claimed.

Only the reference coefficients $(1,1)$ and rational trial times
are numerical inputs. The full original transport is still (8.3),
including its maximal domain, both complex coefficients, zero line,
form, trace, entrance and calibration. In a passive application
$\tau=a^2d/\eta$ lies in a statistically certified bracket; (15.2)
and (16.1) apply to every time in that bracket. They do not turn
$\tau$ or $a,\eta,d$ into supplied exact scalar names. The original
$e$-start, first read $2d$, later gaps $d$, four labels and conditional
noise remain intact. Numerical reference coordinates are proof
and computation variables, never readings of the realized path.
No jet query has been numerically executed here and no new Lean
verification is asserted. The finite-order supplier changes none
of the distinct successor-sign and old-factor questions of §13.

## 追加锚（本行以下为增补区）
