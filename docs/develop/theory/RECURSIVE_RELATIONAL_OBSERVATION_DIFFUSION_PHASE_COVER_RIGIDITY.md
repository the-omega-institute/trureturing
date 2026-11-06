# Full-source recovery and finite native phase covers

## 1. The common source and the native interface

**Definition 1.1 (the inherited full endpoint).** The source in this
volume is the single original conservative diffusion of
[the endpoint appendix, §112](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX.md)
and [Appendix II, §§115–116](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md).
Write these suppliers as [E] and [S], and write
[Native free diffusion descent, §§7–10](FIB_NATIVE_FREE_DIFFUSION_QUOTIENT_RIGIDITY.md)
as [N]. Their objects, without a change of units or extension, are

$$
\begin{gathered}
G=H^1\times\mathbb R,\quad e=(0,0,0,0),\quad
(x,y,z,w)(x',y',z',w')=(x+x',y+y',z+z',w+w'+xy'),\\
d\mu=dx\,dy\,dz\,dw,\quad
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\quad L=-\sum_{j=1}^3X_j^2,\\
L\Gamma=\delta_e,\quad \deg\Gamma=-3,\quad
a,\eta>0,\quad g_c=16\sqrt{a\eta},\\
S_{\min}=(aL-\eta\partial_w^2-g_c\Gamma)
                   |_{C_c^\infty(G\setminus\{e\};\mathbb C)}.
\end{gathered}
\tag{1.1}
$$

The field $\Gamma$ is the original unit-source Green field, not an
adjustable attraction. Let $h$ be its supplied coefficient-positive
normalized zero state. The symbols $A,C$ mean exactly the maximal-domain
coefficients of [E, (112.1)–(112.5)], including their normalization;
$c_h=C(h)>0$ and $\rho=A(h)/C(h)$. In particular the Friedrichs
operator $F$ has $D(F)=\{C=0\}$, the closed minimal domain has
$A=C=0$, and the actual full operator is

$$
\begin{gathered}
D(H)=\{u\in D(S_{\min}^*):A(u)=\rho C(u)\},\quad Hu=S_{\min}^*u,
\quad H\ge0,\quad\ker H=\mathbb Ch,\quad H\ne F,\\
m=h^2\mu,\quad m(G)=1,\quad J_hv=hv,\quad
K=J_h^{-1}HJ_h,\quad T_t=e^{-tK}.
\end{gathered}
\tag{1.2}
$$

The entire complex form is retained. Explicitly, $\mathscr V_0$ is
the closure of $C_c^\infty(G\setminus\{e\};\mathbb C)$ in the norm
given by $\|v\|_{L^2(m)}^2+\mathscr E[v]$, and

$$
\begin{gathered}
\mathscr V=\mathscr V_0\dotplus\mathbb C1,\qquad
\mathscr E[v,u]=\int_Gh^2\left(
 a\sum_{j=1}^3\overline{X_jv}X_ju+
 \eta\overline{\partial_wv}\partial_wu\right)d\mu,\\
D(K)=\{v\in\mathscr V:hv\in D(S_{\min}^*),\ A(hv)=\rho C(hv)\}.
\end{gathered}
\tag{1.3}
$$

These are [S, (115.14)–(115.17)], with the derivatives on the constant
summand equal to zero. The semigroup is selfadjoint and conservative
in $L^2(m)$. Off $e$, $h$ is smooth and strictly positive. We use the
legitimate source start $\mathbb P_e$ of [S, Theorem 116.4], and its
original elapsed time $t$. A properly exceptional set $N$ is $m$-null
and excludes $e$. No ordinary value $h(e)$ is assigned. Contact with
$e$ is followed by conservative continuation with zero ordinary
residence time, rather than killing or holding. Hilbert pairings are
antilinear in the first argument.

**Definition 1.2 (preparation and current native display).** Fix
arbitrary $0<Z<1$, put $r=1-Z$, $H_{\rm n}=r/2$, and fix
$k_0\in(0,H_{\rm n})$, phases $\alpha_0,\beta_0$ and the original
preparation rotations $\delta_{ij}$. All are known fixed preparation
data. Define

$$
\begin{gathered}
\mathcal S=\{-k_0<x<H_{\rm n}-k_0\},\quad
c_0=\tfrac12-k_0/r,\quad \ell=2\pi r,\\
\vartheta(p)=(y/2,c_0y-w/r),\qquad
\Psi(p)=(k_0+x,[\alpha_0+y/2]_{2\pi},
                         [\beta_0+c_0y-w/r]_{2\pi})\quad(p\in\mathcal S).
\end{gathered}
\tag{1.4}
$$

This is [N, (7.3)], with its real $z$ coordinate erased. With
$u(s)=(\cos s,\sin s)$, the complete original signed doubled output
menu is, in the same edge order,

$$
\begin{aligned}
Y_{01}&=2\sqrt{k(H_{\rm n}-k)}u(\delta_{01}+\alpha),&
Y_{02}&=2\sqrt{Zk}u(\delta_{02}+\beta),\\
Y_{03}&=2\sqrt{k(H_{\rm n}-k)}u(\delta_{03}+\alpha),&
Y_{1,13}&=2\sqrt{k(H_{\rm n}-k)}u(\delta_{1,13}-\alpha),\\
Y_{3,13}&=2\sqrt{k(H_{\rm n}-k)}u(\delta_{3,13}-\alpha).
\end{aligned}
\tag{1.5}
$$

The probabilities remain $(k,H_{\rm n}-k,Z,H_{\rm n}-k,k)$.
Equation (1.5) reuses [N, (7.8)] and its original holonomy and native
continuation suppliers. It changes neither signs nor preparation
rotations and uses no whitening.

**Proposition 1.3 (the precise static inverse).** On the open native
slab, the ten outputs and the triple $(k,[\alpha],[\beta])$ determine
each other, with the fixed preparation data. They do not determine a
full point of $G$.

Proof. The forward map is (1.5). Conversely,

$$
k=|Y_{02}|^2/(4Z),\qquad
[\alpha]=[\arg Y_{01}-\delta_{01}]_{2\pi},\qquad
[\beta]=[\arg Y_{02}-\delta_{02}]_{2\pi}.
\tag{1.6}
$$

Both amplitudes used for arguments are nonzero because
$0<k<H_{\rm n}$ and $Z>0$. Arguments mean circle-valued arguments,
not chosen real lifts. Every $z\in\mathbb R$ gives the same triple
when the other coordinates are fixed. At a wall the first amplitude
vanishes, so this inverse is asserted only on the open slab. $\square$

## 2. Finite phase sheets and lawful continued use

**Definition 2.1 (every finite-index lattice and both outside rules).**
Let $L_{\rm ph}\le(2\pi\mathbb Z)^2$ be any subgroup of finite index
$d\ge1$, without a rectangular-lattice assumption. Put

$$
\mathbb T_L=\mathbb R^2/L_{\rm ph},\quad
\mathcal M_L=(0,H_{\rm n})\times\mathbb T_L,\quad
\psi_L(p)=(k_0+x,[\vartheta(p)]_L)\quad(p\in\mathcal S).
\tag{2.1}
$$

The two global standard Borel observation spaces and maps are

$$
\begin{array}{ll}
\mathcal B_L^0=\mathcal M_L\sqcup\{\bot\},&
\chi_L^0(p)=\begin{cases}\psi_L(p)&p\in\mathcal S,\\\bot&p\notin\mathcal S,\end{cases}\\[3pt]
\mathcal B_L^+=\mathcal M_L\sqcup(\{\mathrm{out}\}\times(G\setminus\mathcal S)),&
\chi_L^+(p)=\begin{cases}\psi_L(p)&p\in\mathcal S,\\(\mathrm{out},p)&p\notin\mathcal S.\end{cases}
\end{array}
\tag{2.2}
$$

The wall points belong to the outside part. The bottom symbol means
current unavailability; it is not a held last value or an absorbing
state. The second rule discloses the exact current outside point.
In both rules the source continues on all of $G$, can leave and
reenter the slab, and starts at
$b_0=\chi_L^\sigma(e)=(k_0,[0]_L)$, $\sigma\in\{0,+\}$.

**Proposition 2.2 (what the sheet adds and what it leaves in a fiber).**
The map from $\mathcal M_L$ to the native triple, obtained by reducing
phases modulo $2\pi$ and adding $(\alpha_0,\beta_0)$, is a $d$-sheet
cover. Fixing a Borel section of the ordinary torus that takes zero
to zero identifies a cover point with the native triple and one element of
$(2\pi\mathbb Z)^2/L_{\rm ph}$. These data recover the cover point in
both directions, including the neutral sheet at the source. They
leave an arbitrary real $z$ and infinitely many real phase lifts.

Proof. The projection is the quotient by the finite group
$(2\pi\mathbb Z)^2/L_{\rm ph}$. A half-open fundamental square with
zero as a corner supplies the normalized Borel section; subtraction
of that representative gives its unique
group class. This section need not be continuous. More explicitly,
if $[u,v]_L$ represents the cover phase and $k\in(0,H_{\rm n})$,
its full source fiber is exactly

$$
\left\{\left(k-k_0,\ 2(u+\lambda_1),\ z,
 r\{2c_0(u+\lambda_1)-v-\lambda_2\}\right):
 (\lambda_1,\lambda_2)\in L_{\rm ph},\ z\in\mathbb R\right\}.
\tag{2.3}
$$

Substituting into (1.4) proves both inclusions and surjectivity.
The outside fibers of $\chi_L^+$ are singletons; the bottom fiber of
$\chi_L^0$ is the entire complement of the slab. $\square$

**Proposition 2.3 (the actual command square and its domain).**
Use the original relative commands $\gamma=(a_c,b_c)$, starting at
$(0,0)$ and absolutely continuous or piecewise $C^1$ as in
[N, Definition 1.2 and Proposition 7.2]. Write
$A=a_c(T)$, $B=b_c(T)$ and $J=\int_0^T a_c\,db_c$.
The same chronological triple $(A,B,0,J)$ updates a full point by
right multiplication and a cover point by

$$
\begin{gathered}
(x,y,z,w)\longmapsto(x+A,y+B,z,w+J+xB),\\
(k,[\theta_1,\theta_2]_L)\longmapsto
\left(k+A,\left[\theta_1+B/2,
 \theta_2+(\tfrac12-k/r)B-J/r\right]_L\right).
\end{gathered}
\tag{2.4}
$$

Their entire common refusal domain is

$$
k+\min_{[0,T]}a_c>0,\qquad k+\max_{[0,T]}a_c<H_{\rm n}.
\tag{2.5}
$$

On that domain, source update followed by $\psi_L$, cover update,
and native update followed by (1.5) agree on their common images.
This agreement persists under every finite lawful concatenation and
for every prefix. It is an algebraic interface correspondence, not
an identification of native control with the stochastic semigroup.

Proof. Substitute the first line of (2.4) into $\vartheta$.
The second phase increment is
$c_0B-(J+xB)/r=(1/2-k/r)B-J/r$. Adding an element of
$L_{\rm ph}$ before the update adds the same element afterwards, so
the cover update is well-defined even for mixed lattices. At every
prefix the height is $k+a_c(t)$, proving (2.5). For consecutive
triples the product is

$$
(A+A',B+B',0,J+J'+AB').
\tag{2.6}
$$

The coefficient of $B'$ after the first height update contributes
$-AB'/r$, precisely the cross term of (2.6). The concatenation
domain is the first guard intersected with the inverse image of the
second guard. Induction proves the assertion for all finite scripts,
with no endpoint-only relaxation of guards. The empty command has
$A=B=J=0$ and is the identity. $\square$

**Definition 2.4 (installation and retained data).** There is one
mathematical source path $\mathsf Z\sim\mathbb P_e$. Space means its
current $p\in G$; Time means the actual semigroup clock $t$; Boundary
means (1.5) on the native slab; Memory here means the current
$d$-valued sheet relative to the fixed section. The cover record is
an ideal additional current observation, not a consequence of
measuring the ten numbers once. A service returning
$\chi_L^\sigma(\mathsf Z_t)$ would have to be installed and coupled
to this same source. Formulae (1.6), (2.3) and (2.4) compute views or
updates from supplied data; they do not install that service, measure
windings, or obtain $J$. Retaining a cover point and an actually
supplied lawful command makes its update callable by (2.4). No
unobserved past, hidden $z$, source-dependent advice, or future path
is included in this retained record.

## 3. Direct obstruction on every finite cover

**Theorem 3.1 (full-source fixed Markov recovery fails).** For every
$a,\eta>0$ and every native preparation in Definitions 1.1–1.2, for
every finite-index $L_{\rm ph}\le(2\pi\mathbb Z)^2$, and separately
for each $\sigma\in\{0,+\}$, put $\chi=\chi_L^\sigma$ and
$\mathcal B=\mathcal B_L^\sigma$. There is no Borel probability
kernel $\Lambda:\mathcal B\rightsquigarrow G$ and conservative
time-homogeneous Borel Markov semigroup $(Q_t)_{t\ge0}$ on
$\mathcal B$ satisfying all of

$$
\begin{gathered}
\Lambda_b(\chi^{-1}\{b\})=1\quad\hbox{for every }b\in\mathcal B,
\qquad \Lambda_{b_0}=\delta_e,\\
(\Lambda T_tf)(b)=(Q_t\Lambda f)(b)
\quad\hbox{for every }t\ge0,\ b\in\mathcal B,
\ f\in B_b(G;\mathbb C).
\end{gathered}
\tag{3.1}
$$

Here $T_t$ is the legitimate full source transition kernel of
Definition 1.1, and $B_b$ denotes all bounded complex Borel functions.
The link is one fixed kernel, with no density, continuity, finite
support or computation restriction. The time in both semigroups is
the same original elapsed time. In particular the result includes
$d=1$, the bare current native display, under each outside rule.

Proof. Fix either outside rule and suppose (3.1). The proof has four
source-specific steps.

First, source anchoring forces the invariant disintegration. For
bounded Borel $g$ on $\mathcal B$, fiber support gives
$\Lambda(g\circ\chi)=g$. Evaluating (3.1) at $b_0$ gives, as
probability measures,

$$
T_t(e,\cdot)=Q_t(b_0,\cdot)\Lambda,\qquad
Q_t(b_0,\cdot)=\chi_*T_t(e,\cdot).
\tag{3.2}
$$

Use the actual source resolvent [S, (116.14)]. With

$$
b_\lambda=1-\lambda h^{-1}(F+\lambda)^{-1}h,\quad
d_\lambda=\int b_\lambda\,dm,\quad
\zeta_\lambda=\lambda\int_0^\infty e^{-\lambda t}T_t(e,\cdot)\,dt,
\tag{3.3}
$$

that supplier states $\zeta_\lambda=(b_\lambda/d_\lambda)m$,
$0\le b_\lambda\le1$, $d_\lambda>0$,
$b_\lambda\to1$ in $L^2(m)$ and $d_\lambda\to1$ as
$\lambda\downarrow0$. The last two limits also follow directly by
applying the spectral theorem to
$1-b_\lambda=\lambda h^{-1}(F+\lambda)^{-1}h$ and
$\ker F=0$. No positive spectral gap is required. The use of $F$
here is exactly the supplied resolvent formula for the full source,
not replacement of $H$ by $F$.

Integrating (3.2), and writing $\nu_\lambda=\chi_*\zeta_\lambda$,
gives $\zeta_\lambda=\nu_\lambda\Lambda$. For the total variation
norm of signed measures,

$$
\|\zeta_\lambda-m\|_{\rm var}
\le\frac{\|b_\lambda-1\|_{L^1(m)}+|1-d_\lambda|}{d_\lambda}
\longrightarrow0.
\tag{3.4}
$$

Pushforward and probability kernels contract this norm. Passing to
the limit proves

$$
\nu=\chi_*m,\qquad m=\nu\Lambda.
\tag{3.5}
$$

Together with fiber support, (3.5) is the disintegration of the joint
law $(\chi,\operatorname{id})_*m$. For example, on rectangles its
value is $\int_B\Lambda_b(A)\,\nu(db)$ because $\chi(p)=b$
$\Lambda_b$-almost surely. Thus the link has been identified on
the relevant measure class without assigning countable weights to
the continuous $z$ fibers in (2.3).

Second, this disintegration reduces the full semigroup. Let
$U:L^2(\nu)\to L^2(m)$ be $Ug=g\circ\chi$. It is an isometry;
Jensen and (3.5) extend $\Lambda$ to a contraction in the opposite
direction. Fiber support gives

$$
\langle Ug,f\rangle_m=\langle g,\Lambda f\rangle_\nu,
\qquad U^*=\Lambda,\quad U^*U=I.
\tag{3.6}
$$

Selfadjointness and $T_t1=1$ give $mT_t=m$. The bounded-Borel identities imply
$\nu Q_tg=\nu\Lambda T_tUg=mT_tUg=\nu g$, so $Q_t$ too extends
to an $L^2(\nu)$ contraction. Intertwining and (3.6) yield

$$
Q_t=U^*T_tU=Q_t^*,\qquad U^*T_t=Q_tU^*,\qquad T_tU=UQ_t.
\tag{3.7}
$$

The last equality is the adjoint of the middle one, using
selfadjointness of both semigroups. Consequently
$\mathcal H=\operatorname{ran}U$ and $\mathcal H^\perp$ reduce
$T_t$ and its generator $K$. All equalities extend by density from
bounded inputs. The compression formula also gives strong
continuity of $Q_t$. For the properly exceptional $N$,
(3.5) gives $\Lambda_b(N)=0$ for $\nu$-almost every $b$; the
Hilbert argument therefore uses legitimate versions. The source
formula (3.2) uses the legitimate $e\notin N$. No claim about an
ordinary value of an $L^2$ function at $e$ enters this step.

Third, a central period survives every finite cover. The finite
group $(2\pi\mathbb Z)^2/L_{\rm ph}$ has order $d$, so
$(0,2\pi d)\in L_{\rm ph}$. Set

$$
\Delta=d\ell>0,\qquad D(x,y,z,w)=(x,y,z,w+\Delta).
\tag{3.8}
$$

Inside the slab, $\vartheta(Dp)=\vartheta(p)+(0,-2\pi d)$;
hence $\chi(Dp)=\chi(p)$ for either rule (2.2). We use only this
inside equality, not any assertion about outside fibers. For any
$q\in\mathcal S\setminus\{e,D^{-1}e\}$ choose a relatively compact
open box $O$ around $q$ such that $O,DO\subset\mathcal S$ have
disjoint closures avoiding $e$. No local injectivity of $\chi$ on
$O$ is required or asserted. Given real
$\varphi\in C_c^\infty(O)$, set

$$
W(p)=\varphi(p)/h(p)^2\quad(p\in O),\qquad
W(Dp)=-\varphi(p)/h(Dp)^2\quad(p\in O),\qquad W=0\text{ otherwise}.
\tag{3.9}
$$

Its compact supports avoid $e$, so $hW$ is in the punctured smooth
core and $A(hW)=C(hW)=0$. Therefore $W\in D(K)$ for the full
selector (1.3). Translation preserves raw Haar measure, and the
two weighted integrals cancel against every bounded basic function
$Ug$. Thus $W\in\mathcal H^\perp$ and reduction gives
$KW\in\mathcal H^\perp$.

Take any real smooth $f(k,\alpha)$, periodic in $\alpha$ with
period $2\pi$, compactly supported in $0<k<H_{\rm n}$. Its
pullback

$$
v(p)=f(k_0+x,\alpha_0+y/2)\quad(p\in\mathcal S),\qquad
v(p)=0\quad(p\notin\mathcal S)
\tag{3.10}
$$

is a bounded basic function under either outside rule. It is smooth
across the slab walls since its height support is interior. It need
not be in $D(K)$. On the compact punctured supports of $W$, the
actual generator has local expression $K=-\mathcal D_h$, where

$$
\mathcal D_hv=a\sum_{j=1}^3X_j^2v+\eta\partial_w^2v
 +2a\sum_{j=1}^3(X_j\log h)X_jv
 +2\eta(\partial_w\log h)\partial_wv.
\tag{3.11}
$$

Local weighted integration by parts, valid on those compact
supports, gives

$$
0=\langle v,KW\rangle_m
 =-\int_O\varphi(p)\{
                  \mathcal D_hv(p)-\mathcal D_hv(Dp)\}\,d\mu(p).
\tag{3.12}
$$

There are no source, wall or infinity boundary terms. This is a
full-domain test using $W$; it does not differentiate a periodic
function in an unverified generator domain. Direct differentiation
of (3.10) gives

$$
\mathcal D_hv=a f_{kk}+\tfrac a4 f_{\alpha\alpha}
 +2a(X_1\log h)f_k+a(X_2\log h)f_\alpha.
\tag{3.13}
$$

The values of $k$ and $\alpha$ at $p,Dp$ agree modulo the period.
Since $\varphi$ is arbitrary, (3.12) is pointwise equality of the
smooth expressions. Smooth tests $f$ can have arbitrary independent
first jets $f_k,f_\alpha$ at the given interior height and circle
point, by a local circle chart and cutoffs. The second-order terms
cancel identically. Since $a>0$, (3.13) forces

$$
(X_1\log h)(Dp)=(X_1\log h)(p),\qquad
(X_2\log h)(Dp)=(X_2\log h)(p)
\quad(p\in\mathcal S\setminus\{e,D^{-1}e\}).
\tag{3.14}
$$

Finally, put $g(p)=\log h(Dp)-\log h(p)$ on this punctured slab.
Central translation commutes with the fields, so (3.14) says
$X_1g=X_2g=0$. Their bracket is $[X_1,X_2]=\partial_w$;
therefore $\partial_wg=0$, then
$\partial_yg=X_2g-x\partial_wg=0$ and $\partial_xg=0$.
For each fixed $z$, the horizontal slice
$(-k_0,H_{\rm n}-k_0)\times\mathbb R_y\times\mathbb R_w$ with
at most the two displayed points removed is connected. A polygonal
path can avoid finitely many points in this three-dimensional open
strip. Thus $g$ is constant on each such slice, and

$$
h(Dp)=c(z)h(p),\qquad 0<c(z)<\infty.
\tag{3.15}
$$

There is no need to prove constancy in $z$. For definiteness choose
one fixed $x_*\ne0$ in the slab, $y=w=0$; the ratio there defines
$c(z)$ for all $z$ and is smooth, hence measurable.

Choose a bounded open box $E\subset\mathcal S$ whose $x$ interval
avoids zero and whose $w$ width is less than $\Delta$. Such an
interval exists for every permitted preparation. The boxes $D^nE$,
$n\in\mathbb Z$, are pairwise disjoint. Their points and all their
successive translates avoid both singular points, so iterating
(3.15) forwards and backwards gives

$$
\begin{aligned}
1=\int_Gh^2\,d\mu
&\ge\sum_{n\in\mathbb Z}\int_{D^nE}h^2\,d\mu\\
&=\int_E h(p)^2\sum_{n\in\mathbb Z}c(z)^{2n}\,d\mu(p)
=\infty.
\end{aligned}
\tag{3.16}
$$

Tonelli applies to these nonnegative terms. For every positive
$c$, the bilateral geometric series diverges: the positive tail
does when $c\ge1$, the negative tail when $c\le1$.
The box has positive measure and $h>0$ there. This contradiction
proves (3.1) impossible. All tests used inside the slab are valid
separately for each outside convention. $\square$

## 4. Recovery directions, acquisition and the same-run bill

**Definition 4.1 (the task actually excluded).** The two routes
equated by (3.1) are: from a current cover point, sample a full
source point using the same $\Lambda$ and evolve for elapsed $t$;
or evolve the cover by $Q_t$ and apply that same $\Lambda$.
Equality is for every bounded full-$G$ test, with the actual initial
conditional law $\delta_e$. It is distributional recovery with
continued Markov use, not merely output reproduction or deterministic
selection of a representative of (2.3). The static forward maps,
the inverse (1.6), the display-plus-sheet inverse of Proposition 2.2,
and the lawful update square of Proposition 2.3 are positive
correspondences on their stated images. Theorem 3.1 says that these
correspondences cannot be completed by the stipulated full-source
Markov reverse arrow. Its proof is direct on the native finite
cover; failure of [N, Theorem 9.1] on the finer quotient retaining
real $y,z$ would by itself give no implication for this coarser map.

**Proposition 4.2 (a full-current-state comparator).** If instead the
observation is the actual current $p\in G$, the identity link
$\Lambda_p=\delta_p$ and $Q_t=T_t$ satisfy the analogous conditions
with source $e$. For $\chi_L^+$ the same pointwise recovery is
available at each outside point, but not as a global link (3.1).

Proof. For the identity observation both orders apply $T_t$ to
the same bounded Borel function at $p$. Its fibers are singletons
and the initial link is $\delta_e$. The outside assertion follows
from the singleton fibers in (2.2); Theorem 3.1 prevents extending
it to the whole cover observation. This comparator is a mathematical
information allowance, not an acquired sensor. $\square$

**Definition 4.3 (one resource vector, without free phase acquisition).**
For a run with fixed $d$, the current inside record contains one
height, two exact circle coordinates and one of $d$ sheet labels,
with the fixed lattice, section, calibration and preparation held
as context. A fixed-width injective binary code for all $d$ possible
labels requires and suffices $\lceil\log_2d\rceil$ bits: $b$ bits
have $2^b$ codewords, and enumeration supplies the converse. For
$d=1$ this discrete contribution is zero. It says nothing about
bits for exact reals, source-reference storage, a path-tracking
algorithm, or total memory. Even the full cover record has the
continuous fibers (2.3). Outside the slab, rule $0$ returns one
unavailability symbol, while rule $+$ returns a tag and four exact
real coordinates. Their acquisition, precision and traffic also
belong to the same unpaid resource coordinates.

For $n$ actually supplied lawful commands, (2.4) consumes their
same-run chronological triples, performs $n$ cover updates and $n$
whole-prefix guard checks, and retains the current cover point.
If commands are retained for later replay, their $n$ descriptions
and actual chronology must also be retained; the empty script costs
zero updates. Acquisition of each triple, evaluation of its real
integral and extrema, lattice reduction, real arithmetic and the
five output pairs are separate costs. A piecewise command needs
its actual representation and prefix checks; a finite formula
does not bound their bit complexity. No diffusion step, source read,
shot, energy expenditure or notification is manufactured by this
algebraic count.

In the impossibility theorem the ideal current record and arbitrary
Borel computation are granted. Its same-run bill must therefore
keep installation/calibration, source access, exact phase and sheet
acquisition, original clock, arithmetic precision, record traffic,
storage and actuation as unpaid coordinates. No finite-bit upper
bound, physical lower bound or cheapest apparatus is inferred.
These ideal allowances concern only a fixed current finite-cover
map and fixed link; arbitrary history-dependent finite-memory
controllers are a different quantified class.

**Definition 4.4 (the existing positive timed consumer is retained).**
[N, §§24–28] uses the same source $\mathbb P_e$, but its added
Assumption 25.1 returns types, original-clock timestamps and four
real coordinates at release, together with nonarrival while pending.
The calibrated entrance/contact/survival laws and exact clock are
premises. Its completed events on $[0,T]$ number at most

$$
2\lfloor T/\epsilon\rfloor+\lfloor T/\delta\rfloor,
\tag{4.1}
$$

with at most one extra pending primitive; at $T=0$ there are zero
completed events. Assumption 26.1 additionally supplies exact real
computation and native actuation. These are one source's jointly
coupled records and costs, not independently optimized marginals.
Theorem 24.3's coupling, Theorem 25.2's filtration containment and
Theorem 27.1's same-original-time ten-output/own-exit convergence
remain available with their explicit premises. That consumer uses
its fixed interior interval $I=[l,u]$, $0<l<k_0<u<H_{\rm n}$,
and uses $(x,y,w)$, even though its service releases $z$ too. Its
observation exit is not substituted for full source evolution in
Theorem 3.1. Theorem 3.1
does not remove these positive results or pay their calibration,
exact timing, notification, real computation, command, traffic or
storage costs. Their finite-event record and causal controller are
not the current finite sheet in (2.1).

## 5. Scope, suppliers and adjacent quantifiers

**Definition 5.1 (source-specific reuse and literature).** This is a
`repo-derived` finite-cover application of [N, §§8–9]'s
source-occupation/disintegration and selfadjoint reduction argument.
The new inference is that just height and one wrapped phase in
(3.13), available even on the bare native display, force horizontal
constancy of a central log-ratio; the bracket then suffices for the
bilateral contradiction without recovering its $z$ derivative.
The proof needs no local injectivity of the observation and handles
the continuous fibers and both global outside rules directly.
The endpoint, local generator, source resolvent and native command
and output formulae are reused suppliers, not new endpoint or
control theorems. The supplier snapshot in [N, Definition 7.1] is
`69eee5580efb61cf70564cc46a0fa24fc18351dd`; [E, §112] and
[S, §§115–116] retain those exact statements.

The standard intertwining convention is `literature-attested`:
Pal–Shkolnikov, [*Intertwining diffusions and wave equations*,
arXiv:1306.0857v2, §1, Definitions 1–2](https://arxiv.org/html/1306.0857v2),
uses $Q_t\Lambda=\Lambda P_t$ on bounded measurable tests and a
compatible initial conditional law. Here $P_t=T_t$, the upper
state is a cover point, and its initial conditional law is
$\delta_e$. Their subsequent smooth-density diffusion-coupling
hypotheses are not assumed for the possibly singular fiber kernel
in (3.1). Disintegration, Jensen contraction, Hilbert adjoints,
Lie brackets, finite covering groups and Tonelli are mature tools;
their use is explicit in the proof, not a worldwide priority claim.

The repository's
[`DynamicsDescent.dynamics_descends_iff`](../../../D5/S0/Rewriting/Quotients/DynamicsDescent.lean)
and its owning Scribe concern deterministic self-map descent.
[`StrongLumpabilityDescent.strong_lumpability_descent_tfae`](../../../D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent.lean)
and
[`StochasticDescentEquivalence.stochastic_descent_equivalence`](../../../D5/S3/Estimation/DecisionRisk/StochasticDescentEquivalence.lean),
with their owning Scribes, concern pushed-forward one-step PMF
laws. They do not supply this source-anchored continuous-state
reverse link or its obstruction. At the pinned mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`,
[`Kernel.Invariant` and `Kernel.IsReversible.invariant`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Invariance.lean)
and
[`eq_condKernel_of_measure_eq_compProd`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Kernel/Disintegration/Unique.lean)
supply the general meanings of invariance and almost-everywhere
uniqueness for a finite measure on a standard Borel product.
Equation (3.5) verifies the needed joint-law property here rather
than treating a declaration name as a proof of this application.
This volume is ordinary mathematical source, without new Lean
verification or an exhaustive literature/novelty claim.

**Definition 5.2 (the distinct public additions).** The following
positive suppliers retain their actual tasks and assumptions.
[Selection calculus §27](AURIC_FIB_ATOM_SELECTION_CALCULUS.md) gives
conditional paid finite complete-assignment counting, generation
and growth under its fixed external counting supply; projected
boundary counts need their multiplicities. [Hierarchical phases
§14](AURIC_FIB_OBSERVATION_HIERARCHICAL_PHASES_AND_PREDICTIVE_SPECTRA.md)
preserves the original-vertex parameter by explicit deterministic
auxiliaries for quantity-constrained completions. Neither result
constructs the current phase-cover link (3.1), changes $h$, or
identifies its discrete law with $\mathbb P_e$.

[S, Theorem 121.2] supplies an overlap-free stochastic optimum for
the original passive pair law, minimizing its temporal $1/3$
cross mass second. It retains strictly positive distance to its
native pair target; it asserts neither zero temporal cross mass,
an indicator partition, deterministic attainment nor a constructive
sampler. It addresses emissions at two positive times with fresh
conditional read noise, not recovery of full source transitions.
The separately public
[Appendix II, Theorem 122.1](https://github.com/the-omega-institute/trureturing/blob/27db8edb6c06d3ea80575cba4078f0a9ee287a57/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md#122-exact-deterministic-attainment-for-the-original-passive-pair)
does supply an indicator partition attaining the passive-pair
minimum, and equality of its deterministic and stochastic pair-law
sets, with its full source and analytic premises. That two-time
emission theorem imposes no fiber-supported full-source reverse
link or all-time intertwining (3.1), so the two conclusions coexist.
[Self-calibrating relation IV, Theorem 15.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md)
gives two constant and unequal first responses as a necessary
condition for an exact four-world original-root failure. It does
not exhibit a failing tuple or change the original complete-world
task. The formal `NativeFunctionalEffectivePrefix.effective_prefix`
and its owning Scribe compute finite cutoffs of the original
canonical native solution, using the publicized original helpers
in `NativeSymbolicFiniteForcing` and `NativeCompletionPrefixLifting`.
Their native-tree parameters, recursion and finite-state bound do
not recover the diffusion's hidden coordinates. The projected
gradient-memory discussion in the owning `SchurMinimum` Scribe
concerns finite-dimensional real linear trajectories, not this
singular endpoint. None of these additions is used as an unproved
bridge between the respective carriers.

[Coherent reconstruction §36](AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION.md)
is specifically the physical $\mathbb C^5$ polar-support/full-read
incompatibility: waiting preserves a polar complex structure, but
the full native read separates a polar ray and can leak mass into
the zero mode. Its polar support is a real four-dimensional space
inside the physical five-level apparatus; its effects have no
supplied identification with (1.5). [Attractive boundary gluing §35](FIB_NATIVE_ATTRACTIVE_BOUNDARY_RESPONSE_GLUING.md)
retains its finite compatibility correction and remaining full
residual. These different tasks supply no common physical
apparatus or universal minimal resource vector.

**Definition 5.3 (history and contact quantifiers remain separate).**
[N, Theorem 18.2] recovers the Revuz-normalized stopped source clock
from the exact continuous output history and completed genuine
preparation-return gaps, with its spectral denominator and original
time units. [N, Definition 28.2] says that its finite approximations
do not themselves derive that clock recovery. These are different
observation domains, with compatible conclusions. A current cover
point contains neither such a history nor its clock construction.

The noncontact conditional-density question and the full-history
reflection/sign question require separate proofs, observation
records and stopping/contact domains. Theorem 3.1 supplies neither
of those proofs. In particular a claimed noncontact density result
would imply, for a record-measurable exact estimator, zero success
off contact. If genuine contact identifies $z_R=0$, the complete
success identity is

$$
\mathbb P\{\widehat z=z_R\}
 =\mathbb P\{v_R=0,\ \widehat z=0\},\qquad v=(x,y,w),
\tag{5.1}
$$

conditional on those density and contact premises. It is the
optimal success probability, attained by the zero estimator, that
equals $\mathbb P\{v_R=0\}$; this equality does not hold for every
estimator. Already $R=0$, $z_R=0$, $\widehat z\equiv1$ gives
success zero and contact probability one. Likewise equal positive
and negative conditional sign masses at a random contact do not
give the deterministic-positive-time value $1/2$: at the source
both strict sign events are empty. This records the exact
quantifier boundaries without claiming either adjacent theorem
from finite-cover reduction.

**Definition 5.4 (remaining original-goal duties).** Theorem 3.1
excludes only the stated current finite-cover recovery links.
Time-dependent posteriors, arbitrary histories or finite-memory
controllers, infinite phase lifts, real chronological area,
source-changing interventions, output-only tasks, different starts
or source laws, stopped/killed processes and added hidden-coordinate
ports have other hypotheses. There is no physical impossibility
or spatial-dimension conclusion here. The full native legal-source,
evolution, representation and readout correspondence must still
earn its source trace, selector, contact and resolvent laws as
specified in [S, Definition 116.5]. Mere equality of the off-source
differential expression does not earn them.

The native zero-appending completion problem concerns a separate
material tree. [Native Leaf Boundary Acquisition III, §§94–102](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_III.md)
already proves serial sampling aliasing and period repair for a
known rational unit adjacency, followed by fixed-phase inverses
on $\operatorname{im}A$. Its period is the number of actual native
Ticks between scalar samples, whereas $L_{\rm ph}$ here is a
subgroup of the two angular period lattices. Changing that serial
schedule does not remove the central translation in (3.8).
[Atomic Generation Acquisition III, §§28–34](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_III.md)
uses floor-valued reads and separates dense rational entrances from
assured lattices under a known integral symmetric law. Neither that
channel nor its eigenvalue conditions identify the present Borel
source fibers. [Cyclic Leaf Boundary Ambiguity, §§11–20](RECURSIVE_RELATIONAL_OBSERVATION_CYCLIC_LEAF_BOUNDARY_AMBIGUITY.md)
uses installed Reset/Square, unknown weighted-law controllability
and acquired multiplication; its axis reconstruction and cyclic
assay do not change $T_t$, $\chi$ or the source anchor in (3.1).
[Measurement-Relative Quantum Boundary Continuation I, §§4–7](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY_CONTINUATION_I.md)
derives an immediate-F-read selective converse and a finite exact-law
certification obstruction on one fixed-DU initialized quantum
source. It retains that reference/effect contract. These positive
acquisition and converse results are public results on different
carriers; none supplies a full-source Markov link here, and no
resource or impossibility statement is transferred between them.
The exact old fixed-$G_{g_c}$, original-$Q$, parked-consumer and
unchanged-initialization problems retain their original scopes.
No standalone ownership/factorization theorem is needed for the
positive interfaces already in [N, §§24–28]. A single jointly
acquired apparatus with mutually recoverable independent Space,
Time, Boundary and Memory views, a faithful common physical law,
and a simultaneous resource comparison remains unconstructed by
these scoped results. This boundary preserves the conditional
models and their positive mathematics; it does not impose the
different demand of deriving all physical laws without premises.


## 6. Coefficient-world inverses and the phase-cover boundary

**Boundary 6.1 (positive inverses retain their source and image).**
[Third Germ Retention Threshold, Theorems 15.2–15.3](RECURSIVE_RELATIONAL_OBSERVATION_THIRD_GERM_RETENTION_THRESHOLD.md)
proves an inverse Lipschitz inequality from its clock-eight boundary
$B_M=(p,v,f_M)$ to original complete-world coordinates on the full
preimage of a suitable compact base rectangle. Its local and remote
branches and all permitted strata are included. It then bounds all
common finite-word responses on that domain. Sections 16–17 retain
the actual frozen-record growing-mode witnesses and exact
singleton-world recovery routes on the exposed image, including
the seven-action/eight-read and eight-action/nine-read experiments.
These inverses do not acquire their stipulated original observations
or grant further execution.

Section 18, with the owning
[`CommonWordSensitivity` source exposition](../../../Blueprint/D5/S3/Observer/CubicGain/CommonWordSensitivity.md),
separately gives the explicit source-coordinate estimate with
constant $1+1048576H$, golden-exponential factor $\varphi^n$ and
cubic factor $(1+n)^3$. It compares two worlds with common bound
$H\ge1$, their one whole cubic and the same chronological $J/M$
word, from the absolute clock-eight matrix
$\left(\begin{smallmatrix}3&1\\8&3\end{smallmatrix}\right)$.
That estimate alone does not replace source distance by boundary
distance; the extra inverse is precisely the earlier §15.2 result
on its declared preimage. None of these coefficient-world maps
identifies a phase sheet or a conditional distribution on the
Heisenberg source fibers. Theorem 3.1 therefore keeps its exact
fixed-link, full-source and original-time hypotheses under both
outside conventions.

The coefficient-world response and the Heisenberg source in this
volume share neither a state-space identification nor a hidden
coordinate. No response bound from that public supplier is used as a
conditional law or as evidence for a finite-cover recovery route.

## 追加锚（本行以下为增补区）

## 7. The original finite first-order calibration cannot close under heat

**Definition 7.1 (the original source and its three-read calibration).**
Retain the entire endpoint, source and time domains of Definition 1.1,
with arbitrary finite $a,\eta>0$. In particular $H=H_{\rm end}$,
$h=w_*/\|w_*\|_{L^2(\mu)}$, $m=h^2\mu$ and $K=J_h^{-1}HJ_h$ are
unchanged; $A=\rho C$ is the original maximal-domain selector, not
an additional boundary condition. The following results are conditional
on those owning endpoint statements and on
[Appendix II, Theorems 115.3, 117.2 and 133.2][HC-S]. The actual
conservative continuous-path process starts at $Z_0=e$ in the original
clock, and its positive-time laws satisfy

$$
\begin{gathered}
m(G)=1,\qquad m(\{e\})=0,\qquad
\mathbb P_e(Z_s\in dx)=g_s(x)m(dx),\\
g_s\in L^2(m;\mathbb R),\quad g_s\ge0,\quad
\int_Gg_s\,dm=1\quad(s>0),\qquad
g_{s+t}=T_tg_s\quad(s>0,\ t\ge0),\\
T_t=e^{-tK},\qquad K\ge0,\qquad T_t1=1.
\end{gathered}
\tag{7.1}
$$

The full complex self-adjoint domain is retained, while calibration
uses its real classes. $T_t$ preserves real bounded classes and is a
Markov contraction on them. Only positive-time laws have the densities
in (7.1); the law at zero is the measure $\delta_e$.

Fix any finite $d>0$ and every permitted Borel representative $b$ from
[Appendix III, Definition 134.1][HC-C]. Keep its precise readout:

$$
\begin{gathered}
P=T_d,\qquad g=g_{2d},\qquad
M=1+\|g_d\|_\infty,\qquad c=\frac1{4M},\qquad
[b]=g_d,\quad 0<b\le M,\\
\mathcal L=\{0,1,3,B\},\qquad f_3=cb,\quad f_B=\frac14,\quad
f_0=f_1=\frac{3/4-f_3}{2},\qquad
(\sigma_0,\sigma_1,\sigma_3,\sigma_B)=(1,-1,0,0).
\end{gathered}
\tag{7.2}
$$

The three epochs are exactly $2d,3d,4d$. Conditional on the source
path, reads use the same $f$ and independent fresh read noise; each
read leaves the source evolution unchanged. This is the equal-gap
passive read contract of [HC-S, Definition 117.3] and [HC-C,
Definition 134.1], separate from the native phase display of Definition
1.2. No stationary initialization or additional source access is used.
Theorem 133.2 supplies the boundedness of $g_d$, hence of $g=Pg_d$.

Let $\mathcal H_{\mathbb R}=L^2(G,m;\mathbb R)$ and
$X=L^\infty(G,m;\mathbb R)\subset\mathcal H_{\mathbb R}$.
For $\alpha=(y,z,w)\in\mathcal L^3$ use precisely the bounded
representers of [Appendix IV, Definition 166.1 and Proposition
166.2][HC-R]:

$$
\begin{aligned}
\psi_{yzw}={}&\sigma_y gP(f_zPf_w)
 +\sigma_zP(gf_y)Pf_w
 +\sigma_wP\bigl(f_zP(gf_y)\bigr),\\
\ell_\alpha(v)={}&\langle v,\psi_\alpha\rangle_m,\qquad
\Lambda(v)=(\ell_\alpha(v))_{\alpha\in\mathcal L^3},\\
W={}&\operatorname{span}_{\mathbb R}\{\psi_\alpha:\alpha\in\mathcal L^3\},
\qquad r=\dim W\le64,\qquad
V=\ker\Lambda=X\cap W^\perp.
\end{aligned}
\tag{7.3}
$$

All function equalities are $m$-class equalities. The real pairings in
(7.3) are those of $\mathcal H_{\mathbb R}$. In particular, a singular
raw Gram matrix of the 64 generators is allowed.

**Theorem 7.2 (actual-source nonclosure and a bounded original-coordinate
witness).** For every parameter tuple and representative in Definition
7.1, the vectors $g,Pg,\ldots,P^Ng$ are linearly independent for every
integer $N\ge0$. Moreover

$$
P(W)\not\subseteq W,\qquad P(V)\not\subseteq V.
\tag{7.4}
$$

If $\Pi_W$ is orthogonal projection onto $W$, at least one of the
original label triples $\alpha$ has

$$
v=(I-\Pi_W)P\psi_\alpha\ne0,\qquad
v\in V,\qquad
\ell_\alpha(Pv)=\|v\|_2^2>0.
\tag{7.5}
$$

For every independent bounded basis of $W$, the exact residual Gram
matrix of [HC-R, Proposition 167.4] is positive semidefinite and
nonzero.

*Proof.* First extend the degree-two source argument of [HC-C, Lemma
147.2] to arbitrary finite degree. Work in the supplied full complex
$L^2(m)$ for spectral calculus, and let $E_K$ be the spectral resolution
of the actual $K$. For any vector $u$, write
$\nu_u(A)=\|E_K(A)u\|_2^2$. For $t>0$,

$$
\|T_tu\|_2^2
 =\int_{[0,\infty)}e^{-2t\lambda}\,d\nu_u(\lambda).
\tag{7.6}
$$

The multiplier is strictly positive at every finite spectral
parameter, so $T_t$ is injective. This standard spectral-calculus
step is also the heat injectivity used in [HC-S, Proposition 124.1].
For the norm identity and commuting spectral projections one may use
Teschl, [*Mathematical Methods in Quantum Mechanics*, §3.1, Theorems
3.1 and 3.7, (3.18)–(3.21)][HC-T], with his self-adjoint operator
$A=K$ and bounded multiplier $e^{-t\lambda}$ on its nonnegative
spectrum. No assumption about compact resolvent or pure point spectrum
is needed.

Suppose that a nonzero real polynomial $p$ satisfies $p(P)g=0$.
The same calculus gives

$$
0=\|p(P)g\|_2^2
 =\int_{[0,\infty)}|p(e^{-d\lambda})|^2\,d\nu_g(\lambda).
\tag{7.7}
$$

Because $d>0$, the function $\lambda\mapsto e^{-d\lambda}$ is
injective on $[0,\infty)$. The set
$E=\{\lambda\ge0:p(e^{-d\lambda})=0\}$ is therefore finite.
A root of $p$ at zero creates no finite spectral point. Equation
(7.7) implies $E_K(E)g=g$. If $E$ is empty, this already contradicts
$\int g\,dm=1$. Otherwise put $v_\lambda=E_K(\{\lambda\})g$;
then $g=\sum_{\lambda\in E}v_\lambda$.

For every $0<s<2d$, the original propagation identity in (7.1) gives
$g=T_{2d-s}g_s$. Spectral projections commute with this heat operator.
Projecting outside $E$ and using injectivity gives
$E_K([0,\infty)\setminus E)g_s=0$. Projection onto each member of
$E$ now yields

$$
g_s=\sum_{\lambda\in E}e^{(2d-s)\lambda}v_\lambda
 \longrightarrow R_0:=\sum_{\lambda\in E}e^{2d\lambda}v_\lambda
 \quad\hbox{in }L^2(m)\quad(s\downarrow0).
\tag{7.8}
$$

Only the finitely many scalar multipliers on $E$ have been inverted;
no bounded inverse or surjectivity of the full heat operator is used.
Since the $g_s$ are real, so is their $L^2$ limit. Since $m$ is a
probability, $R_0\in L^1(m)$ and the convergence also holds in $L^1$.
For every $\phi\in C_c(G)$, the source-start law and continuity at
zero give

$$
\int_G\phi R_0\,dm
 =\lim_{s\downarrow0}\int_G\phi g_s\,dm
 =\lim_{s\downarrow0}\mathbb E_e\phi(Z_s)=\phi(e).
\tag{7.9}
$$

The first limit follows from (7.8), and the last from bounded
convergence on the original continuous paths with $Z_0=e$.
Compactly supported continuous tests determine finite signed Borel
measures on this locally compact metrizable $G$. Thus
$R_0m=\delta_e$, contradicting $m(\{e\})=0$. The time-zero measure
has not been treated as an $L^2$ vector. Hence no such nonzero $p$
exists, proving independence at every finite degree, rather than
inferring it from the three-vector statement alone.

The constant label $B$ now connects this result to the actual
calibration. Substituting $f_B=1/4$, $\sigma_B=0$ and
$\sigma_0=1$ into (7.3), and using $P1=1$, gives

$$
\psi_{0BB}=\frac{g}{16},\qquad
\psi_{B0B}=\frac{Pg}{16},\qquad
\psi_{BB0}=\frac{P^2g}{16}.
\tag{7.10}
$$

In particular $g\in W$ and $3\le r\le64$. If $P(W)\subseteq W$,
the $r+1$ independent vectors $g,Pg,\ldots,P^rg$ would all lie in
the $r$-dimensional $W$, a contradiction.

Since the original $\psi_\alpha$ span $W$, some
$(I-\Pi_W)P\psi_\alpha$ is nonzero. Fix such an $\alpha$.
Both $P\psi_\alpha$ and $\Pi_WP\psi_\alpha$ are bounded: the first
by the Markov contraction, the second because $W$ has a finite bounded
basis. Thus their difference $v$ is bounded and orthogonal to $W$,
so $v\in V$. Self-adjointness gives the exact positive witness

$$
\ell_\alpha(Pv)
 =\langle Pv,\psi_\alpha\rangle_m
 =\langle v,P\psi_\alpha\rangle_m
 =\langle v,v+\Pi_WP\psi_\alpha\rangle_m
 =\|v\|_2^2>0.
\tag{7.11}
$$

This directly proves $Pv\notin V$ and agrees with the already supplied
invariance equivalence [HC-R, Proposition 167.3]. It selects an actual
coordinate by existence, without asserting a named numerical index or
residual magnitude.

Finally use [HC-R, (167.6)]: for any independent bounded basis of $W$,
its residual matrix is the Gram matrix of $(I-\Pi_W)Pw_j$. It is
positive semidefinite and cannot vanish, since vanishing would give
$P(W)\subseteq W$. This uses the Gram inverse only for an independent
basis, and gives neither positive definiteness nor a parameter-uniform
positive lower bound. $\square$

**Corollary 7.3 (finite linear boundary records do not determine their
own heat continuation).** Put $\mathcal B_{\rm cal}=\Lambda(X)$.
There is no map $F:\mathcal B_{\rm cal}\to\mathcal B_{\rm cal}$,
even an unrestricted set map, such that
$\Lambda(Px)=F(\Lambda(x))$ for every $x\in X$.
No finite-dimensional linear subspace of $\mathcal H_{\mathbb R}$
containing $W$ is $P$-invariant. In particular no addition of finitely
many bounded $L^2(m)$ representers can make the entire augmented
bounded calibration kernel $P$-invariant. The finite stages

$$
W_n=\operatorname{span}_{\mathbb R}
 \{P^jw:w\in W,\ 0\le j\le n\}
\quad\hbox{satisfy}\quad W_n\subsetneq W_{n+1}
\quad(n\ge0).
\tag{7.12}
$$

*Proof.* The pair $0,v$ in (7.5) has equal present records and different
successor records. Apply the existing fibre criterion of [HC-R,
Proposition 163.4] to $X$, its surjective record map
$\Lambda:X\to\mathcal B_{\rm cal}$ and the update $P:X\to X$;
that pair violates its necessary fibre preservation.

Any invariant finite-dimensional space containing $W$ would contain
every $P^jg$, contradicting Theorem 7.2. For finitely many extra
bounded representers, their joint span $\widetilde W$ with $W$ is
finite-dimensional and bounded. The bounded-kernel equivalence of
[HC-R, Proposition 167.3] applies to this span too, so invariance of
$X\cap\widetilde W^\perp$ would imply the excluded invariance of
$\widetilde W$. If $W_n=W_{n+1}$ for some $n$, then
$P(W_n)\subseteq W_{n+1}=W_n$, also contradicting that exclusion.
This proves (7.12). $\square$

The closed linear orbit generated by $W$ is therefore infinite
dimensional. This conclusion establishes neither its density in
$\mathcal H_{\mathbb R}$ nor the existence or description of a
nonzero bounded vector in its orthogonal complement. The finite-prefix
and limiting-kernel distinctions of [HC-R, §§165–166] remain in force.
The assertion concerns exact global continuation of these linear
records on all of $X$; it is not an obstruction to arbitrary nonlinear
records, restricted input families, approximate recovery or a fixed
finite prediction horizon.

**Proposition 7.4 (simplex legality and the nonlinear-law boundary).**
For the witness $v$ in (7.5) put $u=v/\|v\|_\infty$. Bounded Borel
representatives can be chosen so that, for every $|s|\le1/4$, both
$f+s\sigma u$ and $f+s\sigma Pu$ are pointwise simplex-valued common
readouts. The first is calibrated to first order, but for every
$0<|s|\le1/4$ its complete three-read law differs from that of $f$.
More precisely, with the original coefficients of [HC-C, (134.10)–
(134.13)],

$$
\nu^{(3)}_{f+s\sigma u}(0,0,3)-\nu^{(3)}_f(0,0,3)
 =s^2q_{003}(u)
 =s^2c\|T_{d/2}(gu)\|_2^2>0.
\tag{7.13}
$$

*Proof.* The normalization gives $\|u\|_\infty=1$, and the Markov
contraction gives $\|Pu\|_\infty\le1$. Choose Borel representatives
bounded pointwise by one by repairing their null sets. The fixed
$f_0=f_1\ge1/4$ margin then makes both perturbed 0 and 1 entries
nonnegative for every indicated $s$; their sum is unchanged, and the
3 and $B$ entries are unchanged. Hence all four entries are in $[0,1]$
and sum to one. These repairs do not affect any of the three
positive-time laws in (7.1).

Since $u\in V$, all first-order coefficients vanish. The exact common
readout expansion [HC-S, Proposition 125.2] still contains
$s^2q_{yzw}(u)+s^3\sigma_y\sigma_z\sigma_w\mathcal C(u,u,u)$,
where $\mathcal C(a,b,c)=\int gaP(bPc)\,dm$. At the original coordinate
$(0,0,3)$ the cubic coefficient vanishes because $\sigma_3=0$;
[HC-C, Proposition 134.2] supplies the strict positivity of $q_{003}$
on every nonzero bounded direction. This proves (7.13). $\square$

The map $u\mapsto Pu$ here is a map of perturbation classes. The
passive source/read contract supplies no operation implementing this
map from acquired records, and the projection witness supplies no
acquisition map for $u$ or its index. All source-start, original-time
and fresh-read hypotheses remain separate from such an operation.
Failure to preserve the whole $V$ does not say every vector leaves
$V$, nor exclude a proper invariant calibrated subspace. Neither
(7.4) nor simplex legality supplies a full-law-calibrated nonlinear
family, a physical successor, or mutual recovery of the source,
spatial geometry, chronology and retained usable memory.

The source-specific consequence is `repo-derived`: (7.10) connects the
original readout to the arbitrary-degree source argument, and (7.5)
turns it into failure of the actual calibration closure left unevaluated
in [HC-R, §168]. The endpoint, density and bounded-representer
suppliers, the degree-two argument of Lemma 147.2, the residual and
fibre criteria, and Teschl's spectral calculus are reused with their
stated scopes. No general spectral theorem or general quotient
criterion is introduced, and no external priority is asserted.

[HC-S]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md
[HC-C]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_III.md
[HC-R]: FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_IV.md
[HC-T]: https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf

## 追加锚（本行以下为增补区）
