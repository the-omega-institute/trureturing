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

## 8. The original calibrated entrance law from one continuing record

**Definition 8.1 (the unchanged source, words and comparison law).**
Retain the entire source of Definitions 1.1 and 7.1, for every fixed
original finite $a,\eta,d>0$. Thus $G$, $\mu$, $e$, the unit-source
field $\Gamma$, the full complex endpoint $H=H_{\rm end}$ with
$A=\rho C$, $\rho=A(h)/C(h)$, and the coefficient-positive normalized
$h=w_*/\|w_*\|_{L^2(\mu)}$ are unchanged. In particular

$$
\begin{gathered}
D(H)=\{u\in D(S_{\min}^*):A(u)=\rho C(u)\},\quad Hu=S_{\min}^*u,\\
m=h^2\mu,\quad m(G)=1,\quad m(\{e\})=0,\quad
K=J_h^{-1}HJ_h\ge0,\quad\ker K=\mathbb C1,\\
T_t=e^{-tK},\quad T_t1=1,\quad P=T_d=P^*,\\
\mathbb P_e(Z_t\in dx)=g_t(x)m(dx),\quad
g_t\in L^2(m),\quad g_t>0\ (m\text{-a.e.}),\quad
\int g_t\,dm=1,\quad g_{t+s}=T_sg_t\quad(t>0,s\ge0).
\end{gathered}
\tag{8.1}
$$

These are the owning endpoint statements and [HC-S, Theorems 115.3,
117.2 and 133.2], not additional regularity or spectral hypotheses.
Keep every permitted repaired Borel representative $b$ and exactly

$$
\begin{gathered}
M=1+\|g_d\|_\infty<\infty,\quad M\ge2,\quad
c=\frac1{4M},\quad [b]=g_d,\quad0<b\le M,\\
\mathcal L=\{0,1,3,B\},\quad
f_3=cb,\quad f_B=\frac14,\quad
f_0=f_1=\frac{3/4-f_3}{2}.
\end{gathered}
\tag{8.2}
$$

All four emissions are strictly positive pointwise and sum to one;
$f_3\le1/4$ and $1/4\le f_0=f_1<3/8$. The boundedness of $g_d$
is supplied for this original tuple, without a parameter-uniform bound.
No upper estimate is substituted for the norm in (8.2).

Use the already specified fixed-gap passive contract [HC-S, Definition
117.3] with its permitted positive lead-in: the actual process still
starts at $Z_0=e$, and the sampled hidden states and emitted labels are

$$
X_j=Z_{(j+2)d},\qquad Y_j\in\mathcal L\qquad(j\ge0).
\tag{8.3}
$$

Conditional on the entire source path, the labels have probabilities
$f_y(X_j)$ with independent fresh read noise. Reading leaves the source
and every subsequent transition unchanged. Thus the first three reads
remain exactly at $2d,3d,4d$, and every subsequent gap is the original
$d$. Write $Q_e$ for the actual law of $(Y_j)_{j\ge0}$.

For a finite word $u$ let $F_\varnothing=1$ and recursively set
$F_{yu}=f_yP F_u$, as bounded real $m$-classes. Conservation gives
$F_y=f_y$. The complete original $k$-read law is

$$
\nu_e^{(k)}(u)=\langle g_{2d},F_u\rangle_m
             =\mathbb P_e(Y_0\cdots Y_{k-1}=u)
\quad(u\in\mathcal L^k).
\tag{8.4}
$$

For $k=3$ this is precisely [HC-S, (123.1)–(123.3)] and [HC-C,
(134.10)]: $\nu_e^{(3)}(y,z,w)=\int g_{2d}f_yP(f_zPf_w)\,dm$,
with all 64 coordinates.

Define $\widetilde Q_m$ on the joint one-sided hidden/read sequence
space by initial hidden law $m$, the same actual transition kernel
$P$, and the same emissions with fresh conditionally independent
noise. Its output marginal is $Q_m$, with cylinder probabilities

$$
q(u)=Q_m([u])=\int F_u\,dm,\qquad
[u]=\{y:y_0\cdots y_{|u|-1}=u\}.
\tag{8.5}
$$

These measures are comparison objects defined by the original kernels.
Neither $m$-initialization, a sample from $\widetilde Q_m$, nor any
coefficient $q(u)$ is an input to the actual observer. The shift on
output sequence space is $S(y)_j=y_{j+1}$. Since $P1=1$ and $P=P^*$,
$\int Pv\,dm=\int v\,dm$ for bounded real $v$, so $m$ is invariant
and $Q_m$ is stationary.

**Theorem 8.2 (source-specific marked-word identity and actual-path
frequency transfer).** Under Definition 8.1, for every $k\ge1$ and
$u\in\mathcal L^k$,

$$
q(3)=c,\qquad q(3u)=c\,\nu_e^{(k)}(u).
\tag{8.6}
$$

The shift $(S,Q_m)$ is ergodic. There is one $Q_e$-probability-one
event on which, simultaneously for every nonempty finite word $v$,

$$
\frac1N\sum_{j=0}^{N-1}
 \mathbf1\{Y_j\cdots Y_{j+|v|-1}=v\}
 \longrightarrow q(v)\qquad(N\longrightarrow\infty).
\tag{8.7}
$$

This is a statement for each fixed original source and every fixed
finite word, without a rate, spectral gap or independence of windows.

*Proof.* The first identity in (8.6) is
$\int f_3\,dm=c\int g_d\,dm=c$. For an entire word $u$, the original
read product, the repaired class identity and self-adjointness give

$$
\begin{aligned}
q(3u)&=\langle f_3,PF_u\rangle_m
 =c\langle g_d,PF_u\rangle_m\\
 &=c\langle Pg_d,F_u\rangle_m
 =c\langle g_{2d},F_u\rangle_m
 =c\,\nu_e^{(k)}(u).
\end{aligned}
\tag{8.8}
$$

In particular the single original interval $d$ propagates the
calibration class $g_d$ to exactly the original first-read density
$g_{2d}$. This uses the same $P$ and $f$, not a newly calibrated source.
For $k=3$, (8.8) reads
$q(3yzw)=c\int g_{2d}f_yP(f_zPf_w)\,dm$ for every original triple.

We next establish the ergodicity needed for (8.7). The original zero
line $\ker H=\mathbb Ch$ and the unitary $J_h$ give
$\ker K=\mathbb C1$. Let $E_K$ be its spectral resolution and put
$\Pi_0v=(\int v\,dm)1$. The spectral calculus of Teschl,
[*Mathematical Methods in Quantum Mechanics*, the online edition
corresponding to Graduate Studies in Mathematics 99, §3.1, Theorems
3.1 and 3.7, (3.18)–(3.21)][HC-T], applies to this self-adjoint
nonnegative $K$. Its bounded-multiplier norm identity gives

$$
\|P^nv-\Pi_0v\|_2^2
 =\int_{(0,\infty)}e^{-2nd\lambda}\,
       d\|E_K(\lambda)v\|_2^2\longrightarrow0
\quad(v\in L^2(m)).
\tag{8.9}
$$

The notation on the right denotes integration against the finite
spectral measure $A\mapsto\|E_K(A)v\|_2^2$. Bounded convergence
proves the limit even if positive spectrum accumulates at zero.
No compact resolvent, pure point spectrum or uniform rate is used.

For finite output cylinder events $A,B$, let $A$ use indices
$0,\ldots,r$ and shift $B$ to start at $n>r$. On the stationary
joint comparison space take
$a_A(x)=\mathbb E_m[\mathbf1_A\mid X_r=x]$ and let $b_B(x)$ be
the probability of the finite block $B$ given its first hidden state
$x$. Both functions are in $[0,1]$, and their $m$-integrals are
$Q_m(A)$ and $Q_m(B)$. The actual Markov transitions and fresh read
noise imply

$$
Q_m(A\cap S^{-n}B)
 =\langle a_A,P^{n-r}b_B\rangle_m
 \longrightarrow Q_m(A)Q_m(B)
\tag{8.10}
$$

by (8.9). Finite-coordinate events approximate every measurable output
event in $Q_m$-measure. Stationarity makes the approximation error of
$S^{-n}B$ independent of $n$, so the same limit holds for arbitrary
measurable $A,B$. For an invariant event $A$ modulo null sets, its
left side with $B=A$ equals $Q_m(A)$ for every $n$, while its limit
is $Q_m(A)^2$. Hence invariant events have probability zero or one:
the output shift is ergodic. This qualitative mixing consequence is
not a numerical mixing estimate.

Apply the existing pointwise ergodic theorem to the bounded cylinder
indicator $\mathbf1_{[v]}$ on $(\mathcal L^{\mathbb N},Q_m,S)$.
Its orbit average is exactly the left side of (8.7), and its integral
is $q(v)$. The reusable repository supplier is
[BirkhoffPointwise.birkhoff_pointwise_ergodic](../../../D5/S3/Analytic/Probability/BirkhoffPointwise.lean),
whose inputs are a probability measure, an ergodic transformation
and a real integrable observable. Here these inputs are respectively
$Q_m$, $S$ and $\mathbf1_{[v]}$; no generic ergodic theorem is added.
For a primary qualitative statement see Avigad–Gerhardy–Towsner,
[*Local stability of ergodic averages*, arXiv:0706.1512v3, Theorem
3.1][MW-A]. That statement supplies almost-everywhere convergence
for $L^1$ observables of a measure-preserving probability
transformation; ergodicity identifies the invariant limit with the
integral, as also expressed in their Corollary 5.4. There are only
countably many finite words, so their conull convergence events have
one conull intersection $E$ under $Q_m$.

It remains to transfer this event to the actual source, rather than
assuming stationarity of $Q_e$. Let $\widetilde Q_e$ be the joint
hidden/read law from (8.3). At its first sampled time the hidden law
is $g_{2d}m$ by (8.1). All later hidden transitions and read kernels
are exactly those defining $\widetilde Q_m$. Their finite-cylinder
products therefore satisfy, and a monotone-class extension gives on
the entire joint sequence sigma algebra,

$$
\widetilde Q_e(D)
 =\int g_{2d}(X_0)\mathbf1_D\,d\widetilde Q_m,
\qquad
\frac{d\widetilde Q_e}{d\widetilde Q_m}=g_{2d}(X_0).
\tag{8.11}
$$

The right side has mass one. In particular for every measurable output
event $D$, pulling it back to the joint space shows

$$
Q_e(D)\le\|g_{2d}\|_\infty Q_m(D)
        \le(M-1)Q_m(D),
\qquad Q_e\ll Q_m.
\tag{8.12}
$$

The last norm bound is the actual $g_{2d}=Pg_d$ and the Markov
$L^\infty$ contraction. No numerical value of this bound is required
to transfer null sets. Apply (8.12) to $E^c$ to obtain (8.7) under
the original $e$-start law. Equation (8.11) transfers the complete
future path law after the already specified lead-in; it is stronger
than a separate absolute-continuity assertion for each finite marginal.
It neither supplies a second trajectory nor changes the initial source.

Finally, the Borel repairs in (8.2) cause no ambiguity. Under the
stationary comparison, every $X_j$ has law $m$; under the actual
source, it has law $g_{(j+2)d}m$. Every fixed Borel $m$-null repair
set is therefore avoided at all sampled indices simultaneously,
by a countable union of null events. The properly exceptional set of
the original process is treated in the same way. Transition-kernel
and bounded-class representatives suffice in every displayed integral.
This argument concerns the countable positive-time skeleton, not
avoidance of the source by the continuous path at all times. It
assigns no value to $h(e)$ and no density at time zero. $\square$

**Definition 8.3 (a total finite-record statistic).** Fix a target
length $k\ge1$ and put $K_k=4^k$. For any acquired finite record
$Y_0,\ldots,Y_{L-1}$, including $L=0$, let $N=(L-k)_+$ and retain
all $4^{k+1}$ counters

$$
\begin{gathered}
A_{N,k}(v)=\sum_{j=0}^{N-1}
 \mathbf1\{Y_j\cdots Y_{j+k}=v\}
 \quad(v\in\mathcal L^{k+1}),\\
\sum_{v\in\mathcal L^{k+1}}A_{N,k}(v)=N,\qquad
Z_N=\sum_{u\in\mathcal L^k}A_{N,k}(3u)
   =\sum_{j=0}^{N-1}\mathbf1\{Y_j=3\},\\
\widehat\nu_{N,k}(u)=\frac{A_{N,k}(3u)+1}{Z_N+K_k}
 \quad(u\in\mathcal L^k).
\end{gathered}
\tag{8.13}
$$

Empty sums are zero. For $L\le k$, no window is complete, so $N=0$
and the statistic is the uniform vector. For any $L$, if $Z_N=0$,
all its marked counters vanish and it is again the uniform vector.
The integer $1$ added to each numerator is numerical smoothing of
the retained counters, not an emission or an added observation.

**Theorem 8.4 (the complete original three-read law is consistently
acquired at fixed horizon).** For every fixed original source in
Definition 8.1, (8.13) is a rational probability vector for every
finite record. Under its actual $Q_e$ law, on one probability-one
event, for every fixed $k\ge1$,

$$
\begin{gathered}
\frac{A_{N,k}(3u)}N\longrightarrow c\nu_e^{(k)}(u)
 \quad(u\in\mathcal L^k),\qquad
\frac{Z_N}N\longrightarrow c>0,\\
\operatorname{TV}(\widehat\nu_{N,k},\nu_e^{(k)})
 =\frac12\sum_{u\in\mathcal L^k}
       |\widehat\nu_{N,k}(u)-\nu_e^{(k)}(u)|
 \longrightarrow0.
\end{gathered}
\tag{8.14}
$$

Here $N\to\infty$ uses the first $L=N+k$ actual labels. The TV
error also tends to zero in $Q_e$ expectation. In particular $k=3$
recovers every one of the original 64 probabilities at $2d,3d,4d$
from the complete 256-counter four-word histogram.

*Proof.* Nonnegativity is immediate and the sum of the numerators is
$Z_N+K_k$, a strictly positive denominator even at $N=0$. Theorem
8.2 applied to every $3u$ gives the first limit in (8.14). Summing
its finitely many terms, or applying (8.7) to the one-letter word
$3$, gives $Z_N/N\to q(3)=c$. Thus $Z_N>0$ eventually almost
surely. Divide numerator and denominator of (8.13) by $N$:

$$
\widehat\nu_{N,k}(u)
 =\frac{A_{N,k}(3u)/N+1/N}{Z_N/N+K_k/N}
 \longrightarrow\frac{c\nu_e^{(k)}(u)}c
 =\nu_e^{(k)}(u).
\tag{8.15}
$$

For fixed $k$ there are finitely many coordinates, proving TV
convergence. TV is at most one, so bounded convergence gives the
expectation assertion. The common event from Theorem 8.2 supports all
fixed $k$, but supplies no uniform control when $k$ grows with $N$.
The windows can overlap and have arbitrarily long dependence; no
independent-sample premise was used. $\square$

**Proposition 8.5 (conditional error transfer for these exact counters).**
For $N\ge1$ define the unknown true-frequency discrepancy

$$
\delta_{N,k}=\sum_{u\in\mathcal L^k}
 \left|\frac{A_{N,k}(3u)}N-q(3u)\right|.
\tag{8.16}
$$

For every record, without any independence assumption,

$$
\operatorname{TV}(\widehat\nu_{N,k},\nu_e^{(k)})
 \le\min\left\{1,\frac{N\delta_{N,k}+K_k}{Z_N+K_k}\right\}.
\tag{8.17}
$$

Under $Q_e$, $\delta_{N,k}\to0$ almost surely for fixed $k$.
The right side in (8.17) is a conditional error transfer, not an
acquired error bar.

*Proof.* Put $a_u=A_{N,k}(3u)/N$, $p_u=q(3u)=c\nu_e^{(k)}(u)$,
and $z=Z_N/N$. Since $\sum a_u=z$ and $\sum p_u=c$,
$|z-c|\le\delta_{N,k}$. With $\nu_u=\nu_e^{(k)}(u)$, the
numerator of $\widehat\nu_{N,k}(u)-\nu_u$ can be written

$$
N(a_u-p_u)+N(c-z)\nu_u+1-K_k\nu_u.
\tag{8.18}
$$

The sum of its absolute values is at most
$N\delta_{N,k}+N|c-z|+2K_k$. Divide by
$2(Z_N+K_k)$ and use TV at most one. The convergence of
$\delta_{N,k}$ follows from Theorem 8.2. Its definition contains
unknown $q(3u)$, so finite counter values alone do not evaluate it.
For example a separately certified bound $\delta_{N,3}\le r_N$
would give $(Nr_N+64)/(Z_N+64)$ as an error bound for the original
64-coordinate consumer. No such $r_N$ is supplied here. $\square$

**Proposition 8.6 (paid chronology, finite memory and the remaining
recovery relations).** For $N\ge1$, the statistic (8.13) at fixed
$k$ consumes exactly $N+k$ chronological labels, with final read at
original time $(N+k+1)d$. For $k=3$ these are $N+3$ reads, ending
at $(N+4)d$. It can retain the complete histogram with
$4^{k+1}$ integer counters and a buffer of $k+1$ labels. Its
persistent working storage can be bounded by

$$
O\!\left(4^{k+1}\log_2(N+2)+k+\log_2(k+2)\right)
\quad\text{bits}.
\tag{8.19}
$$

All these operations terminate for a supplied finite record, including
every zero-marker branch. Their consistency does not supply a stopping
time certified to reach a requested TV precision, a confidence radius,
or a current-history predictor.

*Proof.* The last complete window starts at $N-1$ and ends at
$N+k-1$; (8.3) places that last label at $(N+k+1)d$. The initial
$2d$ lead-in and every later gap are paid elapsed time. All $N$
windows increment exactly one of the $4^{k+1}$ counters, including
windows starting with $0,1,B$, and the final $k$ labels are paid
reads completing those windows. No retained label or failed branch
is removed from the histogram. $Z_N$ counts natural markers among
the $N$ starting positions, not independent trials or free prepared
states. The finite law conditioned on an actual marker at a particular
nonstationary time is not asserted to equal $\nu_e^{(k)}$; (8.6)
is a comparison-cylinder identity, used only through the long-record
limits. The source is never reset or conditioned by an intervention.

A counter in $[0,N]$ needs at most $\lceil\log_2(N+2)\rceil$
bits. A rolling word buffer uses $2(k+1)$ bits, and its position,
window total and marked total require only the corresponding finite
integer registers. For $N\ge1$, the record length $L=N+k$ can be
encoded within the order in (8.19). Initializing all histogram
entries, processing each acquired label and summing the marked row
are finite integer operations. The output can share its denominator
$Z_N+K_k$ among $K_k$ integer numerators; its additional written
size is $O(K_k\log_2(N+K_k+1))$ bits. At $k=3$ the retained
histogram has exactly 256 counters and the output has 64 numerators.
The counters' bit lengths grow with $N$; a finite fixed-state
observer is not asserted. A record shorter than a window is handled
by the uniform branch of Definition 8.3.

The statistic takes only $k$ and the actual finite label record as
inputs. It does not query $a,\eta,d,h,\rho,g_d,M$, hidden states
or coefficient/posterior values. This presupposes the unchanged
calibrated passive channel as a mathematical experiment; it constructs
no physical instrument realizing that channel. In particular,
removing $M$ from the statistic's input does not replace the exact
$M$ defining the installed emissions.

The almost-sure statement has the quantifiers: for each fixed source,
each fixed $k$ and almost every actual record, every positive error
tolerance eventually holds for all sufficiently large $N$. It gives
no finite-record test locating that eventual time. A confidence
statement for adaptive stopping would additionally require an
appropriately simultaneous probabilistic guarantee. The discrepancy
in (8.16) identifies a sufficient next obligation for this estimator;
it is not an assertion that all acquisition routes must compute $M$
first or must use these counters.

For a fixed finite history $v$ of length $r\ge1$ and fixed continuation
word $w$, strict positivity of the original emissions gives
$\nu_e^{(r)}(v)>0$. The identity (8.6) then implies

$$
\frac{\nu_e^{(r+|w|)}(vw)}{\nu_e^{(r)}(v)}
 =\frac{q(3vw)}{q(3v)}.
\tag{8.20}
$$

Thus fixed-history conditionals can be obtained as limits of the
corresponding fixed-word probabilities. This does not give error
control for the actual growing history $Y_0\cdots Y_{L-1}$ at the
current cut: its length changes with $L$, and its probability can
shrink. Nor does fixed-horizon convergence establish an inverse from
record laws to $G,H,h,\rho$, source parameters or boundary geometry.
Exact continuation of the linear calibration on all bounded inputs
in Corollary 7.3 has a different domain and remains as stated.
Direct model evaluation from effective parameter names, finite-error
acquisition, current-cut prediction and full mutual recovery of
spatial structure, chronology, boundary and usable memory remain
separate mathematical obligations. Their absence here is not an
impossibility theorem. $\square$

The source correspondence (8.8), its complete actual-path transfer
(8.11), and its original three-read consumer are `repo-derived`
application mathematics. The original full endpoint, normalized zero
line, source densities, boundedness and calibration are the cited
owning suppliers; spectral calculus and Birkhoff convergence are
mature results used inside this derivation. In particular this adds
no general spectral/ergodic theorem or finite-positive existence
claim. The source statements retain their conditional mathematical
scope, and no external priority or formal verification of this
application is asserted.

Avigad–Gerhardy–Towsner's Theorems 5.2–5.3 and Corollary 5.4
also separate convergence from effective access: their rate conclusions
consume representations of the observable and operator, with the
limiting projection norm in Theorems 5.2–5.3, or effective measure
data in the ergodic case. Here the relevant operator would be the
Koopman operator of $S$ on the comparison path probability space,
and the observable a fixed cylinder indicator. A single observed
record supplies neither that effective path-space presentation nor
the required integration procedure. Those positive rate results
therefore do not furnish a rate from the present input; their general
negative examples do not prove one impossible for this diffusion.

[MW-A]: https://arxiv.org/html/0706.1512v3

## 追加锚（本行以下为增补区）

## 9. The original contact defect controls dependent word counts

**Definition 9.1 (the unchanged source and the capacity-defect profile).**
Fix the original finite positive $a,\eta,d$, the full endpoint
$H=H_{\rm end}$ with its selector $A=\rho C$, the coefficient-positive
normalized zero vector $h$, and

$$
m=h^2\mu,\qquad K=U_h^{-1}HU_h,\qquad T_t=e^{-tK},\qquad P=T_d.
$$

All of these are the source, boundary and clock of Definitions 1.1,
7.1 and 8.1. In particular $m$ is the original invariant probability,
$K$ is the full source-inclusive operator, $T$ is conservative,
self-adjoint and Markov, and $\ker K=\mathbb R1$ on real classes. Let
$F$ be the original Friedrichs operator in Appendix II §115 and write

$$
R_r^0=U_h^{-1}(F+r)^{-1}U_h,\qquad R_r=(K+r)^{-1},\qquad
b_r=1-rR_r^01,\qquad d_r=\int_Gb_r\,dm
$$

for $r>0$. The original §§115--116 identities give

$$
0\le b_r\le1,\qquad 0<d_r<1,\qquad
R_r=R_r^0+\frac{|b_r\rangle\langle b_r|}{r d_r},\qquad
d_r\longrightarrow1\quad(r\downarrow0).
$$

Define the source-specific capacity defect

$$
\Theta(r)=\frac{1-d_r}{d_r}.
\tag{9.1}
$$

The number $d_r$ is the exact shifted source capacity divided by $r$:
Appendix II (116.4) gives $\operatorname{Cap}_r(\{e\})=r d_r$.
It is a mathematical value of the fixed original source, not a supplied
numerical name and not a quantity read from the label record.

**Theorem 9.2 (a source-specific centered resolvent estimate).**
Let $u\in L^\infty(G,m;\mathbb R)$ satisfy
$\int u\,dm=0$ and $\|u\|_\infty\le L$. For every $r>0$,

$$
r\langle u,R_ru\rangle_m\le L^2\Theta(r).
\tag{9.2}
$$

If $\nu_u$ is the spectral measure of $K$ at $u$, then

$$
\nu_u((0,r])\le2L^2\Theta(r),\qquad
\langle u,T_su\rangle_m\le L^2\Theta(1/s)\quad(s>0).
\tag{9.3}
$$

The zero spectral atom is absent because $u$ is orthogonal to
$\ker K=\mathbb R1$. Thus (9.1)--(9.3) give a weak low-energy profile
for every centered bounded observable, although they give no power,
exponential or parameter-uniform rate.

*Proof.* Put $Q_r=rR_r^0$ and $\alpha_r=1-d_r$. The resolvent definition
gives $Q_r1=1-b_r$ and $\int Q_r1\,dm=\alpha_r$. Positivity of the
killed resolvent implies

$$
\langle u,Q_ru\rangle_m
 \le\langle |u|,Q_r|u|\rangle_m
 \le L^2\langle1,Q_r1\rangle_m=L^2\alpha_r.
\tag{9.4}
$$

The first inequality follows by writing $u=u_+-u_-$; the cross term
of the positive operator $Q_r$ is nonnegative. The second follows from
$0\le|u|\le L1$ and positivity. Since $\int u\,dm=0$,

$$
|\langle b_r,u\rangle_m|
 =|\langle b_r-1,u\rangle_m|
 \le L\alpha_r.
\tag{9.5}
$$

Multiplying the exact rank-one formula by $r$ and using (9.4)--(9.5)
gives

$$
r\langle u,R_ru\rangle_m
 \le L^2\alpha_r+\frac{L^2\alpha_r^2}{d_r}
 =L^2\frac{\alpha_r}{d_r}=L^2\Theta(r).
$$

The spectral theorem gives
$r\langle u,R_ru\rangle=\int r(\lambda+r)^{-1}\,d\nu_u(\lambda)$.
The multiplier is at least $1/2$ on $(0,r]$, proving the first part of
(9.3). Also $e^{-s\lambda}\le(1+s\lambda)^{-1}$; taking $r=1/s$ in
(9.2) and using functional calculus proves the second part. Finally,
$\nu_u(\{0\})=0$ by the centering assumption. $\square$

**Definition 9.3 (the original passive word stream).** Keep exactly the
readout of Definition 8.1:

$$
M=1+\|g_d\|_\infty,\qquad c=\frac1{4M},\qquad
f_3=cg_d,\qquad f_B=\frac14,\qquad
f_0=f_1=\frac{3/4-f_3}{2},\qquad
\mathcal L=\{0,1,3,B\}.
\tag{9.6}
$$

Here $g_d$ means any permitted bounded Borel representative of its
original $L^2(m)$ class; the exact norm in (9.6) is retained. The source
starts at $e$ at time zero, the lead-in is $2d$, and $Y_j$ is the
passive read at time $(j+2)d$. Conditional on the one source path, all
reads use the fixed functions (9.6) and fresh independent conditional
read noise. No source reset, selected outcome, hidden coordinate or
second trajectory is introduced.

For a nonempty word $w=(w_0,\ldots,w_{L-1})\in\mathcal L^L$ define

$$
F_\varnothing=1,\qquad
F_w=f_{w_0}P F_{(w_1,\ldots,w_{L-1})},\qquad
\pi_L(w)=\int_G F_w\,dm.
\tag{9.7}
$$

The probability vector $\pi_L$ is the invariant comparison law of the
same source and same readout. It is a proof comparison, not a prepared
stationary experiment. Write $w^{\leftarrow}$ for the reversed word and
$\bar F_w=F_{w^{\leftarrow}}$. Reversibility gives
$\int\bar F_w\,dm=\pi_L(w)$, and all these functions take values in
$[0,1]$.

For $N\ge1$ let

$$
A_{N,L}(w)=\sum_{j=0}^{N-1}
 \mathbf1\{Y_j\cdots Y_{j+L-1}=w\},\qquad
a_{N,L}(w)=\frac{A_{N,L}(w)}N.
\tag{9.8}
$$

The windows overlap and use one chronological record. The last label is
$Y_{N+L-2}$, acquired at the original time $(N+L)d$.

**Theorem 9.4 (capacity defect, overlap and the actual source start).**
For every fixed $L\ge1$, every $w\in\mathcal L^L$ and every $N\ge1$, put

$$
V_{N,L}=\min\left\{\frac14,
 \frac{2L-1}{4N}+2\Theta\left(\frac1{Nd}\right)\right\}.
\tag{9.9}
$$

Under the invariant comparison law,

$$
\operatorname{Var}_m(a_{N,L}(w))\le V_{N,L}.
\tag{9.10}
$$

Under the actual $e$-start law $Q_e$,

$$
\mathbb E_e\left[(a_{N,L}(w)-\pi_L(w))^2\right]
 \le (M-1)V_{N,L}.
\tag{9.11}
$$

There is also a certificate-friendly bound that does not require a
numerical name for $M$. Set

$$
D_0=d_{1/(4d)}.
\tag{9.12}
$$

Then the complete $4^L$-vector $a_{N,L}$ satisfies, for every
$\varepsilon>0$,

$$
\mathbb P_e\left(
 \operatorname{TV}(a_{N,L},\pi_L)>\varepsilon\right)
 \le\min\left\{1,\frac{2^{2L-1}}{\varepsilon}
 \sqrt{\frac{V_{N,L}}{D_0}}\right\}.
\tag{9.13}
$$

For $L=4$, this controls all $256$ word counters simultaneously.

*Proof.* Under the invariant law, for a word $w$ and a lag $j\ge L$,
conditioning on the end of the first window and the start of the next,
then using reversibility and the fresh read noises, gives

$$
\operatorname{Cov}_m(I_0(w),I_j(w))
 =\left\langle \bar F_w-\pi_L(w),
 T_{(j-L+1)d}\bigl(F_w-\pi_L(w)\bigr)\right\rangle_m.
\tag{9.14}
$$

Both centered factors have sup norm at most one. Since $T_s$ is positive
self-adjoint, Cauchy--Schwarz in the positive form
$\langle x,T_sy\rangle$ and (9.3) give

$$
|\operatorname{Cov}_m(I_0(w),I_j(w))|
 \le\Theta\left(\frac1{(j-L+1)d}\right).
\tag{9.15}
$$

For $1\le j<L$ the universal Bernoulli bound is $1/4$; it is used
because the windows overlap. To sum the separated lags, let

$$
S_N=\sum_{n=1}^{N-1}(N-n)T_{nd},\qquad
r_N=\frac1{Nd}.
$$

Its spectral multiplier obeys

$$
\sum_{n=1}^{N-1}(N-n)e^{-nd\lambda}
 \le\int_0^N(N-t)e^{-td\lambda}\,dt
 \le\frac{N^2}{1+Nd\lambda}
 =N^2\frac{r_N}{\lambda+r_N}.
\tag{9.16}
$$

The final inequality is $(1+x)e^{-x}\le1$ after putting
$x=Nd\lambda$; the value at $\lambda=0$ follows by continuity.
Thus $S_N\le N^2r_NR_{r_N}$ in the spectral order. Applying the
positive-form Cauchy--Schwarz inequality to the two centered factors in
(9.14), then (9.2), shows that all separated-lag contributions to the
variance, after division by $N^2$, are at most
$2\Theta(r_N)$. The diagonal and the at most $L-1$ overlapping lags
contribute at most $(2L-1)/(4N)$. The variance is also at most $1/4$,
which proves (9.10).

For the actual source start, the future hidden-and-read path beginning
at time $2d$ has Radon--Nikodym derivative $g_{2d}(X_0)$ relative to
the invariant comparison path. The Markov contraction and the original
propagation identity give

$$
\|g_{2d}\|_\infty=\|T_dg_d\|_\infty\le\|g_d\|_\infty=M-1.
\tag{9.17}
$$

Therefore every nonnegative future-record functional $H$ satisfies
$\mathbb E_eH\le(M-1)\mathbb E_mH$. Applying this to the squared
error and using (9.10) proves (9.11).

For (9.13), the source-density estimate of Appendix II (117.3), with
$t=2d$ and $r=1/(4d)$, has
$\sup_{\lambda\ge0}(\lambda+r)e^{-4d\lambda}=r$, hence

$$
\|g_{2d}\|_2^2\le D_0^{-1}.
\tag{9.18}
$$

For every event $E$ depending on the future record,
$\mathbb P_e(E)\le D_0^{-1/2}\mathbb P_m(E)^{1/2}$ by Cauchy--Schwarz.
Under $Q_m$, Cauchy--Schwarz over the $4^L$ coordinates and (9.10)
give

$$
\mathbb E_m\|a_{N,L}-\pi_L\|_1^2
 \le4^{2L}V_{N,L}.
$$

Markov's inequality for $\operatorname{TV}=\frac12\|\cdot\|_1$ and
the preceding change of initial law yield (9.13). $\square$

The defect profile in (9.1) tends to zero as its argument decreases to
zero. Consequently $V_{N,L}\to0$ for every fixed original source and
fixed $L$. This is a fixed-word mathematical convergence statement;
it is not a finite-record stopping rule. It also does not estimate a
growing current history.

**Corollary 9.5 (the complete 256-to-64 original consumer).**
For $w\in\mathcal L^3$, let

$$
\nu_e^{(3)}(w)=\int_G g_{2d}f_{w_0}P(f_{w_1}Pf_{w_2})\,dm,
\tag{9.19}
$$

the original $e$-start law at exactly $2d,3d,4d$. For every such $w$,

$$
\pi_4(3w)=c\,\nu_e^{(3)}(w),\qquad
\sum_{w\in\mathcal L^3}\pi_4(3w)=c.
\tag{9.20}
$$

Indeed, if $F_w=f_{w_0}P(f_{w_1}Pf_{w_2})$, then

$$
\pi_4(3w)=\langle f_3,PF_w\rangle_m
 =c\langle g_d,PF_w\rangle_m
 =c\langle Pg_d,F_w\rangle_m
 =c\langle g_{2d},F_w\rangle_m.
$$

This uses the exact original $f_3=cg_d$, the same $P=T_d$ and the
original density propagation; label $3$ is not a selected outcome or a
source contact.

Retain all $256$ counters from (9.8) at $L=4$. Put

$$
Z_N=\sum_{w\in\mathcal L^3}A_{N,4}(3w),\qquad
\widehat\nu_N(w)=\frac{A_{N,4}(3w)+1}{Z_N+64}.
\tag{9.21}
$$

The integer $1$ is record-side smoothing. It adds no emission and no
source operation. For

$$
\Delta_N=\sum_{w\in\mathcal L^3}
 \left|a_{N,4}(3w)-c\nu_e^{(3)}(w)\right|,
$$

every record satisfies

$$
\operatorname{TV}(\widehat\nu_N,\nu_e^{(3)})
 \le\min\left\{1,
 \frac{\Delta_N+64/N}{Z_N/N+64/N}\right\}.
\tag{9.22}
$$

To see this, use $|Z_N/N-c|\le\Delta_N$ and
$\sum_w|1-64\nu_e^{(3)}(w)|\le128$ after putting the two fractions
over the common denominator. In particular, for every $0<t<c$,

$$
\mathbb P_e(\Delta_N>t)
 \le\min\left\{1,\frac{256}{t}
 \sqrt{\frac{V_{N,4}}{D_0}}\right\},
\tag{9.23}
$$

and on $\{\Delta_N\le t\}$ the right side of (9.22) is at most

$$
\frac{t+64/N}{c-t+64/N}.
\tag{9.24}
$$

Thus a fixed mathematical confidence statement is obtained by choosing
$N$ and $t$ so that the expression in (9.23) is at most a prescribed
$\alpha$ and (9.24) is at most a prescribed error
$\varepsilon$. The statement retains every one of the $256$ length-four
outcomes and all $64$ original length-three outcomes. The $N$ windows
use exactly $N+3$ chronological labels, ending at original time
$(N+4)d$, and a streaming implementation needs $256$ counters, a
four-label buffer and integer arithmetic on counters of $O(\log(N+1))$
bits.

**Proposition 9.6 (what a numerical certificate would and would not
close).** The preceding inequalities are symbolic source-specific
bounds. They become a finite numerical confidence certificate for a
fixed $N$ only if an input packet supplies certified lower bounds

$$
0<D_0^-\le d_{1/(4d)},\qquad
0<D_N^-\le d_{1/(Nd)}.
\tag{9.25}
$$

The packet must identify the same $a,\eta,d$, the same $H_{\rm end}$
selector, the same $h,m,F$ and the original clock, and must state the
encoding, precision and construction or validation cost of the two
rational bounds. Substitution gives the explicit rational upper envelope

$$
\overline V_{N,4}=\frac7{4N}+2\frac{1-D_N^-}{D_N^-},\qquad
\mathbb P_e(\Delta_N>t)
 \le\min\left\{1,\frac{256}{t}
 \sqrt{\frac{\overline V_{N,4}}{D_0^-}}\right\}.
\tag{9.26}
$$

An alternative certificate may supply an original-domain vector $v$ and
validated residual data for $(F+q)^{-1}h$; such data can lower-bound
$d_q$ without using a global $F^{-1}$. Concretely, if
$v\in D(F)$, $\|h-(F+q)v\|_2\le\epsilon_q$ and
$\langle h,v\rangle\le B_q$, then

$$
d_q=1-q\langle h,(F+q)^{-1}h\rangle
 \ge1-qB_q-\epsilon_q.
\tag{9.27}
$$

Indeed $\|(F+q)^{-1}\|\le q^{-1}$, so
$\|(F+q)^{-1}h-v\|_2\le\epsilon_q/q$. The residual proof still has to
refer to the original normalized $h$ and the full space, and its
construction cost is an additional resource. The present passive
contract supplies neither (9.25), a residual evaluator, nor a numerical
name for the fixed real parameters. A conditional evaluator taking those
extra inputs would therefore be a separate access contract, not a
record-only acquisition result. The label record alone supplies the
counters and the observed denominator $Z_N$, but it does not certify
$d_r$, $D_0$, $M$, a confidence radius or a stopping time.

The exact rank-one/contact identities used here are the original
Appendix II §§115--117 suppliers; the readout and $Pg_d=c^{-1}Pf_3
=g_{2d}$ correspondence is the original Appendix III Definition 134.1
and (134.15). The covariance summation, spectral calculus, Cauchy--Schwarz,
Markov inequality and change-of-initial-law step are mature tools used
inside this source-specific composition. General weak-Poincaré and
reversible-chain rate results, such as Röckner--Wang [RW] and
Andrieu--Lee--Power--Wang [ALPW], require a supplied profile or
certificate and do not furnish one for this singular original endpoint;
Paulin's [PAULIN] spectral-gap route likewise is not invoked. No
finite-chain replacement,
global Nash or doubling hypothesis, spectral gap, source reset or
stationary preparation has been added.

The bridge changes the missing relation from an unspecified covariance
supplier to the explicit original scalar $d_r$ and its certified lower
bound. It does not close effective numerical acquisition, record-only
stopping, current-history prediction, or mutual recovery of space, time,
boundary and memory. Those remain separate relations for the same
source and clock.

[RW]: https://doi.org/10.1006/jfan.2001.3776
[ALPW]: https://arxiv.org/html/2312.11689v1
[PAULIN]: https://arxiv.org/html/1212.2015v3

## 追加锚（本行以下为增补区）

## 10. Explicit original-source exterior mass and a zero-energy correction modulus

**Definition 10.1 (the same source and the correction to be estimated).**
Retain (1.1)--(1.3), including raw Haar measure, the original unit-source
$\Gamma$, finite positive $a,\eta,d$, the maximal coefficient maps and
the derived selector $A=\rho C$. Write

$$
A_0=aL-\eta\partial_w^2,\qquad V=g_c\Gamma,\qquad
g_c=16\sqrt{a\eta},\qquad F=H_F,\qquad D(F)=\{C=0\}.
\tag{10.1}
$$

Here $F$ is the original Friedrichs operator, rather than the full
$H_{\rm end}$. Denote the particular compactly supported vector and
its annular error in [E, (110.12)--(110.14)] by
$\gamma_{\log}$ and $f_{\log}=S_{\min}^*\gamma_{\log}$, respectively.
Thus $\gamma_{\log}$ has logarithmic coefficient one, its local equation
is the actual original equation, and $f_{\log}$ is smooth and supported
on a compact punctured annulus. The existing compact-source range result
[E, (110.15)] defines

$$
w_* =\gamma_{\log}-F^{-1}f_{\log},\qquad
h=w_*/\|w_*\|_2,\qquad m=h^2\mu,
\tag{10.2}
$$

with the original coefficient-positive choice. The inverse in (10.2)
is its spectral inverse on its domain. It is not bounded on all of
$L^2(G,d\mu)$. No numerical name for either local vector in (10.2)
is included in this definition.

The estimates below change no experiment. In particular
$P=T_d$, $g=g_{2d}$, $M=1+\|g_d\|_\infty$, $c=1/(4M)$,
$f_3=cg_d$ as a bounded Borel class, $f_B=1/4$, and
$f_0=f_1=(3/4-f_3)/2$ remain exactly as in §8. The start is $e$,
the clock is the original elapsed time, and the only empirical outputs
are the original chronological labels with their fresh conditional
read noise.

**Definition 10.2 (explicit constants).** Use symmetric coordinates
$\xi=(x,y,z)$, $s=w-xy/2$, and the homogeneous gauge
$\varrho=(|\xi|^4+s^2)^{1/4}$. This $\varrho$ is distinct from the
endpoint selector $\rho$. Set

$$
\begin{gathered}
v_0=9,\qquad B=32,\qquad H_2=10^7,\qquad H=H_2/a,\\
\beta=\min\{(512a)^{-1},(1024\eta)^{-1}\},\qquad
D=\frac38a^{-5/2}\beta^{-3/2},\qquad
T=64D\sqrt{5v_0},\qquad D_1=4Hg_cB,\qquad \ell=10/\sqrt a,\\
C_\psi=17a/4+\eta,\qquad B_\psi=23a+4\eta,\qquad
J_\phi=17a+16\eta,\qquad W=\sqrt{32v_0},\\
j_0=B_\psi+2\sqrt{C_\psi}\sqrt{8g_cB+J_\phi},\qquad
j_1=2\sqrt{C_\psi},\\
c_1=g_cB\sqrt{5v_0}+Wj_0,\qquad c_2=Wj_1.
\end{gathered}
\tag{10.3}
$$

For a rational support radius $\Lambda\ge1$, define

$$
\begin{gathered}
c_3=\sqrt{v_0\Lambda^5},\qquad R_{\min}=4\max\{2,\Lambda\},\\
R_* =\max\{R_{\min},(8Tc_1)^2,8D_1\},\qquad
A_* =\sqrt{\ell R_*},\qquad
B_* =Tc_2/\sqrt{R_*},\qquad C_* =Tc_3/\sqrt{R_*},\\
C_{\Lambda}=\max\{1,(4A_*)^4,(4B_*)^2,4C_*\},\\
A_{\Lambda}=T(c_1C_{\Lambda}+c_2\sqrt{C_{\Lambda}}+c_3),\qquad B_{\Lambda}=D_1C_{\Lambda},\\
\tau_{\Lambda}(R)=A_{\Lambda}R^{-1/2}+B_{\Lambda}R^{-1},\qquad
D_{\Lambda}=\sqrt{\ell C_{\Lambda}^2/2+8A_{\Lambda}^2+8B_{\Lambda}^2}.
\end{gathered}
\tag{10.4}
$$

All these are finite positive expressions in the original coefficients
and the support radius. They are sufficient bounds, with no sharpness
or practical-efficiency assertion. In particular $B$ bounds the actual
$\Gamma$; it does not define a different potential or replace $g_c$.

**Theorem 10.3 (source-specific exterior and low-energy bounds).**
Let $f\in L^2(G,d\mu;\mathbb C)$ have support in
$\{\varrho\le\Lambda\}$, put $t_f=\|f\|_2$, and retain the original
$C=0$ boundary for

$$
u_r=(F+r)^{-1}f\quad(r>0),\qquad y=F^{-1}f.
$$

The existence of $y$ is the already supplied compact-source result.
For every $r>0$ and every $R\ge R_{\min}$,

$$
\begin{gathered}
\|u_r\|_2,\ \|y\|_2\le C_{\Lambda}t_f,\\
\|\mathbf1_{\{\varrho>R\}}u_r\|_2,
\ \|\mathbf1_{\{\varrho>R\}}y\|_2\le t_f\tau_{\Lambda}(R),\\
\|y-u_r\|_2^2
 \le t_f^2\left(\frac{\ell R C_{\Lambda}^2\sqrt r}{2}
                         +4\tau_{\Lambda}(R)^2\right).
\end{gathered}
\tag{10.5}
$$

Consequently

$$
\|F^{-1}f-(F+r)^{-1}f\|_2\le t_fD_{\Lambda}r^{1/8}
\quad\left(0<r\le\min\{1,R_{\min}^{-4}\}\right).
\tag{10.6}
$$

For every original maximal zero vector $z\in\ker S_{\min}^*$,

$$
\|\mathbf1_{\{\varrho>R\}}z\|_2
 \le\left(\frac{Tc_1}{\sqrt R}+\frac{D_1}{R}\right)\|z\|_2
\quad(R\ge8).
\tag{10.7}
$$

In particular the original normalized state satisfies the coefficient-only
exterior probability estimate

$$
m\{\varrho>R\}
 \le\min\left\{1,
       \left(Tc_1R^{-1/2}+D_1R^{-1}\right)^2\right\}.
\tag{10.8}
$$

For the particular pair in (10.2), choose $\Lambda\ge1$ containing both
supports, and use the constants for that $\Lambda$. Put
$w_r=\gamma_{\log}-(F+r)^{-1}f_{\log}$ and
$I_R=\int_{\{\varrho\le R\}}|w_*|^2d\mu$. Then

$$
\begin{gathered}
I_R\le\|w_*\|_2^2
 \le I_R+\|f_{\log}\|_2^2\tau_{\Lambda}(R)^2\quad(R\ge R_{\min}),\\
\|w_*-w_r\|_2\le\|f_{\log}\|_2D_{\Lambda}r^{1/8}
 \quad\left(0<r\le\min\{1,R_{\min}^{-4}\}\right).
\end{gathered}
\tag{10.9}
$$

Thus the global exterior remainder and the discount error have explicit
vanishing bounds. Formula (10.9) does not construct $I_R$,
$f_{\log}$, $\gamma_{\log}$ or the positive-$r$ solution.

Proof. The following free estimates and cutoff computations supply the
constants; all interacting steps retain the original source and domain.
The symmetric group law gives
$\varrho(pq)\le2(\varrho(p)+\varrho(q))$ and
$\varrho(p^{-1})=\varrho(p)$. For example, if
$A=\varrho(p)$ and $B'=\varrho(q)$, the horizontal component of $pq$
has length at most $A+B'$, while its central component has absolute
value at most $A^2+B'^2+AB'/2\le(A+B')^2$. This even gives the
smaller factor $2^{1/4}$. The dilation Jacobian is $R^5$ and

$$
\mu\{\varrho<1\}
 =8\pi\int_0^1t^2\sqrt{1-t^4}\,dt<9=v_0.
\tag{10.10}
$$

The original free heat formula [Continuation III, (85.12)](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md), including its
$1/(2\pi)$ inverse central Fourier factor and the independent $z$
Gaussian, is

$$
h_t^L(\xi,s)=\frac{t^{-5/2}}{16\pi^{5/2}}e^{-z^2/(4t)}
 \int_{\mathbb R}\frac{u}{\sinh u}
 \exp\!\left(-\frac{(x^2+y^2)u\coth u}{4t}
                         +\frac{ius}{t}\right)du.
\tag{10.11}
$$

This is Krötz--Thangavelu--Xu [EXT-HEAT, (4.1.2)] at $n=1$ for
the horizontal generator, with the stated product Gaussian. Shift the
contour to $u+i\theta\operatorname{sgn}s$, $\theta=\pi/4$; at
$s=0$ either sign is allowed. The apparent singularity at zero is
removable, the strip contains no poles, and the exponential decay of
$u/\sinh u$ makes the vertical sides tend to zero. On this line,

$$
\operatorname{Re}[(u+i\theta)\coth(u+i\theta)]
 =u\tanh(2u)+\frac{\theta}{\cosh(2u)}\ge\frac18.
$$

For $|u|\le1$, use $\theta>3/4$ and $\cosh2<4$; for
$|u|\ge1$, use $u\tanh(2u)\ge\tanh2>1/2$.
Moreover the integral of $|(u+i\theta)/\sinh(u+i\theta)|$ is
at most $4+18/e<16$: the integrand is at most $2$ on $[-1,1]$,
and at most $3(|u|+1)e^{-|u|}$ outside it. Positivity of the
original heat kernel and $|\xi|^2+|s|\ge\varrho^2$ give

$$
0\le h_t^L(p)\le\frac18t^{-5/2}
                 e^{-\varrho(p)^2/(32t)},\qquad
0<\Gamma(p)\le B\varrho(p)^{-3}\quad(p\ne e).
\tag{10.12}
$$

Indeed integration of the first bound gives the sufficient coefficient
$32^{3/2}\sqrt\pi/16<24<32=B$. This uses the free heat formula only
to estimate the original Green coefficient. It is not a formula for
the interacting heat kernel of $F$ or $H_{\rm end}$.

Here is an explicit instance of the mature weighted Schur argument in
[EXT-HARDY, Theorem 3.1 and Corollary 3.2]. For $2<\alpha<5$ set

$$
J(\alpha)=2880\left(\frac1{5-\alpha}+\frac1{\alpha-2}\right)
                          +2250\,4^\alpha.
$$

For $\varrho(p)=1$, split
$\int\varrho(q)^{-\alpha}\varrho(q^{-1}p)^{-3}d\mu(q)$
into $\varrho(q)<1/4$, $1/4\le\varrho(q)\le4$, and
$\varrho(q)>4$. In the first part the other distance is at least
$1/4$, giving
$5v_0\,4^{\alpha-2}/(5-\alpha)\le2880/(5-\alpha)$.
In the middle part $\varrho(q)^{-\alpha}\le4^\alpha$ and
$\varrho(q^{-1}p)\le10$; integration of the latter distance to power
$-3$ is at most $5v_0\,10^2/2=2250$. In the last part
$\varrho(q^{-1}p)\ge\varrho(q)/4$, giving at most
$5v_0\,4^{5-\alpha}/(\alpha-2)\le2880/(\alpha-2)$.
Translation preserves Haar measure; homogeneous radial integration and
dilation therefore prove, for arbitrary $p\ne e$,

$$
\int_G\varrho(q)^{-\alpha}\varrho(q^{-1}p)^{-3}d\mu(q)
 \le J(\alpha)\varrho(p)^{2-\alpha}.
\tag{10.13}
$$

Apply the two-sided Schur test to
$\varrho(p)^{-2}\Gamma(q^{-1}p)$ with weight $\varrho^{-5/2}$.
Its row and column constants are bounded by $BJ(5/2)$ and $BJ(9/2)$.
Here $J(5/2)=78912<80000$ and
$J(9/2)=1158912<1160000$, so its norm is less than
$32\sqrt{80000\cdot1160000}<H_2$.
Green representation on the free smooth core, followed by its graph
density, gives $\|\varrho^{-2}v\|_2\le H_2\|Lv\|_2$ on $D(L)$.
The original strongly commuting joint spectral calculus has
$\|L(A_0+r)^{-1}\|\le1/a$. Duality and the zero-energy spectral
limit, on exactly the weighted forcing class, consequently give

$$
\|Q_rb\|_2\le H\|\varrho^2b\|_2,
\quad Q_r=(A_0+r)^{-1},\quad r\ge0,
\quad b,\varrho^2b\in L^2.
\tag{10.14}
$$

At $r=0$ the uniform positive-$r$ estimate and monotone convergence
put these $b$ in $D(A_0^{-1})$; $\ker A_0=0$ is the original free
fact [E, (105.4)--(105.6)]. No unweighted globally bounded zero inverse
is asserted.

Strong commutation also gives the actual free $A_0$ heat kernel by
convolving $h_{at}^L$ in $s$ with the Gaussian of variance $2\eta t$.
For a central displacement $v$ with $|v|\le\varrho(p)^2/16$,
the quasi-triangle inequality gives
$\varrho(p(0,0,0,-v))\ge\varrho(p)/4$.
The complementary Gaussian probability is at most
$2\exp[-\varrho(p)^4/(1024\eta t)]$.
For $\varrho(p)\ge1$, (10.12) thus bounds the free heat kernel by
$\frac38a^{-5/2}t^{-5/2}\exp[-\beta\varrho(p)^2/t]$.
After time integration its zero Green kernel is at most
$D\varrho(p)^{-3}$, since $\sqrt\pi/2<1$. Positive-$r$ free
Green kernels are bounded by this one. If $b$ is supported in
$\{\varrho\le S\}$ and $R\ge4\max\{S,1\}$, separation gives
$\varrho(q^{-1}p)\ge\varrho(p)/4\ge1$ on the exterior.
Minkowski's inequality and
$\int_{\{\varrho>R\}}\varrho^{-6}d\mu\le5v_0/R$ imply

$$
\|\mathbf1_{\{\varrho>R\}}Q_rb\|_2
 \le TR^{-1/2}\|b\|_1\quad(r\ge0).
\tag{10.15}
$$

Here compactly supported $L^2$ data are in the weighted class of
(10.14), so the zero inverse and its kernel expression are legitimate.

For the interacting localization, let
$p_0(t)=10t^3-15t^4+6t^5$ on $[0,1]$, extended by zero below
and one above. It is $C^2$, $|p_0'|\le2$, $|p_0''|\le6$.
Set $\psi=p_0(\varrho-1)$. Choose $\phi=p_0(2\varrho-1)$ below
$\varrho=1$, $\phi=1$ on $[1,2]$, and
$\phi=p_0(3-\varrho)$ above $2$.
Thus $\phi$ has compact punctured support and is one on
$\operatorname{supp}d\psi$. In these coordinates the fields are
$X_1=\partial_x-(y/2)\partial_s$,
$X_2=\partial_y+(x/2)\partial_s$, $X_3=\partial_z$.
Writing $Q=\varrho^4$, direct differentiation gives

$$
\begin{gathered}
\sum_i(X_iQ)^2=16|\xi|^6+(x^2+y^2)s^2,\qquad
\sum_iX_i^2Q=20|\xi|^2+(x^2+y^2)/2,\\
\sum_i|X_i\varrho|^2\le17/16,\qquad
\left|\sum_iX_i^2\varrho\right|\le133/(16\varrho),\\
|\partial_s\varrho|\le(2\varrho)^{-1},\qquad
|\partial_s^2\varrho|\le5/(4\varrho^3).
\end{gathered}
\tag{10.16}
$$

For $\mathcal C[v]=a\sum_i|X_iv|^2+\eta|\partial_sv|^2$, these
give $\mathcal C[\psi]\le C_\psi$,
$|A_0\psi|\le B_\psi$, and $\mathcal C[\phi]\le J_\phi$.
All derivatives occur off $e$. The $C^2$ cutoffs may be used directly
in the weak product identities, or obtained by smooth approximation
on their fixed punctured derivative supports.

Take $u=u_r$ and $N=\|u\|_2$. Punctured local elliptic regularity
for the actual symbol [E, (108.4), (110.19)] makes the following compact
test legal. The complex cutoff identity is

$$
\sum_i a\|X_i(\phi u)\|_2^2+\eta\|\partial_s(\phi u)\|_2^2
 =\operatorname{Re}\langle\phi^2u,f\rangle
  +\int(V-r)\phi^2|u|^2d\mu+\int\mathcal C[\phi]|u|^2d\mu.
$$

On the support of $\phi$, $V\le8g_cB$.
In particular the free energy of $u$ on $1\le\varrho\le2$ is at
most $(8g_cB+J_\phi)N^2+t_fN$. For
$b_u=[A_0,\psi]u=(A_0\psi)u-2a\sum_i(X_i\psi)X_iu
-2\eta(\partial_s\psi)\partial_su$, Cauchy--Schwarz gives

$$
\|b_u\|_2\le j_0N+j_1\sqrt{t_fN},\qquad
\|b_u\|_1\le W(j_0N+j_1\sqrt{t_fN}).
\tag{10.17}
$$

The existing exterior-domain passage [E, (110.10)] puts
$\psi u\in\mathcal E_2$. Its exact equation is

$$
(A_0+r)\psi u=V\psi u+b_u+\psi f.
\tag{10.18}
$$

The right side and its product by $\varrho^2$ belong to $L^2$:
the commutator and forcing have compact support, while
$\varrho^2\Gamma\psi\le B/\varrho$ for $\varrho\ge1$.
Free form representation therefore puts $\psi u\in D(A_0)$ and
permits (10.14)--(10.15). This is precisely the original-domain
argument [E, (110.20)], not an identification of $D(F)$ with a free
or punctured graph domain.

For $R\ge R_{\min}$, split the right side of (10.18) at
$S=R/4$. The commutator and $\psi f$ are inside this ball, and
$\|\Gamma\psi\|_2\le B\sqrt{5v_0}$ by (10.12) and radial
integration from $1$ to infinity. Its inside part has $L^1$ norm
at most $c_1N+c_2\sqrt{t_fN}+c_3t_f$.
The outside part is just $\mathbf1_{\{\varrho>S\}}V\psi u$;
its weighted $L^2$ norm is at most $g_cBN/S$.
Since $\psi=1$ on $\{\varrho>R\}$, (10.14)--(10.15) yield

$$
\|\mathbf1_{\{\varrho>R\}}u_r\|_2
 \le\left(\frac{Tc_1}{\sqrt R}+\frac{D_1}{R}\right)N
      +\frac{Tc_2}{\sqrt R}\sqrt{t_fN}
      +\frac{Tc_3}{\sqrt R}t_f.
\tag{10.19}
$$

For $z\in\ker S_{\min}^*$, the same compact test uses $f=r=0$.
The needed global free-domain membership of $\psi z$ is
[E, (108.6)--(108.9)], also included in the full maximal-domain
statement (112.7). Equation (10.18) and the weighted zero inverse
then hold on their actual domains. The preceding split needs only
$R\ge8$ and proves (10.7). Applying it to $h$, whose norm is already
one by its mathematical definition, proves (10.8) without querying
its normalization.

It remains to remove $N$ from (10.19) and control the zero-energy
error. The whole-closure inequality [E, (107.5)] states, for
$v\in\mathcal Q_c$,

$$
\int_{\{|\xi|<R\}}|v|^2d\mu
 \le\frac{\pi^2R}{\sqrt a}\|v\|_2\sqrt{\overline q_c[v]}
 \le\ell R\|v\|_2\sqrt{\overline q_c[v]}.
\tag{10.20}
$$

This supplier includes singular form-domain vectors; finite separate
kinetic and potential integrals at the source are unnecessary.
For $u_r$, form representation gives
$\overline q_c[u_r]+rN^2=\operatorname{Re}\langle u_r,f\rangle
\le t_fN$. Since $\{\varrho\le R\}\subset\{|\xi|\le R\}$,
its inside norm is at most $\sqrt{\ell R}N^{3/4}t_f^{1/4}$.
At $R=R_*$ the coefficient of $N$ in (10.19) is at most $1/4$.
If $t_f>0$, the inside/outside decomposition with $x=N/t_f$ gives

$$
\frac34x\le A_*x^{3/4}+B_*\sqrt x+C_*.
\tag{10.21}
$$

For $x>C_{\Lambda}$, each term on the right is strictly less than $x/4$,
a contradiction. Thus $N\le C_{\Lambda}t_f$; if $t_f=0$ the resolvent
vector is zero. Substitution in (10.19) proves the uniform tail in
(10.5). The existing strong limit $u_r\to y$ as $r\downarrow0$
[E, (110.15)] passes both bounds to $y$.

Set $e_r=y-u_r=r(F+r)^{-1}y\in D(F)$. The spectral theorem gives

$$
\|e_r\|_2\le C_{\Lambda}t_f,\qquad
\overline q_c[e_r]\le\frac r4C_{\Lambda}^2t_f^2,
\tag{10.22}
$$

because $\sup_{\lambda\ge0}\lambda r^2/(\lambda+r)^2=r/4$.
Equation (10.20) bounds its squared inside mass by
$\ell RC_{\Lambda}^2t_f^2\sqrt r/2$.
The two exterior bounds give exterior norm at most $2t_f\tau_{\Lambda}(R)$.
This proves the last line of (10.5). Set $R=r^{-1/4}$ in the stated
range of $r$. Then
$\tau_{\Lambda}(R)^2\le2A_{\Lambda}^2r^{1/4}+2B_{\Lambda}^2r^{1/2}$;
since $r\le1$, (10.4) proves (10.6).
Finally, outside the support of $\gamma_{\log}$ one has
$w_*=-F^{-1}f_{\log}$. Splitting its total squared norm at $R$
proves the first line of (10.9), and (10.6) proves the second.
$\square$

**Definition 10.4 (numerical input, certificates and their cost).**
A numerical parameter name, as an additional model-side contract,
returns on input $j\in\mathbb N$ rational intervals containing the
exact original $a$ and $\eta$, each of width at most $2^{-j}$.
Query successive $j$ until both lower endpoints are positive.
This terminates for every fixed positive pair. No uniform bound over
all pairs, or bound on the cost of a name's response, is assumed.
Rational interval arithmetic, with rational outward square-root bounds,
then supplies finite rational upper bounds on every constant in
(10.3)--(10.4); use a positive lower bound for $\beta$ and all other
denominators. Coarse initial positive brackets suffice. The minimum
and maximum operations require no equality decision.

From these parameter names alone, let $U_1\ge Tc_1$ and
$U_2\ge D_1$ be positive rational upper bounds. On input $k\ge1$,
choose a dyadic radius satisfying

$$
R\ge\max\{8,(2^{k+1}U_1)^2,2^{k+1}U_2\}.
\tag{10.23}
$$

The finite packet consisting of the parameter brackets, outward constant
bounds, $k$ and $R$ certifies
$m\{\varrho>R\}\le2^{-2k}$. Its conclusion is about the original
normalized state even though the packet contains no state name, local
mass, boundary coefficient, tail oracle or norm of $w_*$.

For a general forcing in Theorem 10.3, a further conditional input is
a rational $\Lambda\ge1$ with the stated support promise and a global $L^2$
name of that exact $f$. One concrete encoding returns rational complex
step functions on finite rational boxes in the original coordinates,
with certified $L^2(d\mu)$ error at most $2^{-j}$.
Their norms are enclosed by finite rational arithmetic and square-root
bounds. Thus a positive rational $\bar t\ge\|f\|_2$ is obtainable
without deciding whether $f=0$. For positive rational $\varepsilon$,
outward upper bounds for $A_{\Lambda},B_{\Lambda},D_{\Lambda}$ allow finite dyadic choices
satisfying

$$
\begin{gathered}
R\ge\max\{R_{\min},(2\bar t A_{\Lambda}/\varepsilon)^2,
                               2\bar t B_{\Lambda}/\varepsilon\},\\
0<r\le\min\{1,R_{\min}^{-4},
                         (\varepsilon/(\bar t D_{\Lambda}))^8\}.
\end{gathered}
\tag{10.24}
$$

These certify, respectively, an exterior norm error at most
$\varepsilon$ for $F^{-1}f$ and a discount error at most
$\varepsilon$. In (10.24) replace the displayed constants by their
outward bounds before making the rational comparisons. This constructs
the radius and discount certificates, not the corresponding solution
vectors. For fixed enclosing constants the sufficient radius is
$O(\varepsilon^{-2})$, and a sufficient discount can be chosen within
a fixed positive factor of $\varepsilon^8$ for small $\varepsilon$.
The binary scale lengths grow as $O(\log(1/\varepsilon))$.
Charge every parameter/forcing-name query and every rational operation;
no complexity bound for the names, PDE solution, local integration or
empirical sampling follows. The constants are coarse and no numerical
solver performance is asserted.

For (10.9), the supplied forcing must actually be
$S_{\min}^*\gamma_{\log}$ from the same source, with logarithmic
coefficient one. An arbitrary step-function name or an unrelated
coefficient field does not establish that correspondence. If the
actual local integral has been enclosed by
$I_R^-\le I_R\le I_R^+$ and the actual forcing norm by $\bar t$,
the new global remainder makes
$[I_R^-,I_R^++\bar t^2\tau_{\Lambda}(R)^2]$ a norm-squared enclosure.
No numerical procedure for the local interval is supplied here; it
must include the region meeting $e$. In particular (10.8) is a
normalized-state exterior certificate, not an evaluation of the
unnormalized $\|w_*\|_2$.

**Definition 10.5 (suppliers and the unpaid relation).** The original
Green normalization, group, Fourier units and clock are the supplies
of Continuation III §§82--85. The free domains and joint calculus
are [E, (102.6), (105.4)--(105.6)], the whole-closure local-mass
inequality is (107.5), and the legal exterior cutoff passages are
(108.9), (110.10), (110.20) and (112.7).
The actual local logarithmic solution, its cutoff error, compact-source
range and global gluing are (110.12)--(110.22).
Those qualitative results are reused. The additional deduction is the
explicit same-source exterior remainder and its combination with the
whole-closure inequality into (10.5)--(10.9).

The heat supplier [EXT-HEAT] uses Lebesgue Haar measure and the
$n=1$ horizontal sub-Laplacian; its full Laplacian with an additional
central derivative is not used. The Hardy supplier [EXT-HARDY] concerns
stratified groups, a homogeneous norm, $1<p<\infty$ and order
$0<\alpha<Q/p$. Here $Q=5$, $p=2$, $\alpha=2<5/2$.
Its finite norm is not taken as a numerical input: (10.13) supplies
the displayed sufficient constant. The row exponents $5/2$ and $9/2$
in that computation are Schur weights, not the order $\alpha$ of the
literature theorem. The complex cutoff and local regularity steps are
the existing original-domain supplies, which require ellipticity only
on compact punctured sets.

Colbrook--Horning--Townsend [EXT-SPECTRAL, §6.1, (26)] implement
resolvent computation for regular self-adjoint ordinary differential
operators on a line or half-line, with smooth coefficients and
nonvanishing leading coefficient; self-adjointness is a client
obligation. This does not supply an evaluator for the present singular
four-coordinate $C=0$ problem. The native cylinder/Dirichlet exterior
results concern different operators and boundary conditions, and no
transfer by their exterior terminology is made. These are bounded
supplier correspondences, with no literature-priority, exhaustive
absence or noncomputability assertion.

The remaining source-owned construction is a numerical name for the
actual weighted-cylinder logarithmic solution and its annular graph
data, including an effective choice and inverse control for the
original thin-layer error in [E, (110.11)--(110.14)]. A certified
positive-$r$ Friedrichs solution with the original $C=0$ source
boundary is also still required. Neither an abstract form core nor
punctured-only strong residual searches supply these inputs.
Consequently $\|w_*\|_2$, evaluated $d_r$, and numerical confidence
or stopping rules for the passive record remain unpaid. The parameter
and forcing names in Definition 10.4 are additional mathematical
access; the original passive contract supplies neither. This exterior
and low-energy intermediate neither closes record-only acquisition nor
adds distinguishability to the fixed linear readout stack. Mutual
recovery of space, time, boundary and memory remains a separate,
continuing programme.

[EXT-HEAT]: https://arxiv.org/html/math/0401243v2
[EXT-HARDY]: https://arxiv.org/html/1308.2373v1
[EXT-SPECTRAL]: https://arxiv.org/html/2006.01766v1

## 追加锚（本行以下为增补区）

## 11. Numerical names of the original zero state from its actual coefficients

**Definition 11.1 (access, norms and finite representatives).** Retain
the original source, operators, coefficient maps and normalizations in
Definitions 1.1 and 10.1. The numerical inputs are interval names of the
exact original $a,\eta>0$ as in Definition 10.4 and a requested rational
absolute error. A positive-discount query additionally supplies a name of
the requested $r>0$. A general resolvent query supplies a global
$L^2(d\mu)$ name of its forcing. The construction of $w_*$ below generates
its own forcing from $a,\eta$. There is no input naming a local solution,
boundary coefficient, operator matrix, resolvent, tail, normalization or
$h$. A name is a total mathematical function on requested precisions;
the cost of answering its queries is charged separately.

A finite $L^2$ representative is a rational complex step function on
finitely many bounded rational boxes in the original coordinates. A name
returns such representatives with certified global norm errors tending
to zero at a prescribed rate. In particular finite norms and inner
products have arbitrarily accurate rational enclosures. A graph-pair
name of an **exact** pair $(u,S^*u)$ returns $(U,V;\alpha,\beta)$ with

$$
\|U-u\|_2\le\alpha,\qquad \|V-S^*u\|_2\le\beta.
\tag{11.1}
$$

It asserts neither $U\in D(S^*)$ nor $S^*U=V$. Errors of intermediate
cylinder names are measured in the ordinary product Sobolev norms on
$\mathbb R\times S^3$. Finite compact smooth tensor sums, with rational
coefficients, ordinary spherical harmonics and computable compact smooth
functions of the real coordinate, are a dense representation of $H^1$.
For the real factors use the fixed bump
$\beta(v)=\exp(-1/(1-v^2))$ on $|v|<1$, zero outside, and its rational
translates, dilates and rational polynomial multiples. Their supports
and derivative bounds are computable from this finite description.
The dual norm is the ordinary $H^{-1}$ norm. Distributional multiplication
is used for weights on this dual space.

Use the exact chart [E, (109.1)--(109.3)],

$$
\begin{gathered}
\kappa=\sqrt{\eta/a},\quad s=w-xy/2,\quad t=s/\kappa,
\quad Z=(\xi,t),\quad R=|Z|,\quad\tau=-\log R,\\
(\mathcal Uu)(\xi,t)=\sqrt\kappa\,u(x,y,z,\kappa t+xy/2),
\qquad (\mathcal Uu)(R\omega)=R^{-1}H_u(\tau,\omega),\\
\mathcal G(\xi,s)=\Gamma(x,y,z,s+xy/2),\qquad
Y_1=\partial_x-\frac y{2\kappa}\partial_t,\quad
Y_2=\partial_y+\frac x{2\kappa}\partial_t,\quad Y_3=\partial_z,\\
\mathcal A=a\left(-\sum_iY_i^2-\partial_t^2\right).
\end{gathered}
\tag{11.2}
$$

Thus $\mathcal U$ is unitary and the original expression is
$\mathcal A-16a\kappa\mathcal G(\xi,\kappa t)$. The polar expression of
its form divided by $a$ is denoted by $\mathfrak p$. Let
$\mathfrak p_0$ be exactly the comparison cylinder form (109.12), and
$\mathfrak e=\mathfrak p-\mathfrak p_0$. These are the actual linear
forms; the comparison does not replace the original potential. Put

$$
\begin{gathered}
N_0=2\pi/\sqrt3,\qquad
e_0(\sin\theta\,\Omega,\cos\theta)
 =\frac{2\min(\theta,\pi-\theta)}{\pi N_0\sin\theta},\\
b[v]=\|\nabla_{S^3}v\|_2^2+\|v\|_2^2
                  -\frac4\pi\|v|_\Sigma\|_2^2,\qquad
\Sigma=\{t=0\}\cap S^3,\qquad P_0=-\partial_\tau^2+B,\\
X=\{J:e^{\tau/8}J\in H^1\},\qquad
Y=\{Q:e^{\tau/8}Q\in H^{-1}\},\qquad K_0=256.
\end{gathered}
\tag{11.3}
$$

Here $B$ is the form operator of $b$; its nonnegativity, normalized
kernel $\mathbb Ce_0$ and gap $B|_{e_0^\perp}\ge2$ are precisely
[E, (109.6)--(109.7)]. Only this angular operator has that gap.

Let $q(v)=0$ for $v\le0$, $q(v)=6v^5-15v^4+10v^3$ for $0<v<1$,
and $q(v)=1$ for $v\ge1$. It is $C^2$, with
$0\le q\le1$, $|q'|\le2$, $|q''|\le6$. Define

$$
\begin{gathered}
C_{\rm ann}=8(\kappa^{-1}+\kappa^{-2})
                  +128B_G\kappa^{-1/2}+640B_G\kappa^{-1/4},\qquad
C_E=2^{40}C_{\rm ann},\qquad B_G=32,\\
\theta_T=q(\tau-T),\qquad
\langle K,E_TJ\rangle=\mathfrak e(\theta_TK,\theta_TJ).
\end{gathered}
\tag{11.4}
$$

The scalar $B_G$ is the **same Green bound** $B=32$ as in (10.3);
$B$ in (11.3) denotes the angular operator.
Choose an integer $T\ge4$ and a rational $\bar q<1/2$ by the strict,
outward-enclosed inequality

$$
K_0C_Ee^{-T/4}\le\bar q<1/2.
\tag{11.5}
$$

For $p(\tau)=1$ and $p(\tau)=\tau$ set

$$
\begin{gathered}
D_p=2^{20}C_E
 \left[\int_{T-2}^\infty e^{-\tau/4}(p^2+|p'|^2)d\tau\right]^{1/2},
\quad L_T=P_0^{-1}E_T,\quad b_p=P_0^{-1}E_T(pe_0),\\
Z_p=-\sum_{j=0}^\infty(-L_T)^jb_p,\qquad H_p=pe_0+Z_p,
\qquad \chi_T=q(\tau-T-2),\\
(\mathcal U\gamma_p)(R\omega)=\chi_T R^{-1}H_p,\qquad
\mathcal U\ell_p=[\mathcal A,\chi_T](R^{-1}H_p).
\end{gathered}
\tag{11.6}
$$

The inverse and the series in this definition are justified and computed
in Theorem 11.2. The vectors are zero outside the displayed source
cutoff. Write $(\gamma_c,\ell_c)$ for $p=1$ and
$(\gamma_l,\ell_l)$ for $p=\tau$; none of the $\ell$ symbols denotes an
emission. All norm bounds and stopping comparisons use rational outward
enclosures of the constants for the exact named parameters.

**Theorem 11.2 (constructed local graph names for the original source).**
From the $a,\eta$ names alone, (11.2)--(11.6) construct global original
$L^2$ names of both graph pairs, with

$$
\begin{gathered}
S^*\gamma_c=\ell_c,\quad (A,C)(\gamma_c)=(1,0),
\quad\gamma_c\in D(F),\quad F\gamma_c=\ell_c,\\
S^*\gamma_l=\ell_l,\quad (A,C)(\gamma_l)=(0,1).
\end{gathered}
\tag{11.7}
$$

Both vectors have compact support. Their images have compact punctured
support $T+2\le\tau\le T+3$. Put

$$
\begin{gathered}
\Lambda_Q=4(1+\kappa^{-2}),\qquad
B_{\rm graph}=1+100a\Lambda_Qe^{2(T+3)},\\
Z_{p,n}=-\sum_{j=0}^n(-L_T)^jb_p,\qquad
\beta_{p,n}=K_0D_p\frac{\bar q^{,n+1}}{1-\bar q}.
\end{gathered}
\tag{11.8}
$$

Then $\|Z_p-Z_{p,n}\|_X\le\beta_{p,n}$. Applying the two maps in
(11.6) separately to this approximation gives graph-pair naming error
sum at most $B_{\rm graph}\beta_{p,n}$, before separately budgeted
finite evaluation errors. For $L\ge T+3$ the source-end truncation has
the certificate

$$
\|\mathbf1_{\{R<e^{-L}\}}\gamma_p\|_2^2
 \le2\int_L^\infty e^{-2\tau}p(\tau)^2d\tau
       +2e^{-9L/4}\left(\frac{K_0D_p}{1-\bar q}\right)^2.
\tag{11.9}
$$

Every inverse and norm computation used in these names is specified
below from the actual coefficients. No numerical local-solution or
weak-action oracle is an additional input.

Proof. First construct the original coefficient on punctured compact
sets. Use exactly (10.11), with its literal inverse Fourier factor and
independent $z$ Gaussian, and $\Gamma=\int_0^\infty h_t^Ldt$.
The contour proof of (10.12) also gives

$$
h_t^L(\xi,s)\le\tfrac18t^{-5/2}
             e^{-(|\xi|^2+|s|)/(32t)}.
\tag{11.10}
$$

For a compact set separated from $e$, take a finite effective cover by
charts with a certified positive lower bound either for $|\xi|^2$,
or for $s$, or for $-s$. Use the real contour on the first charts and
the contour $u+i(\pi/4)\operatorname{sgn}s$ on the others. The sign is
fixed within each latter chart. On the real contour
$u\coth u\ge1$; on the shifted contour the estimates preceding
(10.12) hold uniformly. If $D>0$ is the certified lower bound appropriate
to a chart, the omitted heat times have bounds

$$
\frac18\int_0^\alpha t^{-5/2}e^{-D/(32t)}dt,
\qquad \frac1{12}b^{-3/2}\quad(t>b).
\tag{11.11}
$$

On $\alpha\le t\le b$, the frequency tail $|u|>U\ge1$ is bounded
by $6(U+2)e^{-U}$ times the explicit integral of the prefactor
$t^{-5/2}/(16\pi^{5/2})$. This follows from
$|(u+i\pi/4)/\sinh(u+i\pi/4)|\le3(|u|+1)e^{-|u|}$;
the real contour has the same sufficient tail. Real parts of the
quadratic exponents are nonnegative. Choose $\alpha\downarrow0$,
$b,U\uparrow\infty$ by these three inequalities. On the remaining
compact rectangle the integrand and its coordinate derivatives are
computable elementary functions with bounded derivatives. Its removable
real-contour origin is evaluated by its convergent series. Subdivision
and interval quadrature consequently give uniform names of $\Gamma$ on
each specified compact punctured set. Parameter enclosures refine these
names continuously on the same positive brackets. This constructs the
coefficient, rather than assuming its evaluator, and computes no
interacting heat kernel.

Here are quantitative bounds for the weak local problem. On
$1/2\le|(X,u)|\le2$, put
$W_r=r^2\mathcal G(rX,\kappa ru)$, $0<r\le1$. The exact original
marginal [E, (109.9)] and (10.12) give

$$
\int W_rdu=\frac1{4\pi\kappa|X|},\qquad
\int |u|^{1/4}W_rdu
 \le10B_G\kappa^{-5/4}r^{1/4}|X|^{-1/2}.
\tag{11.12}
$$

For the second inequality substitute $u=r|X|^2v/\kappa$ in the
homogeneous Green bound; the remaining integral is at most
$2/(5/4)+2/(1/4)<10$. For $|X|<1/4$, annular support forces
$|u|>1/4$, the trace is zero, and
$W_r\le8B_G\kappa^{-3/2}r^{1/2}$. For $|X|\ge1/4$ use

$$
|\overline{h(u)}k(u)-\overline{h(0)}k(0)|
 \le2|u|^{1/4}\|h\|_{H^1(\mathbb R)}\|k\|_{H^1(\mathbb R)}.
\tag{11.13}
$$

For $|u|\le1$ this follows from the fundamental theorem and the
one-dimensional $H^1$ supremum bound; for $|u|>1$ the supremum bound
alone suffices. Cauchy--Schwarz in $X$ and multiplication by the unchanged
$16\kappa$ give the last two terms of $C_{\rm ann}$. Expanding the
two shear kinetic terms in (11.2) gives an error bounded by
$8(\kappa^{-1}+\kappa^{-2})r\|h\|_{H^1}\|k\|_{H^1}$.
Since $r\le r^{1/4}$, the actual/model annular form difference is at
most $C_{\rm ann}r^{1/4}$ times these norms. This is the quantitative
version of the original bilinear comparison, including its axis.

For clarity, the fixed-cylinder localization can use triangular hats
at spacing $l=(\log2)/4$, and companion cutoffs equal to one on each
hat and supported within $2l$ of its center. At most five enlarged
slabs overlap. Each hat or companion has $H^1$ multiplier norm below
$8$. The polar map to the relative annulus $[1/2,2]$ has norm below
$3$: its squared $H^1$ integral is bounded by
$4\|J\|_2^2+\|J+J'\|_2^2+\|\nabla_SJ\|_2^2$.
Each product of $\theta_T$ with either relative weight
$e^{\pm(\tau-jl)/8}$ has multiplier norm below $8$. The first
intersecting slab contributes at most $2e^{-T/4}$.
Partition in one slot and use its companion in the other. Locality and
the sum of the hat derivatives being zero make this the **exact** form
difference. The bound for its weighted sum is at most
$9\cdot8^4\cdot5\cdot2\,C_{\rm ann}e^{-T/4}<C_Ee^{-T/4}$.
Piecewise linear multipliers are legal by $H^1$ continuity. Thus

$$
\|E_T\|_{X\to Y}\le C_Ee^{-T/4}.
\tag{11.14}
$$

For an affine input $pe_0$, the same paired sum leaves the squared
weight $e^{-\tau/4}(p^2+|p'|^2)$ after Cauchy--Schwarz. The local
$H^1$ norm of $e_0$ is less than $2$, as also computed below.
The slot factors just bounded, finite overlap, and a unit-width terminal
cutoff give total factor below $2^{20}C_E$. Consequently
$\|E_T(pe_0)\|_Y\le D_p$. Removing the input beyond level $L$
with a cutoff changing on $[L-1,L]$ gives the same sufficient bound
with lower integration endpoint $L-2$. This is an effective vanishing
forcing tail. The two integrals for $p=1,\tau$ equal, respectively,
$4e^{-(T-2)/4}$ and
$4e^{-(T-2)/4}((T-2)^2+8(T-2)+33)$.

Next prove the inverse bound in the **ordinary** norms used for names.
Integration by parts on the two hemispheres, including the derivative
jump at $\Sigma$, gives

$$
b[v]=\int_{S^3}e_0^2|\nabla_S(v/e_0)|^2,
\qquad
\|v\|_{H^1}^2\le3\bigl(b[v]+\|v\|_2^2\bigr),
\quad b[v]+\|v\|_2^2\le2\|v\|_{H^1}^2.
\tag{11.15}
$$

Indeed $e_0$ is positive and Lipschitz, and
$|\nabla\log e_0|=|1/\theta-\cot\theta|\le2/\pi<1$ on the
first hemisphere and by reflection on the other. On $(0,\pi/2)$
this quantity increases from zero, since
$\csc^2\theta-\theta^{-2}>0$. The product rule therefore bounds
$\|\nabla v\|_2^2$ by $2b[v]+2\|v\|_2^2$; the last inequality
in (11.15) follows directly from trace subtraction. These arguments
extend by form density. Direct angular integration gives
$\|e_0\|_2=1$, $\|e_0\|_{H^1}^2=12/\pi^2$; equivalently use
$b[e_0]=0$, its equator value $1/N_0$ and equator area $4\pi$.

Conjugation of $P_0$ by $e^{\tau/8}$ and Fourier transformation give
the symbols

$$
\mu+\zeta^2-1/64+i\zeta/4.
\tag{11.16}
$$

At $\mu=0$ their modulus is $\zeta^2+1/64$; at $\mu\ge2$ their
real part is at least $(1+\mu+\zeta^2)/2$. Spectral division thus
gives an inverse bound $64$ between the $B$ Sobolev scales. The two
norm conversions (11.15), also on their duals, cost at most $3$ in
total. Hence $\|P_0^{-1}\|_{Y\to X}\le192<K_0$. Division by
these symbols proves surjectivity and uniqueness, exactly on the
weighted whole cylinder. It introduces no gap for $F$.

Here is a finite procedure for that inverse and for the weak data it
uses. On a compact dense tensor input, $P_0$ and $E_T$ have computable
$L^2$ scalar and divergence terms and a known equatorial trace
distribution. The actual terms use the just constructed $\Gamma$
names and the polynomial kinetic coefficients. For a smooth compact
density $a(\tau,\Omega)$ on $\mathbb R\times\Sigma$, replace
$a\delta_\Sigma$ by a symmetric normal layer of width $\nu<1/4$,
dividing its density by the spherical volume Jacobian. The fundamental
theorem in the normal variable and Cauchy--Schwarz give

$$
\|a\delta_\Sigma-\operatorname{layer}_\nu(a)\|_{H^{-1}}
 \le8\sqrt\nu\,\|a\|_2.
\tag{11.17}
$$

The normal Jacobian is $\cos^2 v\ge1/2$ on this tube; integrating
$|\phi(v)-\phi(0)|\le\sqrt{|v|}\,
(\int_{-|v|}^{|v|}|\partial_v\phi|^2)^{1/2}$ proves this
sufficient constant, also after integration in $\tau,\Omega$.
The layer is an explicitly named $L^2$ function. Divergence is a bounded
map from $L^2$ vector fields to $H^{-1}$. Approximate those fields first
by compact smooth fields in $L^2$, with an allocated norm error, before
evaluating their divergences. Thus all these distributions have strong
$H^{-1}$ names, rather than just computable test pairings.

Their norms can be computed by ordinary spherical harmonics and the
real Fourier transform. For a smooth compact $L^2$ scalar approximant,
discarding the region $\zeta^2+l(l+2)>Q$ has $H^{-1}$ norm at most
$\|f\|_2/\sqrt{1+Q}$. The finitely many remaining harmonic integrals
and compact Fourier integrals are computable quadratures. The preceding
strong distributional approximations bound the additional errors. This
also computes residual norms with cancellations. No eigenbasis of the
interacting source is supplied or used.

An effective ordinary $H^1$ name of $e_0$ needs no convergence-rate
assumption: compute its spherical-harmonic coefficients from its explicit
profile, and use the known total squared norm $12/\pi^2$. Parseval gives
the squared $H^1$ projection tail as this number minus the finite weighted
coefficient sum. Refine the coefficients and enlarge the finite projection
until a rational upper tail bound is below the requested squared error.
Completeness proves termination; coefficient rounding is separately
budgeted. Compact integration treats the equator by its two continuous
pieces and the pole values by the removable series for
$\theta/\sin\theta$.

To compute $P_0^{-1}Q$ for any named $Q\in Y$, enumerate
$v=e^{-\tau/8}W$ over dense compact smooth tensors $W$ and dovetail
their residual precisions. Accept a finite $v$ when a computed upper
enclosure satisfies

$$
\|e^{\tau/8}(P_0v-Q)\|_{H^{-1}}<\varepsilon/K_0.
\tag{11.18}
$$

This certifies $X$ error below $\varepsilon$. Surjectivity, density and
boundedness of $P_0:X\to Y$ prove finite termination. The layer and
norm constructions above compute every ingredient in this test. Extend
$E_T$ from compact tensors to arbitrary $X$ names using (11.14).
For $E_T(pe_0)$ first use its displayed forcing tail, then its finite
cylinder $H^1$ approximations. This constructs $b_p$, every finite
Neumann sum and their accumulated evaluation errors. Inequality (11.5)
proves contraction and precisely the geometric remainder (11.8).

The exact limit satisfies $(P_0+E_T)H_p=0$. On $\tau>T+1$ this is
the actual original weak equation. On every punctured annulus there it
is locally $H^1$ and the coefficients are smooth and elliptic. The local
regularity used in [E, (108.4)] applies. Multiplying by $\chi_T$ leaves
only the first-order commutator in (11.6). It is $L^2$ and is supported
on the specified annulus. Testing the product against original punctured
smooth tests proves $\gamma_p\in D(S^*)$, $S^*\gamma_p=\ell_p$.
No distribution at the excluded point is assigned to this adjoint action.
The decaying $X$ remainder fixes exactly the unrescaled coefficients
in [E, (112.2)]; [E, (112.3)] then gives (11.7).

For numerical graph errors, the physical cutoff map sends an $X$ error
$\Delta Z$ to an $L^2$ error of norm at most $\|\Delta Z\|_X$.
On the commutator annulus the physical gradient of $R^{-1}\Delta Z$
has norm at most $3\|\Delta Z\|_X$. The free coefficient matrix
in (11.2) has divergence zero and norm and trace bounded by
$\Lambda_Q$ on $R\le1$; directly it is
$\sum_iY_iY_i^{\mathsf T}+e_te_t^{\mathsf T}$.
Also $|\nabla\chi_T|\le2e^{T+3}$ and
$\|\operatorname{Hess}\chi_T\|\le8e^{2(T+3)}$.
The product rule proves the sufficient factor $B_{\rm graph}$ in
(11.8). It uses only first derivatives of $\Delta Z$. Finite Neumann
approximants are put into this **commutator map**, not into $S^*$.
The exact limit alone owns the original graph identity.

The physical squared measure is $e^{-2\tau}d\tau d\omega$ and
$Z_p=e^{-\tau/8}W_p$, with
$\|W_p\|_{H^1}\le K_0D_p/(1-\bar q)$. Splitting the two squares
proves (11.9). Discard that source tail and approximate the remaining
compact functions and the compact commutator in $L^2$ to any prescribed
error. This yields finite chart names.

Finally these are **original-coordinate** names. First approximate a
chart name by a compact smooth $v$ with known $L^2$ error. For its inverse
transport $T_kv=k^{-1/2}v(\xi,s/k)$,

$$
\|\partial_kT_kv\|_2=k^{-1}\|v/2+t\partial_tv\|_2.
\tag{11.19}
$$

A positive bracket for $\kappa$ therefore bounds replacement by a finite
rational $k$. On the resulting compact support a rational box mesh and
computable derivative bounds give rational step functions with certified
$L^2$ error. This proves the conversion without an exact real coordinate
service. Choose $n$ so that $B_{\rm graph}\beta_{p,n}$ uses less than
one quarter of a requested graph error, and allocate the remainder to
the finite sum, its two bounded maps, source truncation and coordinate
conversion. Each operation just described terminates. $\square$

**Theorem 11.3 (an actual original positive-discount evaluator).** From
the names in Definition 11.1 there is a terminating procedure returning
a finite original-coordinate $U$ and a rational $E<\varepsilon$ such
that, for the **actual** original Friedrichs realization,

$$
\|U-(F+r)^{-1}f\|_2\le E.
\tag{11.20}
$$

It constructs the graph information used by its residual test from
$a,\eta$. Neither a coefficient matrix nor an assumed solver is an
input. The finite output need not belong to $D(F)$.

Proof. Fix the computable bump $\beta(v)=\exp(-1/(1-v^2))$ for
$|v|<1$, zero elsewhere. Enumerate finite rational complex linear
combinations of rational translates and dilates of its tensor products
on rational original-coordinate boxes whose closures avoid $e$.
Call them $\phi_i$. Include finite sums and all rational complex
coefficients $z_i$ in the enumeration. Their supports and all required
derivative bounds are finite computable data. Compact mollification
followed by rational Riemann sums proves $C^2$ density on each compact
punctured support; the supports may be enlarged within a fixed punctured
neighborhood. All coefficients of $S$ are bounded there. Thus these
functions are graph dense in the original punctured core closure.
Theorem 11.2 and compact $\Gamma$ evaluation give names of the exact
pairs

$$
u_i=\phi_i+z_i\gamma_c,\qquad
v_i=S\phi_i+z_i\ell_c=Fu_i.
\tag{11.21}
$$

Use [E, (112.3), (112.5)] on their stated original domains. Every
$y\in D(F)$ has $y-A(y)\gamma_c\in D(\overline S)$.
Rational approximation of this scalar and punctured-core approximation
therefore prove graph density of (11.21) in $F$. The algorithm does not
evaluate $A(y)$; it searches $z_i$. This reuses the domain classification,
and adds no claim that punctured tests alone are an $F$ operator core.

Find rational $0<r_-\le r\le r_+$ from the positive name. At each
candidate and precision, compute finite names $U_i,V_i,f_0$ with errors
$\alpha,\beta,\gamma$, and rational $r_0$ with error $e_r$.
Compute a rational upper enclosure

$$
\mathcal R\ge
 \|V_i+r_0U_i-f_0\|_2+\beta+r_+\alpha
                         +e_r\|U_i\|_2+\gamma.
\tag{11.22}
$$

All quantities are norms of finite names and rational error terms.
Accept only when

$$
E=\alpha+\mathcal R/r_-<\varepsilon.
\tag{11.23}
$$

The triangle inequality makes $\mathcal R$ an upper bound for the
**exact** residual $\|(F+r)u_i-f\|_2$. Nonnegativity of $F$ gives
$\|(F+r)^{-1}\|\le1/r$, proving (11.20). No use of $FU_i$ occurs.

Enumerate every pair of candidate index and naming precision, for example
in increasing sum of indices. Graph density and surjectivity of $F+r$
give a candidate with exact residual smaller than $r\varepsilon/4$.
For that fixed candidate, shrinking all name errors and norm-rounding
errors eventually satisfies the strict inequality (11.23). Each finite
name calculation terminates by Theorem 11.2, and every candidate occurs
at arbitrarily fine precision. Hence the specified search terminates.
The finite certificate consists of its dictionary index, the two
graph-name errors, forcing and discount enclosures, and (11.22)--(11.23).
Its soundness refers to the exact pair in (11.21). $\square$

**Theorem 11.4 (the identical normalized zero line, endpoint and capacity
have numerical names).** Under exactly the additional coefficient access
of Definition 11.1, the preceding procedures compute global original
$L^2$ names of the coefficient-one $w_*$ and normalized $h$, and real
names of the original endpoint selector $\rho$. With the requested
positive $r$ name they compute

$$
d_r=1-r\langle h,(F+r)^{-1}h\rangle,
\qquad \operatorname{Cap}_r(\{e\})=rd_r.
\tag{11.24}
$$

They return finite error certificates and terminate at every requested
absolute precision. The original time $d$ may supply $r$ through its
specified clock formula only when its numerical name is also supplied.
No numerical name of $d$ is inferred from its mathematical positivity.
Any other compact source graph representative with original coefficient
$C=1$, corrected by its own original Friedrichs inverse, yields exactly
the same $w_*$, not just a proportional zero vector.

Proof. The exact $\ell_l$ of Theorem 11.2 is compactly supported
complex $L^2$ forcing. Choose rational $\Lambda>1+\kappa$ by an upper
parameter enclosure. On its support $R\le1$, and
$\varrho^4=|\xi|^4+\kappa^2t^2\le1+\kappa^2$; this also contains
the support of $\gamma_l$. Thus Theorem 10.3 applies with precisely
this forcing, the original $C=0$ domain, raw Haar norm and the original
$a,\eta$. Use its constants (10.3)--(10.4) **without changing their
coefficient family**. Its modulus is valid for all compact $L^2$ data,
so no smoothness of our $C^2$ cutoff image is needed. The source/domain
ingredients of that bound are the exterior passage [E, (110.10)] and
whole-closure inequality [E, (107.5)], not local source bounds for $h$.

Compute positive rational $\bar t\ge\max(1,\|\ell_l\|_2)$ and an
upper enclosure $\overline D$ of $D_\Lambda$. For requested zero-vector
error $E_w>0$, choose a positive dyadic discount satisfying

$$
s\le\min\left\{1,R_{\min}^{-4},
                     \left(\frac{E_w}{4\bar t\overline D}\right)^8\right\}.
\tag{11.25}
$$

Name $\gamma_l$ to error $E_w/4$ by Theorem 11.2 and
$(F+s)^{-1}\ell_l$ to error $E_w/4$ by Theorem 11.3. Their finite
difference $W$ has error less than $E_w$ from

$$
w=\gamma_l-F^{-1}\ell_l,
\tag{11.26}
$$

since (10.6) bounds the remaining error by $E_w/4$. The spectral inverse
here defines the mathematical vector; (11.25) and the positive solver
construct its name. The forcing name and its support were produced
internally, and neither inverse nor its zero-energy modulus is an input.

To verify exact source correspondence, let $(\gamma',\ell')$ be another
actual compact maximal graph pair with $C(\gamma')=1$ and compact
$L^2$ image. By the original selector,
$k=\gamma_l-\gamma'\in D(F)$ and $Fk=\ell_l-\ell'$.
The compact-source range result applies to both images and $\ker F=0$.
Consequently $F^{-1}(\ell_l-\ell')=k$, proving equality of the two
corrected vectors. In particular (11.26) equals the particular vector
(10.2), and hence the unique original $w_*$. Its maximal action is zero
and its original coefficient is $C(w_*)=1$. Changing $T$, the local
solution or its cutoff has introduced no change of endpoint or source.

The original Green pairing [E, (112.3)], applied with $u=w_*$ and
$v=\gamma_c$, gives a useful denominator certificate:

$$
\langle w_*,\ell_c\rangle=a,
\qquad
\|w_*\|_2\ge\nu:=a_-/Q_c>0,
\tag{11.27}
$$

where $a_->0$ is a rational lower parameter bound and
$Q_c>\|\ell_c\|_2$ is any computed positive rational upper bound.
Theorem 11.2 supplies $Q_c$. No global norm query is assumed. If
$\|W-w_*\|_2\le E_w<\nu/2$, then $W\ne0$, and

$$
\left\|\frac W{\|W\|_2}-h\right\|_2\le2E_w/\nu.
\tag{11.28}
$$

This follows by adding and subtracting $W/\|w_*\|_2$ and the reverse
triangle inequality. For requested $h$ error $\varepsilon$, take
$E_w\le\min(1,\varepsilon)\nu/8$. From the finite norm enclosures
of Definition 11.1 compute a rational
$Q_W\ge\max(1,\|W\|_2)$. Choose a positive rational
$\theta<\varepsilon/(4Q_W)$ and a rational $q$ satisfying
$|q-1/\|W\|_2|<\theta$. Norms of finite box functions are
computable, and $\|W\|_2\ge\nu-E_w\ge7\nu/8>0$, so this
reciprocal approximation terminates. Its vector-norm rounding error is

$$
\left\|qW-\frac W{\|W\|_2}\right\|_2
\le\theta\|W\|_2<\varepsilon/4.
$$

Together with (11.28), whose bound is at most $\varepsilon/4$,
this gives a finite rational box name $qW$ with error below
$\varepsilon$ from the normalized vector. Uniqueness and the inherited coefficient-positive
choice identify it with the original $h$.

With $v=\gamma_l$, the **same** boundary pairing gives

$$
\langle w_*,\ell_l\rangle=-a\rho,
\qquad \rho=-\operatorname{Re}\langle w_*,\ell_l\rangle/a.
\tag{11.29}
$$

Indeed $A(\gamma_l)=0$, $C(\gamma_l)=C(w_*)=1$, and the inherited
$\rho=A(w_*)$ is real. Computed $L^2$ names of the two vectors,
Cauchy--Schwarz and the positive lower bound for $a$ give converging
rational intervals for (11.29). Explicitly, for names $W,L$ with errors
$E_w,E_l$ and $Q_l\ge\|\ell_l\|_2$, the inner-product error is at
most $E_wQ_l+\|W\|_2E_l$, before scalar rounding; interval division by
the positive $a$ bracket completes the certificate. The endpoint $A=\rho C$ is thus derived
from its actual original zero vector, rather than supplied freely.

For (11.24), choose a finite $h_0$ with
$\|h_0-h\|_2\le\delta$ and use Theorem 11.3 to compute $U$ with
$\|U-(F+r)^{-1}h_0\|_2\le\zeta$. If $\widehat d$ is a scalar
evaluation of $1-r\operatorname{Re}\langle h_0,U\rangle$ with
rounding and parameter error at most $\sigma$, then

$$
|d_r-\widehat d|
 \le(2+\delta)\delta+r_+(1+\delta)\zeta+\sigma.
\tag{11.30}
$$

The first term follows from $\|r(F+r)^{-1}\|\le1$ and
$\|h\|_2=1$; the second is Cauchy--Schwarz. For example take
$\delta\le\min(1,\varepsilon/16)$,
$\zeta\le\varepsilon/[8r_+(1+\delta)]$, and
$\sigma\le\varepsilon/4$. These make the displayed sum smaller than
$\varepsilon$. Named positive $r$ causes no additional oracle: the
solver already handles it, and interval arithmetic includes its remaining
scalar evaluation error in $\sigma$. Multiplication computes the capacity
with an independently allocated error. The original strict positivity
$d_r>0$ from [S, (115.11)] implies that refining these intervals until
their lower endpoint is positive terminates, if a positive rational
lower certificate is requested. This includes $d_{1/(4d)}$ when the
original $d$ has the additional numerical name.

Every step is a finite algorithm on the stated names. The local Neumann
depth is bounded by (11.8), logarithmically in reciprocal graph error
for fixed enclosing constants. Count coefficient-name queries with their
precisions, compact quadrature subdivisions, normal-layer approximations,
finite spectral norm calculations, auxiliary inverse tests, Neumann
applications and original dictionary tests. Each auxiliary and original
search has a proved terminating strict certificate. No upper bound for
the successful dictionary index or for the cost of parameter-name
answers is assumed. Formula (11.25) permits $s$ of order $E_w^8$ for
fixed enclosures, so a sufficient inner residual tolerance can be of
order $E_w^9$. These are error budgets, not practical or polynomial
runtime bounds. No parameter-uniform cost is asserted. $\square$

**Definition 11.5 (the numerical relation and its remaining interfaces).**
Theorems 11.2--11.4 are a repository-derived construction for the actual
original coefficient family. The constructed local graph names pay the
source-boundary input of the positive-discount evaluator, and its outputs
combine with the unchanged §10 modulus to give the same normalized zero
state. Ordinary spherical harmonics, strong Sobolev representations,
Neumann inversion, graph-density residual certification and nonnegative
spectral calculus are mature intermediate tools. The augmented domain
identity itself is reused from [E, (112.5)]. An abstract dense range,
form Ritz upper bound, or strong residual assigned to a finite $H^1$
approximation would not provide this construction.

The free coefficient used here is Krötz--Thangavelu--Xu
[EXT-HEAT, §4.1, (4.1.2)], at $n=1$, with the original
$1/(2\pi)$ inverse transform and independent $z$ Gaussian. Its full
Laplacian formula with an additional central heat factor is not substituted
for the horizontal source. Local regularity uses only Shubin,
[*Essential self-adjointness for semi-bounded magnetic Schrödinger
operators on non-compact manifolds*, Lemma 5.1](https://arxiv.org/html/math/0007019v1),
on compact punctured sets with the original smooth elliptic symbol, zero
magnetic form, raw Haar measure and locally bounded potential. The
complete-manifold theorem following that lemma is not applied across the
puncture. The weighted estimates retain exactly the correspondence in
§10 to Ciatti--Cowling--Ricci [EXT-HARDY], with $p=2$, order $2$ and
homogeneous dimension $5$. No unspecified literature constant is used
as a numerical name. Colbrook--Horning--Townsend [EXT-SPECTRAL, §6.1,
(26)] treats regular differential realizations with smooth coefficients,
nonvanishing leading coefficient and client-verified self-adjointness;
its shifted-solve input is not a supplier of the singular source graph
names constructed here. These correspondences identify the reused
methods without asserting worldwide novelty or formal verification.

The additional access is to the mathematical model. The original
passive chronological $0,1,3,B$ record supplies neither the parameter
names nor the computational service. Its emission remains exactly
$P=T_d$, $g=g_{2d}$, $M=1+\|g_d\|_\infty$, $c=1/(4M)$,
$f_3=cg_d$ as the original bounded Borel class, $f_B=1/4$ and
$f_0=f_1=(3/4-f_3)/2$. No exact $M$, interacting source-time density,
word-likelihood evaluator or record-only confidence stopping rule is
constructed by these theorems. No hidden coordinates, reset, selected
outcome, second trajectory, stationary preparation or timed-release
service has been added. Numerical queries of the same fixed model are
not extra observations of its physical path.

The nonlinear readout compensation of [Appendix IV,
§171](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_IV.md)
and the conditional insertion-comparison representation of [C128,
§358](AURIC_C128_ORIGINAL_WORD_CALIBRATION_AND_FIXED_RELATION.md)
have their own source and access hypotheses; neither supplies diffusion
coefficient names or the solver. No conclusion about full passive word
Hankel rank follows. The remaining acquisition relation is from the
original fixed-emission record to whatever finite model/capacity
certificates a statistical consumer requires. These theorems prove no
such relation, impossibility or noncomputability. Mutual recovery of
space, time, boundary and memory retains its full original scope.

## 追加锚（本行以下为增补区）

## 12. The original heat and source names, and the exact calibration needed by passive words

**Definition 12.1 (source, numerical inputs and unchanged consumer).**
Retain the analytic suppliers [E, §§109–112] and [S, §§115–117, 133],
with all their hypotheses, and the coefficient constructions of §11.
The group, product and raw Haar measure are

$$
\begin{gathered}
G=H^1\times\mathbb R,\quad e=(0,0,0,0),\quad
pp'=(x+x',y+y',z+z',w+w'+xy'),\quad
d\mu=dx\,dy\,dz\,dw,\\
X_1=\partial_x,\quad X_2=\partial_y+x\partial_w,\quad
X_3=\partial_z,\quad L=-\sum_{j=1}^3X_j^2,\quad L\Gamma=\delta_e,\\
S_{\min}=(aL-\eta\partial_w^2-16\sqrt{a\eta}\,\Gamma)
             |_{C_c^\infty(G\setminus\{e\};\mathbb C)}.
\end{gathered}
\tag{12.1}
$$

The field $\Gamma$ has its original unit-source normalization. Fix
arbitrary finite $a,\eta,d>0$, supplied by total rational interval
names, and rational requested absolute errors. A separately requested
time $t>0$ also has a total interval name; the times $d,2d,3d/2$
below are computed from the same $d$ name. Retain exactly

$$
\begin{gathered}
C(w_*)=1,\quad h=w_*/\|w_*\|_{L^2(\mu)},\quad
c_h=C(h)>0,\quad \rho=A(h)/C(h),\\
D(H)=\{u\in D(S_{\min}^*):A(u)=\rho C(u)\},\quad
H=H_{\rm end}\ge0,\quad \ker H=\mathbb Ch,\\
D(F)=\{u\in D(S_{\min}^*):C(u)=0\},\quad F\ge0,\quad
\ker F=\{0\},\\
m=h^2\mu,\quad m(G)=1,\quad J_hv=hv,\quad
K=J_h^{-1}HJ_h,\quad T_t=e^{-tK},\quad S_t=e^{-tH}.
\end{gathered}
\tag{12.2}
$$

All raw-space pairings are in $\mathcal H=L^2(G,\mu;\mathbb C)$,
antilinear in the first slot; a subscript $m$ denotes $L^2(m)$.
The coefficient-positive $h$ is strictly positive $\mu$-almost
everywhere and has norm one. The source trace is the continuous
functional on the full form domain
$\mathscr V=\mathscr V_0\dotplus\mathbb C1$ of [S, (116.1)–(116.4)].
It is quasi-continuous evaluation at the original nonpolar $e$.
It is not a value assigned to an arbitrary measurable representative.

A global raw $L^2$ name has exactly the meaning of Definition 11.1:
finite rational complex step functions on bounded rational boxes in
the original coordinates, with certified global norm errors at each
requested precision. A weighted name of $v\in L^2(m)$ may be given
by a raw name of $J_hv$. Ordinary box-step approximations in the
weighted norm will also be constructed below. A real scalar name
returns certified rational intervals of arbitrarily small width.
No heat, pointwise value, modulus, tail, supremum, word probability
or full-law service is among the numerical inputs.

The actual process starts at $e$ at time zero. Its positive-time
density is the original $g_t$ of [S, Theorem 117.2]. Put

$$
\begin{gathered}
v_t=J_hg_t=hg_t,\qquad N_d=\|g_d\|_{L^\infty(m)},\qquad
M=1+N_d,\qquad c=\frac1{4M},\\
\mathcal L=\{0,1,3,B\},\qquad
f_3=cg_d,\quad f_B=\frac14,\quad
f_0=f_1=\frac38-\frac12f_3,\qquad P=T_d.
\end{gathered}
\tag{12.3}
$$

The emissions in (12.3) are classes with any permitted repaired
Borel representatives of Definition 8.1. The first read is at $2d$,
and subsequent gaps are $d$. Read noise is fresh and independent
conditional on the same undisturbed path. These definitions retain
every original label, history and elapsed interval. In particular
$F$ and $H$ remain different operators. Section 133 of [S] supplies
the finiteness of $N_d$, without supplying a numerical name for it.

**Theorem 12.2 (a computed resolvent of the full original endpoint).**
From the $a,\eta$ names and the constructed services of §11,
the action of $R=(H+1)^{-1}$ on every supplied global raw $L^2$
name is computable at every rational absolute error. The output is a global name with a finite
error certificate. The auxiliary discount $1$ is in the original
units and does not change the physical clock. Explicitly set

$$
G_1=(F+1)^{-1},\quad n=h-G_1h,\quad
D=\langle h,n\rangle=d_1,\quad z=n/D.
\tag{12.4}
$$

Then the computed action is that of

$$
R=G_1+\frac{|n\rangle\langle n|}{D},\qquad
0<D<1,\quad \|n\|_2\le1,\quad 0\le R\le I.
\tag{12.5}
$$

Proof. Theorems 11.3–11.4 compute $G_1$ on all global inputs,
$h,n$ and $D$. The full-complex-domain identity [S, (115.5)],
at $r=1$, is precisely (12.5). Its original boundary-pairing
calculation imposes $A=\rho C$; it does not identify $H$ with $F$.
The bounds for $D,n$ follow from [S, (115.11), (116.17)] and the
nonnegative spectral calculus of $F$. The bound for $R$ follows
from the nonnegativity of the same $H$.

Refine the $D$ intervals until their lower endpoint is positive.
Fix rational $\ell>0$ smaller than that endpoint, so $D>\ell$.
Positivity proves termination. All later center approximations
$\widehat D$ can be chosen at least $\ell$. Suppose
$\|\widehat n-n\|_2\le\alpha$ and
$|\widehat D-D|\le\beta$. The rank-one operator error is at most

$$
\left\|\frac{|n\rangle\langle n|}{D}
       -\frac{|\widehat n\rangle\langle\widehat n|}{\widehat D}
\right\|
\le \frac{(2+\alpha)\alpha}{\ell}
       +\frac{(1+\alpha)^2\beta}{\ell^2}.
\tag{12.6}
$$

Indeed split first the numerators at denominator $D$, then the
denominators with numerator
$|\widehat n\rangle\langle\widehat n|$. Use
$\|n\|\le1$, $\|\widehat n\|\le1+\alpha$ and
$D,\widehat D\ge\ell$. For a finite forcing of norm at most
$Q$, multiply (12.6) by $Q$, add the requested $G_1$ action
error and finite arithmetic error, and obtain an explicit output
certificate. Inner products of finite box steps are finite sums
over their common rational partition, so their rounding can be
bounded by rational interval arithmetic. Approximating an arbitrary
forcing by a finite one adds at most its input error, since
$\|R\|\le1$. Every term can therefore be made smaller than an
allocated fraction of the requested error.

The same data compute $z$; for
$Z=\widehat n/\widehat D$, before final rounding,

$$
\|Z-z\|_2\le
 \frac{\alpha}{\ell}
 +\frac{(1+\alpha)\beta}{\ell^2},\qquad \|z\|_2\le1/\ell.
\tag{12.7}
$$

No inverse at spectral value zero is applied to a general forcing.
In particular $n$ is a full form vector but need not lie in $D(H)$;
its boundary defect in [S, (116.5)] is retained. $\square$

**Theorem 12.3 (the exact source vector at each deterministic time).**
Under Definition 12.1 and (12.4), for every $t>0$,

$$
v_t=(H+1)S_tz.
\tag{12.8}
$$

This is the vector representing the original source-start law at
that very time, with its original normalization, rather than just
a density for almost every time or a discounted occupation law.

Proof. The trace of the full resolvent in [S, (116.13)] gives,
for every $\phi\in\mathcal H$,

$$
\operatorname{tr}(J_h^{-1}R\phi)=\langle z,\phi\rangle_\mu.
\tag{12.9}
$$

Fix $t>0$. Spectral smoothing puts $S_t\phi$ in $D(H)$,
and $(H+1)S_t$ is bounded and self-adjoint. Apply (12.9) to
$(H+1)S_t\phi$. Using $R(H+1)S_t\phi=S_t\phi$ gives

$$
\begin{aligned}
\operatorname{tr}(T_tJ_h^{-1}\phi)
 &=\langle z,(H+1)S_t\phi\rangle_\mu\\
 &=\langle(H+1)S_tz,\phi\rangle_\mu.
\end{aligned}
\tag{12.10}
$$

The all-input, deterministic-time Riesz identity [S, (117.2),
(117.5)] identifies the left side with
$\langle J_hg_t,\phi\rangle_\mu$. Riesz uniqueness proves
(12.8), including its complex pairing convention. The source
normalization in (12.9) is fixed by the equilibrium identity
$\mathscr E_1[b_1,u]=D\operatorname{tr}u$,
$J_hb_1=n$, of [S, (116.4)]. Thus there is no missing source
factor, no division by $h(e)$ and no insertion of a Dirac mass as
an $L^2$ vector. Smoothing precedes the unbounded operator in
(12.8); no assertion $z\in D(H)$ is needed. $\square$

**Theorem 12.4 (certified global heat and source computation).**
From only the numerical inputs in Definition 12.1 and the
constructed services of §11, one can compute $S_tu$ for every
global raw name of $u$ and every named $t>0$, and the same $v_t$
of (12.8), with any prescribed global $L^2(\mu)$ error. One can
also produce finite box-step approximations to $g_t$ in global
$L^2(m)$ and to the actual raw-Haar density $h v_t$ in global
$L^1(\mu)$. These are numerical names of mathematical objects.

Proof. Use the computed positive self-adjoint contraction $R$.
On its compact spectral interval $[0,1]$ set

$$
\begin{gathered}
\chi_t(x)=e^{-t(x^{-1}-1)},\qquad
\psi_t(x)=x^{-1}e^{-t(x^{-1}-1)}\quad(0<x\le1),\\
\chi_t(0)=\psi_t(0)=0,\qquad
S_t=\chi_t(R),\qquad v_t=\psi_t(R)z.
\end{gathered}
\tag{12.11}
$$

The limits at zero are zero. The spectral substitution
$x=(1+\lambda)^{-1}$ proves the operator identities, using
(12.8). The endpoint $x=0$ controls the entire unbounded
$\lambda$ tail; it is not a spatial or spectral cutoff.

For complete finite certificates find rational
$0<t_-\le t\le t_+$ from the time name, and rational
$E>e^{t_+}$. Computable rational bounds are

$$
\begin{gathered}
L_\chi=4Et_+/t_-^2,\qquad
L_\psi=E(4/t_-^2+27t_+/t_-^3),\\
C_\chi=1/t_-,\qquad C_\psi=1/t_-+4/t_-^2,\\
\|\chi_t\|_\infty\le1,\qquad
\|\psi_t\|_\infty\le1+1/t_-.
\end{gathered}
\tag{12.12}
$$

Here $L$ bounds the Lipschitz constant in $x$ on $[0,1]$;
$C$ bounds variation per unit change of time within
$[t_-,t_+]$. To check them, write $y=1/x$. Then

$$
\partial_x\chi_t=t y^2e^t e^{-ty},\qquad
|\partial_x\psi_t|
 \le e^t(y^2+t y^3)e^{-ty}.
\tag{12.13}
$$

The maxima over $y\ge0$ of $y^j e^{-t_-y}$ are
$(j/(\mathrm e t_-))^j$, bounded by $j^j/t_-^j$.
This proves the displayed $L$ bounds, including their continuous
extension at zero. With $\lambda=x^{-1}-1\ge0$,
$|\partial_t\chi_t|=\lambda e^{-t\lambda}$ and
$|\partial_t\psi_t|=(\lambda^2+\lambda)e^{-t\lambda}$.
The same maxima give the $C$ bounds. Finally
$(1+\lambda)e^{-t\lambda}\le1+1/t_-$ proves the last
bound. Every constant in (12.12) is computed from the time bracket.

The following polynomial approximation is a reused intermediate
method, applied to these specific scalar functions. Let
$f$ denote either $\chi$ or $\psi$. Choose rational
$\tau\in[t_-,t_+]$ with $|t-\tau|\le e_t$, and compute
each $f_\tau(j/N)$ to rational error at most $\kappa$, with
the value at $j=0$ set to zero. For $N\ge1$ form the rational
Bernstein polynomial

$$
P(x)=\sum_{j=0}^N\widehat f_j{N\choose j}
                    x^j(1-x)^{N-j}.
\tag{12.14}
$$

For a binomial random variable $J$ with parameters $(N,x)$,
$\mathbb E|J/N-x|\le\sqrt{x(1-x)/N}\le1/(2\sqrt N)$.
Consequently the exact Bernstein polynomial differs from
$f_\tau$ by at most $L_f/(2\sqrt N)$. Its nonnegative
weights sum to one, so coefficient rounding adds at most
$\kappa$. Time uncertainty adds at most $C_f e_t$. Hence

$$
\|P-f_t\|_{C([0,1])}
 \le\Delta:=\frac{L_f}{2\sqrt N}+C_f e_t+\kappa.
\tag{12.15}
$$

For any desired rational $\delta>0$, choosing
$N>(3L_f/(2\delta))^2$, with $N$ a perfect square,
$e_t<\delta/[3(C_f+1)]$ and $\kappa<\delta/3$
makes $\Delta<\delta$. Elementary exponential evaluation at
the finitely many positive rational nodes is total. No unknown
modulus or approximation constant has been supplied.

To include every vector error, expand (12.14) by exact rational
arithmetic as $P(x)=\sum_{j=0}^Na_jx^j$. Put
$A_P=\sum_j|a_j|$ and $B_P=\sum_jj|a_j|$.
For an exact named input $u$, first compute a rational
$Q\ge\|u\|_2$ from the norm of any finite approximation plus
its certified error; this is not an additional input. Start
with a finite $U_0$ of error $\alpha$, and compute
$U_j$ with $\|U_j-RU_{j-1}\|_2\le\beta_j$ using
Theorem 12.2. Contractivity gives inductively

$$
\|U_j-R^ju\|_2\le\alpha+\sum_{i=1}^j\beta_i.
\tag{12.16}
$$

If the finite linear combination $\widehat V$ of the $U_j$
has arithmetic error at most $\sigma$, then continuous spectral
calculus and (12.15) give the global certificate

$$
\|\widehat V-f_t(R)u\|_2
 \le\Delta Q+
    \sum_{j=0}^N|a_j|\left(\alpha+\sum_{i=1}^j\beta_i\right)
       +\sigma.
\tag{12.17}
$$

For a vector target $\varepsilon>0$, take
$\Delta<\varepsilon/[4(Q+1)]$,
$\alpha<\varepsilon/[4(A_P+1)]$,
every $\beta_i<\varepsilon/[4(B_P+1)]$ and
$\sigma<\varepsilon/4$. The right side is strictly less
than $\varepsilon$. First choose the scalar polynomial; its
finite rational coefficients then determine the vector precisions.
For heat use the input name of $u$; for the source use $z$,
$Q=1/\ell$ and the approximation (12.7). Each resolvent call
uses a finite raw input. Even large coefficients are included
in $A_P,B_P$; cancellation is not treated as exact numerical
stability. This proves finite error control and termination.

Useful additional global norm bounds come directly from the
original source trace bound [S, (117.3)]:

$$
\|v_t\|_2^2=\|g_t\|_{L^2(m)}^2
 \le \frac{1+1/(2t_-)}{\ell}.
\tag{12.18}
$$

Indeed $\sup_{\lambda\ge0}(\lambda+1)e^{-2t\lambda}
\le1+(2\mathrm e t)^{-1}\le1+(2t_-)^{-1}$.
A rational upper bound $Q_t$ for the square root in (12.18)
is computable; it is independent of any spatial truncation.

For ordinary weighted representatives enumerate all finite rational
complex box-step functions $s$. Each $hs$ has a computable global
raw name: multiplication by the fixed bounded $s$ increases the
$h$ error by at most $\|s\|_\infty$. Norms of differences
with $v_t$ are computable from global names. Dovetail candidates
and precisions until a strict upper test certifies

$$
\|hs-v_t\|_{L^2(\mu)}<\varepsilon.
\tag{12.19}
$$

The box steps are dense in $L^2(m)$: $m$ is a finite Radon
measure on the original coordinate space and rational boxes
generate its Borel sets. As $h>0$ almost everywhere, $J_h$ is
onto and $\{hs\}$ is dense in raw $L^2$. Some candidate has
error less than $\varepsilon/2$, and its strict upper test
eventually succeeds. This proves termination and exactly
$\|s-g_t\|_{L^2(m)}<\varepsilon$. No algorithm for a
pointwise reciprocal of $h$ is used.

Finally the actual positive-time law has raw density $hv_t$.
For finite names $H_0,V_0$ of $h,v_t$ with errors
$\alpha,\beta$, respectively, Cauchy–Schwarz gives

$$
\|H_0V_0-hv_t\|_{L^1(\mu)}
 \le \alpha Q_t+(1+\alpha)\beta.
\tag{12.20}
$$

Thus finite products on their common box partition supply a
global $L^1$ name as well. Every norm and error above is on all
of $G$; none omits an unmeasured source or exterior region.
$\square$

**Theorem 12.5 (original bounded multiplication conditional on
exact calibration).** Suppose a scalar name of the exact $M$
in (12.3) has been computed. Then, using the preceding constructed
services, multiplication by each original $f_y$ is computable on
every global raw $L^2$ input, with arbitrary certified absolute
error. This is a reduction conditional on deriving that scalar;
it does not add $M$ to the inputs of Definition 12.1.

Proof. The exact class bounds are
$0\le f_3\le1/4$, $f_B=1/4$ and
$1/4\le f_0=f_1\le3/8$. Thus each multiplication operator
$D_y$ has norm at most $L_0=3/8$. Compute $c=1/(4M)$ and
the global vectors

$$
k_3=hf_3=cv_d,\qquad k_B=h/4,\qquad
k_0=k_1=3h/8-cv_d/2.
\tag{12.21}
$$

For example a rational $\widehat c$ and finite $V$ give
$\|\widehat cV-cv_d\|_2
\le|\widehat c|\|V-v_d\|_2
       +|\widehat c-c|Q_d$.
The $Q_d$ of (12.18) is computed, so this and the affine
formulas give all $k_y$ names with finite error budgets.

Given raw $u$ and a target $\varepsilon>0$, use the same
dense search as (12.19) to find a bounded finite box step $s$
with a strictly certified
$\|u-hs\|_2<\varepsilon/(2L_0)$.
Then compute $s k_y$ to error less than $\varepsilon/2$.
This is possible by requesting the $k_y$ error less than
$\varepsilon/[2(1+\|s\|_\infty)]$.
The exact correspondence on the dense vectors is
$D_y(hs)=s k_y$, and therefore the output error is at most

$$
L_0\|u-hs\|_2+\|\widehat{k_ys}-k_ys\|_2
 <\varepsilon.
\tag{12.22}
$$

Density and the strict residual test prove termination. The search
needs neither a lower pointwise bound for $h$ nor local division,
and no supremum of an approximate $g_d$ is computed. The output
is an approximation to the original multiplier, not a new emission.
$\square$

**Theorem 12.6 (exact calibration, first-read probability and
finite words have the same numerical obligation).** Relative to
the constructed services of §11 and Theorems 12.2–12.4, the
following services on the original parameter-name class are
uniformly mutually computable: a scalar name of $N_d$, a scalar
name of $M$, a scalar name of the actual $p(3)$ at the first
read $2d$, and an absolute-error evaluator for $p(w)$ for every
supplied finite chronological $w\in\mathcal L^*$. No one of
these four services is asserted to have been constructed from
the coefficients by this equivalence.

Proof. The passage $N_d\leftrightarrow M$ is addition or
subtraction of one. Given $M$, use Theorem 12.5 and the already
constructed heat action. Reuse exactly the cylinder recursion
(8.4), also [Original Passive Predictive Memory, (1.3)](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_PASSIVE_PREDICTIVE_MEMORY.md):

$$
\begin{gathered}
W_\varnothing=h,\qquad W_{yu}=D_yS_dW_u,\qquad
W_w=hF_w,\\
F_\varnothing=1,\qquad F_{yu}=f_yT_dF_u,\qquad
p(w)=\langle v_{2d},W_w\rangle_\mu.
\end{gathered}
\tag{12.23}
$$

Induction proves $W_w=hF_w$ by unitary conjugation. Conditional
independence and the Markov property give the cylinder law with
the original first-read density $g_{2d}$ and every gap $d$.
Computing from the last letter to the first is just an order of
evaluation. The transition after the final letter in (12.23)
acts on $1$, since $T_d1=1$, and adds no observation. Positive-time
absolute continuity in [S, (117.2)] ensures that every allowed
Borel repair gives the same finite-word probabilities.

Here is a finite budget. All exact heat and emission operators
are contractions and $\|W_w\|_2\le1$. If the initial $h$
error is $E_0$ and at stage $j$ the heat-action and multiplication
errors on the actually supplied intermediate vectors are
$s_j,b_j$, the accumulated error satisfies

$$
E_W\le E_0+\sum_{j=1}^{|w|}(s_j+b_j).
\tag{12.24}
$$

This follows at each stage by contractivity for propagation of
the previous error, then the triangle inequality for the two
new errors. With $\|V-v_{2d}\|_2\le E_v$,
$Q\ge\|v_{2d}\|_2$ computed by (12.18), and scalar rounding
error $\sigma$, the final pairing obeys

$$
|\widehat p(w)-p(w)|
 \le E_v+(Q+E_v)E_W+\sigma.
\tag{12.25}
$$

For $0<\varepsilon\le1$, set
$E=\varepsilon/[8(Q+1)]$, take
$E_v\le\varepsilon/8$, $E_0\le E/2$,
$s_j,b_j\le E/[4(|w|+1)]$ and
$\sigma\le\varepsilon/4$. Then $E_W<E$ and (12.25)
is less than $\varepsilon$. For larger requested errors use
$\min(\varepsilon,1)$; return $p(\varnothing)=1$ directly.
Every nonempty word requires finitely many terminating heat and
multiplier calls. This proves sufficiency of exact $M$.

For necessity no asymptotic word or stationary preparation is
needed. The already computed source names give the scalar

$$
\begin{aligned}
I_d&=\langle v_{2d},v_d\rangle_\mu
     =\langle T_dg_d,g_d\rangle_m
     =\|g_{3d/2}\|_{L^2(m)}^2
     =\|v_{3d/2}\|_2^2\ge1,\\
p(3)&=cI_d=\frac{I_d}{4M}>0,\qquad
M=\frac{I_d}{4p(3)}.
\end{aligned}
\tag{12.26}
$$

Self-adjointness and $g_{t+s}=T_sg_t$ prove the norm equality.
Mass one and $\|h\|_2=1$ give
$1=|\langle h,v_{3d/2}\rangle|\le\|v_{3d/2}\|_2$.
The formula for $p(3)$ integrates the same original $f_3=cg_d$
against the actual first-read density $g_{2d}$. Thus any name
of just that first marginal computes $M$. Refine its intervals
until a rational $q_->0$ lower-bounds both $p(3)$ and its
chosen approximation $\widehat p$. Positivity proves finite
termination of this search. If $|I_d-\widehat I|\le e_I$
and $|p(3)-\widehat p|\le e_p$, then

$$
\left|\frac{I_d}{4p(3)}-
             \frac{\widehat I}{4\widehat p}\right|
 \le \frac{e_I}{4q_-}
           +\frac{|\widehat I|e_p}{4q_-^2}.
\tag{12.27}
$$

Interval division, with these errors and arithmetic rounding,
therefore yields any requested $M$ precision. Finally an
all-word evaluator includes the single word $3$. These
implications prove the equivalence on the same source class.
They compute no unknown probability by requesting it as an
additional original input. $\square$

**Proposition 12.7 (computed lower information and the source
trace).** The original coefficients and positive clock names
compute the lower cut of $N_d$. More precisely, for every
rational $q\ge0$ the real number

$$
E(q)=\|(v_d-qh)_+\|_{L^2(\mu)}
\tag{12.28}
$$

has a scalar name, and $E(q)>0$ if and only if $q<N_d$.
They also compute, for every named $t>0$,

$$
\operatorname{tr}g_t=\|v_{t/2}\|_2^2
       \le\|g_t\|_{L^\infty(m)}.
\tag{12.29}
$$

No equality with the essential supremum is asserted in (12.29).

Proof. Real-part projection and positive part are contractions
on real $L^2$. Thus finite real approximations to $v_d,h$
with errors $e_v,e_h$ give an approximation to $E(q)$ with
error at most $e_v+q e_h$, plus the finite norm rounding.
For box steps the positive part and its norm are explicitly
computable. Since $h>0$ almost everywhere, and $m$ and $\mu$
have the same null sets,

$$
(v_d-qh)_+=h(g_d-q)_+,\qquad
E(q)>0\ \Longleftrightarrow\ m\{g_d>q\}>0
             \ \Longleftrightarrow\ q<N_d.
\tag{12.30}
$$

Strict positivity of a named real is semidecidable by interval
refinement. Dovetail all rational $q\ge0$ and all precisions;
enumerate a $q$ only when a strictly positive lower endpoint
for $E(q)$ is certified. This enumerates exactly the nonnegative
rationals below $N_d$. Taking successive maxima, starting at
zero, gives rational lower bounds converging to $N_d$.
Every rational below $N_d$ is eventually found. Boundedness
comes from [S, Theorem 133.2], and $N_d\ge1$ follows from
mass one; no upper numerical input is used by this enumeration.

For (12.29), propagation gives
$g_t=T_{t/2}g_{t/2}\in D(K)\subset\mathscr V$.
Apply the original trace identity at $t/2$ to $g_{t/2}$:
$\operatorname{tr}g_t=\langle g_{t/2},g_{t/2}\rangle_m$.
This norm is computable by Theorem 12.4. For
$N_t=\|g_t\|_\infty<\infty$, the form vector
$(g_t-N_t)_+$ is zero almost everywhere and hence is the zero
form vector. Its quasi-continuous value at the nonpolar $e$
is zero. The normal-contraction rule for the form and the
source trace then give $\operatorname{tr}g_t\le N_t$.
One cannot infer the reverse inequality from this argument.
$\square$

**Definition 12.8 (the remaining original upper-certificate
obligation and its exact sufficiency).** The unpaid source-side
obligation is to construct, from the same $a,\eta,d$ names,
an enumeration of finite certificates with rational conclusions
$U_j$ such that

$$
v_d\le U_jh\quad\mu\text{-a.e. on all }G,
\qquad \inf_jU_j=N_d.
\tag{12.31}
$$

Each accepted certificate must have proved soundness for the
original full endpoint and normalization. The enumeration must
be effective from the stated names and cofinal at $N_d$.
No acceptance criterion, cofinality theorem or certificate
producer for (12.31) is assumed here.

If such a producer is derived, it suffices: dovetail it with
the lower enumeration in Proposition 12.7, retain finite minima
of upper conclusions and finite maxima of lower conclusions,
and stop when their gap is less than a requested error.
Soundness encloses $N_d$ and cofinality of both sides proves
termination. Conversely a scalar interval name of $N_d$
supplies cofinal rational upper enclosures, whose a.e. order
conclusions follow from the definition of essential supremum.
Thus at the level of effective numerical information (12.31)
is exactly the missing upper side of the calibration, not an
extra spatial observation. A particular finite certificate
language would additionally require its own proved adequacy.

In the original source notation the same obligation can be
expressed without a pointwise kernel. Define on $L^1(m)\cap L^2(m)$
$\ell_d(u)=\operatorname{tr}(T_du)$.
The original Riesz identity is
$\ell_d(u)=\int g_du\,dm$. Since $g_d\ge0$ is bounded,

$$
\|\ell_d\|_{L^1(m)\to\mathbb C}=N_d.
\tag{12.32}
$$

For proof, the upper estimate is Hölder. For every $q<N_d$,
the indicator of $\{g_d>q\}$ belongs to $L^1\cap L^2$
because $m(G)=1$, and its normalized integral gives an operator
norm at least $q$. Taking $q\uparrow N_d$ proves (12.32).
Consequently cofinal certified bounds for this full source-trace
functional would pay (12.31), while avoiding a full pointwise
heat-kernel construction. They still require arbitrarily sharp
global bounds, not just a boundedness theorem.

In particular [S, (133.10)–(133.16)] proves finiteness by a
source-neighborhood estimate on heat orbits of globally supported
inputs, followed by $L^1/L^\infty$ duality. It supplies no
cofinal numerical upper enumeration. Even computing a single
finite bound for its local comparison, radius, weighted Sobolev
and parabolic constants would give only a majorant. Such a
majorant does not determine the original exact $M$, and replacing
$M$ by it in (12.3) changes the emissions.

The lower test (12.28) cannot certify (12.31): a small positive
residual is compatible with exceeding $U_j$ on a small set,
whereas the required certificate asserts zero residual. This
observation identifies a missing proof step and is not a
counterexample within the original coefficient family. Another
sufficient, stronger route would construct computable bounded
approximants $s_j$ with computable essential norms and prove
$|v_d-hs_j|\le2^{-j}h$ globally almost everywhere. Then
$|N_d-\|s_j\|_\infty|\le2^{-j}$ by the norm triangle
inequality. Such uniform relative approximation is also unpaid;
the weighted $L^2$ approximation (12.19) is weaker.

Any regional proof of (12.31) must derive its quantitative
source-neighborhood control, punctured compact evaluation and
oscillation bounds, and exterior order bounds from the original
coefficients and the same full trace. Global $L^2$ tails are
not exterior supremum bounds. Alternatively a proved sharp
source maximum principle could identify the norm with a
computed quantity such as (12.29); no maximum-at-source theorem
is used here. No noncomputability or original-family
impossibility conclusion follows from the unpaid obligation.

**Definition 12.9 (mathematical correspondence, economy and
remaining recovery scope).** The source-specific construction
in Theorems 12.2–12.4 is the composition of the actual
$A=\rho C$ resolvent [S, (115.5)], its correctly normalized
trace [S, (116.4), (116.13)], the deterministic entrance
[S, (117.2)–(117.6)] and the computed coefficient services
of §11. The new numerical correspondence is to these very
source vectors and global norms. Theorems 12.5–12.6 then
identify exactly the scalar obligation consumed by the unchanged
finite passive likelihoods. These are repository-derived
applications and deductions relative to the cited analytic
suppliers, not new generic spectral calculus or general
approximation theorems.

The mature resolvent-to-semigroup method is literature-attested
in Colbrook, [*Computing semigroups with error control*,
arXiv:2110.06350v1, §3, Theorem 7, and §4, Theorem 8](https://arxiv.org/html/2110.06350v1),
[DOI 10.1137/21M1398616](https://doi.org/10.1137/21M1398616).
Theorem 7 uses a common core for generator and adjoint, graph
Gram and input norm/coefficient evaluations, and semigroup
growth bounds. The PDE route of Theorem 8 additionally uses
the stated smooth-core, coefficient growth/variation and
input-tail access. Those hypotheses are not a construction
of this singular endpoint. Here (12.5) supplies the actual
resolvent, and (12.12)–(12.17) use its positive self-adjoint
structure to give a sufficient elementary scalar approximation
with explicit errors. No contour efficiency estimate is
transferred. Likewise Colbrook–Horning–Townsend
[EXT-SPECTRAL, §6.1, (26)] treats regular line or half-line
differential realizations, smooth coefficients, nonvanishing
leading coefficient and a separately verified self-adjoint
realization. Its shifted-solve method does not supply this
four-coordinate source trace or exact essential supremum.

The domain formulas of Ashbaugh et al., [*A Survey on the
Krein–von Neumann Extension*, arXiv:1203.5713v1, Theorem 2.1,
(2.9)–(2.11)](https://arxiv.org/html/1203.5713v1), require
$S\ge\epsilon I$ for $\epsilon>0$. No such positive lower
bound is imported at this threshold endpoint; the original
boundary calculation supplies (12.5). The equilibrium/trace
correspondence retains the mapping to Chen–Fukushima–Ying
specified in [S, §116], rather than applying transient
zero-order formulas to this recurrent conservative source.

The existing D5 Dyson–Phillips result,
[DysonPhillipsPerturbation](../../../D5/S3/Quantum/Analysis/DysonPhillipsPerturbation.lean),
including its private input and native-semigroup helpers,
assumes a supplied strongly continuous contraction semigroup
and a bounded perturbing operator. It is not a supplier of
the singular endpoint or entrance in (12.2). The pinned
mathlib at `56a005855ea17e0b0958f73ec801ae140b0a1679`,
`Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Isometric.lean`
(`norm_cfcHom`, `norm_cfc_le`) and
`Analysis/SpecialFunctions/Bernstein.lean`
(`bernstein.probability`, `bernstein.variance`,
`bernsteinApproximation_uniform`) supply generic norm and
approximation results. They are reused mathematical
intermediates; none names the original source or calibration.
The Bernstein variance estimate is included in (12.15) only
to quantify its use in this source construction. No worldwide
priority or kernel-verification claim is attached to these
ordinary mathematical deductions.

The dense multiplication in Theorem 12.5 uses less numerical
information than a full pointwise interacting heat kernel or
uniform division by $h$. Rebuilding the §11 source graphs or
substituting the killed $F$ heat would not supply the missing
calibration. The converse (12.26) proves that a direct evaluator
for original words, even just the first label $3$, cannot
leave exact $M$ unpaid as a computational obligation. It
does not prove that paying it is impossible.

The immediate consumers are original finite chronological
likelihoods and finite predictive profiles
$R_u(v)=p(uv)/p(u)$ of [Original Passive Predictive Memory,
Theorem 2.1 and §5](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_PASSIVE_PREDICTIVE_MEMORY.md).
Once exact calibration is supplied, each original $p(u)>0$
permits certified division by refinement to a positive lower
bound, just as in (12.27). This is compatible with infinite
exact Hankel rank: each requested finite computation uses
finitely many contractions, while a uniform finite-dimensional
realization is a different assertion. The generic algebraic
and private factorization helpers in
[WordHankelRealization](../../../D5/S3/Observer/Hankel/WordHankelRealization.lean)
retain their own finite-dimensional hypotheses.

The [original-word geometry, Theorems 3.1–3.3, 4.1–4.5
and §7](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_WORD_GEOMETRY_RECOVERY.md)
uses exact full-law information to identify the observable
equivalence class, sample-time continuation and the normalized
source boundary. Its unbounded spectral inverses, limiting
projections and improper integrals retain their own domains
and lack numerical rates under that premise. A finite-word
evaluator is not an automatic effective inverse for all those
operations, a decision procedure for equality of whole
predictive states or a recovery of the full spatial algebra.
The parameter-fibre classification and invisible-direction
obstructions there are unchanged.

For resource accounting, each polynomial action uses $N$
sequential calls to the actual resolvent and a finite rational
linear combination, with degree, coefficient sizes and requested
precision given by (12.12)–(12.17). Each conditional word uses
at most $|w|$ heat and $|w|$ multiplication calls. The costs
also include parameter/clock-name answers, inherited §11 graph
and residual searches, the positive-$D$ refinement, dense
step searches and any positive-probability divisions. The
successful dictionary indices and input-name answer costs
have no bound asserted here; small $t,D$ or $p(u)$ can require
high precision. Termination is proved for the stated services,
but no parameter-uniform, polynomial or practical runtime is
deduced. No numerical PDE execution is part of these theorems.

Coefficient access remains mathematical model access. It is
not evidence that a passive observer has acquired $a,\eta,d$
or an exact probability from one physical record. There is
no hidden-coordinate probe, reset, extra label, stationary
preparation, disturbance or timed release. Finite-record
confidence, physical realization, arbitrary $\alpha,\beta$
operational meanings and full mutual recovery of space, time,
boundary and memory retain their separate obligations. The
coefficient-to-exact-word objective remains unresolved at
(12.31); the strict heat/source construction and conditional
reductions do not complete the continuing recovery programme.

## 追加锚（本行以下为增补区）


## 13. Sharp source-resolvent suprema and separation from the original fixed-time source

**Definition 13.1 (the original source and its simple-resolvent cone).**
Retain all hypotheses and normalizations of Definition 12.1, for every
finite positive $a,\eta,d$. Thus $G=H^1\times\mathbb R$, raw Haar $\mu$,
the unit-source $\Gamma$, $C(w_*)=1$, $h=w_*/\|w_*\|_2$,
$m=h^2\mu$ and $m(G)=1$ remain fixed. The actual complex operator is
$H=H_{\rm end}$ with $A=\rho C$, not the auxiliary $F$ with $C=0$.
All discounts below use the original time units. Put

$$
\begin{gathered}
G_r=(F+r)^{-1},\quad n_r=h-rG_rh,\quad
 d_r=\langle h,n_r\rangle>0,\quad b_r=J_h^{-1}n_r,\\
p_r=\frac{n_r}{r d_r},\quad
\psi_r=J_h^{-1}p_r=\frac{b_r}{r d_r},\qquad r>0,\\
D=d_1,\quad z=n_1/D,\quad R=(H+1)^{-1}.
\end{gathered}
\tag{13.1}
$$

The $z,R$ in (13.1) are exactly (12.4)–(12.5). In particular
$p_1=z$, and $R=G_1+|n_1\rangle\langle n_1|/D$ is the full
endpoint resolvent. The inverse $J_h^{-1}$ denotes the unitary map
between the two Hilbert spaces, not a numerical pointwise division.
For a finite integer $J\ge0$, arbitrary real $\beta$, nonnegative
real coefficients $\alpha_j$ and positive real discounts $r_j$, define

$$
\begin{gathered}
B=\beta+\sum_{j=1}^J\alpha_j\psi_{r_j},\qquad
W=J_hB=\beta h+\sum_{j=1}^J\alpha_jp_{r_j},\\
\Phi(\lambda)=\sum_{j=1}^J\frac{\alpha_j}{\lambda+r_j},\qquad
S_B=\beta+\sum_{j=1}^J\frac{\alpha_j}{r_jd_{r_j}}.
\end{gathered}
\tag{13.2}
$$

An empty sum is permitted. This is the cone of positive simple source
resolvents with arbitrary constant addition. It is a mathematical
comparison class, without a change to the source evolution or readout.
The exponentially averaged probability density is
$\zeta_r=r\psi_r=b_r/d_r$, since [S, (116.14)] gives
$\psi_r=\int_0^\infty e^{-rt}g_t\,dt$ in $L^2(m)$.
Consequently finite probability mixtures $\sum_jq_j\zeta_{r_j}$,
$q_j\ge0$, $\sum_jq_j=1$, are the subclass
$\beta=0$, $\alpha_j=q_jr_j$. The coefficients in (13.2) have
no mass constraint; their integrals are
$\int B\,dm=\beta+\sum_j\alpha_j/r_j$.

**Theorem 13.2 (an exact global supremum for the source-resolvent
cone).** For every $B$ in (13.2),

$$
\mathop{\rm ess\,sup}_{m}B
 =\operatorname{tr}B=S_B.
\tag{13.3}
$$

For $\beta\ge0$, also $\|B\|_{L^\infty(m)}=S_B$.
If the finite coefficients and discounts have total interval names,
then the original coefficient services of §11 compute $S_B$ to every
requested absolute error and enumerate cofinal rational global upper
certificates $B\le U$. No value $h(e)$ is needed.

Proof. The equilibrium-potential identity [S, (116.4)] states
$b_r\in\mathscr V$, $0\le b_r\le1$ quasi-everywhere and
$\operatorname{tr}b_r=1$. Constants belong to the full form domain.
Thus $B\in\mathscr V$, $B\le S_B$ almost everywhere, and
$\operatorname{tr}B=S_B$. These are statements for the same full
form and nonpolar source.

For any real form vector $v$ and real constant $U$, the implication

$$
v\le U\quad m\text{-a.e.}
\quad\Longrightarrow\quad\operatorname{tr}v\le U
\tag{13.4}
$$

follows from normal contraction and quasi-continuous evaluation:
$(v-U)_+$ is the zero form vector, so its source trace is zero,
whereas that trace equals $(\operatorname{tr}v-U)_+$.
This is the same order argument used in Proposition 12.7; it does
not assign a value to an arbitrary density representative at $e$.
Taking $U=\mathop{\rm ess\,sup} B$ proves the lower bound in
(13.3); boundedness makes this a finite essential upper bound.
If $\beta\ge0$, then $B\ge0$ and its norm is its essential supremum.
For negative $\beta$, (13.3) is an essential-supremum formula;
no formula for the absolute norm is inferred from it.

For the numerical assertion, §11 computes each $d_{r_j}$ from the
original names. Refine its intervals until their lower endpoints
are positive. This terminates because $r_j,d_{r_j}>0$. Finite
interval multiplication, division and addition then enclose $S_B$
with arbitrarily small width. Rational upper endpoints, enlarged by
a vanishing rational slack if necessary, give $U\ge S_B$ converging
to $S_B$. Formula (13.3) proves soundness and cofinality for this
comparison class. The argument uses the supplied nonnegativity of
the coefficients, without attempting to decide equality to zero.
$\square$

**Theorem 13.3 (positive distance in every original source member,
including arbitrary constant addition).** For every original
$a,\eta,d>0$ there is a rational $\delta>0$ such that, simultaneously
for every finite $J$, every $\beta\in\mathbb R$, every
$\alpha_j\ge0$ and every $r_j>0$,

$$
\begin{aligned}
\left\|v_d-\beta h-\sum_{j=1}^J\alpha_jp_{r_j}\right\|_{L^2(\mu)}
 &=\left\|g_d-\beta-\sum_{j=1}^J\alpha_j\psi_{r_j}\right\|_{L^2(m)}
 \ge\delta.
\end{aligned}
\tag{13.5}
$$

The same $\delta$ works for the $L^2(m)$ closure of this entire
comparison class. A construction of such a $\delta$ from only the
original coefficient and clock names is given in Theorem 13.4.

Proof. Let $E_H$ be the spectral resolution of the actual $H$ and set

$$
\nu(A)=\langle z,E_H(A)z\rangle_\mu.
\tag{13.6}
$$

This is a finite positive measure on $[0,\infty)$. It is the spectral
measure of the actual source-resolvent vector, not that of an
independently chosen example. The original maximal-domain identity
[S, (116.5)] gives

$$
A(z)-\rho C(z)=-\frac1{a c_h}\ne0.
\tag{13.7}
$$

Indeed its boundary defect for $n_1$ is $-D/(a c_h)$; divide by
$D>0$. Hence $z\notin D(H)$, although $z$ is a full form vector
and is in $D(S_{\min}^*)$. If $\nu$ were supported in a bounded
interval, the spectral domain criterion
$\int\lambda^2\,d\nu<\infty$ would put $z$ in $D(H)$,
contradicting (13.7). Thus

$$
\nu((L,\infty))>0\qquad\text{for every finite }L\ge0.
\tag{13.8}
$$

Only this consequence of the defect, rather than any numerical
estimate of its high-frequency mass, will be needed.

Theorem 12.3 supplies the exact fixed-time identity
$v_d=(H+1)e^{-dH}z$. The corresponding resolvent identity is

$$
p_r=(H+1)(H+r)^{-1}z.
\tag{13.9}
$$

Here the right side is the bounded spectral multiplier
$(1+\lambda)/(r+\lambda)$ applied to $z$; it does not apply
$H$ directly to $z$. To verify its source factor, transport
[S, (116.4)] to the raw form $\mathfrak q_H$:

$$
\mathfrak q_{H,r}[p_r,y]
 =\operatorname{tr}(J_h^{-1}y)
 =\mathfrak q_{H,1}[z,y].
\tag{13.10}
$$

For $y\in D(H)$ the last expression is
$\langle z,(H+1)y\rangle$, and the first is
$\langle p_r,(H+r)y\rangle$. Since $H+r$ maps $D(H)$ onto
$\mathcal H$, bounded spectral calculus proves (13.9).
All pairings have the antilinear-first convention of §12.
This calculation reuses the source-trace and heat identities;
it supplies the correspondence needed for the separation.

Also $\langle h,z\rangle=1$, so
$E_H(\{0\})z=h$, because $\ker H=\mathbb Ch$ and $\|h\|_2=1$.
For $E=\|v_d-W\|_2$, spectral orthogonality now gives

$$
E^2=
 \left|1-\beta-\sum_j\frac{\alpha_j}{r_j}\right|^2
 +\int_{(0,\infty)}(1+\lambda)^2
       |e^{-d\lambda}-\Phi(\lambda)|^2\,d\nu(\lambda).
\tag{13.11}
$$

In particular the arbitrary, possibly negative constant affects only
the zero eigenspace. It cannot cancel a positive-frequency discrepancy.

Choose rational bands and rational triangular tents satisfying

$$
\begin{gathered}
1/d<L_1<U_1<L_2<U_2,\qquad I_i=[L_i,U_i],\\
0\le\theta_i\le1,\quad\theta_i=0\text{ outside }I_i,
\quad\theta_i(L_i)=\theta_i(U_i)=0,\\
\sigma_i=\int\theta_i\,d\nu>0\quad(i=1,2).
\end{gathered}
\tag{13.12}
$$

The peak of each tent is at a rational interior point and has height
one. Such bands and tents exist by (13.8): choose a finite open
interval of positive mass above $1/d$, and then another above its
upper endpoint. Each interval is covered by countably many rational
tents' positivity sets, so some such tent has positive integral.
No absolute continuity or absence of spectral atoms is required.

The scalar function $k_d(\lambda)=\lambda e^{-d\lambda}$ is strictly
decreasing for $\lambda>1/d$. Consequently

$$
\Delta=U_1e^{-dU_1}-L_2e^{-dL_2}>0.
\tag{13.13}
$$

In contrast, every permitted positive simple-resolvent sum satisfies

$$
\frac{d}{d\lambda}\bigl[\lambda\Phi(\lambda)\bigr]
 =\sum_j\frac{\alpha_jr_j}{(\lambda+r_j)^2}\ge0.
\tag{13.14}
$$

This elementary Stieltjes-cone property is used as a classical scalar
fact, not as a new functional-calculus assertion. Define probability
measures $d\pi_i=\theta_i\,d\nu/\sigma_i$ on the two bands. Then

$$
\begin{gathered}
\int k_d\,d\pi_1-\int k_d\,d\pi_2\ge\Delta,\\
\int\lambda\Phi(\lambda)\,d\pi_1
 \le\int\lambda\Phi(\lambda)\,d\pi_2.
\end{gathered}
\tag{13.15}
$$

For
$E_i^2=\int\theta_i\lambda^2|e^{-d\lambda}-\Phi(\lambda)|^2\,d\nu$,
disjointness of the tents and $\lambda^2\le(1+\lambda)^2$
give $E_1^2+E_2^2\le E^2$. Combine the two lines of
(13.15) and apply Cauchy–Schwarz twice:

$$
\begin{aligned}
\Delta
 &\le \left|\int(k_d-\lambda\Phi)\,d\pi_1\right|
       +\left|\int(k_d-\lambda\Phi)\,d\pi_2\right|\\
 &\le E_1/\sqrt{\sigma_1}+E_2/\sqrt{\sigma_2}
 \le E\sqrt{1/\sigma_1+1/\sigma_2}.
\end{aligned}
\tag{13.16}
$$

Thus every member has distance at least
$\Delta\sqrt{\sigma_1\sigma_2/(\sigma_1+\sigma_2)}>0$.
Any smaller positive rational proves (13.5). Distance is continuous
in $L^2$, giving the closure assertion. Equations (13.7) and
(13.9) are why this is an obstruction for every original member:
the separated bands are forced by its actual source boundary defect
and refer to its actual entrance vector at its actual clock $d$.
$\square$

**Theorem 13.4 (a finite effective separation certificate).** From
only total interval names of the original positive $a,\eta,d$ and
the constructed services of §11, there is a terminating mathematical
algorithm returning a rational $\delta>0$ for (13.5). A finite
certificate consists of the rational bands and tents in (13.12),
certified scalar enclosures for their masses and for (13.13), and
positive rational $s_1,s_2,q,\delta$ satisfying

$$
\sigma_i\ge s_i>0,\qquad \Delta\ge q>0,\qquad
0<\delta^2<q^2\frac{s_1s_2}{s_1+s_2}.
\tag{13.17}
$$

Acceptance requires finitely many certified interval and rational
inequalities. It never tests whether an unknown spectral mass is zero.

Proof. First use §11 and Theorem 12.2 to construct the global raw
name of $z$ and the action of the contraction $R$ on global names.
Refine the $D$ intervals to a rational $0<\ell<D$ and fix the
rational norm bound $Q=1/\ell\ge\|z\|_2$. That search terminates
by $D>0$. This reuses the already constructed full resolvent;
a semigroup or a spectral-projection oracle is not an input.

Here is a scalar mass evaluator with explicit finite errors.
For a candidate tent $\theta$ supported in a rational
$[L,U]\subset(0,\infty)$, define on $[0,1]$

$$
\varphi(x)=
\begin{cases}
\theta(x^{-1}-1),&x>0,\\
0,&x=0.
\end{cases}
\qquad
\int\theta\,d\nu=\langle z,\varphi(R)z\rangle.
\tag{13.18}
$$

The function vanishes on $[0,(1+U)^{-1}]$ and on
$[(1+L)^{-1},1]$. If $L_\theta$ bounds the absolute slopes
of the tent, the rational number
$L_\varphi=L_\theta(1+U)^2$ is a global Lipschitz bound.
On the active interval this follows by differentiating
$x^{-1}-1$; across the endpoints it follows from continuity and
the zero endpoint values. Therefore $\varphi$ is computably
continuous at $0$ without a high-frequency tail estimate.

Use the rational Bernstein polynomial

$$
P_N(x)=\sum_{k=0}^N\varphi(k/N){N\choose k}
                         x^k(1-x)^{N-k}.
\tag{13.19}
$$

All its coefficients are rational, including the value at $k=0$.
The usual binomial-variance estimate gives
$\|P_N-\varphi\|_\infty\le L_\varphi/(2\sqrt N)$:
for a binomial random variable $Y$ with parameters $N,x$, bound
$\mathbb E|\varphi(Y/N)-\varphi(x)|$ by
$L_\varphi\sqrt{x(1-x)/N}$. This is a reused polynomial
approximation estimate. For any rational $\varepsilon_P>0$,
choose $N$ by the rational test
$L_\varphi^2<4N\varepsilon_P^2$. Spectral calculus gives
$\|P_N(R)z-\varphi(R)z\|_2\le Q\varepsilon_P$.

For completeness, polynomial action has a terminating error budget
using exactly the supplied resolvent action. Expand
$P_N(x)=\sum_{k=0}^Nc_kx^k$ in monomials. Choose a finite rational
box-step $Z$ with $\|Z-z\|_2\le\varepsilon_0$ and put $Y_0=Z$.
For each $k\ge1$ compute a finite box-step $Y_k$ with
$\|Y_k-RY_{k-1}\|_2\le\varepsilon_k$. Since $\|R\|\le1$,

$$
\|Y_k-R^kz\|_2\le\varepsilon_0+\sum_{j=1}^k\varepsilon_j.
\tag{13.20}
$$

The finite combination $W=\sum_kc_kY_k$, including any chosen
finite arithmetic error $\varepsilon_A$, obeys

$$
\begin{gathered}
\|W-\varphi(R)z\|_2\le e_W,\\
e_W=Q\varepsilon_P+
 \sum_{k=0}^N|c_k|
       \left(\varepsilon_0+\sum_{j=1}^k\varepsilon_j\right)
       +\varepsilon_A.
\end{gathered}
\tag{13.21}
$$

The finite inner product $\operatorname{Re}\langle Z,W\rangle$
is computed on the common rational box partition. If its rounding
allowance is $\varepsilon_I$, it encloses the desired mass with
absolute error at most

$$
\varepsilon_0Q+(Q+\varepsilon_0)e_W+\varepsilon_I.
\tag{13.22}
$$

Indeed $\|\varphi(R)z\|_2\le Q$, and split the pairing error
as $\langle Z-z,\varphi(R)z\rangle+
\langle Z,W-\varphi(R)z\rangle$. First choose the polynomial
error, then choose the finitely many action tolerances using its
known coefficients. Every term in (13.22) can be made arbitrarily
small. Large polynomial coefficients affect cost, not convergence
of this finite error search. Formula (13.22) supplies total interval
names of every candidate mass from the original inputs.

To choose the bands, refine the positive $d$ name to a rational
$d_->0$ with $d_-\le d$, and choose a rational $L_*>1/d_-$.
Enumerate all rational quadruples
$L_*<L_1<U_1<L_2<U_2$ and all rational interior tent peaks.
Dovetail their mass evaluations, so that no zero-mass candidate
can block the search. Accept a pair when both mass intervals
have strictly positive rational lower endpoints $s_i$.
Existence in (13.12) ensures that a positive pair appears, and
convergence of its enclosures ensures eventual acceptance.

For an accepted pair compute (13.13) from the total $d$ name,
using certified elementary exponential arithmetic, until its
lower endpoint $q$ is positive. This terminates: all four
endpoints exceed $1/d$, so $\Delta>0$. Ordinary scalar
exponential intervals can, for example, use range reduction and
Taylor remainder bounds on a rational compact interval; their
width tends to zero. Finally enumerate positive dyadic
$\delta$ until the rational squared inequality in (13.17)
holds. Its positive right side proves termination.

The function $xy/(x+y)$ is increasing separately on
$(0,\infty)^2$, since its partial derivatives are
$y^2/(x+y)^2$ and $x^2/(x+y)^2$. Thus the lower mass bounds
in (13.17) and $q\le\Delta$ imply the lower distance in
(13.16) is strictly greater than $\delta$. This proves
soundness of the finite acceptance rule for every permitted
$\beta,\alpha_j,r_j$, whether or not those parameters are
computably named. Only construction of the certificate uses
the original numerical names. No uniform bound on the successful
band indices, polynomial degrees or number of precision queries
is asserted. $\square$

**Proposition 13.5 (the excluded transfer and the surviving sharp
upper obligation).** For a fixed original member, no sequence
$B_n$ of (13.2) converges to $g_d$ in $L^2(m)$ or uniformly in
essential supremum. More quantitatively, there is no such $B$
with a global relative-carrier error

$$
|v_d-J_hB|\le\varepsilon h\quad\mu\text{-a.e.},
\qquad 0\le\varepsilon<\delta,
\tag{13.23}
$$

where $\delta$ is any certificate of Theorem 13.4. This includes
unrestricted positive coefficient sums and probability mixtures,
even with arbitrary constant addition. It excludes neither signed
simple-resolvent sums, repeated resolvent powers, nor pure upper
envelopes without an approximation assertion. In particular it does
not decide $N_d=\operatorname{tr}g_d$ or the existence of the cofinal
upper certificates (12.31).

Proof. The $L^2$ statement is (13.5). Since $m(G)=1$,
$\|g_d-B\|_2\le\|g_d-B\|_\infty$, and (13.23) would imply
$\|v_d-J_hB\|_2\le\varepsilon\|h\|_2=\varepsilon$,
contradicting (13.5). Thus approximation of the original source
by this cone cannot transfer (13.3) to an exact name of $N_d$.
Signed coefficients do not obey (13.14); a repeated pole
$(\lambda+r)^{-k}$, $k\ge2$, has derivative
$[r-(k-1)\lambda]/(\lambda+r)^{k+1}$ after multiplication by
$\lambda$, so the monotonicity used in the proof also fails for
that different class. The theorem makes no exclusion for either.

A one-sided upper envelope $g_d\le B$ need not have small
$\|B-g_d\|_2$, even if its essential supremum approaches $N_d$.
Consequently (13.5) is not an obstruction to every possible use
of the cone in upper certificates. Its precise target is a
vanishing-error approximation retaining the simple positive
source-resolvent formula. Equations (13.3) and (13.5) alone
provide no certificates (12.31) for $g_d$.

The original likelihood consumer remains (12.3), with exactly
$c=1/[4(1+N_d)]$, $f_3=cg_d$, $f_B=1/4$ and
$f_0=f_1=(3/4-f_3)/2$. It has the original $e$-start, first passive
read at $2d$, gaps $d$, and fresh conditional noise without
disturbance. Theorems 12.5–12.6 already identify the exact calibration,
first-read and finite-word numerical interfaces. A computable
upper bound substituted for $N_d$ would change these emissions.
Theorem 13.2 supplies sharp suprema for $B$, not that calibration.

For comparison, a proof of $N_d=\operatorname{tr}g_d$ would use
the computed scalar (12.29) directly, and would not require a
full pointwise kernel. A different global supersolution certificate
could instead bound the functional (12.32), provided both soundness
and cofinality were established. Effective local-to-global peak
detection would need quantitative control of the original source
neighborhood and exterior, together with a proved global error.
Spatial $L^2$ tails alone bound integrated error and do not certify
$g_d\le U$ on all $G$. None of these additional relations follows
from the source-resolvent norm formula or the separation theorem.
Numerical evaluation, resource bounds and confidence from a single
passive record likewise require their respective hypotheses; the
present mathematical certificate performs no source preparation,
record acquisition or hidden-coordinate observation. $\square$

**Definition 13.6 (source correspondence, antecedents and scope).**
The spectral theorem and elementary positive-kernel facts used inside
the proofs are `literature-attested`; the relations (13.3), (13.5)
and their effective certificate are `repo-derived` for the source
of Definition 12.1. The classical scalar monotonicity (13.14),
polynomial approximation and generic resolvent-to-functional-calculus
steps are antecedents, not additional singular-source constructions.
The relevant correspondences are:

| Antecedent | Exact use and boundary |
| --- | --- |
| [S, (115.5), (116.4)–(116.5), (116.13)–(116.14)] | The full complex endpoint supplies $b_r$, its nonpolar trace, the actual rank-one resolvent and the nonzero boundary defect (13.7). $F$ supplies only $G_r$; it is never substituted for $H$. |
| §§11–12, especially (12.5), (12.7)–(12.10), (12.29)–(12.32) | The original coefficient names give $h,z,R$, the deterministic-time source correspondence and the exact outstanding upper obligation. Their heat, calibration and word equivalences are reused. |
| G. Teschl, [Mathematical Methods in Quantum Mechanics](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), Theorems 3.1–3.2 and (3.21) | Scalar spectral measures and the unbounded-operator domain criterion apply to this self-adjoint $H$ and its actual $z$. They give (13.8) from (13.7), and the spectral error identity; they provide no original source trace or sharp supremum. |
| Z.-Q. Chen, M. Fukushima and J. Ying, [Traces of symmetric Markov processes and their characterizations](https://arxiv.org/pdf/math/0606784v1), §2, hitting kernel before (2.14) | The equilibrium/hitting framework is the antecedent used by [S]. The closed set here is exactly $\{e\}$ and the energy is the original $\mathscr E$, without an imported Brownian factor or changed clock. |
| D. Braess and W. Hackbusch, [On the approximation of Stieltjes functions by exponential sums and rational functions with applications to partial differential equations](https://doi.org/10.1007/s00211-025-01523-1), §4.3 | Positive simple-pole interpolation there assumes a Cauchy–Stieltjes target. A Laplace–Stieltjes or completely monotone target alone does not supply that hypothesis. Equation (13.14) and the actual-source two-band argument specify the obstruction needed here. |
| A. Burchard and Á. D. Martínez, [On monotonicity of heat kernels: a new example and counterexamples](https://arxiv.org/html/2502.08212v1), Theorems 1.2 and 2.2 | Rotational symmetry on compact smooth manifolds and failures for a simple first eigenvalue concern different source families. Neither statement decides source maximality for this singular weighted endpoint. |

The existing D5 tree-boundary contraction statements, including the
private helpers in `BiasedBoundaryMarkovSemigroup`, have tree carriers;
the private pair argument and public representative theorem in
`IntervalLInfinityRepresentative` assume interval translation control.
Neither instantiates the source/domain map (13.7)–(13.10).
`LocalizedStieltjesNevanlinnaKernel` treats finite atomic complex
Cauchy kernels and their support localizer, rather than this actual
unbounded spectral source measure. Pinned mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` supplies generic
essential-supremum and continuous-functional-calculus order results;
these do not construct the source-specific upper side (12.31).
The antecedents support the displayed deductions within their stated
hypotheses, without a worldwide-priority assertion or a new Lean claim.
The exact original $N_d$ upper enumeration, source maximum relation
and finite-record confidence remain separate mathematical obligations.

## 追加锚（本行以下为增补区）

## 14. Gaussian exterior decay for the original source quotient

**Definition 14.1 (full-source hypotheses and propagation gauge).** Retain the analytic suppliers of Definition 12.1: [E, §§109–112] and [S, §§115–117, 133], with their hypotheses. For arbitrary original $a,\eta,d>0$, the group is $G=H^1\times\mathbb R$, with $e=0$, product $pp'=(x+x',y+y',z+z',w+w'+xy')$, raw Haar measure $\mu=dx\,dy\,dz\,dw$, and fields $X_1=\partial_x$, $X_2=\partial_y+x\partial_w$, $X_3=\partial_z$. Write

$$
P=aL-\eta\partial_w^2,\quad L=-\sum_{i=1}^3X_i^2,\quad
V=16\sqrt{a\eta}\,\Gamma,\quad L\Gamma=\delta_e.
\tag{14.1}
$$

Here $\Gamma$ is the original unit-source Green field of $L$, not that of $P$. Retain the full nonnegative endpoint $H$ with $A=\rho C$, its coefficient-positive normalized zero state $h=w_*/\|w_*\|_2$, $C(w_*)=1$, $m=h^2\mu$, $J_hu=hu$, $K=J_h^{-1}HJ_h$, and $T_t=e^{-tK}$. Thus $\|h\|_2=1$, $m(G)=1$, and $h$ is smooth and strictly positive on $G\setminus\{e\}$, where $(P-V)h=0$. The full regular strongly local form is

$$
\mathscr E[u]=\int_G\left(a\sum_{i=1}^3|X_i u|^2+\eta|\partial_wu|^2\right)dm,
\qquad \mathscr V=\mathscr V_0\dotplus\mathbb C1.
\tag{14.2}
$$

Its source trace $\operatorname{tr}$ is quasi-continuous evaluation at the nonpolar $e$. For the original deterministic-time source density $g_t$, put $v_t=hg_t$. The suppliers give

$$
\operatorname{tr}(T_tf)=\int_Gg_tf\,dm,\qquad
|\operatorname{tr}u|^2\le\frac{\mathscr E[u]+\|u\|_{L^2(m)}^2}{D},\qquad
D=\langle h,h-(F+1)^{-1}h\rangle=d_1>0.
\tag{14.3}
$$

The scalar $D$ has the name constructed in §12. In symmetric coordinates $\xi=(x,y,z)$ and $s=w-xy/2$, set

$$
\varrho=(|\xi|^4+s^2)^{1/4},\quad
q=(1+|\xi|^4+s^2)^{1/4},\quad
\psi=(q-1)/\beta,\quad \tau=\min(d/4,1),
\tag{14.4}
$$

where $\beta>0$ is rational and $\beta^2\ge a+\eta/4$. Such a $\beta$ is obtained from positive rational coefficient enclosures. The original bound from §10 is $0<\Gamma(p)\le32\varrho(p)^{-3}$. All times and coordinates retain the original units.

**Theorem 14.2 (computed global source-vector Gaussian tail).** For every $t,r>0$,

$$
\|1_{\{\psi\ge r\}}v_t\|_{L^2(\mu)}
\le\frac{2(1+t/r)}{\sqrt{\pi tD}}e^{-r^2/(4t)}.
\tag{14.5}
$$

Consequently, for $R>1$,

$$
\|1_{\{\varrho\ge R\}}v_t\|_2
\le\frac{2(1+\beta t/(R-1))}{\sqrt{\pi tD}}
\exp\left(-\frac{(R-1)^2}{4\beta^2t}\right).
\tag{14.6}
$$

The right side is computable from the permitted coefficient/time names and $D$. This is a norm-tail bound; it is not an exterior pointwise order certificate.

Proof. Let $d_A$ be the length distance for velocities $\sum_i u_iX_i+u_4\partial_w$, with length integrand $\sqrt{\sum_i u_i^2/a+u_4^2/\eta}$. It is a complete smooth left-invariant Riemannian distance. Its energy density is exactly (14.2), relative to $m$; multiplication by $h$ does not alter the principal symbol.

Compact Lipschitz tests belong to the local full form also at $e$. To see this, subtract the source value using a fixed local cutoff, and cut the remainder off on an Euclidean $\epsilon$-ball. There $|f-f(e)|\le C\epsilon$ and $|D\chi_\epsilon|\le C/\epsilon$, so the cutoff energy error is bounded by a constant times $m(B_{2\epsilon})\to0$. The gradient and norm errors also tend to zero. The subtracted cutoff is a full-form vector: locally it is the constant $1$, with its remaining part supported away from $e$. Punctured local smoothing and the full form core finish the approximation. Here $m=h^2\mu$ has no atom at $e$. The argument applies to Lipschitz distance cutoffs. Thus $d_A$ is the full form's intrinsic metric, with the original topology and source coordinate retained.

For bounded Lipschitz $\phi$ with $a\sum_i|X_i\phi|^2+\eta|\partial_w\phi|^2\le1$, the full-form product rule and weighted energy estimate give

$$
\|e^{\alpha\phi}T_te^{-\alpha\phi}\|_{2\to2}\le e^{\alpha^2t}.
\tag{14.7}
$$

Optimizing $\alpha$ between separated supports gives the Davies–Gaffney bound $\exp[-\operatorname{dist}_A(U,W)^2/(4t)]$. For this nonnegative self-adjoint $K$, the Davies–Gaffney/finite-wave equivalence [GT-CS, Theorem 3.4] therefore says that $\cos(u\sqrt K)$ propagates supports by at most $|u|$ in $d_A$. No global doubling or global $A_2$ property is assumed.

In symmetric coordinates the horizontal fields are $Y_1=\partial_x-(y/2)\partial_s$, $Y_2=\partial_y+(x/2)\partial_s$, $Y_3=\partial_z$. Writing $F_0=1+|\xi|^4+s^2$, direct differentiation gives

$$
\sum_i|Y_iq|^2=
\frac{16|\xi|^6+(x^2+y^2)s^2}{16F_0^{3/2}}\le1,
\qquad |\partial_sq|^2=\frac{s^2}{4F_0^{3/2}}\le\frac14.
\tag{14.8}
$$

Hence $\psi$ is $1$-Lipschitz in $d_A$ and $\psi(e)=0$. If $f\in\mathscr V$ is supported in $\{\psi>r\}$, finite propagation gives $\operatorname{tr}(\cos(u\sqrt K)f)=0$ for $0\le u<r$. Indeed the wave vector stays in the form domain and vanishes on a source neighborhood, so its actual quasi-continuous trace is zero.

Define the bounded spectral multiplier

$$
m_{r,t}(\lambda)=\frac1{\sqrt{\pi t}}\int_r^\infty e^{-u^2/(4t)}\cos(u\sqrt\lambda)\,du.
\tag{14.9}
$$

Heat transmutation [GT-CS, (3.8)] and the preceding trace vanishing give $\operatorname{tr}(T_tf)=\operatorname{tr}(m_{r,t}(K)f)$. For form inputs the transmutation integral converges in form norm, so this trace operation is legitimate. One integration by parts yields

$$
\begin{aligned}
|m_{r,t}(\lambda)|&\le\frac1{\sqrt{\pi t}}\int_r^\infty e^{-u^2/(4t)}du
 \le\frac{2t}{r\sqrt{\pi t}}e^{-r^2/(4t)},\\
\sqrt\lambda|m_{r,t}(\lambda)|&\le\frac2{\sqrt{\pi t}}e^{-r^2/(4t)}.
\end{aligned}
\tag{14.10}
$$

For the second bound, the boundary term and the integral of the absolute Gaussian derivative are each $e^{-r^2/(4t)}$; $\lambda=0$ is immediate. Since $\sqrt{1+\lambda}\le1+\sqrt\lambda$,

$$
\|(K+1)^{1/2}m_{r,t}(K)\|
\le\frac{2(1+t/r)}{\sqrt{\pi t}}e^{-r^2/(4t)}.
\tag{14.11}
$$

Applying the exact trace bound (14.3) gives the same right side divided by $\sqrt D$, times $\|f\|_{L^2(m)}$. Punctured smooth tests are dense in $L^2(\{\psi>r\},m)$. To include $\{\psi\ge r\}$, apply the bound first with $r'<r$ and then let $r'\uparrow r$. Duality proves the $L^2(m)$ tail of $g_t$, equal to the raw tail of $v_t$. Since $q\ge\varrho$, using $r=(R-1)/\beta$ gives (14.6). At no point is the source delta treated as an $L^2$ vector. $\square$

**Theorem 14.3 (exterior order decay of the actual quotient).** For every original $a,\eta,d>0$, there exist finite $C_d,R_d>0$ such that the smooth punctured representative satisfies

$$
0\le g_d(p)\le C_d\exp\left(-\frac{\varrho(p)^2}{32d\beta^2}\right)
\quad(\varrho(p)\ge R_d).
\tag{14.12}
$$

In particular $\lim_{R\to\infty}\operatorname{ess\,sup}_{\varrho\ge R}g_d=0$. Equivalently, for every $\epsilon>0$, $v_d\le\epsilon h$ outside a sufficiently large original coordinate box. The constants specified in the proof exist mathematically; no total coefficient-name algorithm for them or for these exterior radii is asserted.

Proof. Use left-translate charts $pQ$, with $Q=(-1/4,1/4)^4$, and the nested cube $Q'=(-1/8,1/8)^4$, in original coordinates. The principal symbol in a chart is

$$
a[\zeta_x^2+(\zeta_y+u_x\zeta_w)^2+\zeta_z^2]+\eta\zeta_w^2,
\qquad |u_x|\le1/4.
\tag{14.13}
$$

It has uniform ellipticity bounds $\lambda_0=\min(a,\eta)/3$ and $\Lambda_0=3\max(a,\eta)$. The gauge satisfies $\varrho(u)<1$ on $Q$ and $\varrho(pu)\ge\varrho(p)/2-\varrho(u)$. Thus, if $\varrho(p)\ge4$, the whole chart has $\varrho\ge1$, and

$$
0\le V(pu)\le V_0:=512\sqrt{a\eta}.
\tag{14.14}
$$

Bounded-potential local elliptic Harnack supplies a finite $H_0\ge2$ comparing any two values of a positive solution on $pQ'$, uniformly over these $p$. Its dependencies are dimension four, the fixed nested cubes, $\lambda_0,\Lambda_0,V_0$. This is the local Harnack intermediate used for the same $h$ in [S, §§115, 130]. In the Stummel formulation of [GT-CFG, Theorem 2.5], the dimension-four modulus of the bounded potential is at most $\pi^2V_0\sigma^2$ at radius $\sigma$, uniformly on these charts. No Harnack estimate across $e$ is used, and $H_0$ is not a supplied numerical name.

Set $m_4=\min_{\varrho=4}h>0$. A horizontal path from $e$ to $p$ consists of the $X_1,X_2,X_3$ segments, followed by a horizontal commutator rectangle of central area $w-xy$. Its length is bounded by

$$
|x|+|y|+|z|+4\sqrt{|w-xy|}<8\varrho(p),\qquad
|w-xy|\le|s|+|xy|/2\le5\varrho(p)^2/4.
\tag{14.15}
$$

For $\varrho(p)\ge8$, keep the path after its last exit from $\{\varrho<4\}$. Subdivide each of its at most seven horizontal segments into pieces of length at most $1/32$. At most $300(1+\varrho(p))$ links suffice. Each consecutive pair lies in a translated $Q'$, with chart center of gauge at least $4$. Harnack iteration gives

$$
h(p)\ge m_4H_0^{-300(1+\varrho(p))}=c_0e^{-c_1\varrho(p)},\quad
c_0=m_4H_0^{-300}>0,\quad c_1=300\log H_0.
\tag{14.16}
$$

For $t>0$, the actual source vector is $v_t=(H+1)e^{-tH}z$, with $z$ as in (12.4). Spectral smoothing and punctured local elliptic/parabolic regularity make it smooth on punctured compact space-time cylinders; it is nonnegative and satisfies $\partial_tv=\operatorname{div}(A\nabla v)+Vv$ there. Haar measure and the operator are preserved by the left charts. Ordinary uniformly elliptic parabolic Moser iteration supplies a finite uniform constant $A_d$ such that

$$
v_d(p)\le A_d\left(\int_{d-2\tau}^d\int_{pQ}|v_t|^2d\mu\,dt\right)^{1/2},
\qquad \varrho(p)\ge8.
\tag{14.17}
$$

Its dependencies are only $\lambda_0,\Lambda_0,Q,Q',\tau,V_0$. One may take $e^{2V_0\tau}$ times the zero-potential subsolution constant: apply that estimate to $e^{-V_0(t-d+2\tau)}v_t$. Only exterior unweighted local regularity is needed here.

For $u\in Q$, the straight coordinate path from $e$ to $u$ has $d_A$-length at most

$$
L=\sqrt{\frac3{16a}+\frac{25}{256\eta}},\qquad
|\psi(pu)-\psi(p)|\le L.
\tag{14.18}
$$

Put $r_p=\psi(p)-L$. If $r_p>0$, then (14.5), $d-2\tau\ge d/2$ and $t\le d$ imply

$$
\begin{aligned}
\|1_{pQ}v_t\|_2
&\le\frac{2\sqrt2(1+d/r_p)}{\sqrt{\pi dD}}e^{-r_p^2/(4d)},\\
v_d(p)&\le4A_d\sqrt{\frac\tau{\pi dD}}(1+d/r_p)e^{-r_p^2/(4d)}.
\end{aligned}
\tag{14.19}
$$

The second inequality integrates over an interval of length $2\tau$. Write $b=1+\beta L$ and $r(\rho')=(\rho'-b)/\beta$, using $\rho'$ only as a scalar gauge variable, distinct from the endpoint selector $\rho$. Since $q\ge\varrho$, $r_p\ge r(\varrho(p))$. Dividing by the lower bound for this same actual $h$ in (14.16) gives, when $\varrho(p)\ge8$ and $r(\varrho(p))>0$,

$$
g_d(p)\le\frac{4A_d}{c_0}\sqrt{\frac\tau{\pi dD}}
\left(1+\frac d{r(\varrho(p))}\right)
\exp\left(c_1\varrho(p)-\frac{r(\varrho(p))^2}{4d}\right).
\tag{14.20}
$$

Take

$$
\begin{gathered}
R_d=\max(8,2b,b+\beta,32d\beta^2c_1),\\
C_d=\frac{4A_d}{c_0}(1+d)\sqrt{\frac\tau{\pi dD}}.
\end{gathered}
\tag{14.21}
$$

For $\rho'\ge R_d$, $r(\rho')\ge\rho'/(2\beta)$, $r(\rho')\ge1$, and $c_1\rho'-r(\rho')^2/(4d)\le-(\rho')^2/(32d\beta^2)$. This proves (14.12) and the exterior essential-supremum limit. Finally $\varrho(p)\le r$ implies $|x|,|y|,|z|\le r$ and $|w|\le|s|+|xy|/2\le5r^2/4$. The gauge ball lies in the original coordinate box of radius $\max(r,5r^2/4)$, proving the asserted exterior box statement. $\square$

**Corollary 14.4 (qualitative compact localization and its numerical boundary).** Some finite compact gauge ball contains the full essential supremum $N_d$. Also one finite exterior radius suffices for $v_d\le(B_d+2^{-k})h$ simultaneously for all $k\ge0$, where $B_d=\|v_{d/2}\|_2^2$. These are existence assertions, without an algorithm producing that radius.

Proof. The original source law has mass one, so $N_d\ge1$. Choose an exterior bound in (14.12) below $1/2$. The essential supremum is then carried by the remaining compact ball. Cauchy–Schwarz and $m(G)=1$ give $B_d=\|g_{d/2}\|_{L^2(m)}^2\ge(\int g_{d/2}dm)^2=1$, so the same exterior bound is below every $B_d+2^{-k}$. This does not locate a maximum at the source trace. $\square$

The scalars $\beta,D$, (14.6), and the elementary geometry are available from the allowed names. The constants $H_0,A_d$ and the positive normalized anchor $m_4$ have been identified mathematically, but a fully specified total rational extraction of them from those names is not supplied. Nor is sharp certified compact upper approximation of $g_d$ including the nonpolar source supplied. Punctured smoothness and compact localization do not provide that source-inclusive modulus. These are sufficient obligations of this regional route, not necessary conditions for every possible solution of (12.31).

The global cofinal-upper-certificate producer in (12.31) remains unresolved: neither its construction nor its negation follows. The consumer remains exactly $M=1+N_d$, $P=T_d$, $f_3=g_d/(4M)$, $f_B=1/4$, $f_0=f_1=(3/4-f_3)/2$, with the original $e$-start, first read at $2d$, gaps $d$, all labels and finite word laws. A loose upper bound cannot replace this $M$.

**Definition 14.5 (mathematical sources and scope).** The source-specific deductions (14.5) and (14.12) are `repo-derived` conditional on the stated analytic suppliers. Finite propagation, transmutation, spectral calculus, elliptic Harnack and parabolic Moser estimates are `literature-attested` intermediates, not new generic results. No worldwide novelty or Lean/kernel verification is asserted.

| Mathematical source | Correspondence and scope |
| --- | --- |
| This volume, §§10–12, especially (10.12), (12.2), (12.4)–(12.10), Proposition 12.7 and Definition 12.8 | Original unit Green bound, normalized full endpoint, scalar $D$, deterministic source vector and unchanged calibration consumer. The tail-to-order deduction retains these inputs. |
| [S, §§115–117, 130–133](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III_APPENDIX_II.md) | Positivity and punctured smoothness of $h$, full strongly local form, nonpolar trace and actual deterministic-time law. The extension weight of §131 is not substituted for the actual global $m$; Theorem 133.2 remains the source-neighborhood boundedness supplier. |
| [GT-CS] T. Coulhon and A. Sikora, [Gaussian heat kernel upper bounds via Phragmén–Lindelöf theorem](https://arxiv.org/html/math/0609429v1), §3.2, Theorem 3.4 and (3.8) | Nonnegative self-adjoint Davies–Gaffney/finite-wave equivalence and heat transmutation, applied to $K$ after (14.7). Gaussian kernel results needing extra on-diagonal or doubling assumptions are not used. |
| [GT-CFG] F. Chiarenza, E. Fabes and N. Garofalo, [Harnack's inequality for Schrödinger operators and the continuity of solutions](https://doi.org/10.1090/S0002-9939-1986-0857933-4), Proc. Amer. Math. Soc. 98, 415–425, Theorem 2.5; correspondence in [S, §130] | Only local signed-potential Harnack on the exterior charts, with ellipticity (14.13) and bounded Stummel modulus. No effective numerical constant is imported. The primary PDF body is unavailable; this theorem correspondence is used through the stated §130 supplier. |

The parabolic step (14.17) uses ordinary local Moser iteration for the displayed uniformly elliptic divergence-form equation with bounded potential; its analytic hypotheses and constant dependencies are given explicitly above. It supplies existence of $A_d$, not a coefficient-name numerical service. The conclusions are ordinary conditional mathematical deductions within those boundaries.

## 追加锚（本行以下为增补区）
