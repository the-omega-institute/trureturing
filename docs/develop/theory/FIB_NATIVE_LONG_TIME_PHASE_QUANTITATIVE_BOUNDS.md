# Quantitative native long-time phase paths and terminal heights

## 41. Fixed native process, inherited premises and exact laws

**Definition 41.1 (unchanged DEV realization).** Throughout this volume,
DEV means [Native long-time phase diffusion on the complete winding
cover](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md). Fix exactly its
Definition 35.1 data: $0<Z<1$, $H=(1-Z)/2$, $I=(l,u)\Subset(0,H)$,
$\varepsilon>0$, and its compact two-sided parameter interval
$\mathcal K=[-\kappa_*,\kappa_*]$. The native coefficient family
$c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ is precisely the family fixed
there, with its original probabilities and controls. It is not chosen
or fitted in this volume. On the all-real comparison cover
$I\times\mathbb R^3$, with $q=(\theta,v,x)$, the original killed law is

$$
dK_t=\sqrt2\varepsilon\,dW_t^1,\qquad
dq_t=\sqrt2c_\kappa(K_t)\,dW_t^2,\qquad
\zeta=\inf\{t:K_t\notin I\},
\tag{41.1}
$$

where $W^1,W^2$ are independent standard real Brownian motions. Both
height endpoints kill the process. Time is the original time, the
control covariance is $\operatorname{diag}(\varepsilon^2,1)$, and raw
cover measure is $dk\,dq$. Write $L=u-l$ and set

$$
\phi(k)=\sqrt{2/L}\sin\frac{\pi(k-l)}L,\quad
\lambda=\frac{\varepsilon^2\pi^2}{L^2},\quad
\pi(dk)=\phi(k)^2dk,\quad J=\int_I\phi(k)dk,\quad
\gamma=3\lambda.
\tag{41.2}
$$

Here $\pi$ is a probability measure. The ground-state law
$\mathbb Q_{k,q}^\kappa$ has height generator
$\varepsilon^2\partial_k^2+2\varepsilon^2(\phi'/\phi)\partial_k$,
the same phase equation as (41.1), and no height death at finite time.
Denote its height semigroup by $Q_t$. The other probability law used
below is exactly
$\mathbb P_{k,q}^{\kappa,\tau}=\mathbb P_{k,q}^\kappa(\cdot\mid\zeta>\tau)$
on the entire interval $[0,\tau]$.

We use the following supplied DEV facts, retaining their conditional
dependence on DEV's inherited G/C/N/F premises. The height semigroup
is conservative and preserves $\pi$; its relative kernel satisfies

$$
Q_t f(k)=\int_I R_t(k,y)f(y)\pi(dy),\qquad
\sup_{k,y\in I}|R_t(k,y)-1|\le C_R e^{-\gamma t}\quad(t\ge1).
\tag{41.3}
$$

The coefficient and tensor bounds, uniform in $\kappa\in\mathcal K$,
are

$$
|c_\kappa(k)|\le C_c,\qquad
M_\kappa=\int_I c_\kappa c_\kappa^{\mathsf T}\,d\pi,\qquad
0<m\,\mathrm{Id}\le M_\kappa\le M\,\mathrm{Id}.
\tag{41.4}
$$

The coefficients are smooth on the fixed larger height interval and
continuous in the parameter; consequently $M_\kappa$ is continuous.
The exact Doob identity, with $S_k(t)=\mathbb P_k(\zeta>t)$, is

$$
\left.\frac{d\mathbb P_{k,q}^{\kappa,\tau}}
{d\mathbb Q_{k,q}^\kappa}\right|_{\mathcal F_r}
=\frac{e^{-\lambda r}\phi(k)S_{K_r}(\tau-r)}
{\phi(K_r)S_k(\tau)},\qquad 0\le r\le\tau.
\tag{41.5}
$$

Conditional on the complete height history, under either law the
phase driver remains independent standard Brownian motion. Thus for
$b>0$ fixed, $\tau=Tb$, and $X_T(s)=(q_{Ts}-q_0)/\sqrt T$, $0\le s\le b$,
the conditional phase law is a continuous centered Gaussian law with
independent increments and covariance

$$
\mathbb E[X_T(s)X_T(t)^{\mathsf T}\mid K]
=\frac2T\int_0^{T\min(s,t)}c_\kappa(K_r)c_\kappa(K_r)^{\mathsf T}dr.
\tag{41.6}
$$

The full history conditioned on here is $K|_{[0,\tau]}$. Facts
(41.3)--(41.6) are DEV (37.9), (36.1), (37.5), and (38.5),
respectively. They are credited inputs, as are DEV's coordinate and
zero-leaf identifications in §39 and survival asymptotic (37.4).
The quantitative concentration, coupling and cancellation arguments
below supply the additional estimates. This is ordinary mathematical
proof exposition, not a Lean-kernel certification of these premises
or conclusions. Nested sources and the primary literature cited by
DEV are not independently verified here.

**Lemma 41.2 (terminal weighting, bounded prefixes and height error).**
Both exact laws on $[0,\tau]$ can be written

$$
\mathbb E_{g,\tau}A=
\frac{\mathbb E_k^Q[A g(K_\tau)]}{d_\tau},\qquad
d_\tau=Q_\tau g(k),\quad G=\pi(g),\quad
g=1\ \hbox{or}\ g=\phi^{-1}.
\tag{41.7}
$$

For $g=1$ this is Q and $G=1$; for $g=\phi^{-1}$ it is terminal
survival to exactly $\tau$ and $G=J$. For all sufficiently large
$\tau$, uniformly over every initial $k\in I$,

$$
|d_\tau/G-1|\le C_R e^{-\gamma\tau},\quad d_\tau\ge G/2,
\qquad
\left.\frac{d\mathbb P_{g,\tau}}{d\mathbb Q}\right|_{\mathcal F_r}
=\frac{Q_{\tau-r}g(K_r)}{d_\tau}\le2(1+C_R)\quad(r\le\tau-1).
\tag{41.8}
$$

If $\eta_{\tau,g}$ is the terminal-height law and
$\nu_g=g\pi/G$, then

$$
\eta_{\tau,g}(dy)=\frac{R_\tau(k,y)g(y)\pi(dy)}{d_\tau},\qquad
\|\eta_{\tau,g}-\nu_g\|_{\rm var}\le C e^{-\gamma\tau}.
\tag{41.9}
$$

In particular the two normalized targets are $\nu_1=\phi^2dy$ and
$\nu_{\phi^{-1}}=\phi(y)dy/J$.

Proof. The terminal case of (41.5) gives (41.7). The unbounded
function $\phi^{-1}$ is $\pi$-integrable since its integral is $J$.
Integrating (41.3) against $g$ proves the first assertions of (41.8).
Conditional expectation of $g(K_\tau)$ at $r$ gives the prefix
density, also in the full phase/height filtration by the height
Markov property and independence of the phase driver. Apply (41.3)
at $\tau-r\ge1$ to bound it. At $r=\tau$ this density need not be
bounded. Finally the relative density of $\eta_{\tau,g}$ with respect
to $\nu_g$ is $G R_\tau(k,y)/d_\tau$. Its difference from one is
uniformly $O(e^{-\gamma\tau})$, proving (41.9) by integration.
$\square$

## 42. Joint metrics and the two quantitative conclusions

**Definition 42.1 (targets and distances).** Let
$\mathcal W_{\kappa,b}$ be the Brownian probability law on
$C_0([0,b],\mathbb R^3)$ of covariance
$2\min(s,t)M_\kappa$. Its endpoint density is

$$
\Gamma_{\kappa,b}(z)=
\frac{\exp[-z^{\mathsf T}M_\kappa^{-1}z/(4b)]}
{(4\pi b)^{3/2}\sqrt{\det M_\kappa}}.
\tag{42.1}
$$

The joint path distance is
$d((x,y),(x',y'))=\|x-x'\|_\infty+|y-y'|$; its endpoint counterpart
is $|z-z'|+|y-y'|$. In both cases $W_1$ is the infimum of expected
distance over probability couplings. The bounded-Lipschitz distance
is the supremum of expectation differences for functions bounded in
absolute value by one with Lipschitz constant at most one. For a
signed measure $\rho$ on $\mathbb R^3\times I$, put

$$
\|\rho\|_{{\rm var},1}
=\int_{\mathbb R^3\times I}(1+|z|)\,d|\rho|(z,y).
\tag{42.2}
$$

Unweighted variation is denoted by $\|\cdot\|_{\rm var}$; ordinary
total variation distance of probabilities is half this norm.

**Theorem 42.2 (full-horizon joint path and joint endpoint bounds).**
Fix $b>0$ and all data in Definition 41.1. There exist $C_b,T_0$
such that for $T\ge T_0$, $\kappa\in\mathcal K$, arbitrary initial
phase $q_0$, and every initial height $k\in I$, under each of the
two exact laws (41.7), with $\tau=Tb$,

$$
W_1\bigl(\mathcal L_{g,\tau}(X_T,K_\tau),
\mathcal W_{\kappa,b}\otimes\nu_g\bigr)
\le C_b\left[\frac{\log(e+T)^2}{\sqrt T}+e^{-\gamma Tb}\right],
\tag{42.3}
$$

and

$$
\left\|\mathcal L_{g,\tau}(X_T(b),K_\tau)
-\Gamma_{\kappa,b}(z)dz\otimes\nu_g\right\|_{{\rm var},1}
\le C_b\left[T^{-1}+e^{-\gamma Tb}\right].
\tag{42.4}
$$

Joint endpoint $W_1$ and bounded-Lipschitz errors are therefore at
most $C_b[T^{-1}+e^{-\gamma Tb}]$. For fixed $b$ the right sides
of (42.3) and (42.4) are respectively bounded by
$C'_b\log(e+T)^2/\sqrt T$ and $C'_b/T$.

The constants depend only on fixed $b$, fixed interval and noise,
and the common bounds in (41.3)--(41.4). Thus they include the
stipulated initial-height scope $k\in K\Subset I$, and are uniform
in initial phase and both parameter signs. Every target uses the
same current $\kappa$ as its process. No uniformity as $b$, the
height interval or noise intensity degenerates is claimed.

Proof. The estimates of §§43--45 prove (42.3); §46 proves (42.4)
and the endpoint transport assertion. Those proofs construct
couplings of actual continuous paths and bounds on joint signed
measures, respectively, so they also justify the supremum over all
joint Lipschitz tests. $\square$

## 43. Bounded correctors and exact-law interval concentration

**Lemma 43.1 (uniform occupation concentration).** For any entry

$$
f_\kappa=c_{\kappa,i}c_{\kappa,j}-(M_\kappa)_{ij},
\qquad \pi(f_\kappa)=0,
\tag{43.1}
$$

there is one constant $C$ such that, under either law (41.7), for
every deterministic interval $[a,a+L_1]\subset[0,\tau]$,

$$
\mathbb P_{g,\tau}\left(
\left|\int_a^{a+L_1}f_\kappa(K_r)dr\right|
>C\sqrt{L_1 x}\right)\le Ce^{-x}\quad(L_1\ge1,\ x\ge1),
\tag{43.2}
$$

and $\mathbb E_{g,\tau}|\int_a^{a+L_1}f_\kappa|^2\le C L_1$
when $L_1\ge1$. When $L_1<1$ the integral is deterministically
bounded by $F L_1$, with $F$ a common supremum bound on (43.1).
These assertions hold for $\tau$ sufficiently large as in (41.8),
uniformly in all the initial states and parameters above.

Proof. First work under Q. Contraction for $t<1$ and (41.3) for
$t\ge1$ give $\|Q_t f_\kappa\|_\infty\le C e^{-\gamma t}$ for all
$t\ge0$, increasing $C$ on the first unit of time. Hence

$$
u_f=\int_0^\infty Q_t f_\kappa\,dt,\qquad
\|u_f\|_\infty\le U,\qquad
Q_su_f-u_f=-\int_0^s Q_t f_\kappa\,dt.
\tag{43.3}
$$

Absolute integrability justifies moving the semigroup through the
integral. The process
$N_t=u_f(K_t)-u_f(K_0)+\int_0^t f_\kappa(K_r)dr$ is a martingale:
the conditional mean of its increment over $[t,t+s]$ is the last
identity in (43.3) plus its opposite. This needs no differentiability
of $u_f$. Any increment over a time span at most one has absolute
value at most $B=2U+F$.

Here is the bounded-increment estimate used in the proof. If $D$ is
conditionally centered and lies in $[-B,B]$, the convex chord of
$e^{\theta x}$ on that interval gives
$\mathbb E(e^{\theta D}\mid\mathcal F)\le\cosh(\theta B)
\le e^{\theta^2B^2/2}$. The second inequality follows by integrating
$\tanh v\le v$ for $v\ge0$ and using symmetry. Iteration over $n$
martingale increments and Markov's inequality give

$$
\mathbb P\left(\left|\sum_{j=1}^nD_j\right|>v\right)
\le2\exp\left[-\frac{v^2}{2nB^2}\right],
\tag{43.4}
$$

using $\theta=v/(nB^2)$ on each one-sided tail. The same argument
works conditionally on the filtration at the start of the interval.
Subdivide $[a,a+L_1]$ into $n=\lceil L_1\rceil$ parts of length at
most one. Its occupation integral differs from the martingale sum by
at most $2U$. For $L_1\ge1$ and $x\ge1$, (43.4) and
$n\le2L_1$ give (43.2) under Q after increasing $C$.

Under (41.7), split the occupation interval at $\tau-1$. Its part
before this time is measurable at a prefix with density bounded by
(41.8). Its remaining part has length at most one and absolute
integral at most $F$. The early part uses at most $L_1+1\le2L_1$
martingale increments when $L_1\ge1$, even if that early part itself
has length below one. Applying (43.4), multiplying its probability
bound by the prefix-density constant, and absorbing $2U+F$ proves
(43.2) for both laws. An empty early part is covered by the
deterministic final-unit bound. No full-horizon density bound is used.

Finally, if $Y$ denotes the integral, integrate
$\mathbb E|Y|^2=\int_0^\infty2v\mathbb P(|Y|>v)dv$.
The part $v\le C\sqrt{L_1}$ contributes at most $C^2L_1$; in the
rest substitute $v=C\sqrt{L_1x}$ in (43.2), obtaining at most
$C'L_1\int_1^\infty e^{-x}dx$. This proves the second moment.
For $L_1<1$ boundedness of $f_\kappa$ proves the last assertion.
$\square$

**Corollary 43.2 (matrix occupation estimates).** For a macroscopic
interval $I_0\subset[0,b]$ of length $h$ let

$$
S_{I_0}=\frac2T\int_{TI_0}c_\kappa(K_r)c_\kappa(K_r)^{\mathsf T}dr,
\qquad B_{I_0}=2hM_\kappa.
\tag{43.5}
$$

If $Th\ge1$, then under both exact laws

$$
\mathbb P_{g,\tau}\left(\|S_{I_0}-B_{I_0}\|_F
>C_*\sqrt{hx/T}\right)\le C_*e^{-x}\quad(x\ge1).
\tag{43.6}
$$

In particular, for $A=S_{[0,b]}$, $B=2bM_\kappa$,

$$
\mathbb E_{g,\tau}\|A-B\|_F^2\le C_b/T,
\qquad 0\le A\le2bC_c^2\,\mathrm{Id}.
\tag{43.7}
$$

Proof. Apply Lemma 43.1 to the nine entries, multiply by $2/T$,
and take a finite union bound. Sum their second moments for (43.7).
Its deterministic bound follows from
$v^{\mathsf T}cc^{\mathsf T}v\le C_c^2|v|^2$.
$\|\cdot\|_F$ is the Frobenius norm. $\square$

## 44. Gaussian maxima, interpolation and noncommuting square roots

**Lemma 44.1 (Gaussian maxima and continuous interpolation).** If
$Z_1,\ldots,Z_n$ are centered Gaussian vectors in $\mathbb R^d$,
each coordinate having variance at most $v$, then

$$
\mathbb E\max_{j\le n}|Z_j|\le C_d\sqrt{v\log(2n)}.
\tag{44.1}
$$

No independence among these vectors is required. For every height
history, let $P_N$ be polygonal interpolation of the actual
conditional path on $N$ equal intervals of length $h=b/N$. Then

$$
\mathbb E[\|X_T-P_NX_T\|_\infty\mid K]
\le C\sqrt{h\log(2N)},\qquad
\mathbb E[\|X_T\|_\infty\mid K]\le C_b.
\tag{44.2}
$$

The same statements hold for the target Brownian path, with common
constants uniform in $\kappa$.

Proof. Completing the square in a real Gaussian density gives
$\mathbb E e^{\theta Z_{j,i}}=e^{\theta^2\operatorname{Var}(Z_{j,i})/2}$,
also by continuity when variance is zero. Chernoff optimization and
a coordinate union bound show
$\mathbb P(|Z_j|>t)\le2d e^{-t^2/(2dv)}$. A union bound over $j$
therefore gives $2dn e^{-t^2/(2dv)}$. Integrate this bound above
$t_0=\sqrt{2dv\log(2dn)}$ and the bound one below it. With
$t=\sqrt{2dv}(\sqrt{\log(2dn)}+u)$, the remaining tail is at most
$e^{-u^2}$, whose integral is finite. This proves (44.1); $v=0$
is immediate.

By (41.6), every conditional coordinate increment variance is at
most $2C_c^2|s-t|$; the target has the same type of bound from
(41.4). Let $D_r$ be the maximum adjacent increment on the grid
with $N2^r$ intervals, $r\ge0$. Equation (44.1) gives

$$
\mathbb E[D_r\mid K]
\le C\sqrt{h2^{-r}\log(2N2^r)}.
\tag{44.3}
$$

For a time in a base interval, its successive left dyadic
approximations differ by at most one adjacent increment at each
finer level. Continuity gives a distance from the base left endpoint
at most $\sum_{r\ge1}D_r$. The base linear interpolation differs
from that endpoint by at most $D_0$. Thus
$\|X_T-P_NX_T\|_\infty\le\sum_{r\ge0}D_r$. The series of expected
bounds is at most $C\sqrt{h\log(2N)}$, since
$\sum_{r\ge0}2^{-r/2}\sqrt{1+r}<\infty$. It follows also that
the series is finite almost surely. At $N=1$, add the expected norm
of the endpoint to obtain the second assertion of (44.2).
This proof uses the exact continuous process, including on all
unfavorable height events. $\square$

**Lemma 44.2 (matrix square-root comparison).** For positive
semidefinite $A$ and positive definite $B$,

$$
\|A^{1/2}-B^{1/2}\|_F
\le\frac{\|A-B\|_F}{\sqrt{\lambda_{\min}(B)}}.
\tag{44.4}
$$

Proof. Set $S=A^{1/2}$, $R=B^{1/2}$, and $E=S-R$. The exact
identity $SE+ER=A-B$ needs no commutativity. Its Frobenius inner
product with $E$ is
$\operatorname{tr}(E^{\mathsf T}SE)+\operatorname{tr}(E^{\mathsf T}ER)$,
which is at least $\sqrt{\lambda_{\min}(B)}\|E\|_F^2$. Cauchy--Schwarz
then proves (44.4). For a standard Gaussian vector $Z$, the same
square-root coupling satisfies
$\mathbb E|(A^{1/2}-B^{1/2})Z|^2=\|A^{1/2}-B^{1/2}\|_F^2$.
Singular $A$ is allowed. $\square$

## 45. A coupling of the full continuous paths

**Lemma 45.1 (simultaneous covariance event).** Put
$x_T=6\log(e+T)$ and choose a fixed $L_0\ge1$ with
$C_*/\sqrt{L_0}\le m$. For $T$ sufficiently large define

$$
n=\left\lfloor\log_2\frac{bT}{L_0x_T}\right\rfloor,\quad
N=2^n,\quad h_*=b/N,\qquad
L_0x_T/T\le h_*<2L_0x_T/T.
\tag{45.1}
$$

Let $E_T$ require (43.6)'s covariance bound, with $x=x_T$, on
every dyadic interval from $[0,b]$ down to its $N$ leaves. Then

$$
\mathbb P_{g,\tau}(E_T^c)\le C_b(e+T)^{-5},\qquad
S_I\ge m|I|\,\mathrm{Id}\quad\hbox{on }E_T.
\tag{45.2}
$$

Proof. There are fewer than $2N\le C_bT$ intervals. Their physical
lengths are at least $L_0x_T\ge1$, so a union bound in (43.6)
gives the probability assertion. On this event their errors are at
most $C_*\sqrt{|I|x_T/T}\le m|I|$, whereas
$B_I\ge2m|I|\,\mathrm{Id}$. This gives the lower bound and also a
common upper bound proportional to $|I|$. $\square$

**Lemma 45.2 (dyadic grid coupling with exact marginals).** Conditional
on any height history in $E_T$, the actual and target paths have a
coupling on the leaf grid whose polygonal interpolants $U,V$ satisfy

$$
\mathbb E[\|U-V\|_\infty\mid K]
\le C_b\frac{\log(e+T)^2}{\sqrt T}.
\tag{45.3}
$$

Proof. All Gaussian variables in this proof are conditional on the
fixed height history. Use independent standard three-dimensional
vectors $Z_\circ$ at the root and $Z_I$ at each nonleaf node.
Root increments are $U_\circ=S_\circ^{1/2}Z_\circ$ and
$V_\circ=B_\circ^{1/2}Z_\circ$. At a node of length $h$ put
$A=S_{\rm left}$, $C=S_{\rm right}$, $S=A+C=S_I$, and
$B=2hM_\kappa$. Generate its child increments by

$$
\begin{aligned}
U_{\rm left}&=AS^{-1}U_I+R^{1/2}Z_I,&
U_{\rm right}&=U_I-U_{\rm left},& R&=A-AS^{-1}A,\\
V_{\rm left}&=V_I/2+(B/4)^{1/2}Z_I,&
V_{\rm right}&=V_I-V_{\rm left}.&&
\end{aligned}
\tag{45.4}
$$

The inverse exists by (45.2). Since $0\le A\le S$,
$S^{-1/2}AS^{-1/2}\le\mathrm{Id}$; consequently
$AS^{-1}A\le A$ and $R\ge0$. A direct covariance calculation gives
$\operatorname{Cov}(U_{\rm left},U_I)=A$,
$\operatorname{Cov}(U_{\rm left})=AS^{-1}A+R=A$,
$\operatorname{Cov}(U_{\rm right})=C$, and zero cross covariance
between the two children. A jointly Gaussian pair with zero cross
covariance is independent, since its characteristic function
$\exp(-\tfrac12\xi^{\mathsf T}\Sigma\xi)$ then factors.
Fresh independent innovations at separate nodes preserve independence
of their subtrees. Induction gives the exact conditional independent
leaf increments (41.6). The same calculation for $V$ gives
independent Brownian leaf increments of covariance $2h_*M_\kappa$.
This target grid law is constant in the height history.

To estimate the coupling, write $D_J=S_J-B_J$ and

$$
F=A-S/2=(D_{\rm left}-D_{\rm right})/2.
\tag{45.5}
$$

At this node the actual midpoint's deviation from the average of
its own endpoints is $FS^{-1}U_I+R^{1/2}Z_I$, whereas the target's
is $(B/4)^{1/2}Z_I$. Their difference is the centered Gaussian

$$
e_I=FS^{-1}U_I+[R^{1/2}-(B/4)^{1/2}]Z_I.
\tag{45.6}
$$

Expanding $A=S/2+F$ on both sides of $S^{-1}$ gives the exact
noncommutative identity

$$
R=S/4-FS^{-1}F.
\tag{45.7}
$$

On $E_T$, $\|F\|_F\le C\sqrt{hx_T/T}$ and $S\ge mh\,\mathrm{Id}$.
Thus $\operatorname{tr}(FS^{-1}F)\le Cx_T/T$ and

$$
\|R-B/4\|_F\le C\sqrt{hx_T/T}+Cx_T/T
\le C\sqrt{hx_T/T},
\tag{45.8}
$$

because $Th\ge L_0x_T$. Since $B/4\ge mh\,\mathrm{Id}/2$,
(44.4) bounds the squared Frobenius norm of the square-root
difference in (45.6) by $Cx_T/T$. The parent $U_I$ is independent
of its fresh $Z_I$ and has covariance $S$, so
$\mathbb E(|e_I|^2\mid K)\le Cx_T/T$. The root error has the same
bound by (44.4) applied at the root. No independence among the
different errors $e_I$ is needed.

At level $r$ there are $2^r$ midpoint errors. Each is centered
Gaussian with every coordinate variance at most $Cx_T/T$.
Equation (44.1) bounds their expected maximum by
$C\sqrt{x_T(r+1)/T}$. Inserting all midpoints at that level adds
disjoint triangular hats to the difference of the previous
interpolants, with respective heights $e_I$. The supremum can
therefore increase by at most their maximum. Starting with the root
endpoint error and summing gives

$$
\mathbb E[\|U-V\|_\infty\mid K]
\le C\sqrt{x_T/T}\left(1+\sum_{r=0}^{n-1}\sqrt{r+1}\right)
\le C\sqrt{x_T/T}(n+1)^{3/2}.
\tag{45.9}
$$

Since $n+1\le C_b\log(e+T)$, this is (45.3). This is one coupling
controlling the maximum over the whole grid. $\square$

**Proposition 45.3 (continuous extension and terminal independence).**
The grid coupling extends measurably to actual continuous paths and
proves (42.3).

Proof. On a favorable leaf interval, let $C(t)$ be its actual
partial covariance from the left endpoint and $S$ its total
covariance. Take an independent continuous Gaussian integral path
$G(t)$ with these independent-increment covariances. Its bridge

$$
G(t)-C(t)S^{-1}G(\mathrm{end})
\tag{45.10}
$$

has zero covariance with its endpoint and is therefore independent
of that endpoint. Its covariance at $s,t$ is
$C(\min(s,t))-C(s)S^{-1}C(t)$. Add $C(t)S^{-1}U_{\rm leaf}$
to (45.10), using independent bridges on distinct leaves. The
result has the exact conditional mean and covariance of the actual
path given its generated leaf increments. Unconditionally over
those increments it restores exactly (41.6). Use ordinary Brownian
bridges for the target, independently across its leaves. Both
extended paths are continuous and have their claimed marginals.

For completeness these constructions define probability kernels
measurable in height. The integrands $c_\kappa(K_r)$ are bounded
and continuous on each finite continuous height history; their
integrated covariance entries are measurable in that history.
The Gaussian continuous-path law with this covariance exists from
the stochastic integral in (41.6). Its finite-dimensional laws are
measurable functions of these covariance matrices: one may use the
continuous positive matrix square root applied to standard normal
vectors. Cylinder sets at rational times generate the Borel sets
of the separable continuous-path space; a monotone-class argument
then gives measurability of the path kernel. Products of independent
copies of such kernels, followed by the continuous operations in
(45.10), yield measurable bridge kernels. Matrices inverted here
are positive definite on the measurable event $E_T$. Thus mixing
this construction over height introduces no selection gap.

The interpolation estimates (44.2) apply to both extended marginal
paths. Their additional expected cost on $E_T$ is at most
$C\sqrt{h_*\log(2N)}\le C_b\log(e+T)/\sqrt T$. Combine with
(45.3). On $E_T^c$, use independent conditional actual and target
paths; (44.2) at $N=1$ bounds the conditional expected cost by
$C_b$ for every height history. This contributes at most
$C_b\mathbb P_{g,\tau}(E_T^c)$, without a loss from an uncontrolled
first moment or a singular covariance.

In both constructions the target conditional path law given the
entire height history is exactly $\mathcal W_{\kappa,b}$.
Therefore it is independent of that history, particularly $K_\tau$.
We have obtained a coupling from the actual joint law to
$\mathcal W_{\kappa,b}\otimes\eta_{\tau,g}$ with the required path
cost. Couple $\eta_{\tau,g}$ and $\nu_g$ by matching their common
part identically and coupling their residual measures. The heights
differ with probability $\tfrac12\|\eta_{\tau,g}-\nu_g\|_{\rm var}$,
and their distance is at most $L$. Apply this height transition to
the coupled terminal height independently of the target path. Its
new terminal height still has a product law with that path. The
extra cost is at most $C e^{-\gamma\tau}$ by (41.9).

All these laws have finite first moments by (44.2) and boundedness
of $I$. The resulting coupling proves (42.3). For any joint
1-Lipschitz function its expectation difference is bounded by this
same coupling cost; this bound holds simultaneously for the entire
test class. In particular terminal independence is obtained under
the exact full-horizon survivor law without exchanging a supremum
with a height-dependent test. $\square$

## 46. Signed cancellation and the sharper endpoint estimate

**Lemma 46.1 (signed covariance moment with terminal height).** Put
$A=S_{[0,b]}$, $B=2bM_\kappa$, $D=A-B$. For each entry define the
finite signed height measure

$$
m_{ij}(E)=\mathbb E_{g,\tau}[D_{ij}\mathbf1_{\{K_\tau\in E\}}].
\tag{46.1}
$$

Then $\|m_{ij}\|_{\rm var}\le C/T$, uniformly under both exact
laws and in every parameter and initial state in Theorem 42.2.

Proof. For any measurable height test $a$ with $|a|\le1$ and the
centered entry $f=f_\kappa$ in (43.1), Fubini and the Markov
property give

$$
\mathbb E_{g,\tau}\left[a(K_\tau)\int_0^\tau f(K_r)dr\right]
=\frac1{d_\tau}\int_0^\tau
\mathbb E_k^Q[f(K_r)Q_{\tau-r}(ag)(K_r)]dr.
\tag{46.2}
$$

The absolute integrand before conditioning is bounded by
$F g(K_\tau)$, with finite expectation, so Fubini is justified.
For $r\le\tau-1$, put $s=\tau-r\ge1$. Equation (41.3) applies
also to the integrable, possibly unbounded function $ag$, and yields

$$
Q_s(ag)=\pi(ag)+\epsilon_s,\qquad
\|\epsilon_s\|_\infty\le C_R G e^{-\gamma s}.
\tag{46.3}
$$

Use centering only on the constant term:
$\mathbb E_k^Q f(K_r)=Q_rf(k)$, bounded by $Ce^{-\gamma r}$ from
(43.3)'s preceding estimate. Bound the error term absolutely.
Since $|\pi(ag)|\le G$, the integrand in (46.2) has absolute value
at most $CG[e^{-\gamma r}+e^{-\gamma(\tau-r)}]$. Its integral over
$[0,\tau-1]$ is at most $CG$.

For $r\in[\tau-1,\tau]$, take $\tau\ge2$, so $r\ge1$ and the
law of $K_r$ has density at most $1+C_R$ relative to $\pi$.
Positivity of $Q_s$ and $\pi$-invariance, valid for nonnegative
integrable functions by monotone convergence, give

$$
\mathbb E_k^Q|f(K_r)Q_s(ag)(K_r)|
\le (1+C_R)F\int Q_s(|ag|)d\pi
\le (1+C_R)FG.
\tag{46.4}
$$

This includes $s=0$, where $g=\phi^{-1}$ is unbounded. The last
unit contributes at most $CG$. Divide by $d_\tau\ge G/2$ in
(46.2). Multiplication by $2/T$ bounds
$|\int a\,dm_{ij}|$ by $C/T$, uniformly over every measurable
$|a|\le1$. Variation of a signed measure is the supremum over
this class (choose its sign in a Hahn decomposition), proving the
claim. An estimate of $\mathbb E|D_{ij}|$ alone would lose this
signed cancellation. $\square$

**Lemma 46.2 (global weighted Gaussian Taylor bound).** Let $B$
range over positive matrices with eigenvalues in one fixed positive
compact interval. Let $A$ be any positive semidefinite matrix with
a fixed upper bound. Denote by $\mathcal N_A$ its centered Gaussian
probability measure, allowing singular $A$, and let $p_B$ be the
density of $\mathcal N_B$. With $D=A-B$ set

$$
\mathcal L_B[D](z)=\frac{p_B(z)}2
\left[z^{\mathsf T}B^{-1}DB^{-1}z-\operatorname{tr}(B^{-1}D)\right].
\tag{46.5}
$$

There is a uniform constant $C$ such that

$$
\begin{aligned}
\int(1+|z|)|\mathcal L_B[D](z)|dz&\le C\|D\|_F,\\
\int(1+|z|)d|\mathcal N_A-\mathcal N_B-\mathcal L_B[D](z)dz|
&\le C\|D\|_F^2.
\end{aligned}
\tag{46.6}
$$

Proof. The first bound follows directly from (46.5) after writing
$z=B^{1/2}Z$ with $Z$ standard normal. Suppose first
$\|D\|_{\rm op}\le\lambda_{\min}(B)/2$. All matrices
$C_t=B+tD$, $0\le t\le1$, then have uniformly positive lower and
finite upper eigenvalue bounds. Differentiating their explicit
Gaussian density gives

$$
\begin{aligned}
\partial_t p_{C_t}&=p_{C_t}\ell_{C_t}(D),\\
\ell_C(D)&=\tfrac12[z^{\mathsf T}C^{-1}DC^{-1}z-
\operatorname{tr}(C^{-1}D)],\\
\partial_t^2p_{C_t}&=p_{C_t}\left[
\ell_{C_t}(D)^2+\tfrac12\operatorname{tr}(C_t^{-1}DC_t^{-1}D)
-z^{\mathsf T}C_t^{-1}DC_t^{-1}DC_t^{-1}z\right].
\end{aligned}
\tag{46.7}
$$

Indeed $\partial_t C_t^{-1}=-C_t^{-1}DC_t^{-1}$ and
$\partial_t\log\det C_t=\operatorname{tr}(C_t^{-1}D)$; their
substitution proves each line. Under $p_{C_t}$ write
$z=C_t^{1/2}Z$. The weighted absolute first derivative is bounded
in integral by $C\|D\|_F$, and the second by $C\|D\|_F^2$:
the displayed polynomials have degrees at most two and four in $Z$,
and multiplication by $1+|z|$ requires moments only through degree
five. These moments are uniformly finite, since each real Gaussian
density is proportional to $e^{-v^2/2}$ and every polynomial times
that density is integrable; a coordinate bound controls $|Z|^j$.
Taylor's identity with integral remainder
$\int_0^1(1-t)\partial_t^2p_{C_t}dt$ now gives the second bound
in (46.6), with its weighted integration justified by these bounds.

On the complementary region, $\|D\|_F$ is bounded below by half
the common positive lower eigenvalue bound for $B$, and bounded
above by a fixed constant. The weighted variation of $\mathcal N_A$
is $1+\mathbb E|\mathcal N_A|\le1+\sqrt{\operatorname{tr}A}$,
also for singular $A$. The corresponding bound for $B$ and the
already proved bound for the linear term show that the left side
of (46.6) is at most a uniform constant. This is at most another
constant times $\|D\|_F^2$ on this region. Thus (46.6) is global;
it assumes no density for a singular actual conditional Gaussian.
$\square$

**Proposition 46.3 (joint mixture expansion and transport).** Under
both exact laws, (42.4) holds and implies the asserted joint
endpoint $W_1$ and bounded-Lipschitz estimates.

Proof. Conditional on height, the endpoint law is $\mathcal N_A$
with $A$ in (43.7). Mix the signed expansion (46.6) jointly with
$y=K_\tau$. Its constant term is
$\mathcal N_B\otimes\eta_{\tau,g}$. Its linear term is

$$
\sum_{i,j}\ell_{ij,B}(z)dz\otimes m_{ij}(dy),\qquad
\ell_{ij,B}(z)=\frac{p_B(z)}2
\left[(B^{-1}z)_i(B^{-1}z)_j-(B^{-1})_{ji}\right].
\tag{46.8}
$$

All finitely many coefficient functions have uniformly bounded
weighted $L^1$ norms by the Gaussian moment argument in Lemma
46.2. Lemma 46.1 therefore bounds the weighted variation of (46.8)
by $C_b/T$. The remainder has weighted variation at most
$C_b\mathbb E\|D\|_F^2\le C_b/T$ by (43.7).

To justify mixing in weighted variation, test a signed kernel
against any measurable $h(z,y)$ with $|h(z,y)|\le1+|z|$.
The absolute value of its integrated test is bounded by the integral
of the weighted variation of that kernel. Taking the supremum over
these tests gives the same inequality for the mixed signed measure;
the supremum equals weighted variation by its Hahn sign multiplied
by the weight. All integrals here are finite by (46.6). Thus the
estimate is joint in height and phase, including singular conditional
covariances, and uniform over all tests. We have proved

$$
\|\mathcal L_{g,\tau}(X_T(b),K_\tau)
-\mathcal N_B\otimes\eta_{\tau,g}\|_{{\rm var},1}\le C_b/T.
\tag{46.9}
$$

Replacing $\eta_{\tau,g}$ by $\nu_g$ adds at most
$(1+\mathbb E|\mathcal N_B|)\|\eta_{\tau,g}-\nu_g\|_{\rm var}
\le C_b e^{-\gamma\tau}$. Since $B=2bM_\kappa$,
$p_B=\Gamma_{\kappa,b}$, proving (42.4) with the factor two.

For the transport implication let $\mu,\nu$ be two joint endpoint
probabilities and match their common part identically. Their
residual measures $\sigma_+,\sigma_-$ have the same mass $r$.
If $r>0$, couple them using $r^{-1}\sigma_+\otimes\sigma_-$;
if $r=0$ no residual coupling is needed. Its expected cost is at
most

$$
\int|z|d\sigma_++\int|z|d\sigma_-+Lr
\le C_I\int(1+|z|)d|\mu-\nu|.
\tag{46.10}
$$

This gives an explicit $W_1$ coupling, rather than requiring bounded
tests to control an unbounded transport cost. Every bounded-Lipschitz
expectation difference is bounded by its coupling cost. Unweighted
total variation is controlled as well because the weight is at least
one. This completes the proof of Theorem 42.2. $\square$

## 47. Signed coordinates, parameter limits and other exact conventions

**Corollary 47.1 (signed original-coordinate bounds).** For
$\kappa\ne0$, set $J_\kappa=\operatorname{diag}(1,1,\kappa)$ and
$y=(\theta,v,D)=J_\kappa q$. Both bounds of Theorem 42.2 hold
after this phase pushforward, with their corresponding original
targets and a uniform constant multiplier. The target covariance is
$2\min(s,t)\widehat M_\kappa$, where

$$
\widehat M_\kappa=J_\kappa M_\kappa J_\kappa^{\mathsf T},\quad
(\widehat M_\kappa)_{13}=\kappa(M_\kappa)_{13},\quad
(\widehat M_\kappa)_{23}=\kappa(M_\kappa)_{23},\quad
(\widehat M_\kappa)_{33}=\kappa^2(M_\kappa)_{33}.
\tag{47.1}
$$

Its rank is three for every fixed nonzero parameter and
$\det\widehat M_\kappa=\kappa^2\det M_\kappa$. These are signed
formulas, not an assertion that either numerical cross covariance
has the sign of $\kappa$ regardless of its other factor.

Proof. DEV §39 identifies this exact map with the original winding
lift, in the same clock and with the same killing and changes of
law. Its operator norm is at most $C_J=\max(1,\kappa_*)$.
Pushing both members of each coupling forward multiplies its cost
by at most $C_J$ while retaining height. For weighted variation,
an invertible measurable pushforward preserves the variation
measure: push the positive and negative mutually singular parts
forward, which remain mutually singular. Furthermore
$1+|J_\kappa z|\le C_J(1+|z|)$. This proves the weighted bound
uniformly through both signs. Covariance transforms by congruence,
giving (47.1). The raw density transformation remains exactly

$$
\widehat\Gamma_{\kappa,b}(y)
=|\kappa|^{-1}\Gamma_{\kappa,b}(J_\kappa^{-1}y),\qquad
g_\kappa^{\rm orig}(t;k,k';J_\kappa r)
=|\kappa|^{-1}g_\kappa^I(t;k,k';r).
\tag{47.2}
$$

The absolute Jacobian in (47.2) does not remove signed cross terms
and does not yield a uniform point-density rate at zero. $\square$

**Corollary 47.2 (separate parameter moduli and collapse).** Replacing
the current resolved target by a fixed target at
$\bar\kappa\in\mathcal K$ adds at most
$C_b\|M_\kappa-M_{\bar\kappa}\|_F$ to path $W_1$, endpoint
$W_1$, and endpoint weighted variation. In original coordinates,
replacement by the zero-parameter collapsed target adds at most

$$
C_b\bigl(|\kappa|+\|M_\kappa-M_0\|_F\bigr)
\tag{47.3}
$$

to either transport estimate. Thus the temporal errors remain
respectively (42.3) and (42.4), with these additional parameter
errors; arbitrary $\kappa(T)\to\bar\kappa$ supplies no power of
$T$ for those errors. The collapsed covariance is
$2J_0M_0J_0^{\mathsf T}$ of rank two. No total variation convergence
to this singular three-coordinate law is asserted.

Proof. Take one standard three-dimensional Brownian motion $W$ and
couple the two targets as $\sqrt2M_\kappa^{1/2}W$ and
$\sqrt2M_{\bar\kappa}^{1/2}W$, with a common independent terminal
height of law $\nu_g$. Lemma 44.2 and
$\mathbb E\sup_{s\le b}|W_s|\le C_b$ from Lemma 44.1 bound the
path and endpoint coupling costs by the stated modulus. For
endpoint weighted variation, integrate the first density derivative
in (46.7) along the positive segment between $2bM_\kappa$ and
$2bM_{\bar\kappa}$; its common lower eigenvalue is $2bm$, giving
the same bound. Triangle inequalities with Theorem 42.2 prove the
resolved statements.

For collapse use the same Brownian path with coefficient matrices
$J_\kappa M_\kappa^{1/2}$ and $J_0M_0^{1/2}$. Their difference is
bounded by $C(|\kappa|+\|M_\kappa-M_0\|_F)$, by adding and
subtracting $J_\kappa M_0^{1/2}$ and applying Lemma 44.2.
This proves (47.3) in transport. Its limiting upper $2\times2$
block is positive definite, so the rank is exactly two. For every
nonzero $\kappa$ the Gaussian original target is full rank and
gives zero mass to the plane $D=0$, whereas the collapsed target
gives that plane mass one. Their total variation distance is one.
This explicit obstruction excludes a total variation analogue of
(47.3). $\square$

**Corollary 47.3 (actual native zero leaf).** On the actual leaf
$D=D_0$ at $\kappa=0$, the two moving native phases have the same
path bound (42.3) and joint endpoint weighted-variation bound
(42.4), with $z\in\mathbb R^2$, tensor
$N_0=(M_0)_{\{1,2\}\times\{1,2\}}$, and the same two distinct
height targets. Their target covariance is $2\min(s,t)N_0$.
The frozen original coordinate contributes a Dirac factor.

Proof. The projection of the resolved $\kappa=0$ process retaining
height and $(\theta,v)$ solves exactly the zero-leaf SDE in DEV
Theorem 39.2. Explicitly its coefficients are
$a_0=((H-k)/(2H),-k/(2H))$. The same height-only law changes
therefore give exactly its Q and terminal-survivor laws.
Projection contracts the phase norm and the path cost. For a signed
measure its projected variation is at most the projection of its
variation, as follows by testing against measurable functions of
absolute value at most one. The weight satisfies
$1+|\operatorname{pr}z|\le1+|z|$, so weighted variation contracts
as well. Project Theorem 42.2. The projected Gaussian has covariance
$2N_0$, and $N_0$ is positive definite as a principal block of
$M_0$. Adding the constant coordinate $D_0$ changes no distance or
rank. This proves a statement about the actual two-phase process,
not a third native phase or a raw four-dimensional density.
$\square$

**Proposition 47.4 (compensated finite mass and original cemetery).**
Let $\mu^{\rm kill}_{T,\kappa,k}$ be the unnormalized live
endpoint measure of $(X_T(b),K_\tau)$ for the original killed
process. Then

$$
\left\|e^{\lambda\tau}\mu^{\rm kill}_{T,\kappa,k}
-\phi(k)\phi(y)\Gamma_{\kappa,b}(z)\,dy\,dz
\right\|_{{\rm var},1}
\le C_b\phi(k)[T^{-1}+e^{-\gamma\tau}].
\tag{47.4}
$$

The comparison measure has total mass $\phi(k)J$, generally not
one. The original killed/cemetery endpoint law has ordinary total
variation distance exactly $S_k(\tau)$ from the cemetery point mass.

Proof. The exact live measure is $S_k(\tau)$ times the survivor
endpoint probability. DEV (37.4) gives, uniformly in $k\in I$,

$$
a_\tau=e^{\lambda\tau}S_k(\tau)
=\phi(k)J[1+O(e^{-8\lambda\tau})].
\tag{47.5}
$$

Multiply (42.4) for $g=\phi^{-1}$ by $a_\tau$. The remaining
scalar difference from $\phi(k)J$ multiplies the target probability,
whose weighted norm is uniformly bounded. Since $8\lambda>\gamma$,
this proves (47.4). The cemetery law is
$\mu^{\rm kill}_{T,\kappa,k}+(1-S_k(\tau))\delta_\dagger$.
Subtracting $\delta_\dagger$ gives disjoint positive live and
negative cemetery parts each of mass $S_k(\tau)$; half their
variation is exactly the asserted distance. $\square$

**Proposition 47.5 (separately stipulated stopped phases).** If
$q_t^{\rm stop}=q_{t\wedge\zeta}$ under the original law, then

$$
W_1\left(\mathcal L\bigl((q_{Ts}^{\rm stop}-q_0)/\sqrt T
\bigr)_{0\le s\le b},\delta_0\right)\le C/\sqrt T.
\tag{47.6}
$$

For each fixed parameter the normalized stopped path also tends
almost surely uniformly to zero. This assertion attaches no
terminal-height equilibrium target to the stopped path.

Proof. The supplied exit-time identity is
$\mathbb E_k\zeta=(k-l)(u-k)/(2\varepsilon^2)\le L^2/(8\varepsilon^2)$.
For completeness the martingale maximal bound used here follows as
follows. If $M_t$ is a continuous square-integrable vector martingale
on a finite interval and $U=\sup_t|M_t|$, conditional Jensen and
stopping at the first hit of a level $a$ give
$a\mathbb P(U\ge a)\le\mathbb E[|M_{\rm end}|\mathbf1_{\{U\ge a\}}]$.
First use truncated $U$ and bounded stopping times, then integrate
in $a$ and pass by monotone convergence. The identity for second
moments yields
$\mathbb E U^2\le2\mathbb E[|M_{\rm end}|U]
\le2(\mathbb E|M_{\rm end}|^2)^{1/2}(\mathbb E U^2)^{1/2}$,
so $\mathbb E U^2\le4\mathbb E|M_{\rm end}|^2$.

Apply this to the phase stochastic integral stopped at
$\zeta\wedge n$. Its terminal second moment, by the stochastic
integral isometry, is at most $2C_c^2\mathbb E\zeta$.
Let $n\to\infty$. The bounded expected quadratic variation gives
a continuous stopped extension at $\zeta$, and the supremum over
all times has second moment at most $8C_c^2\mathbb E\zeta$.
Coupling the normalized stopped path to the deterministic zero path
and applying Cauchy--Schwarz proves (47.6), uniformly in the fixed
parameter family and initial height. Since $\zeta<\infty$ almost
surely, each such stopped path has a finite unscaled supremum;
division by $\sqrt T$ proves the almost-sure assertion for each
fixed parameter. It does not identify sample paths across different
parameters. $\square$

## 48. Evidence, interpretation and remaining boundaries

**Proposition 48.1 (what the quantitative laws measure).** The
rank-three resolved Brownian covariance is compatible with a
rank-one instantaneous phase covariance and a rank-two full
instantaneous covariance. Bounded height contributes no extra
diffusive coordinate. These conclusions do not infer exact
controllability or a same-clock smooth elliptic observation of
dimension at least three.

Proof. From (41.1), or its Q version, the instantaneous covariance
is $2\operatorname{diag}(\varepsilon^2,c_\kappa c_\kappa^{\mathsf T})dt$.
The nonzero height direction and the nonzero phase vector give
full rank two, with phase rank one. Temporal occupation of different
height levels gives the positive averaged tensor (41.4), rather
than three independent native phase drivers. Deterministically,
$\sup_{s\le b}|K_{Ts}-K_0|/\sqrt T\le L/\sqrt T$ under both
surviving conventions. The zero leaf has only its two moving
phases. For a smooth observation into $d$ dimensions, the pushed
second-order symbol is a sum of two outer products of the pushed
native fields and has rank at most two. Lower-order drift does
not alter this bound. It cannot be positive definite when $d\ge3$.
These are local symbol and averaged covariance statements; neither
is a proof of exact controllability. $\square$

The new quantitative assertions are `repo-derived` in the ordinary
proof sense: Lemma 43.1 and Corollary 43.2, the coupling of §45,
the signed estimate and joint expansion of §46, and the quantitative
transfers of §47. DEV already supplies the height kernel/mixing,
exact Doob and conditional Gaussian identities, uniform coefficient
and tensor facts, qualitative joint path limit, and exact coordinate
and zero-leaf identifications. Bounded martingale exponential
estimates, Gaussian bridge couplings, matrix square roots, density
Taylor expansion and common-part transport are mature methods;
their required forms have been proved here. No global priority or
new general probability method is asserted.

DEV's cited ground-state, martingale-limit and abelian-cover
literature retains only the conditional scope stated in DEV.
In particular a classical elliptic abelian-cover theorem does not
directly cover this rank-two operator. No external literature search
or independent verification of G/C/N/F or those citations is claimed.
The mathematical deliverable is the displayed ordinary deductions
from the explicitly retained premises, not empirical evidence,
formal-kernel evidence or an endorsement of upstream ontology.

The two rates are upper bounds. The dyadic sum of Gaussian maximum
errors in (45.9) explains the present logarithmic loss; it does not
prove that loss necessary. Matching lower bounds, optimal logarithms,
a log-free path rate, and a faster endpoint rate remain outside the
proved conclusions. Weighted endpoint variation controls entire
measures, including their first moments; it supplies no pointwise
kernel or local-density rate. The path estimate is in uniform
continuous-path transport, not path total variation. A fixed limiting
parameter requires the separate modulus of Corollary 47.2.

All estimates concern a full winding record on the all-real cover.
A wrapped endpoint has multiple winding lifts. A continuous wrapped
path with a specified initial lift has a unique mathematical lift,
which is a different observation convention and supplies no device
for acquiring that path. DEV's wrapped compact laws, including the
actual wrapped zero leaf, retain their separate scope; no new
quantitative wrapped mixing rate is claimed. The bounded interval,
original clock, noise intensity, allowed parameter rectangle and
exact conditioning horizons remain fixed. Constants above do not
provide free winding observation, survival conditioning, preparation,
simulation or service resources.

Effective phase rank, topological dimension, local homogeneous heat
dimension and native current-ray dimension are distinct quantities.
Whitening a limiting tensor gives mathematical coordinates, not
physical rotation invariance. No physical spatial dimension,
selection principle, elliptic physical factor, efficiency, Green-tail,
Coulomb or binding conclusion follows here. No empirical machine
learning claim is implied. The original cemetery law, compensated
finite measure, stipulated stopped phases, Q law and exact terminal
survivor law have the separate conclusions proved above.

## 追加锚（本行以下为增补区）
