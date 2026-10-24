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

## 49. Native confinement of an entire winding history

**Definition 49.1 (unchanged source, normal and precision).** Write
[D](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md) for the original diffusion
supplier and
[G](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md) for its source supplier.
Retain D Definition 35.1 and this volume's Definition 41.1,
including their original five probabilities, immutable initial phases,
initial height, two independent drivers, covariance, height guard,
killing at both endpoints of $I$, and original clock. Fix a nonempty
compact two-sided collar

$$
\mathcal K_\times=\{\kappa:\kappa_-\le|\kappa|\le\kappa_+\}
\subset\mathcal K,\qquad 0<\kappa_-\le\kappa_+,
\qquad E\Subset I.
\tag{49.1}
$$

Here $E$ is a fixed nonempty compact subset of $I$.
Each history starts from one fixed $k_0\in E$ and one fixed phase;
uniformity in these choices does not randomize INITIAL. On the original
winding lift put

$$
y=(\theta,v,D),\quad J_\kappa=\operatorname{diag}(1,1,\kappa),\quad
\widehat c_\kappa=J_\kappa c_\kappa,\quad
\widehat M_\kappa=J_\kappa M_\kappa J_\kappa^{\mathsf T}.
\tag{49.2}
$$

Thus $dy_t=\sqrt2\widehat c_\kappa(K_t)dW_t^2$ until the original
height exit $\zeta$. D Theorem 39.1 supplies precisely this signed
coordinate map, not a different source. Select a Euclidean unit normal
$e\in\mathbb R^3$ before the history and define

$$
\begin{aligned}
h&=J_\kappa^{\mathsf T}e,& a(k)&=h\cdot c_\kappa(k),&
\widehat m_{\kappa,e}&=e^{\mathsf T}\widehat M_\kappa e,\\
A(T,R,e)&=\left\{\sup_{0\le t\le T}
             |e\cdot(y_t-y_0)|<R\right\},&
\delta&=R/\sqrt T,& \omega&=\pi/(2R),\\
C_T&=\mathbb P(\,\cdot\mid\zeta>T),&
p(T,R,e)&=C_T(A(T,R,e)).
\end{aligned}
\tag{49.3}
$$

Here $T,R>0$, $A$ is a live-history event, and $\mathbb P$ is exactly
the original killed law. For definiteness $A$ is false on histories
killed by $T$; this convention does not change its meaning under $C_T$.
Let $\mathbb P_T$ be the probability law on full histories through $T$,
including height death and its cemetery record. Initial phases cancel
from (49.3). No wrapping, initial-height averaging, stationary height
preparation or replacement of either driver is made.

**Theorem 49.2 (uniform exact-band confinement probability).** Under
Definition 49.1, as $R\to\infty$ and $T/R^2\to\infty$,

$$
p(T,R,e)=\left(\frac4\pi+o(1)\right)
 \exp\left\{-T\left[
 \Lambda_\kappa\!\left(\frac{\pi J_\kappa^{\mathsf T}e}{2R}\right)
 -\lambda\right]\right\},
\tag{49.4}
$$

uniformly over $\kappa\in\mathcal K_\times$, unit $e$, $k_0\in E$
and initial phases. Here $\Lambda_\kappa$ is D's full-real Dirichlet
height band, with $\Lambda_\kappa(0)=\lambda$.
More precisely, let $v_{\kappa,\eta}$ be the positive, $L^2(dk)$-normalized
height ground eigenfunction used in D (36.7)--(36.8), and put

$$
G_{\kappa,\eta}(k_0)=
\frac{v_{\kappa,\eta}(k_0)\int_I v_{\kappa,\eta}(k)dk}
     {\phi(k_0)J},\qquad J=\int_I\phi(k)dk.
\tag{49.5}
$$

There are $R_0,T_0,c,C>0$ depending only on the fixed data such that,
for $R\ge R_0$, $T\ge T_0$,

$$
\begin{aligned}
p(T,R,e)&=\frac4\pi G_{\kappa,\omega h}(k_0)
 e^{-T[\Lambda_\kappa(\omega h)-\lambda]}(1+\rho),\\
|\rho|&\le C\left[e^{-2\lambda T}+e^{-cT/R^2}\right],\qquad
|G_{\kappa,\omega h}(k_0)-1|\le C R^{-2}.
\end{aligned}
\tag{49.6}
$$

Proof. First condition on the entire surviving height history. By
independence of $W^1,W^2$ and (41.6), the real process
$X_t=e\cdot(y_t-y_0)$ has the same conditional continuous-path law as
$B_{U_t}$, where $B$ is Brownian motion with generator $\partial_x^2$
(starting at zero) and

$$
U_t=\int_0^t a(K_s)^2ds.
\tag{49.7}
$$

This is equality of conditional laws; it adds no driver to the actual
source. For each fixed height path, both are centered continuous
Gaussian processes with covariance $2U_{\min(s,t)}$. The continuous
nondecreasing map $t\mapsto U_t$ has range $[0,U_T]$, even if it has
flat intervals. Consequently the all-prefix event, not just the endpoint,
has conditional probability
$H_R(U_T)$, where $H_R(u)=\mathbb P(\sup_{s\le u}|B_s|<R)$.

The classical Dirichlet interval calculation gives

$$
H_R(u)=\frac4\pi\sum_{j=0}^\infty
 \frac{(-1)^j}{2j+1}e^{-(2j+1)^2\omega^2u},\qquad u>0.
\tag{49.8}
$$

Here is its normalization and the tail control needed here. The
$L^2(-R,R)$-normalized eigenfunctions of $-\partial_x^2$ are
$R^{-1/2}\sin(n\pi(x+R)/(2R))$, with eigenvalues $n^2\omega^2$.
Apply their heat semigroup to the constant function one and evaluate
at $x=0$. The integral coefficient is zero for even $n$ and
$4\sqrt R/(n\pi)$ for odd $n$; the evaluation coefficient for
$n=2j+1$ is $(-1)^j/\sqrt R$. This proves (49.8), with absolute
convergence at every positive $u$. This heat solution equals killed
Brownian survival: Itô's formula stopped at the two faces identifies
the bounded Dirichlet heat solution with the killed expectation;
apply it first away from initial time and pass to the bounded initial
value one at interior points. At $u=0$, survival is one and the same
series has its alternating-series value. Since its term magnitudes
decrease, its first two partial sums bound its value for every $u\ge0$:

$$
\frac4\pi\left[e^{-\omega^2u}-\frac13e^{-9\omega^2u}\right]
\le H_R(u)\le\frac4\pi e^{-\omega^2u}.
\tag{49.9}
$$

Thus no interchange with an uncontrolled high-mode tail is required.
Write

$$
F_T(\eta;k)=\mathbb E_k\left[
 \mathbf1_{\{\zeta>T\}}
 e^{-\int_0^T(\eta\cdot c_\kappa(K_s))^2ds}\right]
       =(e^{-TH_{\kappa,\eta}}1)(k),\quad
H_{\kappa,\eta}=-\varepsilon^2\partial_k^2+
                         (\eta\cdot c_\kappa)^2.
\tag{49.10}
$$

The operator domain is the same two-Dirichlet domain as D (36.5).
The last equality is the bounded-potential killed Feynman--Kac identity:
apply Itô's formula to the backward heat solution multiplied by
$\exp[-\int_0^t(\eta\cdot c_\kappa(K_s))^2ds]$, stop at the height
faces, and pass to the bounded terminal value one. All potentials
here are bounded and nonnegative. In particular (49.10) is a Laplace
transform on the original height law, not an added attractive field.
Taking the expectation of (49.9) over that law yields the exact bounds

$$
\frac4\pi\left[F_T(\omega h;k_0)-\frac13F_T(3\omega h;k_0)\right]
\le S_{k_0}(T)p(T,R,e)
\le\frac4\pi F_T(\omega h;k_0).
\tag{49.11}
$$

Consume D (36.7)--(36.8), rather than proving another band theorem.
They supply, uniformly in a fixed small real-frequency ball,
$v_{\kappa,\eta}/\phi=1+O(|\eta|^2)$ and the integrated remainder

$$
F_T(\eta;k)=e^{-T\Lambda_\kappa(\eta)}
 v_{\kappa,\eta}(k)\int_Iv_{\kappa,\eta}
 +O(\phi(k)J e^{-4\lambda T}),\qquad T\ge1.
\tag{49.12}
$$

In that ball $\Lambda_\kappa(\eta)\le2\lambda$, so the error relative
to the displayed leading term is $O(e^{-2\lambda T})$.
D (37.4) supplies
$S_k(T)=e^{-\lambda T}\phi(k)J[1+O(e^{-8\lambda T})]$.
Division therefore gives

$$
\frac{F_T(\omega h;k_0)}{S_{k_0}(T)}
=G_{\kappa,\omega h}(k_0)e^{-T[\Lambda_\kappa(\omega h)-\lambda]}
 [1+O(e^{-2\lambda T})],\qquad G_{\kappa,\omega h}=1+O(R^{-2}).
\tag{49.13}
$$

All constants are uniform: $h=J_\kappa^{\mathsf T}e$ stays in a compact
annulus and

$$
0<m_-:=m\min(1,\kappa_-^2)
\le\widehat m_{\kappa,e}=h^{\mathsf T}M_\kappa h
\le M\max(1,\kappa_+^2)=:m_+<\infty.
\tag{49.14}
$$

The quadratic band estimate D (36.4) then gives, for large enough $R$,

$$
\Lambda_\kappa(3\omega h)-\Lambda_\kappa(\omega h)
 =8\widehat m_{\kappa,e}\omega^2+O(\omega^4)
 \ge4m_-\omega^2.
\tag{49.15}
$$

Apply (49.12) at both frequencies, making $R_0$ large enough that
both lie in its ball. Their positive prefactors are uniformly comparable
to $\phi(k_0)J$, and their relative errors are uniformly bounded for
$T\ge T_0$. Hence

$$
0\le\frac{F_T(3\omega h;k_0)}{F_T(\omega h;k_0)}
\le C e^{-4m_-\omega^2T}\le C e^{-cT/R^2}.
\tag{49.16}
$$

Equations (49.11), (49.13) and (49.16) prove (49.6). Its three error
terms vanish in the two asserted limits, proving (49.4). The estimate
concerns the entire native winding history; no invariance-principle
error has been used to estimate a rare event.

The supplied autonomous original normal $e=(2,-2,1)/3$ retains its
exact normalization: D Theorem 50.1 gives $a=1/3$, so
$U_T=T/9$, $\widehat m_{\kappa,e}=1/9$, $G=1$ and
$\Lambda_\kappa(\omega h)-\lambda=\omega^2/9$.
For this direction (49.11) is directly the first-two-term bound of
$H_R(T/9)$, consistent with both the coefficient $4/\pi$ and the
original covariance factor two. $\square$

## 50. Precision cost and the existing native quartic coefficient

**Theorem 50.1 (uniform logarithmic law and relative-asymptotic scales).**
In the joint regime of Theorem 49.2,

$$
-\log p(T,R,e)\sim
 \frac{\pi^2}{4}\widehat m_{\kappa,e}\frac{T}{R^2}
 =\frac{\pi^2}{4}\frac{e^{\mathsf T}\widehat M_\kappa e}{\delta^2},
\tag{50.1}
$$

where the ratio tends to one uniformly in Definition 49.1's choices.
For $h=J_\kappa^{\mathsf T}e$, the coefficient already supplied by
D Definition 51.1 and Theorem 51.3 gives

$$
\begin{aligned}
T[\Lambda_\kappa(\omega h)-\lambda]
 &=\frac{\pi^2}{4}\widehat m_{\kappa,e}\frac{T}{R^2}
 -\frac{\pi^4}{16}\mathcal B_\kappa(h)\frac{T}{R^4}
 +O(T/R^6),\\
-\log p(T,R,e)
 &=T[\Lambda_\kappa(\omega h)-\lambda]-\log(4/\pi)+o(1).
\end{aligned}
\tag{50.2}
$$

No condition $T/R^4\to0$ is needed for (50.1). That condition is
sufficient to replace the exact band by its quadratic term in the
relative probability asymptotic (49.4); without it that replacement
is not valid in general.

Proof. D (51.6) applies to the unit vector $h/|h|$ and scalar
$r=\omega|h|$. Its quadratic and quartic homogeneities give exactly
the first line of (50.2); boundedness on the fixed annulus makes its
remainder uniform. This consumes the native quartic coefficient and
its sign and does not introduce a new one. The logarithm of (49.6),
with $G=1+O(R^{-2})$, gives the second line. Divide both lines by
$\widehat m_{\kappa,e}T/R^2$, bounded below by $m_-T/R^2$.
The relative quartic and remainder errors are $O(R^{-2})$ and
$O(R^{-4})$; the bounded prefactor contributes $O(R^2/T)$.
All vanish under just the two stated limits, proving (50.1).

For the relative probability, its quadratic replacement changes the
exponent by $O(T/R^4)$, explaining the sufficient extra condition.
For a fixed pair $(\kappa,e)$ with $\mathcal B_\kappa(h)>0$ and
$R=T^{1/4}$, (49.4) and (50.2) give instead

$$
\frac{p(T,T^{1/4},e)}
 {(4/\pi)\exp[-(\pi^2/4)\widehat m_{\kappa,e}\sqrt T]}
\longrightarrow \exp[(\pi^4/16)\mathcal B_\kappa(h)]>1.
\tag{50.3}
$$

Such native directions exist: $e=(0,0,1)$ makes
$a=\kappa b_\kappa$ nonconstant by G (25.4), and D Theorem 51.2
makes its quartic coefficient strictly positive. The collar is within
the fixed small source neighbourhood. On autonomous directions
D Theorem 50.1 gives constant $a^2$ and an exactly quadratic band;
the additional scale condition is unnecessary there. $\square$

## 51. Sharp information frontier on the same killed history space

**Theorem 51.1 (attained survival-relative confinement optimum).** Use
Definition 49.1 and natural logarithms. Fix $0\le\alpha<1$ and set
$r=1-\alpha$. Whenever $0<p=p(T,R,e)<r$, among all probability
laws $V$ on the original history space satisfying

$$
V\ll\mathbb P_T,\qquad V(\zeta>T)=1,\qquad V(A(T,R,e))\ge r,
\tag{51.1}
$$

the exact minimum is

$$
\begin{aligned}
\inf_V D(V\Vert\mathbb P_T)
 &=-\log S_{k_0}(T)+d_{\rm bin}(r\Vert p),\\
d_{\rm bin}(r\Vert p)
 &=r\log(r/p)+(1-r)\log((1-r)/(1-p)).
\end{aligned}
\tag{51.2}
$$

The minimum is attained by

$$
V_* =r\,C_T(\,\cdot\mid A)+(1-r)\,C_T(\,\cdot\mid A^c).
\tag{51.3}
$$

At $\alpha=0$ the second summand is omitted and $0\log0=0$.
Survival alone has minimum $-\log S_{k_0}(T)$, attained by $C_T$.
For every fixed $\alpha<1$, in Theorem 49.2's regime the minimum
excess over survival is uniformly

$$
\inf_V\{D(V\Vert\mathbb P_T)+\log S_{k_0}(T)\}
\sim (1-\alpha)\frac{\pi^2}{4}
                    \frac{e^{\mathsf T}\widehat M_\kappa e}{\delta^2}.
\tag{51.4}
$$

Proof. Positivity of $H_R(u)$ for every finite $u$ and boundedness of
$a$ show $p>0$. By (49.4), $p\to0$ uniformly in the joint regime,
so $p<r$ there eventually. Under survival, the original probability
is $S_{k_0}(T)C_T$. Therefore every admissible $V$ obeys the exact
entropy decomposition, including the value $+\infty$,

$$
D(V\Vert\mathbb P_T)=-\log S_{k_0}(T)+D(V\Vert C_T).
\tag{51.5}
$$

This follows directly by factoring its Radon--Nikodym density on the
surviving set. The mature nonnegativity and partition chain rule for
relative entropy yield, with $q=V(A)$,

$$
\begin{aligned}
D(V\Vert C_T)
 ={}&d_{\rm bin}(q\Vert p)
 +qD(V(\,\cdot\mid A)\Vert C_T(\,\cdot\mid A))\\
 &+(1-q)D(V(\,\cdot\mid A^c)\Vert C_T(\,\cdot\mid A^c)).
\end{aligned}
\tag{51.6}
$$

For clarity, on $A$ the density factors as $(q/p)$ times the
conditional density, and on $A^c$ as $((1-q)/(1-p))$ times its
conditional density; integrate its logarithm on the two sets. Terms
of zero $V$-mass are omitted. Nonnegativity follows from
$z\log z\ge z-1$ integrated against the reference probability.
These are classical measure identities, not a new entropy theorem.
Their path-measure interpretation is also the abstract relative-entropy
and Gibbs variational principle of Chetrite--Touchette,
[*Variational and optimal control representations of conditioned and
driven processes*, arXiv:1506.05291v3](https://arxiv.org/html/1506.05291v3),
§III.4, equations (52) and (56). Only that measure-level principle is
used; no diffusion-matrix inverse or control-cost representation is
applied to this rank-two source.

For $p<q<1$,
$\partial_q d_{\rm bin}(q\Vert p)=\log[q(1-p)/(p(1-q))]>0$.
Continuity at $q=1$ shows its minimum on $[r,1]$ is attained at $r$.
Equation (51.3) has $q=r$ and both positive-mass conditional
entropies zero, proving attainment and (51.2). Omitting the event
constraint in (51.5) proves the survival-only minimum. Finally,

$$
d_{\rm bin}(r\Vert p)
 =r(-\log p)+r\log r+(1-r)\log(1-r)
                  -(1-r)\log(1-p).
\tag{51.7}
$$

For fixed $r>0$ the last three terms are bounded as $p\to0$.
Apply (50.1), whose leading term tends uniformly to infinity, to
obtain (51.4). The attaining law is an analytic conditioning of
existing histories, not a newly acquired native operation. $\square$

## 52. What entropy rate fails to select

**Corollary 52.1 (bounded excess and an attained subextensive collapse).**
In the joint regime of Theorem 49.2, for probability laws
$V\ll\mathbb P_T$ with $V(\zeta>T)=1$, a uniformly bounded excess
$D(V\Vert\mathbb P_T)+\log S_{k_0}(T)$ cannot give fixed positive
confidence of all-prefix $\delta$-closeness to any predeclared plane
$\Pi_e=\{z:e\cdot z=0\}$ through the initial displacement.
In fact, if that excess is at most $B<\infty$, then

$$
V(A(T,R,e))\le\frac{B+\log2}{\log(1/p(T,R,e))}\longrightarrow0
\tag{52.1}
$$

uniformly over the same collar, normals and initial heights.
Conversely choose $R=T^{1/4}$ and set $V_T=C_T(\,\cdot\mid A)$.
Then for every $T$ this is a probability law absolutely continuous
with respect to the unchanged original $\mathbb P_T$, and

$$
\begin{aligned}
V_T\left(\zeta>T,\
 \sup_{0\le s\le1}\operatorname{dist}
   ((y_{Ts}-y_0)/\sqrt T,\Pi_e)<T^{-1/4}\right)&=1,\\
D(V_T\Vert\mathbb P_T)+\log S_{k_0}(T)
 &=\frac{\pi^2}{4}\widehat m_{\kappa,e}\sqrt T
   -\frac{\pi^4}{16}\mathcal B_\kappa(h)-\log(4/\pi)+o(1),\\
\frac1T D(V_T\Vert\mathbb P_T)&\longrightarrow\lambda.
\end{aligned}
\tag{52.2}
$$

Thus the minimum limiting survival entropy rate, among the
finite-horizon laws quantified in (51.1), does not enforce retention
of three macroscopic transport directions. The conclusion concerns
whole histories, not endpoint flattening.

Proof. Equation (51.6) gives
$D(V\Vert C_T)\ge d_{\rm bin}(q\Vert p)
\ge q\log(1/p)-\log2$: the binary negative entropy is at least
$-\log2$, and $-(1-q)\log(1-p)\ge0$. Use (51.5) and the uniformly
divergent logarithm (50.1) to prove (52.1).
For the converse, Euclidean distance to $\Pi_e$ equals $|e\cdot z|$.
The first line of (52.2) is consequently the very event used in
(51.3) with $\alpha=0$, not a weaker terminal event. The exact
minimum excess is $-\log p$. In (50.2), $T/R^2=\sqrt T$,
$T/R^4=1$ and $T/R^6=T^{-1/2}$, proving the second line.
D (37.4) gives $-\log S_{k_0}(T)=\lambda T-\log(\phi(k_0)J)+o(1)$,
uniformly on $E$. Division by $T$ proves the last line.
Every survival-supported law has entropy at least $-\log S_{k_0}(T)$
by (51.5), so $\lambda$ is the minimum possible limiting rate and
this planar-confined family attains it. This does not assert a
nondegenerate limit within the plane. The laws $V_T$ are a family on
varying horizons; no projective consistency, single time-homogeneous
Markov generator or lawful feedback implementation is asserted.
Those would be additional restrictions beyond this entropy-rate
selection criterion. $\square$

## 53. Source correspondence and the dimensional-selection boundary

**Definition 53.1 (observation, operations and resource meaning).** The
objects of §§49--52 are the actual source and two-driver killed paths
of D Definition 35.1, with its fixed preparation rotations, original
controls, common Brownian history, both height exits, refusal and Stop.
The rational source coefficients are G (25.4); D (39.1) maps their
resolved winding coordinate to the original signed $D$. The source
parameter and $k_0$ are fixed before a path is generated. Uniformity
in the collar compares those fixed experiments without coupling or
restarting them. No reset, source smearing, extra hidden actuator,
attractive potential, Fourier-sector selector or changed covariance
is part of these definitions.

The observation convention is a complete continuous winding history
with a specified initial lift and known fixed calibration. A complete
wrapped history has that unique mathematical lift; a wrapped endpoint
or finitely many paid polls do not supply the same event. The metric
is the declared Euclidean metric in the original coordinates
$(\theta,v,D)$, with supremum over prefixes in the original clock.
The plane normal is fixed before observing. A fitted plane, nonlinear
encoder, unknown calibration, prepared-source observer metric,
environmental metric and physical spatial distance are different
tasks. The absolute phase radius is $R$, and the macroscopic precision
is $\delta=R/\sqrt T$; the quantitative frontier assumes both
$R\to\infty$ and $\delta\to0$.

The cost is relative entropy in nats on that same path space. It is
not a count of bits, Reads, samples, actuations, CPU operations or
acquired services. $C_T$ and (51.3) specify distributions on existing
histories. An operational interpretation would additionally require
a permitted observation and selection or feedback service, its latency,
its handling of survival failures, and a proved relation between its
resource charge and the displayed divergence. Such a service is not
among the original commands. All path selections retain the immutable
initial state and the original path support.

**Proposition 53.2 (the original consumer and the retained boundaries).**
For a proposed selection of native transport by cheapest survival,
Theorems 49.2, 50.1 and 51.1 provide its exact-band whole-history
probability and the sharp confidence-versus-information condition
(51.4), with the explicit native source and metric constant.
Corollary 52.1 excludes entropy rate alone as a sufficient selection
criterion among the specified absolutely continuous horizon laws.
These conclusions do not identify physical axes or derive this native
dynamics from bare FIB.

Proof. On the nonzero collar D Theorem 36.1 and its original-coordinate
map give the positive tensor (49.14). The selection cost in (51.4)
therefore diverges for a shrinking macroscopic slab in every fixed
normal, and (51.3) shows that the confidence bound is attainable on
exactly the same histories. The family (52.2) simultaneously keeps
the minimum asymptotic rate and confines every prefix to a vanishing
macroscopic slab. This is the concrete obstruction for the survival
rate criterion; it does not contradict the original law's rank-three
long-time limit or assert an available command implementing $V_T$.

Current-ray dimension four, direct-control rank two, instantaneous
phase rank one, effective phase rank three and local homogeneous heat
dimension seven have different definitions in the suppliers. None is
a physical-space identification. At the actual $\kappa=0$ leaf,
$D$ is frozen and there are two moving phases. If the collar is
removed, original-coordinate covariance degenerates: for $e=(0,0,1)$,
$\widehat m_{\kappa,e}=\kappa^2(M_\kappa)_{33}\to0$.
Thus the uniform positive constant in (49.14) and its uniform
three-direction entropy frontier cannot be retained. Dividing $D$
by $\kappa$ changes the declared measurement scale. The fixed collar
is a substantive source/metric condition, not an inferred dimension.
$\square$

**Definition 53.3 (reused mathematics and the additional bridge).** The
reused native suppliers are D (36.1), (36.4), (36.7)--(36.8), (37.4),
(39.1) and (51.6), and this volume's conditional-history identity
(41.6). In particular, the covariance tensor, quartic coefficient,
Doob transform and whole-horizon Gaussian limit are existing results.
The path transport bounds in Theorem 42.2 supply no relative estimate
for the exponentially small event here; no such inference is made.
The generic interval sine calculation, killed Feynman--Kac identity,
relative-entropy nonnegativity and partition chain rule are classical
intermediate tools, with the measure-level path principle credited in
Theorem 51.1 to the primary Chetrite--Touchette text. Its drift-control
expressions do not provide an inverse for this degenerate native
symbol, and no absorbing-chain or noncompact Q-process theorem is
substituted for this source's fixed-height spectral estimates.

The additional source-specific deductions are the all-prefix comparison
(49.11), its uniform joint-limit error (49.16), the source-height
prefactor (49.5)--(49.6), and their sharp information frontier and
attained planar-collapse consequence. These are ordinary proofs from
the explicitly retained native premises, not a new general small-
deviation or entropy principle, a literature-priority claim, an
empirical realization or a formal-kernel certificate. The separate
Green, finite hidden-sector, free-quotient and prepared-source
acquisition contracts retain their own operators and operation sets;
none supplies the missing observation or selection service here.

## 追加锚（本行以下为增补区）

## 54. Persistent height feedback on the same original source

**Definition 54.1 (source, analytic permissions and controller class).**
Retain D Definition 35.1, G Definition 25.1 and Definition 49.1,
including the five original probabilities, rational coefficients,
immutable INITIAL $=(k_0,y_0)$ with $k_0\in E\Subset I$, the fixed
$\varepsilon,I$, original time and original signed winding coordinates
$y=(\theta,v,D)$. The parameter is fixed in the nonzero two-sided
collar $\mathcal K_\times$ of (49.1). In particular
$\widehat c_\kappa=J_\kappa c_\kappa$ is exactly (49.2).
The reference $\mathbb P$ is the original killed probability on full
native histories, including both absorbing faces and cemetery histories.
The full continuous winding history has its specified initial lift.
No change of INITIAL or random stationary preparation is made.

The added analytic controller permission is exact continuous height
observation and bias of the original two driver/control columns. A
controller is a pair selected before any horizon,

$$
\psi=\phi f,\qquad f\in C^\infty([l,u];\mathbb R),\qquad
\min_{[l,u]}f>0,\qquad \int_I\psi^2dk=1,\qquad
w\in C^\infty([l,u];\mathbb R).
\tag{54.1}
$$

Here smoothness on the closed interval means smooth extension to a
neighborhood; in particular the real phase current $w$ is bounded
up to both faces. The amplitude is positive in $I$, has simple zeroes
at both faces, and is normalized in real $L^2(dk)$, not in raw phase
volume. Replacing $f$ by $-f$ or by a complex phase is not allowed.
No common positive lower bound on $f$, or common bound on $w$ or
their derivatives, is imposed across the class. Uniform assertions
below range over this whole class, not over a compact set of policies.

The controller is time homogeneous, height only and covariant under
phase translations. Its prescribed dynamics are

$$
\begin{aligned}
dK_t&=\sqrt2\varepsilon\,dB_t^1
       +2\varepsilon^2\frac{\psi'}\psi(K_t)dt,\\
dy_t&=\sqrt2\widehat c_\kappa(K_t)dB_t^2
       +\widehat c_\kappa(K_t)w(K_t)dt,
\end{aligned}
\tag{54.2}
$$

where $(B^1,B^2)$ is standard two-dimensional Brownian motion.
Its two components are independent. Both changes of drift lie in
the original columns; there is no phase-position dependence, hidden
state, extra noise, reset, horizon dependence or change of clock.
These feedback permissions are model assumptions, not commands
already obtained by the native acquisition theories. The singular
height bias keeps a controlled history alive; the reference still
contains its original death and refusal/Stop semantics.

Write $\mathbb V_{\psi,w}$ for the law constructed below, and use
$\mathcal F_t$ for the full native path filtration. Define

$$
\rho=\psi^2,\quad
\mathcal E(\psi)=\varepsilon^2\int_I|\psi'|^2dk,\quad
R(\psi,w)=\lim_{T\to\infty}\frac1T
 D(\mathbb V_{\psi,w}|_{\mathcal F_T}\Vert
                      \mathbb P|_{\mathcal F_T}).
\tag{54.3}
$$

Existence of this limit, rather than its existence as an assumption,
is part of Theorem 55.1. The divergence uses natural logarithms.
The real vector $j$, the tensor $D_{\rm eff}$ and their centering are
defined in Theorem 56.1. A controller may depend on the fixed source,
budget and declared direction, but none of these is chosen from the
observed history. An asymptotic assertion for each controller always
keeps that controller fixed as $T\to\infty$.

## 55. Exact native prefix likelihood and its survival entropy rate

**Theorem 55.1 (one conservative law, exact likelihood and minimum).**
Each controller (54.1) has a conservative continuous infinite path
law satisfying (54.2), from the fixed INITIAL. On every finite
$\mathcal F_T$ it is equivalent to the original Q law and absolutely
continuous with respect to the full killed reference $\mathbb P_T$.
Under Q put

$$
u_1(k)=\sqrt2\varepsilon\frac{f'}f(k),\qquad
u_2(k)=\frac{w(k)}{\sqrt2},\qquad
Z_T=\exp\left\{\sum_{i=1}^2\int_0^T u_i(K_t)dW_t^{Q,i}
             -\frac12\int_0^T(u_1^2+u_2^2)(K_t)dt\right\}.
\tag{55.1}
$$

The Q drivers are those of D (37.8), in the signed coordinates (49.2).
The exact full-path density is zero on histories dead by $T$, and
on surviving histories is

$$
\frac{d\mathbb V_T}{d\mathbb P_T}
 =e^{\lambda T}\frac{\phi(K_T)}{\phi(k_0)}Z_T.
\tag{55.2}
$$

In particular these densities are consistent prefixes of one law.
Its finite entropy has both expressions

$$
\begin{aligned}
D(\mathbb V_T\Vert\mathbb P_T)
 &=\lambda T+\mathbb E_{\mathbb V}
       \log\frac{\phi(K_T)}{\phi(k_0)}
    +\mathbb E_{\mathbb V}\int_0^T
       \left[\varepsilon^2\left(\frac{f'}f\right)^2
                           +\frac14w^2\right](K_t)dt\\
 &=\mathbb E_{\mathbb V}\int_0^T
       \left[\varepsilon^2\left(\frac{\psi'}\psi\right)^2
                           +\frac14w^2\right](K_t)dt.
\end{aligned}
\tag{55.3}
$$

The long-time full-native-path rate exists and equals

$$
R(\psi,w)=\mathcal E(\psi)+\frac14\int_I w^2\psi^2dk
        =\lambda+\varepsilon^2\int_I\phi^2|f'|^2dk
                         +\frac14\int_Iw^2\psi^2dk\ge\lambda.
\tag{55.4}
$$

Equality holds exactly for $\psi=\phi,w=0$. Thus the unique
minimum-rate controller is the already supplied Q law, with the
rank-three original-coordinate phase limit of D §§38--39 on this
collar. No infinite-horizon absolute continuity with respect to
$\mathbb P$ is asserted.

Proof. The normalized height Q process and its prefix density
$\mathbf1_{\{\zeta>T\}}e^{\lambda T}\phi(K_T)/\phi(k_0)$ are D
(37.2), (37.8). Both $u_i$ in (55.1) are bounded for each controller.
Here are the precise bounded-exponential facts needed from classical
Girsanov theory. Stop its stochastic exponential at increasing levels.
If $|u|^2\le C$, Itô's formula and Gronwall give
$\mathbb E_Q Z_{T\wedge\tau_n}^p\le\exp[p(p-1)CT/2]$ for $p>1$.
Uniform integrability removes the stops and gives $\mathbb E_QZ_T=1$.
Under the tilted law, integration by parts with $Z$ makes
$W^{Q,i}-\int_0^\cdot u_i(K_t)dt$ continuous local martingales with
bracket matrix $t\,\mathrm{Id}_2$. The Brownian characterization
therefore makes them independent standard Brownian components.
This proves the required two-driver change of law without an inverse
of the degenerate four-state covariance. Substitution in D (37.8)
gives (54.2), since $\psi'/\psi=\phi'/\phi+f'/f$.

The exponential is positive, so these finite laws are equivalent to
Q, have no finite height death and extend consistently to continuous
paths on every compact time interval, hence to $[0,\infty)$.
Interior smoothness gives pathwise uniqueness up to a boundary hit;
nonexplosion of this law makes that uniqueness global for the fixed
initial point. Composition of the two prefix densities proves (55.2),
including its normalization on the cemetery probability space.
No driver information has been discarded from this calculation:
under Q, $W^{Q,1}$ is reconstructed from $K$ and its stated drift,
and $W^{Q,2}$ from $dv/(\sqrt2 B_\kappa(K))$. The original rational
coefficient $B_\kappa$ in G (25.4) is nowhere zero on the fixed
rectangle because the original probabilities are positive there.
Thus $Z_T$ is a functional of the native paths themselves. This is
a scalar recovery of a driver along an existing nonzero column,
not inversion of the state diffusion matrix or division by $\kappa$.
Consequently (55.2)--(55.3) concern exactly native-path entropy,
not a possibly larger entropy of an enlarged driver record.

The height generator and its invariant probability are

$$
\mathcal L_\psi h=\varepsilon^2\rho^{-1}(\rho h')',
\qquad \rho(k)dk=\phi(k)^2f(k)^2dk.
\tag{55.5}
$$

For clarity, the endpoint and fixed-start facts needed here can be
obtained directly in this one-dimensional problem. Its scale density
is $\rho^{-1}$, whose integral diverges at both faces because
$\rho$ is comparable to squared distance to the boundary. The finite
speed density is $\rho/\varepsilon^2$. Equivalently the reversible
energy form is $\varepsilon^2\int |h'|^2\rho$ in $L^2(\rho dk)$;
integration by parts on the interior gives (55.5). Smooth cutoffs of
one, differing from one only within distance $\delta$ of the faces,
have energy $O(\delta)$ and converge to one in $L^2(\rho)$.
The form realization thus contains the constant one with zero
energy, is conservative and preserves $\rho dk$. It has the same
interior diffusion generator as the already constructed nonexplosive
law; uniqueness up to exit identifies their semigroups. This proves
invariance for the height, without an invariant probability on the
full phase cover. Comparison with the supplied Q Poincare inequality
gives, if $m_f=\min f,M_f=\max f$,

$$
\operatorname{Var}_\rho h\le
 \frac{M_f^2}{3\lambda m_f^2}
          \varepsilon^2\int_I|h'|^2\rho dk.
\tag{55.6}
$$

Indeed minimize over the additive constant, compare $\rho=f^2\phi^2$
to $\phi^2$, use Q's gap $3\lambda$, then compare back. In particular
the invariant height probability is unique. None of these comparisons
asserts a mixing rate uniform over all controllers.

The endpoint logarithms and singular original bias cause no lost
integrability. At each fixed positive time, the supplied Q relative
height kernel is bounded. Cauchy--Schwarz, the finite second moment
of $Z_1$ and D (37.9) show that the height law under $\mathbb V$ at
time one has an $L^2(\rho)$ density. Subsequent $L^2(\rho)$ contraction
keeps its norm bounded. Since $\log\phi\in L^2(\rho)$, this proves

$$
\sup_{T\ge1}\mathbb E_{\mathbb V}|\log\phi(K_T)|<\infty.
\tag{55.7}
$$

For $0<T<1$ the same argument at that fixed time proves finiteness.
A useful stronger finite-interval check is as follows. Put
$d(k)=\min(k-l,u-k)$. For $k_0\in E$, the Dirichlet heat kernel and
its first spatial derivative, away from $k_0$, give
$h_I(t;k_0,k)\le C_A d(k)$ near either face, uniformly for
$0<t\le A$. One obtains this bound directly by differentiating the
reflected Gaussian series: the separation from $E$ makes the small
$t$ Gaussian derivatives bounded. The Q density there is therefore
at most $C_A d(k)^2$. On the remaining interior interval $d$ has a
positive lower bound. It follows that

$$
\sup_{0\le t\le A}\mathbb E_Q d(K_t)^{-r}<\infty\quad(0<r<3).
\tag{55.8}
$$

Choose $1<p<3/2$ and apply Holder to $Z_t d(K_t)^{-2}$, using its
conjugate exponential moment and (55.8) at $r=2p$. Thus
$\sup_{t\le A}\mathbb E_{\mathbb V}d(K_t)^{-2}<\infty$.
Both $\psi'/\psi=O(d^{-1})$ and $\psi''/\psi=O(d^{-1})$ are
integrable to the powers required below. Every finite original
height-bias square integral in (55.3) is finite.

The logarithm of $Z_T$, expressed in the new Brownian drivers,
has mean $\tfrac12\mathbb E_{\mathbb V}\int |u|^2$; the remaining
stochastic integral has mean zero. Together with (55.2) and the
endpoint integrability this proves the first line of (55.3).
Itô's formula for $\log f(K)$ also rewrites the height part of
(55.2) as

$$
\frac{\psi(K_T)}{\psi(k_0)}
 \exp\left[-\varepsilon^2\int_0^T\frac{\psi''}{\psi}(K_t)dt\right].
\tag{55.9}
$$

This formula is on survival only; its zero extension to dead paths
is understood. Applying Itô to $\log\psi(K)$ under (54.2), first
on interior stopped intervals, makes the logarithm of (55.9) equal
to a mean-zero square-integrable martingale plus
$\varepsilon^2\int_0^T(\psi'/\psi)^2(K_t)dt$. The estimates just
proved remove the stops. The phase exponential contributes
$\tfrac14\mathbb E_{\mathbb V}\int w^2$, proving the second line.
In particular the singular expression (55.9) is justified by the
bounded change relative to Q, not by an unverified exponential
moment for a boundary-singular potential.

To take the long-time limit without assuming stationarity at time
zero, let $a$ be any smooth bounded function and center it by its
$\rho$ mean. An explicit solution of
$-\mathcal L_\psi U=a-\int a\rho$, centered by $\int U\rho=0$, is
specified by

$$
U'(k)=-\frac{\int_l^k(a(z)-\int_Ia\rho)\rho(z)dz}
                   {\varepsilon^2\rho(k)}.
\tag{55.10}
$$

At either face the numerator vanishes to third order; at the upper
face use its zero total integral. Hence $U'=O(d)$ and $U,U'$ extend
smoothly and are bounded. Itô's formula yields

$$
\int_0^t(a(K_r)-\textstyle\int a\rho)dr
 =U(k_0)-U(K_t)+\sqrt2\varepsilon\int_0^t U'(K_r)dB_r^1.
\tag{55.11}
$$

Taking expectations gives convergence of expected time averages;
Doob's inequality also gives convergence uniformly in macroscopic
time after division by $T$. Apply this to the bounded integrand in
the first line of (55.3), and use (55.7). The rate becomes
$\lambda+\varepsilon^2\int\phi^2|f'|^2+\tfrac14\int w^2\rho$.
Finally integration by parts, using $\phi(l)=\phi(u)=0$ and
$-\varepsilon^2\phi''=\lambda\phi$, gives

$$
\varepsilon^2\int_I|(\phi f)'|^2
 =\lambda\int_I\phi^2f^2+\varepsilon^2\int_I\phi^2|f'|^2.
\tag{55.12}
$$

The boundary term $\phi\phi'f^2$ is zero at both faces. Normalization
proves (55.4). Equality forces $f$ constant and $w=0$ on $I$;
positivity and real normalization then force $f=1$. Conversely these
values give Q exactly. The original killed source dies eventually
almost surely by D (37.4), while $\mathbb V$ never dies. Their
infinite path laws are consequently singular, despite every finite
prefix being absolutely continuous in the stated direction.
$\square$

## 56. Ballistic centering and the controlled three-phase path limit

**Theorem 56.1 (fixed-start native homogenization with a current).**
For each fixed controller let

$$
v(k)=\widehat c_\kappa(k)w(k),\qquad
j=\int_Iv\rho dk,\qquad g=v-j.
\tag{56.1}
$$

Let $\chi:I\to\mathbb R^3$ be the unique centered Poisson solution

$$
-\mathcal L_\psi\chi=g,\qquad \int_I\chi\rho dk=0,\qquad
\chi'(k)=-\frac{\int_l^k g(z)\rho(z)dz}{\varepsilon^2\rho(k)}.
\tag{56.2}
$$

The solution has zero boundary flux $\rho\chi'=0$ at both faces;
$\chi,\chi'$ are bounded and smooth up to the faces, with
$\chi'(l)=\chi'(u)=0$. For any fixed $b>0$, from the immutable INITIAL,

$$
\left(\frac{y_{Ts}-y_0-jTs}{\sqrt T}\right)_{0\le s\le b}
 \ \Longrightarrow\ \mathcal W_{D_{\rm eff},b}
\quad\hbox{in }C([0,b],\mathbb R^3),
\tag{56.3}
$$

where the topology is uniform, the limit is Brownian motion with
covariance $2\min(s,t)D_{\rm eff}$, and

$$
D_{\rm eff}(\psi,w)=
 \int_I\widehat c_\kappa\widehat c_\kappa^{\mathsf T}\rho dk
 +\varepsilon^2\int_I\chi'\chi'^{\mathsf T}\rho dk.
\tag{56.4}
$$

Thus the centered phase current adds a positive semidefinite tensor;
it cannot cancel the phase-noise contribution. The convergence is
controllerwise. No common convergence time over (54.1), or over
budgets growing with $T$, is part of this assertion.

Proof. The endpoint calculation in (55.10) applies componentwise to
$g$, since its $\rho$ mean is exactly zero. It proves every stated
regularity and flux property in (56.2). If two solutions differ,
$(\rho(\chi_1-\chi_2)')'=0$; zero flux forces a constant difference,
and centering fixes that constant. In particular this Poisson object
is for the actual current $\widehat c_\kappa w-j$, not for an
unrelated scalar band or an uncentered height forcing.

Combining Itô's formula with (54.2) gives the exact decomposition

$$
\begin{aligned}
y_t-y_0-jt
 &=M_t+\chi(k_0)-\chi(K_t),\\
M_t&=\sqrt2\int_0^t\widehat c_\kappa(K_r)dB_r^2
       +\sqrt2\varepsilon\int_0^t\chi'(K_r)dB_r^1,\\
\langle M\rangle_t
 &=2\int_0^t\left[
    \widehat c_\kappa\widehat c_\kappa^{\mathsf T}
                 +\varepsilon^2\chi'\chi'^{\mathsf T}\right](K_r)dr.
\end{aligned}
\tag{56.5}
$$

The two drivers have zero mutual bracket even though the integrands
depend on the first driver's height. This is why there is no negative
cross term. Each entry of the bracket integrand is smooth and bounded.
Apply (55.10)--(55.11) to its centered entries. Doob's inequality
and boundedness of the correctors show, for this fixed controller,

$$
\sup_{0\le s\le b}
 \left\|T^{-1}\langle M\rangle_{Ts}-2sD_{\rm eff}\right\|
       \longrightarrow0\quad\hbox{in probability}.
\tag{56.6}
$$

Indeed each squared martingale supremum after division by $T^2$ is
$O(1/T)$, and its bounded remainder is $O(1/T)$. No stationary
initial law has entered this argument. The scaled martingales are
continuous, start at zero and are square integrable on finite
intervals. Their jumps and bracket jumps are identically zero.
These are exactly the conditions of Whitt,
[*Proofs of the martingale FCLT*, arXiv:0712.1929v2,
Theorem 2.1(ii)](https://arxiv.org/html/0712.1929v2), with covariance
matrix $C=2D_{\rm eff}$. That classical theorem gives the Brownian
limit in Skorohod topology; for continuous paths and continuous
limit it gives the stated uniform-path weak convergence. The
bounded corrector in (56.5), divided by $\sqrt T$, vanishes uniformly.
This proves (56.3)--(56.4), including every factor two.

When $w=0$, $j=0$ and $\chi=0$. When additionally $\psi=\phi$,
(56.4) is exactly the supplied $\widehat M_\kappa$ and (56.3)
is the already owned Q-law limit, rather than a new proof of that
supplier counted as an additional result. $\square$

## 57. Exact all-budget directional frontier in the original metric

**Theorem 57.1 (native control frontier and complete attainment cases).**
For every fixed $\kappa\in\mathcal K_\times$, unit original-coordinate
normal $e$ and budget $B\ge0$, put

$$
\begin{aligned}
h&=J_\kappa^{\mathsf T}e,& a(k)&=e\cdot\widehat c_\kappa(k),&
V_e(k)&=a(k)^2,\\
\mu(s)&=\Lambda_\kappa(\sqrt s\,h)\quad(s\ge0),&
F_{\kappa,e}(B)&=
 \inf_{\substack{(\psi,w)\text{ as in }(54.1)\\R(\psi,w)\le\lambda+B}}
                        e^{\mathsf T}D_{\rm eff}(\psi,w)e.
\end{aligned}
\tag{57.1}
$$

Here $\Lambda_\kappa$ is the inherited full-real Dirichlet band of
D (36.5), not a small-frequency approximation. Then

$$
F_{\kappa,e}(B)
 =\sup_{s>0}\frac{\Lambda_\kappa(\sqrt s\,J_\kappa^{\mathsf T}e)
                                      -\lambda-B}{s}.
\tag{57.2}
$$

The primal infimum is always attained in the positive controller
class. Its precise cases are these.

For $B=0$ its unique controller is $\psi=\phi,w=0$, and
$F_{\kappa,e}(0)=\int_I V_e\phi^2dk$. If $V_e$ is nonconstant, the
dual value is reached only as $s\downarrow0$, with no finite maximizing
$s$. For nonconstant $V_e$ and $B>0$, write $z_s$ for the positive
real $L^2$-normalized first Dirichlet eigenfunction of
$-\varepsilon^2\partial_k^2+sV_e$. There is a unique $s_B\in(0,\infty)$
satisfying

$$
\varepsilon^2\int_I|z_{s_B}'|^2dk
 =\mu(s_B)-s_B\mu'(s_B)=\lambda+B.
\tag{57.3}
$$

The unique primal controller is $\psi=z_{s_B},w=0$, the unique
finite dual maximizer is $s_B$, and
$F_{\kappa,e}(B)=\mu'(s_B)=\int V_ez_{s_B}^2$.
In particular every asserted optimizer has $z_{s_B}/\phi$ smooth
and strictly positive on the closed height interval.

The constant-potential directions are exactly
$e=\pm(2,-2,1)/3$. In either case $V_e\equiv1/9$ and
$F_{\kappa,e}(B)=1/9$ for every $B$. For $B>0$ the dual value is
only a limit as $s\to\infty$, not a finite-multiplier optimum;
for $B=0$ every $s>0$ is a dual maximizer. The primal optimizers
in the constant case are exactly the controllers with $w$ constant
and $\mathcal E(\psi)+w^2/4\le\lambda+B$.

Proof. The phase-current term in (56.4) is nonnegative in every
direction, and its entropy charge in (55.4) is also nonnegative.
Consequently the controlled problem reduces exactly to

$$
F_{\kappa,e}(B)=
 \inf_{\substack{\psi=\phi f\text{ as in }(54.1)\\
                         \mathcal E(\psi)\le\lambda+B}}
                       \int_I V_e\psi^2dk.
\tag{57.4}
$$

One inequality discards these two nonnegative current charges;
the opposite inequality sets $w=0$, for which $\chi=j=0$.
For each normalized $\psi\in H_0^1(I)$, the already supplied
Dirichlet Rayleigh characterization gives

$$
\mu(s)\le\mathcal E(\psi)+s\int_I V_e\psi^2dk.
\tag{57.5}
$$

It implies that every value on the right of (57.2) is a lower bound
in (57.4). This is classical Rayleigh duality, used here as an
intermediate tool, not claimed as a new general spectral principle.
It remains to prove equality and attainment in the exact source
class, including arbitrarily large finite budgets.

The bounded smooth potential has a simple positive first Dirichlet
eigenfunction for every finite $s\ge0$. These are the same scalar
fibres as D (36.5); positivity and simplicity follow from the scalar
ODE and its Wronskian as in D §36. At each face $z_s$ has a nonzero
inward derivative. Otherwise its value and derivative would vanish
there and ODE uniqueness would give $z_s=0$. Dividing two smooth
functions with simple zeroes therefore makes $z_s/\phi$ smooth up
to the faces with positive endpoint limits. Compactness then gives
a strictly positive minimum for that ratio for each fixed $s$.
Thus all these eigenfunctions are actually admitted by (54.1),
not merely elements of a relaxed Sobolev optimization problem.

The following ordinary one-parameter differentiation spells out the
needed spectral facts, beyond the inherited near-zero band expansion.
A bounded perturbation of a simple isolated eigenvalue has a locally
convergent resolvent series, giving analytic $\mu,z_s$ at every finite
$s$. Differentiate its normalized real eigenvalue equation, choosing
$\langle z_s,\partial_s z_s\rangle=0$. With
$q_s=(V_e-\mu'(s))z_s$ this gives

$$
\begin{aligned}
\mu'(s)&=\int_I V_ez_s^2dk,\\
\mu''(s)&=-2\langle q_s,
          (H_s-\mu(s))_{z_s^\perp}^{-1}q_s\rangle,\qquad
H_s=-\varepsilon^2\partial_k^2+sV_e.
\end{aligned}
\tag{57.6}
$$

The inverse is positive on the orthogonal complement because the
first eigenvalue is simple and separated from the second. If $V_e$
is nonconstant, $q_s\ne0$: positivity of $z_s$ would otherwise
force $V_e$ constant. Hence $\mu''(s)<0$ for every finite $s$.
The height energy
$E_s=\mu(s)-s\mu'(s)=\mathcal E(z_s)$ obeys
$E_0=\lambda$ and $E_s'=-s\mu''(s)>0$ for $s>0$.

For this native rational potential, $E_s$ tends to infinity.
Here is the reason this conclusion is not assumed for arbitrary
smooth potentials with a flat minimum. The common denominator in
G (26.7) is nonzero on $[l,u]$, and the numerator of $a=h\cdot c_\kappa$
is a polynomial of degree at most two. If $V_e$ is nonconstant,
its minimum set on $[l,u]$ is finite: the equation $V_e=m_e$, where
$m_e=\min_{[l,u]}V_e$, becomes a nonzero polynomial equation after
multiplication by the squared denominator. Normalized smooth tests
supported arbitrarily near a minimizing point, from inside $I$ even
if it is a face, show

$$
\lim_{s\to\infty}\frac{\mu(s)}s=m_e,\qquad
\lim_{s\to\infty}\int_I V_ez_s^2dk=m_e.
\tag{57.7}
$$

Indeed the Rayleigh upper bound of such a fixed test is
$E_{\rm test}/s+m_e+\eta$, while the lower bound is $m_e$.
Also $m_e\le\int V_ez_s^2\le\mu(s)/s$ because $E_s\ge0$.
If $E_s$ stayed bounded along a sequence tending to infinity,
compactness of $H_0^1(I)\hookrightarrow L^2(I)$ would give a
normalized limit $z$. Equation (57.7) would force
$\int(V_e-m_e)|z|^2=0$, so $z$ would be supported on that finite
set, impossible for a normalized $L^2$ function. This proves
$E_s\to\infty$, including potentials minimized only at the faces.

For every $B>0$ there is therefore exactly one solution of (57.3).
Use its admitted $z_{s_B}$ and $w=0$ in (57.5). The Rayleigh
inequality is an equality and its energy is exactly the budget;
this proves (57.2). Moreover

$$
\frac{d}{ds}\frac{\mu(s)-\lambda-B}s
       =\frac{\lambda+B-E_s}{s^2},
\tag{57.8}
$$

so this dual optimum is unique. Any other primal optimizer must
have equality in its Rayleigh bound and spend the entire energy
budget. Simplicity and positivity force $\psi=z_{s_B}$; the full
budget already spent on height leaves $\int w^2\rho=0$, hence
$w=0$. This also rules out a current improving the optimum through
ballistic cancellation.

At $B=0$, Theorem 55.1 already fixes $\psi=\phi,w=0$.
Since $\mu(0)=\lambda$, (57.6) gives the dual limit
$\lim_{s\downarrow0}(\mu(s)-\lambda)/s=\int V_e\phi^2$.
Strict concavity makes it smaller at every finite $s>0$ when
$V_e$ is nonconstant. This proves the zero-budget statement without
mistaking the limiting multiplier for an attained one.

Finally, if $a^2$ is constant, continuity on the connected height
interval makes $a$ itself constant (including the zero case).
D Theorem 50.1 supplies exactly the constant-coefficient line
$h=t(2,-2,\kappa)$ with $a=t$; its polynomial independence excludes
a zero constant for nonzero $h$. Since $h=J_\kappa^{\mathsf T}e$,
the original unit normals are precisely $\pm(2,-2,1)/3$, with
$a=\pm1/3$. Here $\mu(s)=\lambda+s/9$ and the dual expression is
$1/9-B/s$, proving all its limiting cases. The directional current
contribution vanishes exactly when $(e\cdot\chi)'=0$. By (56.2)
this is equivalent to $a w-j\cdot e=0$ pointwise; $a\ne0$ makes
$w$ constant. Every such controller satisfying the entropy constraint
is an optimizer, and no other one is. $\square$

## 58. Sharp uniform protection of the weakest transport direction

**Theorem 58.1 (all-budget positive rank and matching admitted family).**
There are constants $0<c_*\le C_*<\infty$, depending only on the
fixed native data and nonzero collar, such that for all $B\ge0$ and
$\kappa\in\mathcal K_\times$,

$$
c_*(1+B)^{-2}\le
F_\kappa^{\rm weak}(B):=
 \inf_{\substack{(\psi,w)\text{ as in }(54.1)\\R\le\lambda+B}}
                    \lambda_{\min}(D_{\rm eff})
 =\min_{|e|=1}F_{\kappa,e}(B)
 \le C_*(1+B)^{-2}.
\tag{58.1}
$$

In particular every controller of finite rate budget has three
strictly positive effective transport eigenvalues, with the same
lower bound for every controller, normal and parameter in that
budget and collar. The large-budget upper bound is realized as an
order bound by a family of positive controllers of (54.1), selected
before the horizon from the same fixed INITIAL. It is not merely
an estimate by amplitudes vanishing on part of $I$.

Proof. First consume the inherited native polynomial sublevel
estimate G (26.7)--(26.8). The signed map sends every unit $e$ to
$h=J_\kappa^{\mathsf T}e$ in a fixed compact annulus:

$$
d_-:=\min(1,\kappa_-)\le|h|\le\max(1,\kappa_+)=:d_+.
\tag{58.2}
$$

Applying that estimate to $h/|h|$ gives, with uniform $C_0,r_0>0$,

$$
|\{k\in I:|a(k)|\le r\}|\le C_0\sqrt r\quad(0<r\le r_0).
\tag{58.3}
$$

This reuses the strongest supplied source coercivity; no generic
subelliptic estimate is reconstructed as a new result.
For an admitted normalized amplitude with
$\mathcal E(\psi)\le\lambda+B$, the one-dimensional Dirichlet
Sobolev inequality gives
$\|\psi\|_\infty^2\le2\|\psi'\|_2\le2\sqrt{\lambda+B}/\varepsilon$.
Set $A_e=\int_Ia^2\psi^2$. Splitting the unit mass over the set in
(58.3) and its complement yields

$$
1\le\frac{2C_0}{\varepsilon}\sqrt{r(\lambda+B)}
                              +\frac{A_e}{r^2}.
\tag{58.4}
$$

Choose a fixed $\eta>0$ small enough that $\eta\le r_0$ and
$2C_0\sqrt{\eta\max(\lambda,1)}/\varepsilon\le1/2$.
For $r=\eta/(1+B)$ the first term is at most $1/2$, and hence

$$
e^{\mathsf T}D_{\rm eff}e\ge A_e
             \ge\frac{\eta^2}{2(1+B)^2}.
\tag{58.5}
$$

The entropy constraint in Theorem 55.1 implies exactly the energy
bound used here, regardless of $w$. Thus (58.5) is uniform over the
whole class; it does not depend on a controllerwise mixing or
positivity constant.

For sharpness fix one $k_*\in I$, independently of INITIAL and of
all budgets. At each $\kappa$ choose the deterministic unit normal

$$
e_\kappa=
 \frac{\widehat c_\kappa(k_*)\mathbin{\times}\widehat c_\kappa'(k_*)}
 {|\widehat c_\kappa(k_*)\mathbin{\times}\widehat c_\kappa'(k_*)|}.
\tag{58.6}
$$

G (32.2), transformed by the same signed matrix, gives

$$
\det(\widehat c_\kappa,\widehat c_\kappa',\widehat c_\kappa'')
 =\kappa\det(c_\kappa,c_\kappa',c_\kappa'')\ne0.
\tag{58.7}
$$

The cross product in (58.6) is therefore nonzero and has a uniform
positive lower norm on the collar. For
$a_\kappa=e_\kappa\cdot\widehat c_\kappa$ this implies
$a_\kappa(k_*)=a_\kappa'(k_*)=0$ and
$a_\kappa''(k_*)\ne0$. Bounded coefficient derivatives give the
uniform estimate
$|a_\kappa(k)|\le C_a|k-k_*|^2$ near $k_*$. This is an actual
double contact of the native coefficient curve with its selected
normal, not an extra flat direction of the source.

Choose a nonnegative real $\eta_0\in C_c^\infty(-1,1)$ with
$\int\eta_0^2=1$ and a fixed
$0<\delta_0<\min(1,k_*-l,u-k_*)$. For $0<\delta\le\delta_0$ put

$$
b_\delta(k)=\delta^{-1/2}\eta_0((k-k_*)/\delta),\qquad
\psi_\delta=
 \frac{b_\delta+\delta^2\phi}{\|b_\delta+\delta^2\phi\|_2},\qquad
w_\delta=0.
\tag{58.8}
$$

The normalization denominator is at least one. The ratio
$\psi_\delta/\phi$ is smooth on $[l,u]$ and is at least
$\delta^2/\|b_\delta+\delta^2\phi\|_2>0$, including at both faces.
Thus this family is in the precise positive class. In particular
the small background term is present at every finite budget.
Direct norm bounds, uniformly in the collar, give

$$
\begin{aligned}
\mathcal E(\psi_\delta)
 &\le2\varepsilon^2\|\eta_0'\|_2^2\delta^{-2}
                             +2\lambda\delta^4
 \le C_E\delta^{-2},\\
\int_Ia_\kappa^2\psi_\delta^2dk
 &\le2C_a^2\delta^4\int_{-1}^1 z^4\eta_0(z)^2dz
                    +2\delta^4\int_Ia_\kappa^2\phi^2dk
 \le C_A\delta^4,
\end{aligned}
\tag{58.9}
$$

where, for example, take
$C_E=2\varepsilon^2\|\eta_0'\|_2^2+2\lambda$.
For $\lambda+B\ge C_E/\delta_0^2$ select
$\delta=\sqrt{C_E/(\lambda+B)}$. Its entropy rate is its height
energy and is at most $\lambda+B$, while $j=\chi=0$. Consequently

$$
\lambda_{\min}(D_{\rm eff}(\psi_\delta,0))
 \le e_\kappa^{\mathsf T}D_{\rm eff}(\psi_\delta,0)e_\kappa
 \le C_A C_E^2(\lambda+B)^{-2}.
\tag{58.10}
$$

For the remaining bounded budgets choose $\psi=\phi,w=0$ and
increase $C_*$ using the uniform upper bound on $\widehat M_\kappa$.
Since $\lambda$ is fixed and positive, $(\lambda+B)^{-2}$ and
$(1+B)^{-2}$ are comparable. This proves the two bounds for all
budgets. The initial height has never moved to $k_*$; only the
invariant amplitude of the fixed controller has been concentrated
there. Its transient duration need not be uniform as $B\to\infty$.

Finally, infima over controllers and unit normals commute. The
energy sublevel of normalized $H_0^1$ amplitudes is compact in
$L^2$, and $V_e$ depends continuously on $e$ in supremum norm.
Alternatively (57.4) directly gives
$|F_{\kappa,e}(B)-F_{\kappa,e'}(B)|\le\|V_e-V_{e'}\|_\infty$.
The directional minimum is thus attained on the unit sphere.
Theorem 57.1 supplies an admitted controller at that normal, proving
the equality in (58.1) as well as primal attainment for the weakest
frontier. The matching exponent concerns this weakest-direction
optimization. It does not say that every fixed normal has that
large-budget decay: the constant directions keep value $1/9$.
$\square$

## 59. The conditional transport-selection consumer and its boundaries

**Proposition 59.1 (a positive sufficient condition for the existing
survival-selection task).** For the source and transport-selection
consumer of Proposition 53.2, restrict admissible selections to
(54.1)--(54.2), with a fixed finite excess-rate budget $B$. Then
minimum rate selects the supplied Q controller exactly; every
admitted selection with rate at most $\lambda+B$, after subtracting
its own $j$, has a three-direction continuous-path Brownian limit
whose tensor is bounded below by $c_*(1+B)^{-2}\mathrm{Id}$.
The exact directional cost frontier is (57.2), and this uniform
weakest-direction order cannot be strengthened to a larger order
as $B\to\infty$ within the same class.

Proof. Theorem 55.1 fixes the minimum and its equality case on full
native paths. Theorem 56.1 uses the same law, source, clock and
INITIAL to identify the centered path limit. Theorems 57.1 and 58.1
apply to that identical rate and tensor, so their lower bounds and
positive admitted upper family are simultaneously valid consumers
of the entropy calculation, not separately optimized quantities
from incompatible histories. They prove every assertion.

This restriction changes the quantified selection class in a
substantive way. Corollary 52.1 quantifies over arbitrary
absolutely continuous finite-horizon reweightings; its attaining
planar laws are not supplied as prefixes of a fixed homogeneous
height-only policy. It therefore retains its obstruction to entropy
rate alone in that larger class. The present sufficient condition
uses persistence, phase-translation covariance, independent drivers,
height-only state dependence, the fixed collar and finite rate
budget together. No conclusion is drawn for arbitrary phase
feedback, hidden-memory controllers, nonstationary reweightings,
or policies changed with the observation horizon.
$\square$

**Definition 59.2 (mathematical correspondence and remaining bridges).**
The correspondence to the original task is as follows. The objects
are the original native source histories and the controlled laws
on that same path space. Their common source data are D Definition
35.1 and G (25.2)--(25.5). The original preparation, probabilities,
rational coefficients, two columns, height guard and both killed
faces are retained; the only added drift permissions are the
explicit feedback ones in Definition 54.1. D (39.1) is used solely
as the signed linear map to the original $y$; neither its metric
nor its clock is rescaled. The initial point is deterministic in
every experiment, even when theorems range over a collar or budget.
The two Brownian drivers, current and corrector belong to one common
controlled history, so the covariance and entropy bounds require
no independent attainment or coupling assumption.

The observation permission is a complete continuous height history
and access to the two driver biases, with known fixed calibration.
A specified continuous winding lift is the mathematical phase
record for the path statements. A wrapped endpoint, finite paid
Reads, an estimator with finite precision, or an unknown calibration
is a different observation service. D Theorem 55.2 supplies height
recovery from an already supplied ideal continuous phase record in
its stated experiment; D §§55--60 do not acquire that record or
install driver biases. The metric is the declared
Euclidean metric on the original $(\theta,v,D)$ and the uniform
metric on centered continuous paths over $[0,b]$. Ballistic
centering uses that controller's own mean $j$; it does not remove
its independent phase martingale. There is no vanishing-resolution
tube constraint in (57.2). The precision is the diffusive $\sqrt T$
scaling and weak continuous-path convergence, with exact analytic
height feedback. The resource is full-path relative entropy in
nats per unit original time. It is not a Read count, fixed number
of bits, total command variation, physical energy, or installed
actuator cost. Theorems 55.1 and 56.1 are controllerwise limits;
Theorems 57.1 and 58.1 are uniform mathematical bounds on the
resulting rates and tensors for all controllers and collar
parameters. They do not interchange those limits with a
budget-dependent horizon or give a uniform acquisition latency.

The strongest reused suppliers are D (36.1), (36.4)--(36.5),
(37.2), (37.8)--(37.9), §§38--39 and Theorem 50.1; G (26.7)--(26.8)
and (32.2); and the original entropy consumer in §§49--53.
The Q-law covariance, its rank, scalar Dirichlet band, rational
sublevel bound, nonzero native second-jet determinant and autonomous
line are their existing results. The bounded-corrector method in
this volume §43 is also existing mathematics. The new consumption
is the fixed-source controller's full-path likelihood and rate,
its actual-current corrector tensor, exact budget optimization and
positive sharp all-budget weakest-direction law, combined in
Proposition 59.1. No old Q limit, Carnot rank, fixed-source Green
law or finite-horizon tube frontier is counted again as new content.

The measure-level entropy principle and its reversible spectral
comparison are classical. Chetrite--Touchette,
[*Variational and optimal control representations of conditioned and
driven processes*, arXiv:1506.05291v3](https://arxiv.org/html/1506.05291v3),
§III.4 (52)--(56) and Appendix A.2 (90)--(94), provide the
relative-entropy and reversible Rayleigh/Donsker--Varadhan
correspondence. Their §IV current-cost expressions, including (76),
use $D^{-1}$; those formulas are not applied to this degenerate native
state matrix. Here the scalar band is exactly
$-\varepsilon^2\partial_k^2+s(e\cdot\widehat c_\kappa)^2$ with two
Dirichlet faces, its ground amplitude is positive and normalized in
$dk$, and its sign is a nonnegative potential for a lowest
eigenvalue. The full proof (57.5)--(57.8) supplies the correspondence,
attainment and endpoint cases for this source without importing an
ergodic full-state probability or an invertible diffusion matrix.
The original Donsker--Varadhan PNAS text is not an additional premise.
Whitt Theorem 2.1(ii), cited at its application in Theorem 56.1,
supplies only the classical martingale FCLT: local square
integrability, zero jumps and convergence of every predictable
bracket entry are checked there explicitly. The two-driver
exponential change, endpoint integrability, source-specific
optimization and sharp positive test family are proved above.
These tools are credited classical intermediates; the native
combination is `repo-derived`, with no global originality claim.

Remaining implementation and interpretation obligations are exact
continuous-height acquisition, installed bias access with its
latency and cost, any robustness to finite precision or delay, and
a lawful correspondence to existing native commands and their
refusal/Stop handling. No theorem here provides such a service or
turns the killed reference's failure histories into an acquired
ability to refuse death. The original paths and legal operations
retain their source semantics; the controller law is a conditional
analytic model. No full-cover invariant phase probability is assumed
or constructed: only the height density $\rho dk$ is a probability.

The collar is essential to the uniform original-coordinate rank
statement. At the actual $\kappa=0$ leaf the original $D$ coordinate
is frozen, so no extension of its positive three-direction bound
or division by $\kappa$ is made. Local control rank, predictive
state dimension, effective diffusion rank, spectral or homogeneous
dimension, and physical spatial dimension remain separate notions.
The result supplies a sufficient selection condition for three
effective transport directions under its explicit premises. It
neither identifies physical axes nor derives the diffusion or the
physical relevance of persistent height-only feedback from bare
FIB. These are ordinary mathematical proofs from the stated native
premises, with no Lean/kernel certification or empirical claim.

## 追加锚（本行以下为增补区）

## 60. A hard moving envelope on the unchanged native history

**Definition 60.1 (moving-envelope class and exact scale).** Fix the native
experiment, the inherited G/C/N/F premises, the deterministic initial
state, signed original coordinates and original clock of Definitions 41.1
and 49.1. Keep both absorbing height faces, the complete cemetery-inclusive
killed-history space and the predeclared unit normal $e$. Put

$$
X_t=e\cdot(y_t-y_0),\qquad
h=J_\kappa^{\mathsf T}e,\qquad
 a(k)=h\cdot c_\kappa(k),\qquad
\widehat m=\int_Ia(k)^2\phi(k)^2\,dk,
$$

and fix $0<\alpha<1/2$ and $r>0$. Write

$$
R(t)=r(1+t)^\alpha,\qquad \beta=1-2\alpha,
\qquad c_{\alpha,r}=\frac{\pi^2\widehat m}{4r^2\beta}.
\tag{60.1}
$$

The class $\mathcal C_{\alpha,r}$ consists of probability laws $V$ on the
original full infinite canonical killed-history space such that the initial
state is the prescribed deterministic one,

$$
V\!\left(\zeta=\infty,\ |X_t|<R(t)\ \text{for every }t\ge0\right)=1,
\tag{60.2}
$$

and, for every finite $T>0$, the literal full prefix $V_T$ is absolutely
continuous with respect to the original cemetery-inclusive prefix
$\mathbb P_T$ and has finite natural-logarithm divergence
$D(V_T\Vert\mathbb P_T)$. No law is required to have a global density with
respect to the killed reference. The class is defined on one infinite path
space; it is not replaced by a family of unrelated horizon laws.

The exact question is whether $\mathcal C_{\alpha,r}$ is nonempty and
whether one law $V_*$, chosen independently of $T$, satisfies

$$
\begin{aligned}
\lim_{T\to\infty}
 \frac{D((V_*)_T\Vert\mathbb P_T)-\lambda T}{T^\beta}
 &=c_{\alpha,r},\\
\lim_{T\to\infty}
 \frac{\inf_{V\in\mathcal C_{\alpha,r}}D(V_T\Vert\mathbb P_T)-\lambda T}{T^\beta}
 &=c_{\alpha,r}.
\end{aligned}
\tag{60.3}
$$

The height law, the full killed-prefix convention and all native coefficients in
these formulas are those already fixed above. In particular, no homogeneous
generator, operational controller, uniform rate, physical interpretation or
finite-horizon optimizer is part of this definition.

## 61. One consistent law for every expanding tube

**Proposition 61.1 (native cosine construction).** Under Definition 60.1,
there is one probability law $V_*=V_{*,\alpha,r}$ on the full infinite native
history space with the prescribed initial state such that (60.2) holds. Its
finite-prefix density with respect to $\mathbb P_T$ is

$$
L_T=\mathbf1_{\{\zeta>T\}}e^{\lambda T}
       \frac{\phi(K_T)}{\phi(k_0)}M_T,
\tag{61.1}
$$

where, under the conservative ground-height law $\mathbb Q$ of Definition
41.1,

$$
\begin{aligned}
\omega(t)&=\frac{\pi}{2R(t)},
&H(t,x)&=\cos(\omega(t)x),\\
\sigma&=\inf\{t\ge0:|X_t|\ge R(t)\},
&b(t,x)&=\partial_t\log H(t,x)
 =\frac{R'(t)}{R(t)}\omega(t)x\tan(\omega(t)x),\\
M_t&=\mathbf1_{\{t<\sigma\}}H(t,X_t)
 \exp\!\left\{\int_0^t
 [\omega(s)^2a(K_s)^2-b(s,X_s)]\,ds\right\}.
\end{aligned}
\tag{61.2}
$$

The zero extension in (61.2) is a true $\mathbb Q$-martingale on every
finite interval and satisfies
$\mathbb E_{\mathbb Q}[M_T\mid K_{[0,T]}]=1$. Hence the height marginal
of $V_*$ is exactly the supplied $\mathbb Q$ height law on each finite
prefix. The law in (61.1) is locally absolutely continuous and has finite
relative entropy for every finite $T$.

Proof. Under $\mathbb Q$, conditional on the complete height history, the
projection $X$ starts at zero and has the stochastic-integral form

$$
X_t=\sqrt2\int_0^ta(K_s)\,dW_s^2,
\tag{61.3}
$$

where $W^2$ is independent of the height driver. The native signed
coordinate map is still the one in (49.2); no coordinate is rescaled.
On the open strip $|x|<R(t)$, $H>0$ and

$$
\partial_x^2H=-\omega(t)^2H,
\qquad
\frac{1}{H}\,\partial_tH=b(t,x)\ge0,
\tag{61.4}
$$

because $R'(t)\ge0$ and $x\tan(\omega(t)x)\ge0$. Applying Itô's formula
before $\sigma$ and using the quadratic variation
$d\langle X\rangle_t=2a(K_t)^2dt$ gives

$$
 dM_t=M_t\sqrt2\,a(K_t)\partial_x\log H(t,X_t)\,dW_t^2,
 \qquad t<\sigma.
\tag{61.5}
$$

For a fixed finite $T$, $|a|\le C_a$ and (61.4) imply the deterministic
bound

$$
0\le M_t\le
\exp\!\left(C_a^2\int_0^T\omega(s)^2ds\right),\qquad 0\le t\le T.
\tag{61.6}
$$

Stop additionally before $H$ falls below $1/n$. On this stopped region
$\partial_x\log H$ is bounded on $[0,T]$, so the stopped local martingale
has constant mean one. If $\sigma\le T$, continuity gives $H(t,X_t)\to0$
as $t\uparrow\sigma$, while the exponential factor in (61.2) remains
bounded by (61.6). Thus the stopped variables converge to the zero
extension in (61.2) at a finite boundary hit. Dominated convergence removes
both stops and proves $\mathbb E_{\mathbb Q}M_T=1$ and the martingale
property. The same argument with a fixed continuous height path leaves only
the Brownian integral in (61.5), and proves the conditional mean-one
identity.

Consequently the measures $M_T\mathbb Q_T$ are consistent under literal
restriction from $[0,T]$ to $[0,S]$. The standard countable projective
extension on the continuous native path restrictions gives one law $V_*$
on $[0,\infty)$. For each integer $n$, its restriction to $[0,n]$ assigns
probability one to $\zeta>n$ and $\sigma>n$. A countable union therefore
shows that $\zeta=\infty$ and $|X_t|<R(t)$ for every real $t\ge0$, by path
continuity. The prescribed initial state and all other native path
coordinates are retained by the change of density.

The ground-state identity in Definition 41.1 gives the full density (61.1),
including the cemetery indicator. Since $\phi$ is bounded and positive at
$k_0$, (61.6) bounds $L_T$ by a finite deterministic constant for each
fixed $T$. Therefore $L_T\log L_T$ has an integrable positive part, while
$z\log z\ge-1/e$ controls its negative part under $\mathbb P_T$. Thus
$V_{*,T}\ll\mathbb P_T$ and $D((V_*)_T\Vert\mathbb P_T)<\infty$.

The cosine factor and the time-dependent exponential are the native
specialization of the time-dependent generalized Doob path-density formula
in Chetrite and Touchette, *Nonequilibrium Markov processes conditioned on
large deviations*, arXiv:1405.5157v2, §IV.1, equations (71)--(80). That
classical identity is used only as an intermediate guide: (61.4)--(61.6)
check normalization at the moving zero boundary directly. No positive-interior
formula is used as a conservativity assertion.
$\square$

**Lemma 61.2 (upper entropy estimate for the common law).** For every
fixed $\alpha,r$ in Definition 60.1,

$$
D((V_*)_T\Vert\mathbb P_T)
\le \lambda T+\frac{\pi^2}{4}\int_0^T\frac{\mathbb E_{\mathbb Q}[a(K_s)^2]}{R(s)^2}\,ds+O(1).
\tag{61.7}
$$

The $O(1)$ depends on the fixed native data and on $\alpha,r$, but not on
$T$. Moreover,

$$
\mathbb E_{\mathbb Q}[a(K_s)^2]=\widehat m+O(e^{-3\lambda s})\quad(s\ge1),
\tag{61.8}
$$

so

$$
\limsup_{T\to\infty}
\frac{D((V_*)_T\Vert\mathbb P_T)-\lambda T}{T^\beta}
\le c_{\alpha,r}.
\tag{61.9}
$$

Proof. On the support of $V_*$, (61.1)--(61.2) give

$$
\log L_T=\lambda T+\log\frac{\phi(K_T)}{\phi(k_0)}
 +\log H(T,X_T)+\int_0^T[\omega(s)^2a(K_s)^2-b(s,X_s)]ds.
\tag{61.10}
$$

The last two terms are nonpositive except for the displayed quadratic
term. Conditional mean-one normalization in Proposition 61.1 leaves the
entire height marginal equal to $\mathbb Q$, so taking expectations in
(61.10), using $\log H\le0$, $b\ge0$ and
$\log\phi(K_T)\le\log\|\phi\|_\infty$, proves (61.7). The relative-kernel estimate
(41.3), applied to the bounded function $a^2$, gives (61.8); the integral
over $[0,1]$ is bounded because $a$ is bounded. Since

$$
\int_0^T\omega(s)^2ds
=\frac{\pi^2}{4r^2}\frac{(1+T)^\beta-1}{\beta},
\tag{61.11}
$$

and $\int_1^\infty e^{-3\lambda s}\omega(s)^2ds<\infty$, (61.9) follows.
$\square$

## 62. The matching lower bound from native fixed-strip bands

For the native lower-bound argument, put

$$
E_T=\{\zeta>T,\ |X_s|<R(s)\text{ for every }0\le s\le T\}.
\tag{62.1}
$$

As a classical intermediate step, every $V\in\mathcal C_{\alpha,r}$
satisfies $V_T(E_T)=1$, and therefore

$$
D(V_T\Vert\mathbb P_T)\ge-\log\mathbb P_T(E_T).
\tag{62.2}
$$

Indeed, the event in (62.1) is measurable on the full original killed prefix,
including the cemetery coordinate. The entropy partition identity, or the
Gibbs inequality applied to the restriction to $E_T$, gives (62.2), with
no replacement by an endpoint event or a larger horizon-dependent class.

**Lemma 62.2 (moving-strip probability bound).** There is a constant
$C_0<\infty$ depending only on the fixed native data and the deterministic
initial state such that, for every $T>1$,

$$
-\log\mathbb P_T(E_T)
\ge \int_1^T\Lambda_\kappa(\omega(s)h)\,ds
 -\frac12\log\bigl(2(u-l)R(T)\bigr)-\log C_0.
\tag{62.3}
$$

Here $\Lambda_\kappa$ is the same two-height-Dirichlet band as in D
(36.4)--(36.6), evaluated at the native frequency vector $\omega(s)h$.

Proof. Project the original killed process to $(K,X)$. Conditional on the
complete height path, (61.3) gives the autonomous projected generator

$$
\mathcal A=\varepsilon^2\partial_k^2+a(k)^2\partial_x^2
\tag{62.4}
$$

with both height faces killed. For a fixed $A>0$, kill this projection also
at $x=\pm A$ and let $S_A(t)$ be its zero-extended semigroup on
$L^2(I\times\mathbb R)$. The sine expansion in the $x$ variable separates
the operator into the height fibres

$$
-\varepsilon^2\partial_k^2+
 \frac{n^2\pi^2}{4A^2}a(k)^2,\qquad n=1,2,\ldots,
\tag{62.5}
$$

with the same two Dirichlet height faces. Since the potential is
nonnegative, the variational monotonicity of the bottom eigenvalue and
$L^2$ orthogonality give

$$
\|S_A(t)\|_{2\to2}
 \le \exp\{-t\Lambda_\kappa(\pi h/(2A))\}.
\tag{62.6}
$$

This is the native variable-coefficient band, not a homogenized or
constant-volatility substitute.

It remains to control the entrance at time one in the same $L^2$ space.
The projected free killed kernel has Fourier representation with height
kernel $K_{\kappa,\xi h}(1;k_0,k)$. The supplied all-frequency estimate
D (36.6), restricted to $\eta=\xi h$, and Plancherel imply

$$
\int_{\mathbb R}\int_I
 |K_{\kappa,\xi h}(1;k_0,k)|^2\,dk\,d\xi<\infty,
\tag{62.7}
$$

because the nonzero native collar makes $h\ne0$ and the right-hand side is
bounded by a constant times
$\int_{\mathbb R}\exp[-2c_0\Psi(|\xi h|)]d\xi$. Restricting to $E_1$
only decreases the nonnegative density, so its time-one subdensity $f_1$
has $\|f_1\|_2\le C_0$.

Take any partition $1=t_0<t_1<\cdots<t_N=T$. On the block
$[t_{j-1},t_j]$, the event $E_T$ is contained in the event that the
projection stays in the fixed strip of half-width $R(t_j)$, because $R$
is increasing. The Markov property, zero-extension contractions and (62.6)
therefore yield

$$
\mathbb P_T(E_T)
\le C_0\,[2(u-l)R(T)]^{1/2}
 \exp\!\left\{-\sum_{j=1}^N(t_j-t_{j-1})
 \Lambda_\kappa(\omega(t_j)h)\right\}.
\tag{62.8}
$$

The constant is the same for every partition. Continuity of the band in its
frequency and refinement of right-endpoint sums give (62.3). This argument
uses the full native projection and its cemetery-inclusive starting density;
no infinite partition probability or guessed moving-domain eigenfunction is
introduced.
$\square$

**Theorem 62.3 (native lower asymptotics).** With $\beta=1-2\alpha$,

$$
\liminf_{T\to\infty}
\frac{-\log\mathbb P_T(E_T)-\lambda T}{T^\beta}
\ge c_{\alpha,r}.
\tag{62.9}
$$

Proof. The inherited band expansion D (36.4) gives

$$
\Lambda_\kappa(\omega(s)h)
=\lambda+\widehat m\,\omega(s)^2+O(\omega(s)^4)
=\lambda+\frac{\pi^2\widehat m}{4R(s)^2}+O(R(s)^{-4}).
\tag{62.10}
$$

The contribution of the fixed interval $[0,1]$ is $O(1)$. For
$0<\alpha<1/2$, writing $\beta=1-2\alpha$ gives

$$
\int_1^T R(s)^{-2}ds
=\frac{(1+T)^\beta}{r^2\beta}+O(1),
\tag{62.11}
$$

while

$$
\int_1^T R(s)^{-4}ds=
\begin{cases}
O(T^{1-4\alpha}),&0<\alpha<1/4,\\
O(\log T),&\alpha=1/4,\\
O(1),&1/4<\alpha<1/2,
\end{cases}
=o(T^\beta).
\tag{62.12}
$$

Also $\log R(T)=o(T^\beta)$. Substituting (62.10)--(62.12) into
(62.3) proves (62.9).
$\square$

## 63. The exact frontier and its native consumer

**Theorem 63.1 (one-law sharp moving-envelope entropy frontier).** For every
fixed $0<\alpha<1/2$ and $r>0$, the class $\mathcal C_{\alpha,r}$ of
Definition 60.1 is nonempty. The law $V_*$ of Proposition 61.1 belongs to
that class, is independent of the terminal horizon, and satisfies

$$
\begin{aligned}
\lim_{T\to\infty}
 \frac{D((V_*)_T\Vert\mathbb P_T)-\lambda T}{T^{1-2\alpha}}
 &=\frac{\pi^2\widehat m}{4r^2(1-2\alpha)},\\
\lim_{T\to\infty}
 \frac{\inf_{V\in\mathcal C_{\alpha,r}}D(V_T\Vert\mathbb P_T)-\lambda T}{T^{1-2\alpha}}
 &=\frac{\pi^2\widehat m}{4r^2(1-2\alpha)}.
\end{aligned}
\tag{63.1}
$$

Both limits use natural logarithms and the same full cemetery-inclusive native
prefixes. The attaining law has the prescribed deterministic initial history,
keeps the original signed coordinates and clock, survives both height exits,
and obeys the strict tube for every time. The theorem makes no assertion of
uniqueness, finite-$T$ optimality, a uniform convergence rate, a homogeneous
generator, a global infinite-horizon density relative to $\mathbb P$, or an
operational implementation.

Proof. By Proposition 61.1 and Lemma 61.2,

$$
\limsup_{T\to\infty}
\frac{D((V_*)_T\Vert\mathbb P_T)-\lambda T}{T^\beta}
\le c_{\alpha,r}.
\tag{63.2}
$$

For every $V\in\mathcal C_{\alpha,r}$, the support inequality (62.2) gives
$D(V_T\Vert\mathbb P_T)\ge-\log\mathbb P_T(E_T)$. Taking the infimum and
using Theorem 62.3 yields

$$
\liminf_{T\to\infty}
\frac{\inf_{V\in\mathcal C_{\alpha,r}}D(V_T\Vert\mathbb P_T)-\lambda T}{T^\beta}
\ge c_{\alpha,r}.
\tag{63.3}
$$

Since $V_*$ belongs to the same class for every $T$,

$$
-\log\mathbb P_T(E_T)\le
 \inf_{V\in\mathcal C_{\alpha,r}}D(V_T\Vert\mathbb P_T)
\le D((V_*)_T\Vert\mathbb P_T).
\tag{63.4}
$$

Equations (63.2)--(63.4) squeeze both limits to $c_{\alpha,r}$ and establish
all clauses of (63.1). Corollary 52.1, as consumed by Proposition 53.2,
leaves projective consistency unasserted for its horizon laws. Here the single
law $V_*$ supplies a consistent infinite-law successor for that native
entropy-rate selection question. The lower bound ranges over exactly
$\mathcal C_{\alpha,r}$, the class newly defined in Definition 60.1.
This consumer conclusion follows from the full sandwich.

The scalar power-envelope/Q-process construction of Oçafrain,
*Quasi-stationarity for one-dimensional renormalized Brownian motion*,
arXiv:1809.07547v2, supplies the prior one-dimensional mechanism and its
power-envelope clock. In the constant native scalar case, the generator
normalization here gives the corresponding coefficient
$\pi^2a_0^2/(4r^2\beta)$ after the native time change. No scalar stationary
prefactor is imported into (61.1)--(63.4); normalization there comes from
$H(0,0)=1$ and the proved martingale identity. The general native argument
cannot be reduced to replacing the deterministic scalar clock by
$\widehat m t$, because the actual clock is
$\int_0^ta(K_s)^2ds$ and the tube is imposed in the original time.

The measure-level support inequality (62.2) is the finite-prefix
Gibbs/relative-entropy principle, and the reversible spectral comparison in
(62.5)--(62.6) is the classical Rayleigh correspondence. They are credited
as intermediate tools to Chetrite and Touchette, *Variational and optimal
control representations of conditioned and driven processes*,
arXiv:1506.05291v3, §III.4, equations (52)--(56), and Appendix A.2,
equations (90)--(93). Those classical formulas do not supply the native
moving-strip scale, the full-prefix starting-density estimate, or a common
infinite law; these are the deductions in Proposition 61.1 and Lemma 62.2.
$\square$

**Corollary 63.2 (compatibility with the homogeneous height-only frontier).**
Theorem 63.1 and Proposition 59.1 quantify over different, non-nested
subclasses of the same ambient class of consistent infinite native history
laws with local absolute continuity and finite full-prefix entropy.
Proposition 59.1 restricts selections to fixed, height-only,
phase-translation-covariant controllers with a finite excess-rate budget and obtains a positive
three-direction tensor. The law $V_*$ in Theorem 63.1 is a time-dependent
phase-position reweighting selected for the expanding boundary; its entropy
excess is of order $T^{1-2\alpha}$ and its density depends on the moving
cosine. This law is not a member of the homogeneous height-only class
used in Proposition 59.1. The two conclusions are compatible: 59.1 retains
its positive transport conclusion under its controller restrictions,
while 63.1 gives the sharp all-time leading cost in the class
$\mathcal C_{\alpha,r}$ of consistent infinite tube laws. Neither theorem
changes the other's native premises or consumer.

Proof. Proposition 59.1 applies its rate and tensor estimates only after the
controller restrictions (54.1)--(54.2) and the finite rate budget have been
imposed. Definition 60.1 imposes instead the full path support condition
(60.2), local absolute continuity and finite prefix entropy, with no
height-only or time-homogeneity restriction. The cosine factor in (61.2)
depends on $t$ and on the signed phase coordinate $X_t$; the leading entropy
rate $\lambda$ alone does not impose the controller restrictions of 59.1.

For a direct check of non-nesting, the law $\mathbb Q=\mathbb V_{\phi,0}$
has zero excess-rate budget and belongs to the homogeneous height-only
class. By (61.3), conditional on the height history, $X_T$ is centered
Gaussian with variance $2\int_0^T a(K_s)^2ds$. Positivity of $\widehat m$
and (61.8) imply that this variance is positive with positive probability
for some finite $T$. Thus
$\mathbb Q(|X_T|\ge R(T))>0$, so $\mathbb Q\notin\mathcal C_{\alpha,r}$.
Conversely, Theorem 55.1 makes every homogeneous height-only law equivalent
to $\mathbb Q$ on that finite prefix, while (60.2) gives
$V_*(|X_T|\ge R(T))=0$. Hence $V_*\in\mathcal C_{\alpha,r}$ is outside
the homogeneous height-only class. The two quantified conclusions are
compatible without an inclusion between their admissible classes.
$\square$

**Definition 63.3 (scope of the native result).** The assertions above are
ordinary mathematical consequences of the inherited native G/C/N/F premises.
They concern one fixed native experiment and every fixed pair
$(\alpha,r)$ in the stated range. The lower bound uses the same class of
consistent infinite laws as the infimum, and the upper bound uses one law
constructed without a terminal horizon. The full original history, both
height deaths, deterministic INITIAL, signed coordinates and natural-log
entropy remain in force. No physical claim, command-level acquisition,
global absolute continuity, uniform asymptotic rate, uniqueness or worldwide
priority statement is asserted.

## 追加锚（本行以下为增补区）
