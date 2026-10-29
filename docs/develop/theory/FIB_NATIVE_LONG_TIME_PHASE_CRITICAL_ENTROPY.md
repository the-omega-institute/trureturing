# Native long-time phase critical tube entropy

## 75. Fixed native data and the critical infinite-history class

**Definition 75.1 (native premises, coordinates and clock).** Let
[Q](FIB_NATIVE_LONG_TIME_PHASE_QUANTITATIVE_BOUNDS.md) denote the
quantitative-bounds volume,
[D](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md) the diffusion volume, and
[G](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md) the Green-stability
volume. Retain all the G/C/N/F premises of D Definition 35.1 and Q
Definitions 41.1 and 49.1, with their conditional status unchanged.
Here C, N and F are precisely the sources named in D Definition 35.1.
Fix arbitrary data in their stated ranges:
$0<Z<1$, $H=(1-Z)/2$, $I=(l,u)\Subset(0,H)$,
$\varepsilon>0$, a signed nonzero $\kappa\in\mathcal K_\times$
from Q (49.1), a deterministic $k_0\in E\Subset I$, and the prescribed
deterministic initial phase lift $q_0$. The parameter interval and its
slightly larger height interval are those fixed in D Definition 35.1.
The five probabilities are exactly G (25.2),

$$
(k-2\kappa,H+\kappa-k,Z,H+\kappa-k,k),
$$

with the immutable preparation phases, negative amplitude convention,
$h_2=0$ and $h_1=h_3=v$ of G Definition 25.1. The coefficient
$c_\kappa=(A_\kappa,B_\kappa,b_\kappa)$ is exactly G (25.4).
Use the all-real winding cover $I\times\mathbb R^3$,
$q=(\theta,v,x)$, and the signed original coordinates
$y=J_\kappa q$, $J_\kappa=\operatorname{diag}(1,1,\kappa)$,
so the third original coordinate is $D=\kappa x$.
The original killed reference law $\mathbb P$ is Q (41.1), equivalently
D (35.2), with two independent standard Brownian drivers, covariance
$\operatorname{diag}(\varepsilon^2,1)$, raw cover measure $dk\,dq$,
original time and killing at both endpoints of $I$.
Let $\zeta$ be that exit time, and put

$$
\phi(k)=\sqrt{\frac2{u-l}}\sin\frac{\pi(k-l)}{u-l},\qquad
\lambda=\frac{\varepsilon^2\pi^2}{(u-l)^2},\qquad
\pi(dk)=\phi(k)^2dk.
\tag{75.1}
$$

Let $\mathbb Q$ be exactly its conservative Doob ground-state law of
Q Definition 41.1. Its height semigroup, coefficient bounds and exact
phase laws are Q (41.3)--(41.6). In particular its height generator is
$\varepsilon^2\partial_{kk}+2\varepsilon^2(\phi'/\phi)\partial_k$,
and, conditional on the complete height path, its phase driver is
independent standard Brownian motion. Fix a Euclidean unit vector
$e\in\mathbb R^3$ before the history and $r>0$, and set

$$
\begin{aligned}
h&=J_\kappa^{\mathsf T}e,& a(k)&=h\cdot c_\kappa(k),\\
m=\widehat m&=\int_I a(k)^2\pi(dk)>0,&
A&=\|a\|_\infty^2\ge m,\\
X_t&=e\cdot(y_t-y_0),&
V(t)&=2\int_0^t a(K_s)^2ds.
\end{aligned}
\tag{75.2}
$$

The positivity of $m$ is the native tensor conclusion retained in
Q Theorem 74.1. The actual smooth bounded coefficient $a$ may vanish;
no pointwise positive lower bound is imposed. Write $\nu=\nu(m,r)>0$
for the principal Dirichlet eigenvalue of
$-(m\partial_{zz}-(z/2)\partial_z)$ on $(-r,r)$, in the weighted space
$L^2((-r,r),e^{-z^2/(4m)}dz)$, as in Q (74.4).
All divergences below use natural logarithms.

**Definition 75.2 (one common class of consistent infinite laws).** On the
original full infinite canonical killed-history space, including the
cemetery record after height death, let $\mathcal C_{\mathrm{crit},r}$
consist of probability laws $\mathsf V$ with the prescribed deterministic
initial state such that

$$
\mathsf V\!\left(\zeta=\infty,\quad
 |X_t|<r\sqrt{1+t}\text{ for every real }t\ge0\right)=1,
\tag{75.3}
$$

and, for every finite $T>0$, the literal full prefix $\mathsf V_T$
satisfies

$$
\mathsf V_T\ll\mathbb P_T,\qquad
D(\mathsf V_T\Vert\mathbb P_T)<\infty.
\tag{75.4}
$$

This is exactly the class quantified in Q Corollary 74.2, with the same
native data and strict event. It imposes no additional height-marginal
constraint and requires no global density relative to $\mathbb P$.
One member is a law on the whole infinite space with its literal
restrictions, rather than a separately chosen law for each horizon.

## 76. Attainment by one horizon-independent native law

**Theorem 76.1 (critical common-law entropy attainment).** For every fixed
native data set, unit normal $e$ and $r>0$ in Definition 75.1, there is
one law $\mathsf V_\star\in\mathcal C_{\mathrm{crit},r}$, chosen
independently of $T$, such that

$$
\lim_{T\to\infty}
\frac{D((\mathsf V_\star)_T\Vert\mathbb P_T)-\lambda T}
     {\log(1+T)}=\nu(m,r).
\tag{76.1}
$$

More precisely, fix any $p\in(1/2,1)$. There is a deterministic $C>0$
for which, under the prescribed deterministic-start $\mathbb Q$ height law,

$$
\begin{aligned}
v(t)&=2mt+C((1+t)^p-1),\\
G&=\{V(t)\le v(t)\text{ for every real }t\ge0\},&
q_G&=\mathbb Q(G)>0.
\end{aligned}
\tag{76.2}
$$

The attaining law can have height marginal $\mathbb Q(\,\cdot\mid G)$.
For $\tau=v^{-1}$, $\rho(u)=\sqrt{1+\tau(u)}$ and

$$
s(u)=\int_0^u\frac{dw}{2m\rho(w)^2},
\tag{76.3}
$$

there is a finite $C_1\ge1$, independent of $T$, such that

$$
0\le\frac{d(\mathsf V_\star)_T}{d\mathbb P_T}
\le C_1\exp\{\lambda T+\nu s(2AT)\}
\qquad(T>0).
\tag{76.4}
$$

Consequently

$$
D((\mathsf V_\star)_T\Vert\mathbb P_T)
\le\lambda T+\nu\log(1+T)+O(1).
\tag{76.5}
$$

The constants, including the $O(1)$, depend only on the fixed native
data, $e,r,p$ and the resulting choice of $C$, and have no horizon
dependence. This native common-law bridge is `repo-derived` from Q
Theorem 74.1 and Corollary 74.2. Bounded correctors, OU ground-state
conditioning, stopped Girsanov and transport of density bounds are reused
classical tools in the proof.

Proof. For the positive-probability height event, apply the bounded
corrector in the proof of Q Theorem 74.1 to $f=a^2-m$.
It supplies a bounded $u$ and the martingale

$$
N_t=u(K_t)-u(K_0)+\int_0^t f(K_s)ds,
$$

whose integer increments have absolute value at most
$b=2\|u\|_\infty+\|f\|_\infty$.
The same Azuma estimate gives, when $b>0$,

$$
\mathbb Q(|N_n|>n^p)
\le2\exp\{-n^{2p-1}/(2b^2)\}.
\tag{76.6}
$$

The series is summable. Borel--Cantelli and the bounded corrector give
$V(n)-2mn=O(n^p)$ almost surely. Between consecutive integers the centered
clock changes by at most $2(A+m)$, so the same bound holds for all real
$t\ge1$. If $b=0$, the centered clock is identically zero and this
conclusion holds directly. Near zero,
$|V(t)-2mt|\le2(A+m)t$ and
$((1+t)^p-1)/t\to p$. On every compact interval away from zero the ratio
is continuous. Thus

$$
\sup_{t>0}\frac{V(t)-2mt}{(1+t)^p-1}<\infty
\qquad\mathbb Q\text{-almost surely}.
\tag{76.7}
$$

The events (76.2) for positive integer choices of $C$ increase to an
event of probability one. Some finite positive choice therefore has
$q_G>0$. Continuity of $V$ and $v$ expresses $G$ by rational-time
inequalities, so $G$ is height-measurable. Conditioning on this proved
event changes the height law by the bounded density
$\mathbf1_G/q_G$; it is not an additional native premise.

For the scalar confinement law, direct substitution in (76.3) gives

$$
s(v(t))=\log(1+t)+\frac{Cp}{2m(1-p)}
                   (1-(1+t)^{p-1}).
\tag{76.8}
$$

Both $v$ and $s$ are strictly increasing onto $[0,\infty)$.
Since $v(t)\sim2mt$, (76.8) gives $s(u)=\log(1+u)+O(1)$.
Let $D_r=(-r,r)$, and let $\psi$ be the positive Dirichlet eigenfunction
of $\mathcal L_0=m\partial_{zz}-(z/2)\partial_z$ with eigenvalue
$-\nu$. Q (74.4)--(74.5) supply its smoothness on the closed interval,
zero endpoint values, boundedness and killed-semigroup identity.
For ordinary OU $O$ started at zero, with exit time $\sigma_r$ from
$D_r$, define

$$
Z_S=\mathbf1_{\{\sigma_r>S\}}e^{\nu S}
                         \frac{\psi(O_S)}{\psi(0)}.
\tag{76.9}
$$

This is a true mean-one martingale. Indeed, stopped Itô applied to
$e^{\nu(S\wedge\sigma_r)}\psi(O_{S\wedge\sigma_r})$
has zero drift. On a finite time interval its stochastic-integral
coefficient is bounded, and its value at an exit is zero.
The resulting zero extension is (76.9), has expectation one, and has
the martingale property. This is the classical killed-eigenfunction
Doob conditioning, using the eigenfunction identity already supplied
in Q Theorem 74.1 rather than a stationary initial distribution.

The consistent measures with densities $Z_n$ on $C([0,n])$ extend to
one infinite continuous-path law $Y$. Its restrictions to arbitrary
finite horizons have density (76.9). For every integer $n$, this law
assigns probability one to strict survival throughout $[0,n]$.
Hence, simultaneously at every real $S\ge0$, $|Y_S|<r$, and $Y_0=0$.
Define one infinite operational-time path law by

$$
B_u^\star=\rho(u)Y_{s(u)}\qquad(u\ge0).
\tag{76.10}
$$

In particular

$$
|B_u^\star|<r\sqrt{1+\tau(u)}
\quad\text{for every real }u\ge0.
\tag{76.11}
$$

We need a uniform finite-horizon density bound for (76.10).
Under ordinary standard Brownian $B$, make the inverse change
$R_S=B_{u(S)}/\rho(u(S))$, where $u=s^{-1}$.
The deterministic time-change Itô formula gives diffusion coefficient
$\sqrt{2m}$ and drift $-(1/2+\eta(S))R_S$, where

$$
\eta(s(u))=\frac{m}{v'(\tau(u))}-\frac12.
\tag{76.12}
$$

The function $\eta$ is smooth, bounded, nonpositive and increasing to
zero, because $v'(t)=2m+Cp(1+t)^{p-1}$ decreases to $2m$.
Substituting $dS=v'(t)dt/[2m(1+t)]$ gives

$$
\begin{aligned}
\int_0^\infty|\eta(S)|dS&=\frac{Cp}{4m(1-p)}<\infty,\\
\int_0^\infty\eta(S)^2dS&<\infty,&
\int_0^\infty|\eta'(S)|dS&<\infty.
\end{aligned}
\tag{76.13}
$$

The second bound follows from boundedness and the first; the third
follows from monotonicity and the finite endpoint values.
Stop both $R$ and $O$ on first exit from $D_r$. Their drift difference
is $\eta(S)z$, bounded on this stopped domain. On every finite horizon,
Novikov's condition therefore holds for the stopped Girsanov
exponential. It gives a true change of measure from stopped $R$ to
stopped $O$. For a surviving path $z$ started at zero, its log likelihood
through $S$ is

$$
\begin{aligned}
J_S
 &=\frac1{2m}\int_0^S\eta z\,dz
   +\frac1{4m}\int_0^S(\eta+\eta^2)z^2d\sigma\\
 &=\frac{\eta(S)z_S^2}{4m}
   -\frac12\int_0^S\eta\,d\sigma
   -\frac1{4m}\int_0^S\eta' z^2d\sigma
   +\frac1{4m}\int_0^S(\eta+\eta^2)z^2d\sigma.
\end{aligned}
\tag{76.14}
$$

The second equality is Itô integration by parts, using
$d\langle z\rangle=2m\,d\sigma$ and $z_0=0$.
Since $|z|<r$, (76.13) bounds $|J_S|$ by a deterministic constant
$J_0$, uniformly in $S$ and all surviving paths.
Multiplication by (76.9) bounds the density of $Y$ relative to $R$
by $e^{J_0}e^{\nu S}\|\psi\|_\infty/\psi(0)$.
This comparison also applies on the full unstopped path sigma-field:
$Y$ gives mass zero to exited paths, and on surviving paths stopped
and unstopped records coincide. Transport by the invertible
deterministic path change proves, for Wiener measure $\mathsf W_U$,

$$
\frac{d\operatorname{Law}(B^\star_{[0,U]})}{d\mathsf W_U}
\le C_0 e^{\nu s(U)}\qquad(U\ge0),
\tag{76.15}
$$

where $C_0=e^{J_0}\|\psi\|_\infty/\psi(0)$ can be enlarged to be at
least one. The stopping argument uses only bounded linear-drift
likelihoods; it needs no estimate of the boundary-singular logarithmic
derivative of $\psi$.

To reconstruct the full native vector, first take a reference product
space with the prescribed infinite $\mathbb Q$ height path $K$,
an independent standard Brownian $B$ in operational time, and an
independent standard Brownian $H$ in original time. Conditional on the
complete height path, write $a_s=a(K_s)$ and define

$$
\begin{aligned}
W_t&=\int_0^t\frac{\mathbf1_{\{a_s\ne0\}}}{\sqrt2 a_s}
                      \,d[B_{V(s)}]
       +\int_0^t\mathbf1_{\{a_s=0\}}\,dH_s,\\
q_t&=q_0+\sqrt2\int_0^t c_\kappa(K_s)\,dW_s.
\end{aligned}
\tag{76.16}
$$

The first integrand is defined as zero when $a_s=0$. Conditional on
$K$, the first integral exists in $L^2$ on each finite interval, since

$$
\int_0^t\frac{\mathbf1_{\{a_s\ne0\}}}{2a_s^2}\,dV(s)
=\int_0^t\mathbf1_{\{a_s\ne0\}}ds\le t.
\tag{76.17}
$$

The second, independent integral fills the complementary times.
Their sum is conditionally centered continuous Gaussian with
independent increments and quadratic variation $t$. Thus conditional
$W$ is standard Brownian with a law independent of $K$.
The pair $(K,q)$ consequently has exactly the original full
$\mathbb Q$ law of Q (41.1), (41.6), including all three phase coordinates.
Moreover stochastic-integral associativity gives

$$
e\cdot J_\kappa(q_t-q_0)
=\sqrt2\int_0^t a_s\,dW_s=B_{V(t)}.
\tag{76.18}
$$

Indeed $a_s\mathbf1_{\{a_s=0\}}=0$, and $dV=2a_s^2ds$ charges no
zero set of $a_s$. Hence the omitted integral
$\int_0^t\mathbf1_{\{a_s=0\}}d[B_{V(s)}]$ has zero quadratic
variation. This proves (76.18) even with clock plateaus.

These integrals can be realized as consistent measurable maps of the
input paths. For example, truncate the first integrand to
$\{|a_s|\ge1/n\}$; by (76.17) the omitted variance tends to zero.
Bounded predictable simple approximations, conditional Itô isometry
and the maximal inequality give convergence in probability uniformly
on every fixed integer interval. Choose a common subsequence on the
countably many intervals to obtain measurable continuous versions.
The bounded-coefficient integrals defining $q$ admit the same
construction. Their restriction through $T$ is measurable from
$(K_{[0,\infty)},B_{[0,2AT]},H_{[0,T]})$, since $V(t)\le2At$.
The versions agree on overlapping intervals, and all integral identities
above hold simultaneously at all real times on one reference set of
probability one.

Now change the input product law once, on the whole infinite space:
use independent $K\sim\mathbb Q(\,\cdot\mid G)$,
$B^\star$ from (76.10), and standard $H$, and apply the same maps
(76.16). For each fixed $T$, on the input sigma-field
$\sigma(K_{[0,\infty)},B_{[0,2AT]},H_{[0,T]})$, the new law has density
at most

$$
\frac{C_0}{q_G}e^{\nu s(2AT)}
\tag{76.19}
$$

relative to the reference product law, by (76.15).
All null sets involved in the finite-interval integral construction and
(76.18) therefore remain null. Taking the intersection over integer
intervals shows that the full infinite maps and their identities remain
well-defined under the changed law. Denote their output law by
$\mathsf V_\star$. Its height marginal is precisely
$\mathbb Q(\,\cdot\mid G)$, and its initial state is unchanged.
This is a full native vector law, rather than a law specified only for
its scalar projection.

The height remains in $I$ for every finite time. On $G$, for every real
$t\ge0$, (76.11), (76.18) and the increasing inverse $\tau$ give

$$
|X_t|=|B^\star_{V(t)}|
 <r\sqrt{1+\tau(V(t))}\le r\sqrt{1+t}.
\tag{76.20}
$$

The strict inequality holds simultaneously at every real operational
time under (76.11), so it also holds at every real original time,
including plateaus. The clock is still the actual $V(t)$; $v$ is only
a deterministic envelope on the positive-probability event $G$.
The product construction and its maps are fixed on the infinite space,
so no choice here depends on the terminal horizon.

Finally transport (76.19) by the full prefix map. Since its reference
output is $\mathbb Q_T$, the elementary pushforward density bound gives

$$
\frac{d(\mathsf V_\star)_T}{d\mathbb Q_T}
\le\frac{C_0}{q_G}e^{\nu s(2AT)}.
\tag{76.21}
$$

The exact ground-state identity from Q Definition 41.1, with its
cemetery convention, is

$$
\frac{d\mathbb Q_T}{d\mathbb P_T}
=\mathbf1_{\{\zeta>T\}}e^{\lambda T}
                         \frac{\phi(K_T)}{\phi(k_0)}.
\tag{76.22}
$$

Thus (76.4) holds with
$C_1=(C_0/q_G)\|\phi\|_\infty/\phi(k_0)\ge1$.
This is a finite deterministic density bound for every finite $T$ on
the literal full cemetery-inclusive prefix space. It proves absolute
continuity there. If $L_T=d(\mathsf V_\star)_T/d\mathbb P_T$, its
positive entropy part is integrable by the bound, and
$z\log z\ge-1/e$ controls the negative part. Consequently

$$
D((\mathsf V_\star)_T\Vert\mathbb P_T)
\le\lambda T+\nu s(2AT)+\log C_1<\infty.
\tag{76.23}
$$

Equations (76.20) and (76.23) establish every condition of
Definition 75.2. To identify the bounded error in (76.5), note that

$$
2mt\le v(t)\le(2m+Cp)t,
\qquad
\frac{2AT}{2m+Cp}\le\tau(2AT)\le\frac{A}{m}T.
\tag{76.24}
$$

Here concavity gives $(1+t)^p-1\le pt$.
Since $A\ge m>0$, these bounds and (76.8) imply
$s(2AT)=\log(1+T)+O(1)$ with no horizon dependence in the error.
This proves (76.5). Q Corollary 74.2 applies to the now established
member $\mathsf V_\star$ of exactly its class and gives the matching
liminf. Together with (76.5), it proves (76.1). $\square$

## 77. Sharp infimum over the same infinite-law class

**Corollary 77.1 (same-class sharp entropy coefficient).** Under exactly
Definition 75.1, let

$$
I_r(T)=\inf_{\mathsf V\in\mathcal C_{\mathrm{crit},r}}
                       D(\mathsf V_T\Vert\mathbb P_T).
\tag{77.1}
$$

Then the class is nonempty and

$$
\lim_{T\to\infty}\frac{I_r(T)-\lambda T}{\log(1+T)}
=\nu(m,r).
\tag{77.2}
$$

In addition,

$$
\begin{aligned}
\inf_{\mathsf V\in\mathcal C_{\mathrm{crit},r}}
 \liminf_{T\to\infty}
 \frac{D(\mathsf V_T\Vert\mathbb P_T)-\lambda T}{\log(1+T)}
 &=\nu(m,r),\\
\inf_{\mathsf V\in\mathcal C_{\mathrm{crit},r}}
 \limsup_{T\to\infty}
 \frac{D(\mathsf V_T\Vert\mathbb P_T)-\lambda T}{\log(1+T)}
 &=\nu(m,r).
\end{aligned}
\tag{77.3}
$$

Proof. Put $E_T=\{\zeta>T\}\cap
\{|X_t|<r\sqrt{1+t}\text{ for every real }0\le t\le T\}$,
exactly as in Q Corollary 74.2. For every
$\mathsf V\in\mathcal C_{\mathrm{crit},r}$,
$\mathsf V_T(E_T)=1$. The pointwise support entropy inequality used
in that corollary gives, for each finite $T$ and every such law,

$$
D(\mathsf V_T\Vert\mathbb P_T)\ge-\log\mathbb P(E_T).
\tag{77.4}
$$

For completeness its support form follows by writing
$\mathbb P_T(\,\cdot\mid E_T)$ on $E_T$: divergence relative to
$\mathbb P_T$ is divergence relative to this conditional law minus
$\log\mathbb P(E_T)$, and the first divergence is nonnegative.
Here $\mathbb P(E_T)>0$ follows also from the finite-prefix absolute
continuity of the supported law in Theorem 76.1.
Taking the infimum in the finite-$T$ inequality, and bounding above
by this same single law $\mathsf V_\star$, yields

$$
-\log\mathbb P(E_T)\le I_r(T)
 \le D((\mathsf V_\star)_T\Vert\mathbb P_T).
\tag{77.5}
$$

Q (74.10) evaluates the normalized limit of the left side, and
Theorem 76.1 evaluates that of the right side. Subtracting
$\lambda T$, dividing by $\log(1+T)>0$ and squeezing proves (77.2).
No infimum-limit interchange is used. Q (74.11) bounds every member's
liminf from below by $\nu$, hence also its limsup. The law
$\mathsf V_\star$ has a limit equal to $\nu$, proving both equalities
in (77.3). All infima are over Definition 75.2's same class of
consistent infinite laws. The constructed member conditions its height
on $G$; neither (77.2) nor (77.3) asserts attainment in a class with an
extra requirement that the height marginal remain unconditioned
$\mathbb Q$. $\square$

## 追加锚（本行以下为增补区）
