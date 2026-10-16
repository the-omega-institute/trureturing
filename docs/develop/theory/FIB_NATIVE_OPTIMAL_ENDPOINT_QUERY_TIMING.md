# Optimal endpoint-height query timing in the stationary native source

## 1. The exact native source

**Definition 1.1 (fixed data, full family and actual phases).** Fix
$0<Z<1$, $H=(1-Z)/2$, an interval $I=(l,u)\Subset(0,H)$,
$\varepsilon>0$ and a known horizon $\tau>0$. Put $d=u-l$ and

$$
\phi(k)=\sqrt{\frac2d}\sin\frac{\pi(k-l)}d,\qquad
\lambda=\frac{\varepsilon^2\pi^2}{d^2},\qquad
\pi(dk)=\phi(k)^2dk,\qquad \sigma=\sqrt2\varepsilon.
\tag{1.1}
$$

$\pi(dk)$ denotes the height probability; the $\pi$ in scalar and
trigonometric constants is the circular constant. Retain the
entire fixed two-sided admissible family
$\mathcal K=[-\kappa_*,\kappa_*]$ of Definitions 35.1 and 55.1 of
[Native long-time phase diffusion](FIB_NATIVE_LONG_TIME_PHASE_DIFFUSION.md),
abbreviated L. In particular, the original native probabilities are
strictly positive on a slightly larger height interval, the original
rational denominators have a fixed positive margin, and
$\kappa_*<l/2$ and $|\kappa|<H$ throughout this family. No parameter
interval below depends on a budget or a time window.

For $\alpha_\kappa=\kappa+\kappa^2/H$ and $s_\kappa=H+\kappa$, the
original coefficients, in the notation of L, are

$$
\begin{aligned}
A_\kappa(k)&=\frac{(k-2\kappa)(s_\kappa-k)}{2H(k-\alpha_\kappa)},\\
B_\kappa(k)&=-\frac{k(k-2\kappa)}{2H(k-\alpha_\kappa)},\\
b_\kappa(k)&=\frac{s_\kappa-k}{H(k-\alpha_\kappa)}.
\end{aligned}
\tag{1.2}
$$

Use the single conservative stationary-height probability
$\mathbf Q_\kappa$ with known initial original phases
$(\theta_0,v_0,D_0)$, unobserved $K_0\sim\pi$, and equations

$$
\begin{aligned}
dK_t&=\mu(K_t)dt+\sigma dW_t^1,
&\mu(k)&=\sigma^2\frac{\phi'(k)}{\phi(k)},\\
d\theta_t&=\sqrt2 A_\kappa(K_t)dW_t^2,
&dv_t&=\sqrt2 B_\kappa(K_t)dW_t^2,\\
dD_t&=\sqrt2\kappa b_\kappa(K_t)dW_t^2.
\end{aligned}
\tag{1.3}
$$

The two drivers are independent, and $W^2$ is independent of the complete
height path. Original phases are reduced modulo $2\pi$ when observed.
Their real integrals in (1.3) are mathematical lifts with the prescribed
initial values. The phase coefficients have no phase dependence; the
Itô and Stratonovich phase equations agree. The original clock and all
coefficients are unchanged.

At actual $\kappa=0$,
$A_0=(H-k)/(2H)$, $B_0=-k/(2H)$ and $D_t=D_0$. There are two moving
original phases. A moving comparison coordinate $x$ at zero is not part
of this source or its observations. Only the common $(K,v)$ marginal
will enter the risk theorem.

**Proposition 1.2 (source weights, both faces and a stationary moment).**
Let $h_I(t;x,z)$ be the raw $dz$ kernel of height Brownian motion with
variance rate $\sigma^2$, killed at both $l$ and $u$. The height kernel
in (1.3) is exactly

$$
Q_t(x,dz)=e^{\lambda t}\frac{\phi(z)}{\phi(x)}h_I(t;x,z)dz.
\tag{1.4}
$$

It is conservative, has invariant probability $\pi$, and its finite
paths remain in $I$. With fixed initial height $x$, its derivative
relative to the Brownian path law restricted to survival through $t$ is
$e^{\lambda t}\phi(K_t)/\phi(x)$. With initial law $\pi$, its height
path density relative to Lebesgue-start Brownian height is therefore

$$
e^{\lambda t}\phi(K_0)\phi(K_t)
\mathbf1_{\{K_r\in I\text{ for every }0\le r\le t\}}.
\tag{1.5}
$$

For $0\le s\le t\le\tau$, there is a fixed constant $C_\tau$ such that

$$
\mathbf E_\pi\mu(K)^2=\sigma^4\int_I\phi'(k)^2dk<\infty,
\qquad
\mathbf E|K_t-K_s|^2\le C_\tau(t-s).
\tag{1.6}
$$

Proof. The Dirichlet sine kernel satisfies
$\int_Ih_I(t;x,z)\phi(z)dz=e^{-\lambda t}\phi(x)$.
Consequently (1.4) integrates to one. Cancellation of its middle
$\phi$ factors gives the semigroup identity. Symmetry of $h_I$ gives
detailed balance with $\phi(x)^2dx$, whose mass is one. The Doob
path derivative follows first on cylinder events by the same
cancellation and then on path events by a monotone class argument.
It assigns mass one to continuous paths surviving each finite horizon;
countably many horizons give the conservative interior realization.
The product rule applied to $\phi^{-1}(\varepsilon^2\partial_k^2+
\lambda)(\phi f)$ gives exactly the height generator in (1.3).
Multiplication by the initial density $\phi(K_0)^2$ proves (1.5).
This change of measure uses only height and preserves the independent
phase driver.

The square of $\mu$ multiplied by $\phi^2$ cancels its apparent
endpoint singularities and gives the first identity in (1.6).
Writing the height increment as a Brownian increment plus its drift
integral, the inequality $(a+b)^2\le2a^2+2b^2$, Cauchy--Schwarz and
stationarity give

$$
\mathbf E|K_t-K_s|^2
\le2\sigma^2(t-s)+2(t-s)^2\mathbf E_\pi\mu(K)^2.
\tag{1.7}
$$

This proves (1.6) without removing either height boundary layer.
$\square$

The stationary Q source is a stipulated probability, not a native
preparation service. To fix the source distinction explicitly, let
$\mathbb P_\rho$ be the original law with height equation $dK=\sigma dW^1$
and the same phase equations, killed at
$\zeta=\inf\{t:K_t\notin I\}$, with initial height probability $\rho$.
Let $\mathbb Q_\rho$ be its Q law,
$S_k(t)=\mathbb P_k(\zeta>t)$ and
$S_\rho(T)=\int_I S_k(T)\rho(dk)$. Then on full paths

$$
\frac{d\mathbb P_\rho(\,\cdot\,,\zeta>T)}{d\mathbb Q_\rho}
=e^{-\lambda T}\frac{\phi(K_0)}{\phi(K_T)}.
\tag{1.8}
$$

On a prefix through $r\le T$, conditioning that mixture on survival
through $T$ instead gives the derivative

$$
\frac{e^{-\lambda r}\phi(K_0)S_{K_r}(T-r)}
     {\phi(K_r)S_\rho(T)}.
\tag{1.9}
$$

These identities follow by inverting the fixed-start derivative above
and using the killed Markov property. Conditioning each fixed-start
law before mixing replaces the denominator by $S_{K_0}(T)$, a
different convention. None of these source weights is silently
removed in the present theorem, and no unchanged risk theorem for
those different laws is asserted.

**Lemma 1.3 (uniform native variance margins).** Define

$$
a_\kappa(k)=2B_\kappa(k)^2.
\tag{1.10}
$$

On the full closed rectangle $\mathcal K\times[l,u]$ there are
$a_->0$, $a_+<\infty$ and $c_a>0$ with

$$
a_-\le a_\kappa\le a_+,\qquad a_\kappa'\ge c_a.
\tag{1.11}
$$

All derivatives needed below have common finite bounds.

Proof. Polynomial division and differentiation of (1.2) give

$$
\begin{aligned}
B_\kappa(k)&=-\frac1{2H}\left(k+\alpha_\kappa-2\kappa+
\frac{\alpha_\kappa(\alpha_\kappa-2\kappa)}{k-\alpha_\kappa}\right),\\
B_\kappa'(k)&=-\frac1{2H}\left(1-
\frac{\alpha_\kappa(\alpha_\kappa-2\kappa)}{(k-\alpha_\kappa)^2}\right),\\
\alpha_\kappa(\alpha_\kappa-2\kappa)
&=\kappa^2(\kappa^2/H^2-1)\le0.
\end{aligned}
\tag{1.12}
$$

The retained margins give $k-2\kappa>0$ and $k-\alpha_\kappa>0$.
For example, at positive $\kappa<l/2<H/2$ one has
$\alpha_\kappa<3l/4$, while at negative $\kappa$ it is negative.
Thus $B_\kappa<0$ and $B_\kappa'\le-1/(2H)$.
Compactness gives (1.11), since $a_\kappa'=4B_\kappa B_\kappa'$.
The rational denominator stays uniformly away from zero, which gives
the derivative bounds. This uses the entire already fixed family.
$\square$

## 2. The full lawful finite-query class

**Definition 2.1 (policy, data, loss and infima).** A policy and estimator
share an independent prechosen seed $U$, independent of the whole source
in (1.3). No density or nondegeneracy of its distribution is required.
All decision maps are Borel maps of the seed and finite queried history;
the same arguments apply to any independent seed realization with these
measurability properties. Independent estimator randomization can be
included in this seed.

Set $T_0=0$, whose original phase is known. Immediately after query
$j-1$, choose $T_j$ using only $U$ and the preceding queried timestamps
and wrapped values $e^{iv_{T_i}}$, $i<j$. That next time is fixed before
any intervening information is acquired. The policy makes $M$ actual
positive-time queries, with

$$
1\le M\le n,\qquad 0=T_0<T_1<\cdots<T_M=\tau.
\tag{2.1}
$$

The estimator receives exactly $U$ and this finite time/value record.
Its target is the actual $K_\tau$, with squared loss under
$\mathbf Q_\kappa$. Write

$$
\begin{aligned}
\mathcal R_\kappa(\mathcal P,g)
 &=\mathbf E_{\mathbf Q_\kappa}(g-K_\tau)^2,\\
R^*_{n,\kappa}
 &=\inf_{\mathcal P,g:\,M\le n}\mathcal R_\kappa(\mathcal P,g),\\
R^{=}_{n,\kappa}
 &=\inf_{\mathcal P,g:\,M=n}\mathcal R_\kappa(\mathcal P,g).
\end{aligned}
\tag{2.2}
$$

The known parameters, including $\kappa$, may enter both policy and
estimator. Deterministic nonuniform, adaptive, randomized and
variable-count policies are all included. For each fixed policy the
Bayes estimator is the conditional mean and its risk is the expected
posterior variance. Clipping any estimator to $[l,u]$ decreases loss,
so all infima can be taken over such bounded estimators.

There is no intermediate monitoring, unqueried-path hitting trigger,
height, driver, bridge, unwrapped increment, winding, external stop tag,
future-survival information, unknown-parameter oracle, extra phase or
additional preparation in the data. The terminal count is the length
of the queried record, not an independent observation. Each finite
spacing must be strictly positive. Arbitrarily small positive real
spacings are lawful; time precision has no charge in this query-count
model. No extra actual query is free.

**Lemma 2.2 (completion and exact padding without a class restriction).**
An almost surely lawful policy has a version of the same risk with
lawful decisions on every valid partial record generated by its
recursion, including records of probability zero. Moreover, for every $n\ge1$,

$$
R^*_{n,\kappa}=R^{=}_{n,\kappa}.
\tag{2.3}
$$

Proof. Extend a partially defined decision map by a Borel default if
necessary. At the first proposed decision that would violate the
remaining positive-time order, budget or required terminal query,
replace all remaining decisions by a deterministic equally spaced
schedule ending at $\tau$. For an exactly-$n$ policy this requires
$T_j\in(T_{j-1},\tau)$ when $j<n$ and $T_n=\tau$; violations are
Borel tests of the current record. For a variable-count policy,
admissible continuation or selection of the terminal query is tested
in the same way, with a forced terminal query at the last available
slot. The replacement uses only the permitted record. It occurs on a
source-null event for an almost surely lawful original policy, and
therefore preserves its risk. It ensures a common valid record space
even at histories of probability zero. This is a completion of every
lawful policy, with no continuity assumption on its decisions.

Now simulate an at-most-$n$ policy. Execute each intended query that
is strictly before $\tau$. When it first schedules its final query
$\tau$, let $q$ positive queries have occurred, the current time be
$t$ and $r=n-q\ge1$. Replace its pending last interval by queries at

$$
t+\frac{i}{r}(\tau-t),\qquad i=1,\ldots,r.
\tag{2.4}
$$

Ignore the first $r-1$ added values and pass only the value at $\tau$
to the original estimator. The decision to schedule $\tau$ was already
made at $t$, so all the inserted times are permissible. The original
history, the start of padding and its remaining plan can be reconstructed
recursively from the seed and record. The resulting policy and estimator
are Borel, use exactly $n$ actual positive queries, and have the same
risk. Sampling does not change the source path. This proves
$R^{=}\le R^*$; the reverse inequality is class inclusion. $\square$

## 3. The native scale information and its coefficient

**Definition 3.1 (information at a frozen height).** Put

$$
L_\kappa=\frac{a_\kappa'}{a_\kappa},\qquad
j_\kappa=\frac12 L_\kappa^2,\qquad
w_\kappa=\frac1{j_\kappa}
=2\left(\frac{a_\kappa}{a_\kappa'}\right)^2
=\frac{B_\kappa^2}{2(B_\kappa')^2},\qquad
C_\kappa=\int_I w_\kappa(k)\pi(dk).
\tag{3.1}
$$

Write $p_V(y)=(2\pi V)^{-1/2}\exp[-y^2/(2V)]$ for $V>0$.
The meaning of $j$ is elementary: for $Y\sim N(0,V(z))$ its $z$ score is

$$
\partial_z\log p_{V(z)}(Y)
=\frac{V'(z)}{2V(z)}\left(\frac{Y^2}{V(z)}-1\right),
\quad
\mathbf E\partial_z\log p_{V(z)}=0,
\quad
\mathbf E(\partial_z\log p_{V(z)})^2=\frac{V'(z)^2}{2V(z)^2}.
\tag{3.2}
$$

These follow by differentiating the normal density and using its second
and fourth moments. A frozen-height scale observation with
$V(z)=\delta a_\kappa(z)$ has information $j_\kappa(z)$ for every
$\delta>0$. This observation does not assert that zero-length
increments supply data.

**Proposition 3.2 (explicit full-family coefficient and actual zero).**
The functions $L,j,w,w'$ have common finite bounds on the original
rectangle, and $j,w$ have positive lower bounds. The coefficient is
continuous in $\kappa$ and bounded above and below by positive constants.
Write $0<w_-\le w_\kappa(k)\le w_+<\infty$ for fixed common bounds.
In original native quantities,

$$
C_\kappa=\frac12\int_l^u
\left[\frac{k(k-2\kappa)(k-\alpha_\kappa)}
{(k-\alpha_\kappa)^2-\alpha_\kappa(\alpha_\kappa-2\kappa)}\right]^2
\phi(k)^2dk.
\tag{3.3}
$$

On the actual zero leaf, with $k_c=(l+u)/2$,

$$
w_0(k)=\frac{k^2}{2},\qquad
C_0=\frac12\int_I k^2\pi(dk)
=\frac{k_c^2}{2}+d^2\left(\frac1{24}-\frac1{4\pi^2}\right).
\tag{3.4}
$$

Proof. Lemma 1.3 bounds $a,a'$ above and away from zero and bounds
their derivatives, proving the assertions for $L,j,w,w'$.
The denominator in (3.3) is positive by (1.12), and substituting
$B/B'$ proves that formula. Integration against the fixed probability
gives continuity and positive uniform bounds. At zero $B_0/B_0'=k$.
For completeness, in $x=(k-l)/d$ the prior is
$2\sin^2(\pi x)dx=(1-\cos(2\pi x))dx$. Reflection about $1/2$ gives
mean $1/2$, and two integrations by parts give

$$
\int_0^1(x-1/2)^2(1-\cos(2\pi x))dx
=\frac1{12}-\frac1{2\pi^2}.
\tag{3.5}
$$

Indeed the polynomial integral is $1/12$ and its cosine integral is
$1/(2\pi^2)$. Rescaling proves (3.4). $\square$

The displayed leading coefficient has no additional dependence on the
fixed positive $\tau$ or $\varepsilon$. All remainder constants and
the domain of the theorem retain both; no simultaneous zero-horizon
or zero-height-diffusion limit is asserted.

## 4. Actual positive-spacing wrapped queries attain the coefficient

**Definition 4.1 (a counted late cluster and its estimator).** For $n\ge2$
put $m=n-1$, $h_n=\tau/n^3$ and $\delta_n=h_n/m$. Query at

$$
T_j=\tau-h_n+(j-1)\delta_n,\qquad j=1,\ldots,n.
\tag{4.1}
$$

Thus the first positive query costs one baseline and the remaining
$m$ queries give $m$ short intervals. Every finite spacing is positive,
$T_1>0$ and $T_n=\tau$. From the original wrapped values form

$$
\begin{aligned}
z_j&=\operatorname{Arg}\left(e^{iv_{T_j}}\overline{e^{iv_{T_{j-1}}}}\right)
\in[-\pi,\pi),\qquad 2\le j\le n,\\
S_n&=\frac1{m\delta_n}\sum_{j=2}^n z_j^2,\\
F_\kappa(s)&=a_\kappa^{-1}\left(
\operatorname{clip}_{[a_\kappa(l),a_\kappa(u)]}(s)\right),
\qquad \widehat K_{n,\kappa}=F_\kappa(S_n).
\end{aligned}
\tag{4.2}
$$

The inverse exists by (1.11) and is taken into $[l,u]$. This estimator
is Borel and bounded. The long first interval supplies only the late
wrapped baseline; its winding is immaterial to the group differences.
For $n=1$ query only $\tau$ and use, for example, the prior mean.

**Theorem 4.2 (uniform upper limit with the actual wrapped record).**
The policies and estimators in Definition 4.1 satisfy

$$
\sup_{\kappa\in\mathcal K}
\left|n\mathbf E(\widehat K_{n,\kappa}-K_\tau)^2-C_\kappa\right|
\longrightarrow0.
\tag{4.3}
$$

Proof. Temporarily use real short increments as analysis variables.
Conditional on the entire height path, their variances are
$\delta_n A_j$, where, reindexing the $m$ short intervals,

$$
A_j=\delta_n^{-1}\int_{T_j}^{T_{j+1}}a_\kappa(K_s)ds,
\qquad j=1,\ldots,m.
\tag{4.4}
$$

The exact joint law with height can be represented using independent
standard normals $Z_1,\ldots,Z_m$ independent of height. Define

$$
S_{\rm real}=\frac1m\sum_{j=1}^m A_jZ_j^2,\qquad
S_{\rm fr}=a_\kappa(K_\tau)\frac1m\sum_{j=1}^m Z_j^2.
\tag{4.5}
$$

These are comparison variables, not additional estimator inputs.
By (1.6) and the uniform Lipschitz bound for $a$,
$\mathbf E|A_j-a(K_\tau)|^2\le C_\tau h_n$. Jensen's inequality
and $\mathbf EZ_j^4=3$ imply

$$
\mathbf E|S_{\rm real}-S_{\rm fr}|^2
\le\frac3m\sum_{j=1}^m\mathbf E|A_j-a(K_\tau)|^2
\le C_\tau h_n.
\tag{4.6}
$$

The maps $F_\kappa$ are uniformly Lipschitz, so the same bound holds
for their outputs.

Let $D_m=m^{-1}\sum_{j=1}^m(Z_j^2-1)$. Independence and the Gaussian
moments give

$$
\mathbf ED_m^2=\frac2m,\qquad
\mathbf ED_m^4=\frac{12}{m^2}+\frac{48}{m^3},\qquad
\mathbf E|D_m|^3\le C m^{-3/2}.
\tag{4.7}
$$

For example, a centered $Z^2-1$ has second moment $2$ and fourth
moment $60$; expanding the fourth power of its sum gives (4.7).
Fix an interior compact height interval $J\Subset I$. Uniformly for
$k\in J$ and $\kappa\in\mathcal K$, the distance of $a_\kappa(k)$
from both clipping thresholds is bounded below. Taylor's formula for
the inverse, whose second derivative is uniformly bounded there, gives
for some fixed $c_J>0$

$$
F_\kappa(a_\kappa(k)(1+D_m))-k
=\frac{a_\kappa(k)}{a_\kappa'(k)}D_m+O_J(D_m^2)
\quad\text{on }|D_m|\le c_J.
\tag{4.8}
$$

Globally the absolute value on the left is at most $C|D_m|$,
including the clipping region. On $|D_m|>c_J$,
$m\mathbf E[D_m^2\mathbf1_{\{|D_m|>c_J\}}]
\le m\mathbf ED_m^4/c_J^2\to0$.
The cubic cross term in the squared Taylor formula, multiplied by
$m$, is $O_J(m^{-1/2})$, and its fourth-order term is $O_J(m^{-1})$.
Consequently

$$
m\mathbf E\left(F_\kappa(a_\kappa(k)(1+D_m))-k\right)^2
\longrightarrow2\left(\frac{a_\kappa(k)}{a_\kappa'(k)}\right)^2
=w_\kappa(k)
\tag{4.9}
$$

uniformly on $\mathcal K\times J$. For every $k\in[l,u]$ the same
left side is bounded by a common constant, using the global Lipschitz
bound and (4.7). The two boundary layers have $\pi$ mass tending to
zero as $J$ increases to $I$, independently of $\kappa$. Integrating
(4.9) over $K_\tau\sim\pi$, first on $J$ and then removing both
layers, proves

$$
\sup_\kappa\left|m\mathbf E(F_\kappa(S_{\rm fr})-K_\tau)^2
-C_\kappa\right|\longrightarrow0.
\tag{4.10}
$$

In particular this frozen risk is $O(m^{-1})$. By (4.6) and
Cauchy--Schwarz, the absolute difference between the real-increment
risk and the frozen risk is bounded by
$C_\tau(\sqrt{h_n/m}+h_n)$. Multiplication by $n$ sends that
difference to zero, since $nh_n\to0$ and $n/m\to1$.

For the actual estimator, the exact conditional normal law bounds
the chance that any short real increment has absolute value at least
$\pi$ by

$$
2m\exp\left(-\frac{\pi^2}{2a_+\delta_n}\right).
\tag{4.11}
$$

Outside this event (4.2) equals the real-increment estimator. Both
estimates and the target lie in $[l,u]$, so their expected squared-loss
difference is at most $d^2$ times (4.11). Its product with $n$ also
tends to zero, uniformly in $\kappa$. Combining this with (4.10)
proves (4.3). Every experiment used in (4.1)--(4.2) has strictly
positive spacings; the order $n^{-4}$ of the short spacing is not
replaced by zero at any finite budget. $\square$

## 5. A comparison containing every Borel queried history

**Lemma 5.1 (exact final bridge and inclusion of the original data).**
Fix any exactly-$n$ policy completed as in Lemma 2.2 and any deterministic
$0<h<\tau$. Put $s=\tau-h$, $x=K_s$, $z=K_\tau$ and

$$
b_r=K_{s+r}-x-\frac rh(z-x),\qquad
K^z_r=x+\frac rh(z-x)+b_r,\qquad0\le r\le h.
\tag{5.1}
$$

Let the enlarged past be $P_s=(U,K_{[0,s]},W^2_{[0,s]})$. Given this
past, the joint height kernel in coordinates $(b,z)$ is exactly

$$
\beta_h(db)\,\gamma_h(z-x)\,e^{\lambda h}\frac{\phi(z)}{\phi(x)}
\mathbf1_{\{K^z_r\in I\ \forall r\in[0,h]\}}\,dz,
\qquad
\gamma_h(v)=\frac{e^{-v^2/(2\sigma^2h)}}{\sqrt{2\pi\sigma^2h}},
\tag{5.2}
$$

where $\beta_h$ is centered Brownian bridge measure of variance rate
$\sigma^2$. Enlarge further by revealing the real phase increment
from $s$ to the first actual query after $s$ and the real increments
between subsequent actual queries. These enlarged data determine the
entire original seed/time/wrapped-value record. Their target remains
$z$; it is not revealed. There are between one and $n$ future normal
observations in this comparison, including all crossing cases.

Proof. Ordinary Brownian height on $[s,s+h]$ decomposes into its
endpoint displacement and the residual bridge in (5.1). Their covariance
is zero, so joint Gaussianity gives independence and the reference
kernel $\beta_h(db)\gamma_h(z-x)dz$. Killing imposes the indicator
for both original faces. The exact fixed-start Q derivative in
Proposition 1.2 supplies $e^{\lambda h}\phi(z)/\phi(x)$, proving
(5.2). The height Markov property and independence of $U,W^2$ show
that conditioning on $P_s$ introduces no further factor. Its past
law is its actual stationary Q law, including its original initial
height weight.

The phase past is a causal Borel function of the revealed path
coordinates, modulo one null set. To specify a version, approximate
$\sqrt2\int_0^tB_\kappa(K_r)dW_r^2$ by left-step integrals on dyadic
partitions of a bounded time interval. Lemma 1.3, (1.6), the isometry
and the maximal inequality bound the expected squared uniform error
by $C2^{-m}$ at level $m$. Markov's inequality at threshold
$2^{-m/8}$ and Borel--Cantelli give uniform almost sure convergence.
The step integrals are Borel functions of the paths and their prefixes;
their continuous uniform limit, with a fixed default on failure, is
the required version. The same construction over countably many
bounded horizons suffices. This is a reconstruction only within the
comparison data.

Thus $P_s$ permits recursive simulation of the original policy through
every query at or before $s$. Let $q$ be their number. It also determines
the already chosen next endpoint. Exactly $N=n-q$ future queries
remain, with $1\le N\le n$; $N$ is fixed on each $P_s$ fiber. A query
exactly at $s$ belongs to the revealed past. If an original interval
straddles $s$, its pre-$s$ phase portion is known and the first revealed
future increment is just its remaining portion. This gives one future
increment for that original query, not two. If there is no query at
$s$, its phase value is known from $P_s$ and is not a new original
query. The successive future increments give the wrapped queried
values, and hence every later decision, recursively. This covers
$q=0$, $q=n-1$ and all intermediate cases. Information inclusion
therefore has the direction

$$
\inf_g\mathcal R_\kappa(\mathcal P,g)
\ \ge\ \text{Bayes risk with the enlarged data}.
\tag{5.3}
$$

All revealed coordinates are random variables on the unchanged source.
They are a lower-bound device, not an observation port in Definition
2.1. $\square$

**Lemma 5.2 (sequential likelihood and fixed-record scores).** Conditional
on $P_s,b,z$, use the future real increments $y_1,\ldots,y_N$ as
coordinates. Put $t_0=s$. Recursively each $t_i$ is a Borel function
of $P_s$ and $y_1,\ldots,y_{i-1}$, and $t_N=\tau$. The likelihood is

$$
\mathcal L_z(y)=\prod_{i=1}^N p_{V_i(z)}(y_i),\qquad
V_i(z)=\int_{t_{i-1}}^{t_i}a_\kappa(K^z_{u-s})du.
\tag{5.4}
$$

It is relative to $N$-dimensional Lebesgue measure on each past fiber
and integrates to one. Holding $P_s,b,y$ fixed holds every timestamp,
branch and the count $N$ fixed as $z$ varies. In an interior region
where $K^z$ stays in $I$, its score is $\sum_i U_i$, where

$$
\begin{aligned}
V_i'(z)&=\int_{t_{i-1}}^{t_i}a_\kappa'(K^z_{u-s})\frac{u-s}{h}du,\\
U_i&=\frac{V_i'}{2V_i}\left(\frac{y_i^2}{V_i}-1\right),\\
\mathbf E(U_i\mid P_s,b,z,y_{<i})&=0,\qquad
\mathbf E(U_i^2\mid P_s,b,z,y_{<i})=\frac{V_i'^2}{2V_i^2}\le C.
\end{aligned}
\tag{5.5}
$$

All endpoint derivatives hold the known $\kappa$ fixed. These assertions
require no continuity or differentiability of a timing
function in its history variables, and are uniform in all positive
spacings.

Proof. Conditional on the full height path, $W^2$ remains Brownian.
Enlarge its filtration initially by this independent path and the seed.
Each query time is a stopping time in that filtration: its next endpoint
is already measurable at the preceding query and is later than it.
After conditioning on $P_s,b,z$, the future height coefficient is
deterministic and the future driver after $s$ is still Brownian,
independent of its past. At each subsequent query, Brownian strong
Markov independence and the endpoint already chosen at that query
give the centered normal kernel with variance in (5.4). Conditioning
further down to the preceding queried record leaves that same kernel,
because its variance is a function of just that record and the fixed
height. Induction proves the product formula. Repeated integration
from the last coordinate backward gives mass one, even though the
variances and endpoints depend on preceding coordinates. One is not
conditioning on a whole endogenous vector of timestamps and asserting
independent increments afterward.

The policy uses the reconstructed wrapped values from the fixed past
and preceding $y$ values. It does not use $z$. Thus fixed $P_s,b,y$
fixes all integration endpoints in (5.4). Differentiation in $z$
gives (5.5) and (3.2) gives its conditional moments. The completed
policy is valid at every such history, so no $z$-dependent record-space
boundary appears. Finally
$V_i\ge a_-(t_i-t_{i-1})$ and
$|V_i'|\le C(t_i-t_{i-1})$, giving the uniform bound in (5.5) even
for arbitrarily small spacings. The $U_i$ are martingale differences
in the sequential record. Hence their cross moments vanish and

$$
\int\left(\sum_i U_i\right)^2\mathcal L_z(y)dy\le Cn,
\qquad
\int|\partial_z\mathcal L_z(y)|dy\le C\sqrt n.
\tag{5.6}
$$

The second bound follows by Cauchy--Schwarz. In particular the
likelihood derivatives are integrable. For fixed record the density
is smooth in $z$ on interior compact supports, irrespective of its
mere Borel dependence on $y$. Integrating (5.6) over a compact $z$
support justifies Fubini and differentiation in the integrated
one-dimensional identities below. $\square$

## 6. Weighted information on a dominated part of the same source

**Lemma 6.1 (cutoffs, exact endpoint score and recovered mass).** Fix
$0<\eta<d/8$. Choose smooth $0\le\chi_\eta\le1$, supported where
$\operatorname{dist}(x,\partial I)\ge\eta$ and equal to one where
that distance is at least $2\eta$. Choose smooth $0\le\rho_\eta\le1$
equal to one on $|v|\le\eta/8$ and supported in $|v|<\eta/4$.
Multiply the actual joint law in Lemmas 5.1--5.2 by

$$
\chi_\eta(x)\,
\mathbf1_{\{\sup_{r\le h}|b_r|\le\eta/4\}}\,
\rho_\eta(z-x)^2
\tag{6.1}
$$

to obtain a subprobability $\nu=\nu_{h,\eta,\kappa}$. Its record
coordinates also depend on the chosen policy. It is dominated
by the original joint law with target and enlarged data. On its
density support every interpolated height stays at distance at least
$\eta/2$ from both faces. Its full score at fixed enlarged record is
$S=S_0+\sum_iU_i$, where

$$
S_0=-\frac{z-x}{\sigma^2h}+\frac{\phi'(z)}{\phi(z)}
+2\frac{\rho_\eta'(z-x)}{\rho_\eta(z-x)}.
\tag{6.2}
$$

For all sufficiently small $h>0$, independently of the policy, seed
law and parameter,

$$
\int S_0^2d\nu\le\frac{C_\eta}{h},\qquad
\int M_hd\nu\le C_\eta\sqrt h,
\qquad M_h=\sup_{0\le r\le h}|K^z_r-z|.
\tag{6.3}
$$

Define $A_{h,\eta,\kappa}=\int w_\kappa(z)d\nu$. It is independent
of the chosen policy and

$$
A_{h,\eta,\kappa}\longrightarrow
A_{\eta,\kappa}:=\int_I\chi_\eta(k)w_\kappa(k)\pi(dk)
\tag{6.4}
$$

uniformly over the entire original family as $h\downarrow0$. For any
fixed nonzero $\chi_\eta$, this limit has a common positive lower
bound.

Proof. On (6.1), the linear displacement from $x$ is at most $\eta/4$
and the bridge displacement is at most $\eta/4$. Both faces are
therefore avoided with the indicated margin. In a neighborhood of the
$z$ support the survival indicator in (5.2) is identically one.
The bridge cutoff and $\chi_\eta(x)$ have zero $z$ derivative in
these coordinates. Differentiating the remaining endpoint density
gives exactly (6.2), including the Q factor $\phi'/\phi$.

The expression involving $\rho_\eta'/\rho_\eta$ is used only where
$\rho_\eta>0$; its integrated square cancels the factor $\rho_\eta^2$
and leaves $4\rho_\eta'^2$. All $\phi$ ratios and log derivatives
are bounded on the relevant interior compact sets. Integrating the
Gaussian displacement square gives $O(h)$ and hence $O(h^{-1})$
for the first term of (6.2). The other terms are bounded in integrated
square by constants depending on $\eta$; taking $h\le1$ proves the
first bound in (6.3). At zeros of the cutoff its density derivative
is understood as $2\rho_\eta\rho_\eta'$, so no division is needed.

Write the bridge as $\sigma(W_r-rW_h/h)$. The Brownian maximal
inequality gives $\int\sup|b|^2d\beta_h\le C\sigma^2h$.
Also $M_h\le|z-x|+\sup|b|$. The endpoint Q weight is bounded on
the cutoff by a constant times the Gaussian/bridge reference.
The observation likelihood integrates to one, so these two reference
moment bounds prove the second part of (6.3).

In fact integrating out all sequential observations and then the past
except for $x\sim\pi$ yields the explicit policy-independent formula

$$
\begin{aligned}
A_{h,\eta,\kappa}
={}&e^{\lambda h}\beta_h\{\sup|b|\le\eta/4\}\\
&\ \cdot\int_I\frac{\chi_\eta(x)}{\phi(x)}\pi(dx)
\int_I\gamma_h(z-x)\phi(z)\rho_\eta(z-x)^2w_\kappa(z)dz.
\end{aligned}
\tag{6.5}
$$

The bridge probability tends to one by its maximal second moment.
The Gaussian displacement has second moment $\sigma^2h$, the
endpoint cutoff is one near zero displacement, and $\phi w_\kappa$
is uniformly Lipschitz on the compact sets involved. Approximation
by its value at $x$, with Gaussian tails outside $|z-x|\le\eta/8$,
gives error $O_\eta(\sqrt h)$ in (6.5). This proves (6.4).
Finally $w$ has a common positive lower bound and
$\int\chi_\eta d\pi>0$. $\square$

**Lemma 6.2 (the weighted inequality for all Borel policies).** For every
policy in Lemma 5.1 and every original estimator, for the same small
$h>0$,

$$
\mathcal R_\kappa(\mathcal P,g)
\ge
\frac{A_{h,\eta,\kappa}^2}
{nA_{h,\eta,\kappa}+C_\eta n\sqrt h+C_\eta/h}.
\tag{6.6}
$$

Proof. Clip $g$ to $[l,u]$. Regarding it as a function of the enlarged
data can only permit more estimators. Let $L=a'/a>0$. From (5.5),
$V_i'/V_i$ is a weighted average, with weights proportional to
$a(K^z_r)dr$, of $L(K^z_r)r/h$ on the selected interval. Therefore

$$
0\le\frac{V_i'}{V_i}\le\sup_{r\le h}L(K^z_r),\qquad
\frac{V_i'^2}{2V_i^2}\le j_\kappa(z)+C M_h.
\tag{6.7}
$$

Uniform smoothness of $L$ proves the last inequality; $L$ is bounded
and $M_h\le d$ on this support. It applies to every adaptive interval
and to the remaining piece of an interval crossing $s$. Martingale
score orthogonality yields

$$
\mathbf E\left[\left(\sum_iU_i\right)^2\middle|P_s,b,z\right]
\le n\{j_\kappa(z)+C M_h\}.
\tag{6.8}
$$

The multiplier (6.1) depends only on height coordinates and the past,
so it leaves these conditional observation identities unchanged.

Let $p_\nu$ denote the density with respect to the actual law of $P_s$,
the bridge reference, $dz$, and Lebesgue measure in the $N(P_s)$
future increments. This is a disjoint union of fixed-dimensional
fibers. On each fiber fixing the enlarged observation coordinates
$P_s,b,y$ fixes the estimator, the count and all timestamps. Thus
$g$ has zero $z$ derivative, even if its dependence on the record is
only Borel. The compact smooth endpoint cutoff, extended by zero
outside its interior support, gives zero boundary terms. Integrating
the derivative of $(g-z)w_\kappa(z)p_\nu$ in $z$ gives

$$
\int(g-z)\{w_\kappa(z)S+w_\kappa'(z)\}d\nu
=\int w_\kappa(z)d\nu=A_{h,\eta,\kappa}.
\tag{6.9}
$$

Here is the analytic justification at full Borel scope. For each fixed
record the positive-variance normal product is smooth in $z$ on the
cutoff neighborhood, because all its integration endpoints are fixed.
Equation (5.6), the first bound in (6.3), and boundedness of $w,w'$
give finite integrated absolute derivative of the full density and
of the product just differentiated. The factor $g-z$ is bounded.
Fubini therefore permits one-dimensional integration by parts before
integrating the other coordinates. Zeros of the squared cutoff use
the density derivative specified after (6.3). No differentiation in
a history variable, no lower spacing bound and no derivative of a
survival event are involved. For an original estimator not initially
bounded, clipping decreases its source risk and suffices for the lower
bound; infinite-risk estimators also satisfy it.

The conditional means of the $U_i$ vanish. Their cross terms with
the height-only expression $wS_0+w'$ vanish as well. Consequently,
using $w^2j=w$, (6.3) and (6.8),

$$
\begin{aligned}
\int(wS+w')^2d\nu
&=\int w^2\mathbf E\left[\left(\sum_iU_i\right)^2
\middle|P_s,b,z\right]d\nu+\int(wS_0+w')^2d\nu\\
&\le nA_{h,\eta,\kappa}+C_\eta n\sqrt h+C_\eta/h.
\end{aligned}
\tag{6.10}
$$

Cauchy--Schwarz in (6.9) bounds $\int(g-z)^2d\nu$ from below by
the right side of (6.6). Domination of $\nu$ by the actual joint
source and (5.3) give the same bound for every original estimator.
The constants are independent of policy, seed and parameter.
$\square$

## 7. The universal converse and finite-budget positivity

**Theorem 7.1 (full-class lower limits).** For all original policies,
including arbitrary Borel feedback, independent randomization and
variable counts,

$$
\liminf_{n\to\infty}\inf_{\substack{\kappa\in\mathcal K\\
\mathcal P,g:\,M\le n}}
\left[n\mathcal R_\kappa(\mathcal P,g)-C_\kappa\right]\ge0.
\tag{7.1}
$$

There is also $c_\tau>0$, depending only on the fixed native data and
horizon, such that for every $n\ge1$ and every such pair

$$
\mathcal R_\kappa(\mathcal P,g)\ge\frac{c_\tau}{n+1}.
\tag{7.2}
$$

Proof. First take exactly $n$ queries. Fix $\eta$ and use
$h=\tau/(2\sqrt n)$ in (6.6); for sufficiently large $n$ it lies
in the range of Lemma 6.1. Then $h\to0$ and $nh\to\infty$. After
multiplication by $n$, the lower bound is

$$
\frac{A_{h,\eta,\kappa}^2}
{A_{h,\eta,\kappa}+C_\eta\sqrt h+C_\eta/(nh)}
\ge A_{h,\eta,\kappa}-C_\eta\sqrt h-C_\eta/(nh).
\tag{7.3}
$$

Lemma 6.1 makes this $A_{\eta,\kappa}-o_\eta(1)$ uniformly in
parameter and policy. Both original faces are restored by the ordered
limit

$$
0\le C_\kappa-A_{\eta,\kappa}
\le w_+\int_I(1-\chi_\eta)d\pi\longrightarrow0
\quad(\eta\downarrow0),
\tag{7.4}
$$

uniformly in $\kappa$. Indeed $\chi_\eta=1$ outside the two
$2\eta$ boundary layers, and $\pi$ has no endpoint atoms. Choose
$\eta$ first and $n$ second. This proves (7.1) without an uncontrolled
diagonal choice or an interior-height restriction.

For finite budgets fix one nonzero $\chi_\eta$ and one sufficiently
small $0<h_0<\tau$. By (6.4), $A_{h_0,\eta,\kappa}$ has a common
positive lower bound. It is bounded above as well, and the denominator
in (6.6) is at most $D_\tau(n+1)$ for a fixed finite $D_\tau$.
This proves (7.2) for every $n\ge1$.

The proofs conditioned on the independent seed as part of $P_s$;
no property of its law entered a constant. They thus include every
allowed randomization. Lemma 2.2 converts any at-most-$n$ policy into
an exactly-$n$ pair with identical risk and extends both inequalities
to variable counts. $\square$

## 8. The sharp optimum over the original timing class

**Theorem 8.1 (uniform optimal endpoint-query asymptotic).** Under exactly
Definition 1.1 and the full class in Definition 2.1,

$$
\sup_{\kappa\in\mathcal K}
\left|nR^*_{n,\kappa}-C_\kappa\right|\longrightarrow0,
\qquad
C_\kappa=\int_I\frac{B_\kappa(k)^2}{2B_\kappa'(k)^2}\pi(dk).
\tag{8.1}
$$

The same limit holds for the actual finite wrapped-query sequence
of Definition 4.1. Also $R^*_{n,\kappa}=R^{=}_{n,\kappa}>0$ for every
finite $n$, with the uniform lower bound (7.2). All uniform assertions
allow arbitrary parameter sequences in the full fixed two-sided
family, including actual zero values and approaches through either sign.

Proof. Theorem 7.1 gives a uniform lower error tending to zero for the
infimum. Theorem 4.2 gives a uniform upper error tending to zero with
an actual lawful pair for each $n$. Since its risk bounds $R^*$ from
above, these inequalities prove (8.1). The asserted attaining-sequence
limit is (4.3), and equality of budget infima and positivity are
Lemmas 2.2 and Theorem 7.1. Proposition 3.2 supplies the explicit
coefficient and its actual-zero value. No nonzero-coordinate inverse
or extra phase was used at any parameter. $\square$

The average in (8.1) is the average of inverse local information.
It is not obtained by inverting $\int j_\kappa d\pi$. The weight
$w_\kappa$ in (6.9)--(6.10) is what yields that particular coefficient.

## 9. What every finite posterior retains

**Theorem 9.1 (posterior equivalence for every finite lawful policy).**
For every finite policy in Definition 2.1, the posterior law of
$K_\tau$ given its seed and record is equivalent to $\pi$, almost
surely. It has support $[l,u]$ and gives positive mass to every
nonempty open subinterval of $I$.

Proof. First take exactly $n$ and the completed policy. Fix a seed and
write its record in circle-increment coordinates
$z_1,\ldots,z_n\in[-\pi,\pi)$. The recursively determined times
are fixed at that record, with positive spacings
$\Delta_j=T_j-T_{j-1}$. Conditional on the height path, the same
sequential argument as Lemma 5.2, now on the whole interval and then
wrapped, gives the likelihood

$$
L_z(K)=\prod_{j=1}^n q_{V_j(K)}(z_j),\qquad
q_V(z)=\sum_{r\in\mathbb Z}
\frac{e^{-(z+2\pi r)^2/(2V)}}{\sqrt{2\pi V}},\qquad
V_j(K)=\int_{T_{j-1}}^{T_j}a_\kappa(K_s)ds.
\tag{9.1}
$$

The map between wrapped samples with their known initial value and
circle increments is bijective. The times are determined by preceding
increments and seed; they add no independent likelihood factor.
For this fixed record,
$a_-\Delta_j\le V_j\le a_+\Delta_j$. The periodized normal is
strictly positive and continuous on the circle times any compact
positive variance interval. Its series converges uniformly there,
by the Gaussian tail. Hence there are finite constants
$0<c(z,U)\le C(z,U)<\infty$ bounding $L_z(K)$ over every height
path. These constants need not be uniform across records with tiny
spacings.

Disintegrate the unchanged height-path law over its endpoint
$K_\tau\sim\pi$. Independence of the seed and height and Bayes'
formula give a posterior density

$$
\frac{d\pi_{U,z}}{d\pi}(k)
=\frac{\mathbf E[L_z(K)\mid K_\tau=k]}{\mathbf E L_z(K)}.
\tag{9.2}
$$

The bounds just established make it finite and strictly positive for
$\pi$-almost every $k$, for almost every seed and record. Thus it is
equivalent to $\pi$. For a variable-count policy use the disjoint
union of terminal record branches. Membership in a branch is a
function of the seed and queried history alone. Its indicator is
independent of the height coordinate at a fixed record and cancels
from (9.2) on valid branches. The same positive finite product proof
therefore applies for each possible terminal count. Almost surely
lawful versions are covered by Lemma 2.2.

The sine-squared prior has positive density throughout $I$ and support
$[l,u]$, which proves the support statements. Equivalence implies a
nondegenerate posterior and positive expected variance for each
individual finite policy. The stronger positivity of the infimum
over all policies follows separately from (7.2); individual positivity
alone would not prove it. $\square$

## 10. A precisely limited static comparison at fixed budgets

**Definition 10.1 (a separate scale experiment).** For an integer $m\ge1$
let $K\sim\pi$ and, conditionally on $K$, let
$X_1,\ldots,X_m$ be independent $N(0,a_\kappa(K))$ variables.
Denote its Bayes squared risk by $r_{m,\kappa}$ and put
$r_{0,\kappa}=\operatorname{Var}_\pi(K)$. This is a comparison
experiment, not a supply of repeated same-time native increments.
The statistic $S=m^{-1}\sum_iX_i^2$ is sufficient and its posterior
mean is

$$
g_{m,\kappa}(s)=
\frac{\int_I k\,a_\kappa(k)^{-m/2}
 e^{-ms/(2a_\kappa(k))}\pi(dk)}
{\int_I a_\kappa(k)^{-m/2}
 e^{-ms/(2a_\kappa(k))}\pi(dk)},\qquad s\ge0.
\tag{10.1}
$$

Its denominator is positive. For each fixed $m$ this is a bounded
continuous function, uniformly Lipschitz in $s$ over the full parameter
family: differentiating the ratio gives
$g_{m,\kappa}'(s)=-(m/2)\operatorname{Cov}_s(K,1/a_\kappa(K))$,
whose absolute value has a common finite bound for fixed $m$.
The displayed posterior and sufficiency follow directly by factoring
the product normal density.

**Proposition 10.2 (positive-spacing limiting infimum comparison).**
For each finite $n\ge1$ and parameter,

$$
\frac{c_\tau}{n+1}\le R^*_{n,\kappa}\le r_{n-1,\kappa}.
\tag{10.2}
$$

For $n\ge2$ the upper comparison is obtained as a limit of actual
$n$-query schedules with positive cluster windows. The approximation
can be made uniform in $\kappa$ for each fixed $n$.

Proof. The lower bound is Theorem 7.1. Fix $n\ge2$, $m=n-1$, and
replace $h_n$ in (4.1) by any $0<h<\tau$, with $\delta=h/m$.
Use $g_{m,\kappa}$ of the normalized sum of squared wrapped short
increments as estimator. With real comparison increments, (4.6)
now gives $\mathbf E|S_{\rm real}-S_{\rm fr}|^2\le C_\tau h$.
The fixed-$m$ Lipschitz bound from Definition 10.1 gives convergence
in mean square of the estimator outputs. Boundedness then gives
convergence of their risks. The frozen pair has exactly the static
law in Definition 10.1, because $K_\tau\sim\pi$, so its risk is
$r_{m,\kappa}$. The wrapping error is at most
$2d^2m\exp[-\pi^2/(2a_+\delta)]$, which tends to zero with $h$.
All bounds are uniform in $\kappa$ for this fixed $m$. For every
tolerance, a strictly positive $h$ therefore gives an original lawful
pair within that tolerance of $r_{n-1,\kappa}$. Taking the infimum
proves its upper bound. For $n=1$, ignoring the value at the required
terminal query gives the prior variance $r_{0,\kappa}$. $\square$

For each finite $n$, Definition 4.1 itself is an actual policy with
finite risk. Its sharp coefficient is attained along that sequence
of finite experiments. Proposition 10.2 is a different, fixed-$n$
limiting comparison. At a zero cluster window the short increments
are zero, a repeated same-time query returns the same value, and
normalization by $\sqrt\delta$ is undefined. No independent data
exist at that boundary. The results prove neither
$R^*_{n,\kappa}=C_\kappa/n$ nor
$R^*_{n,\kappa}=r_{n-1,\kappa}$ at finite $n$. The exact finite-$n$
infimum, its relation beyond (10.2) to the static comparison, and
existence, nonexistence or structure of a finite-$n$ optimizing policy
remain unresolved.

## 11. Comparison with the credited uniform-grid theorem

**Theorem 11.1 (grid order and the resulting improvement).** Let
$R^{\rm grid}_{n,\kappa}$ be the Bayes risk when the only positive
queries are $j\tau/n$, $j=1,\ldots,n$. There are constants
$0<c_\tau<C_\tau<\infty$ and $n_0$, uniform on the original family,
such that

$$
c_\tau n^{-1/2}\le R^{\rm grid}_{n,\kappa}
\le C_\tau n^{-1/2}\qquad(n\ge n_0).
\tag{11.1}
$$

This is the supplied L Theorems 58.3 and 59.1 at their grid scope.
Together with Theorem 8.1 it implies that both the optimal risk and
the actual cluster risk, divided by the grid risk, are of order
$n^{-1/2}$ uniformly in $\kappa$. No grid leading coefficient is
asserted.

Proof. A direct account of the credited grid argument also fixes its
source dependence. Let $\Delta=\tau/n$, $m=\lceil\sqrt n\rceil$ and
$h=m\Delta$. Use the last $m$ real increments as comparison and put
$S=(m\Delta)^{-1}\sum(\Delta_jv)^2$. Conditional on height,

$$
\mathbf E(S\mid K)=\frac1h\int_{\tau-h}^\tau a_\kappa(K_s)ds,
\qquad
\operatorname{Var}(S\mid K)
=\frac{2\sum V_j^2}{(m\Delta)^2}\le\frac{2a_+^2}{m}.
\tag{11.2}
$$

By (1.6) the mean squared difference of the conditional mean from
$a_\kappa(K_\tau)$ is at most $C_\tau h$. Applying $F_\kappa$
therefore gives risk at most $C_\tau(m^{-1}+h)$. For actual wrapped
increments the additional loss is at most
$2d^2m\exp[-\pi^2/(2a_+\Delta)]$. This proves the upper bound.

For the lower bound take the grid-aligned final window $[s,\tau]$
of length $h=m\Delta$ and enlarge by the exact past, centered bridge
and its $m$ real grid increments, as in Lemma 5.1. Choose a fixed
compact interval $J\Subset I$ of positive length and $\rho>0$ such
that all $x\in J$ are at distance at least $3\rho$ from both faces.
Let $0\le\psi\le1$ be a nonzero smooth function supported in
$(-1,1)$. Multiply the exact joint density by

$$
\mathbf1_{\{x\in J\}}\mathbf1_{\{\sup|b|\le\rho\}}
\psi((z-x)/\sqrt h)^2
\tag{11.3}
$$

to get a dominated subprobability $\widetilde\nu_h$. For small $h$,
$|z-x|\le\sqrt h\le\rho$ on this support, so the interpolated
height is strictly interior and the survival indicator is constant
there. Stationarity gives $\pi(J)>0$; the bridge cutoff has probability
tending to one. With $z=x+\sqrt h\,v$, the Gaussian endpoint integral
against $\psi(v)^2$ has a positive fixed mass, and the exact Q ratio
$\phi(z)/\phi(x)$ is bounded above and below. Thus
$\widetilde\nu_h(1)\ge c>0$ independently of small $h$ and parameter.

The endpoint score, including this cutoff, is

$$
-\frac{z-x}{\sigma^2h}+\frac{\phi'(z)}{\phi(z)}
+\frac2{\sqrt h}\frac{\psi'((z-x)/\sqrt h)}
{\psi((z-x)/\sqrt h)}.
\tag{11.4}
$$

Its integrated square is $O(h^{-1})$: the Gaussian scaling controls
the first term, the compact interior controls the second, and the
squared cutoff cancels the last denominator. Each grid observation
has information bounded by a constant by (5.5), and their conditional
scores are orthogonal to one another and to (11.4). The full squared
score integral is consequently at most $C(h^{-1}+m)$. The cutoff
gives zero endpoint boundary terms. The unweighted integration by
parts identity
$\int(g-z)\partial_z\log p_{\widetilde\nu_h}
\,d\widetilde\nu_h=\widetilde\nu_h(1)$, justified exactly as in
Lemma 6.2, and Cauchy--Schwarz give

$$
\mathbf E(g-K_\tau)^2\ge\frac{c}{h^{-1}+m}
\ge c_\tau n^{-1/2}.
\tag{11.5}
$$

This is a bound on the same stationary source, with its exact Q
weight, both original faces and the actual endpoint target. It proves
the lower half of (11.1). The positive upper and lower coefficient
bounds in Proposition 3.2 and Theorem 8.1 then prove the ratio
assertion, also for the actual cluster risks by (4.3). $\square$

## 12. Mathematical suppliers and applicability limits

**Mathematical correspondence 12.1 (credited ingredients and scope).**
The native source and full-family margins are those of L Definitions
35.1 and 55.1 and (55.3)--(55.5). Its ground-state conventions and
exact source factors are L (37.2), (37.8) and Proposition 60.2.
The supplied conditional Gaussian and wrapped likelihood, endpoint
moment and wrapping argument are L (58.2)--(58.10). Its native
bridge construction and Bayesian information comparison are
L (59.2)--(59.12). Theorem 11.1 credits and retains the supplied
uniform-grid result. The proofs here give the additional timing-class
converse, the weighted sharp coefficient and the actual finite
positive-spacing matching sequence at the original scope.

Gaussian scale information and moments, Brownian endpoint/bridge
disintegration, the Doob transform, strong Markov conditioning,
martingale score orthogonality, clipping, Taylor expansion, dominated
convergence and integration by parts are classical tools. The
Bayesian information argument is of the van Trees type; compare
R. D. Gill and B. Y. Levit, *Applications of the van Trees Inequality:
A Bayesian Cramér--Rao Bound*, Bernoulli 1 (1995),
[DOI 10.2307/3318681](https://doi.org/10.2307/3318681), already credited
in L Section 61. Its hypotheses here are discharged by (5.2), the
common Borel record domain, the positive-variance sequential kernels,
the compact endpoint cutoffs and the integrability in (5.6)--(6.10).
The information identity itself is proved above. Generic volatility
estimation, endpoint clustering and these general methods are not
claimed as new general results.

The result is a source-specific repository-derived application with
ordinary mathematical proofs. Its parameter uniformity is over the
entire originally fixed $\mathcal K$, not the smaller calibration
family used elsewhere. L Sections 62--68 concern a different experiment
with unknown fixed calibration and ideal continuous histories.
Their variation reconstructions, paired-sign posteriors and continuous
extra-phase augmentations supply no data to a policy here. Known
calibration is used only as stipulated in Definition 2.1.

Every upper policy observes finitely many wrapped $v$ values. The
revealed past, bridge and real increments occur only in a lower-bound
comparison on the same probability; neither the source, target nor
information port of the optimization is changed. The next query must
be selected immediately from preceding queried data. An unqueried-path
trigger or hidden height-dependent stopping tag would define a different
experiment. Conversely, the present proof imposes no smoothness of
feedback, no deterministic-timing restriction and no minimum positive
spacing beyond the stated finite-policy order.

All assertions fix the original interval, stationary prior, known
parameters, clock, positive $\varepsilon$ and positive $\tau$. They
are Bayes bounds under one probability, not minimax bounds over an
unknown function class. They do not transfer unchanged to another
height prior, a killed or terminal-survivor source, unknown calibration,
continuous observations, a moving comparison zero coordinate or noisy
measurement. Exact finite-budget optimization and optimizer existence
remain as specified after Proposition 10.2.

Time precision is uncharged, and the matching spacings decrease as
$n^{-4}$. The theorem gives no physical time-resolution, finite-bit,
CPU, shot, acquisition or empirical resource bound. It selects no
physical spatial dimension or rotation symmetry, supplies no sensor,
new native control, attraction or binding result, and makes no general
neural-network or empirical machine-learning assertion. The statements
are ordinary source-specific mathematics, with no formal-kernel or
worldwide-priority certification implied.

## 追加锚（本行以下为增补区）
