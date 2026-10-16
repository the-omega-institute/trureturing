# Native guarded lift limits and diffusion selection

> This volume uses the `generic-v1` theorem/proof shape. Locators are
> determined by its bytes. Published text is preserved; corrections and
> extensions belong in new sections after the final append anchor.

## 1. Position, evidence and the question being answered

**Reference status.** This is ordinary mathematical exposition, not a
Lean-kernel-verified result or a machine certification. It supplies no
physical stochastic input. The authoring context is the repository's
`formal-thinking-and-answer` and `theory-volume-template` skills under an
ordinary-proof restriction. The mathematical source and its direct checks
are authored by one Codex CLI implementation seat. Independent review is
not asserted by this text and is not a premise of its proofs.

**Source convention 1.1 (fixed published suppliers).** The repository
sources below are read at commit
`1604b2c78dd048bea53452f9e692031da52e72c3`:

| Symbol | Source and exact supplied scope |
| --- | --- |
| N | [Probability, phase transport and holonomy](AURIC_FIB_ATOM_PROBABILITY_PHASE_TRANSPORT_AND_HOLONOMY.md), Definitions 3.1, 8.1 and 9.1, §§9.1–9.3, Definition 10.1 and §10.5: original histories, preparations, chronological partial action, guards, costs and the declared diffusion. |
| O | [Native observation quotient and Green escape](FIB_NATIVE_OBSERVATION_QUOTIENT_GREEN_ESCAPE.md), Definitions 1.1–1.2 and Theorem 2.1: actual two-circle coordinates, guarded bottom-observation quotient and its killed free factor. The specialization used here is its parameter $\varepsilon=1$. |
| G | [Native two-control Green stability](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md), Definition 4.1 and Proposition 6.1: the same declared horizontal clock and height killing. No attraction or stability classification is used here. |

The missing bridge addressed here is between finite lawful N-histories and
N's separately declared diffusion. The finite chronology, the phenomenon
of area corrections in smooth approximations, and stochastic integration
are existing suppliers. The work here is their explicit guarded native
correspondence, including executed costs and the lifetime boundary.
No unmerged rigidity manuscript is a dependency.

**Scope 1.2.** Fix a finite observation horizon $T>0$ and a specified
starting ray. The results distinguish existence of approximating command
laws, uniqueness after the additional joint stochastic law is chosen,
and failure of the native syntax to choose that law. They do not classify
all samplers or optimal costs. Their convergence assertions concern a
fixed starting state and fixed horizons; they are not uniform-in-start,
total-variation, all-Borel-test or heat-kernel convergence assertions.

## 2. The original source, its guard and its entire chronological path

**Definition 2.1 (unchanged source and periods).** Fix

$$
0<Z<1,\qquad r=1-Z,\qquad H=r/2,\qquad X=Y=H.
\tag{2.1}
$$

In mode order $(0,1,2,3,13)$ the probabilities at height $k$ are
$(k,H-k,Z,H-k,k)$, with $0<k<H$. Fix the original preparation height
and arbitrary preparation phases. A common phase gauge makes the middle
amplitude positive; it does not set the other preparation phases to zero.
The representative remains $\psi_s=\sqrt{p_s}e^{-i\theta_s}$.
The grouped phase increments are $u,v$, and

$$
\alpha=u-v\pmod{2\pi},\qquad \beta=u\pmod{2\pi},
\qquad (u,v)=(\beta,\beta-\alpha).
\tag{2.2}
$$

Both circles have period $2\pi$. The integer unimodular change (2.2)
does not double either circle. The current-ray source is
$\mathcal M=(0,H)\times\mathbb T^2$. A starting ray
$q_0=(k,\alpha_0,\beta_0)$ may be the preparation itself or any specified
ray reached from it by N, Theorem 8.2. A preceding preparation history,
if needed, remains a separate finite history with its own cost.

**Definition 2.2 (original relative histories).** An original relative
command $(a,b):[0,T]\to\mathbb R^2$ starts at zero and is absolutely
continuous or piecewise $C^1$, as in N, Definitions 3.1 and 9.1. It has
finite variation. It means $\kappa=k+a$ and
$\chi=\chi_*+b$, with the actual consistent initial relation lift
$\chi_*$. Put

$$
J(t)=\int_0^t a(s)\,db(s),\qquad
m=\min_{[0,T]}a,\qquad M=\max_{[0,T]}a.
\tag{2.3}
$$

The integral is an ordinary integral against an absolutely continuous
integrator. Its exact native domain is

$$
D_{a,b}=(-m,H-M),\qquad
k\in D_{a,b}\ \Longleftrightarrow\ k+m>0\text{ and }k+M<H.
\tag{2.4}
$$

For every starting height in a compact promise $[k_-,k_+]$, the same
numerical command is lawful precisely when
$k_-+m>0$ and $k_++M<H$. This is a whole-path condition. An endpoint
inside the source is insufficient. Neither a signature nor a stochastic
limit supplies permission to execute a command outside this domain.

**Proposition 2.3 (supplied full-path correspondence).** Write
$c_0=1/2-k/r$. At every prefix time of a lawful command, N, Theorem 9.3
gives the following real phase lifts, followed by reduction modulo $2\pi$:

$$
\begin{aligned}
\kappa_t&=k+a_t,\\
\widetilde\alpha_t&=\alpha_0+b_t/2,\\
\widetilde\beta_t&=\beta_0+c_0b_t-J_t/r.
\end{aligned}
\tag{2.5}
$$

Thus the full lifted state path is the image of the joint path
$(a,b,J)$ under this affine map. This is a prefix application of the
existing chronology, not a new chronological action.

Proof. N's double-wall coefficients are
$w_+=1/2-\kappa/r$ and $w_-=-\kappa/r$. Integrating them against $db$
gives $u-u_0=b/2-(kb+J)/r$ and
$v-v_0=-(kb+J)/r$. Subtracting and using (2.2) gives (2.5), with the
negative phase convention unchanged. The guard is exactly N, Theorem 9.2.
$\square$

**Observation 2.4 (which information is lost).** A complete original
finite-variation path $(a,b)$ already determines its ordinary $J$; it needs
no separately chosen area. Its endpoints $(a_T,b_T)$ do not determine
$J_T$. A terminal wrapped state loses still more information, including
possible windings; for fixed $a_T,b_T$ its $\beta$ coordinate sees
$J_T$ only modulo $2\pi r$. The bottom-observation state
$\pi(q)=(k,\alpha)$ loses $J$ entirely.

In contrast, an exact complete continuous wrapped state path with its
starting point admits unique continuous phase lifts once initial real
representatives are fixed. On such a path (2.5) recovers

$$
a_t=\kappa_t-k,\qquad
b_t=2(\widetilde\alpha_t-\alpha_0),\qquad
J_t=r\{c_0b_t-(\widetilde\beta_t-\beta_0)\}.
\tag{2.6}
$$

This is a statement about complete paths, not about finite measurement
resolution. In limits the difficulty is different: the operation
$(a,b)\mapsto\int a\,db$ is not continuous for uniform convergence of
the first-level paths. Section 6 proves this failure within a lawful
native family. A joint law of endpoints, marginal area laws, or a
first-level covariance matrix is not the required joint path law.

For comparison with signed area, the source normalization is

$$
\Omega_t=\frac12\int_0^t(a\,db-b\,da)
          =J_t-\frac12a_tb_t.
\tag{2.7}
$$

An added drift $\lambda t$ in $J$ with unchanged first level adds the
same drift in $\Omega$, not twice that drift.

## 3. Finite-horizon continuity of the native lift

**Theorem 3.1 (joint-path continuity).** On $[0,T]$, let continuous
triples $z_n=(a_n,b_n,J_n)$, starting at zero, converge uniformly to
$z=(a,b,J)$. For finite-stage original commands require
$J_n=\int a_n\,db_n$; the limiting $J$ is specified jointly and is not
defined by an unasserted ordinary integral. With fixed $q_0$, the real
paths (2.5) converge uniformly, as do their wrapped paths wherever those
paths are in the native domain. In particular,

$$
\begin{aligned}
\|\kappa_n-\kappa\|_\infty&=\|a_n-a\|_\infty,\\
\|\widetilde\alpha_n-\widetilde\alpha\|_\infty
 &=\tfrac12\|b_n-b\|_\infty,\\
\|\widetilde\beta_n-\widetilde\beta\|_\infty
 &\le |c_0|\|b_n-b\|_\infty+r^{-1}\|J_n-J\|_\infty.
\end{aligned}
\tag{3.1}
$$

For random triples the same map carries weak convergence in
$C([0,T],\mathbb R^3)$ with its uniform topology to weak convergence
of continuous state paths. It also preserves convergence in probability
or almost surely under a common coupling. No rough-path continuity
theorem is required for this affine native equation.

Proof. The estimates are immediate from (2.5). Circle projection is
1-Lipschitz for the circle distance. Weak convergence follows by composing
bounded continuous tests with this continuous map. If the limiting height
stays in a compact subinterval of $(0,H)$, uniform convergence also
ensures the whole native guard for all sufficiently large $n$.
Otherwise lawfulness must be checked separately. $\square$

**Remark 3.2 (increments and sufficiency).** The triple determines every
interval's chronological increment through

$$
J_{s,t}^{\mathrm{rel}}=J_t-J_s-a_s(b_t-b_s).
\tag{3.2}
$$

There are no missing higher integrals for (2.5). Uniform convergence of
this triple is sufficient for this specific triangular equation, not
a general theorem for arbitrary controlled differential equations.
Conversely (2.6) describes the information needed to distinguish complete
lifted native paths, up to the stated phase lifting convention. These
claims do not characterize the weakest possible probabilistic topology.

## 4. Lifetime continuity, held histories and the cemetery path

**Definition 4.1 (added killing and a suitable state space).** Choose
$I=(l,u)$ with $0<l<k<u<H$. Given a continuous comparison height
$h_t=k+a_t$ on $[0,T]$, put

$$
\tau_T(h)=\inf\{t\in[0,T]:h_t\notin I\},
\qquad \inf\varnothing=\infty,\qquad s_T=\tau_T\wedge T.
\tag{4.1}
$$

The continuously held source path is $\bar q_t=q_{t\wedge s_T}$.
It is a path in $\overline I\times\mathbb T^2\subset\mathcal M$.
The killed observation is instead

$$
q_t^\dagger=
\begin{cases}q_t,&t<\tau_T,\\ \dagger,&t\ge\tau_T,\end{cases}
\tag{4.2}
$$

where $\dagger$ is isolated. Use the compact metric space
$E=(\overline I\times\mathbb T^2)\sqcup\{\dagger\}$, with the
product distance truncated at 1 on the first component and distance 2
to $\dagger$. Then (4.2) belongs to $D([0,T],E)$: it has a boundary
left limit and a jump to $\dagger$. Boundary points are included to
represent that left limit, not to keep the killed process alive there.
Using only the open cylinder with an isolated cemetery would omit this
left limit and would not give the stated càdlàg path space.

**Theorem 4.2 (lifetime and killed-path continuity).** Suppose the triples
in Theorem 3.1 are continuous comparison extensions, and their heights
start at the same $k\in I$. Exclude $\tau_T(h)=T$. If
$\tau=\tau_T(h)<T$, require the following strict-crossing condition:

$$
\text{for every }\epsilon>0\text{ with }\tau+\epsilon\le T,
\text{ some }s\in(\tau,\tau+\epsilon)
\text{ satisfies }h_s\notin[l,u].
\tag{4.3}
$$

If $\tau=\infty$, no crossing condition is needed. Then the censored
lifetimes converge, taking $\infty$ as an isolated no-death mark on
this horizon; the continuously held joint triples and source paths
converge uniformly; and

$$
q_n^\dagger\longrightarrow q^\dagger
\quad\hbox{in the Skorokhod }J_1\hbox{ topology on }D([0,T],E).
\tag{4.4}
$$

For weakly convergent joint triples these conclusions hold in distribution
if the limiting law gives probability one to the conditions above.

Proof. On every $[0,t]$ with $t<\tau$, continuity puts $h$ a positive
distance inside $I$. Uniform approximation yields $\liminf\tau_n\ge\tau$.
When $\tau<T$, a strictly exterior value supplied by (4.3) persists for
$h_n$ and gives $\limsup\tau_n\le\tau+\epsilon$; hence
$\tau_n\to\tau$. If $\tau=\infty$, the entire compact image on
$[0,T]$ lies a positive distance inside $I$, so $\tau_n=\infty$
eventually. Uniform continuity of $z$ and uniform convergence of $z_n$
give $z_n(\cdot\wedge s_n)\to z(\cdot\wedge s)$ uniformly.
The same then holds for (2.5).

When $0<\tau<T$, choose increasing piecewise linear time homeomorphisms
$\lambda_n:[0,T]\to[0,T]$ sending $0,\tau,T$ to
$0,\tau_n,T$. Their distance from the identity tends to zero. Before
$\tau$, both $q_n^\dagger(\lambda_n(t))$ and $q_t^\dagger$ are alive
and their distance tends uniformly to zero by continuity of the held
paths. At and after $\tau$ both are $\dagger$. This is (4.4).
For no death the identity time change suffices. The exit/holding maps
are measurable; for example hitting a closed exterior is measurable
using minima of continuous distance functions on compact time intervals.
The deterministic continuity just proved gives the probabilistic assertion
by the continuous mapping theorem. $\square$

**Remark 4.3 (why the topology and horizon matter).** If
$\tau_n\ne\tau<T$, at times between the two deaths one path is alive
and the other is $\dagger$, so uniform convergence of the killed paths
generally fails. A time change resolves precisely that mismatch.
At $\tau=T$, approximations dying just after $T$ remain alive at the
terminal observation while the limit is dead; a time homeomorphism fixes
$T$ and cannot repair it. This is why Theorem 4.2 excludes an atom of
the lifetime at the chosen horizon. Uniform convergence of held paths
does not by itself encode a death flag.

**Counterexample 4.4 (native boundary touch without crossing).** On
$[0,2]$ fix $k\in(l,u)$ and let $d=k-l>0$. Take

$$
\begin{aligned}
h(t)&=l+d(t-1)^2,\\
h_n(t)&=h(t)+\epsilon_n t(2-t)
       =l+\epsilon_n+(d-\epsilon_n)(t-1)^2,
\end{aligned}
\tag{4.5}
$$

where $0<\epsilon_n<d$ and $\epsilon_n\downarrow0$. The commands
$a=h-k$, $a_n=h_n-k$, $b=b_n=0$ start at zero, are $C^1$, and have
$J=J_n=0$. Every one, including the limit, is a lawful original
history on the entire horizon: all its heights lie in $[l,k]\subset(0,H)$.
Their native extrema satisfy $k+m\ge l>0$ and $k+M=k<H$.
The joint triples converge uniformly, yet $\tau_T(h)=1$ while
$\tau_T(h_n)=\infty$. The limit touches only the added interior
killing boundary and returns; it never crosses below $l$.
Its killed path is dead after time 1, whereas every approximating
killed path is alive throughout. Even terminal evaluation at time 2
separates them. Thus neither original lawfulness nor joint-lift
convergence removes the lifetime hypothesis. $\square$

**Proposition 4.5 (the chosen Brownian height satisfies the hypotheses).**
Let $W^1$ be a real Brownian motion with covariance
$\mathbb E(W^1_tW^1_s)=2\min(s,t)$ and start at $k\in I$.
For $h=k+W^1$, its exit time from $I$ is almost surely finite and
strictly positive, has no atom at any fixed $T>0$, and satisfies (4.3)
almost surely whenever it exits before $T$.

Proof. Positivity follows from continuity and the initial interior margin.
For any fixed positive time block, the Gaussian increment has a fixed
positive probability of magnitude exceeding $u-l$. On survival to the
start of that block, such an increment forces exit during the block.
Independent increments give a geometrically decreasing survival bound,
so exit is finite. At a finite exit the height equals $l$ or $u$.
By the strong Markov property, its subsequent increments are a fresh
Brownian motion. The reflection principle implies that, on every
interval $(0,\epsilon)$, a Brownian motion started at zero has both
positive and negative values almost surely. Applying this to rational
$\epsilon$ proves immediate strict exterior values after either exit
face. Finally $\{\tau=T\}\subseteq\{k+W^1_T\in\{l,u\}\}$, a
probability-zero event because $W^1_T$ has a Gaussian density.
These are the specific Brownian hypotheses needed for Theorem 4.2.
$\square$

**Remark 4.6 (no post-death information requirement).** The comparison
extension and (4.3) are convenient sufficient conditions for proving
lifetime convergence. The killed law itself uses only the joint history
before death and the death time. Equivalently one can assume convergence
of the continuously held joint histories together with their censored
lifetimes, with no atom at $T$, and apply the time-change part of
Theorem 4.2 directly. Extensions which agree before death and have the
same lifetime yield the same killed law, whatever they do afterwards.

## 5. A finite-stage sampling construction and its lawful execution

**Definition 5.1 (additional finite Gaussian sampling).** Fix a real
number $\lambda$ and $n=2^m$, with $\delta=T/n$ and $t_i=i\delta$.
At this stage sample $n$ independent pairs

$$
(\Delta_i^1,\Delta_i^2)\sim N(0,2\delta I_2),
\qquad i=0,\ldots,n-1.
\tag{5.1}
$$

There is no sample rejection or reweighting. Put
$x_i=\sum_{j<i}\Delta_j^1$, $y_i=\sum_{j<i}\Delta_j^2$.
The following piecewise linear comparison extension
$(a_n^\lambda,b_n^\lambda)$ is prescribed on each cell:

1. In time $\delta/2$, follow the straight chord from $(x_i,y_i)$ to
   $(x_{i+1},y_{i+1})$ at constant velocity.
2. In the remaining time, traverse the rectangle with relative vertices
   $(0,0),(s_n,0),(s_n,q_n),(0,q_n),(0,0)$ based at
   $(x_{i+1},y_{i+1})$, giving each of its four legs time $\delta/8$, where

$$
s_n=\sqrt\delta,\qquad q_n=\lambda\sqrt\delta.
\tag{5.2}
$$

Zero-length phase legs when $\lambda=0$ are simply holds. The horizontal
out-and-back part is kept even in that case. All variants have exactly
the same comparison height path $a_n$, the same mesh endpoints, and
the same schedule in the original analytic time variable. Their phase
control paths differ inside rectangles. There is no third random driver.

The construction is an additional law on finite prescribed numerical
commands. It uses finitely many Gaussian real variables at each stage;
it asserts neither a physical Brownian actuator nor exact finite-precision
sampling hardware. The coupling with a Brownian path used in the proof
is a device for comparing these finite laws. Running a chord faster
inside its cell is part of the stated finite command and its stated cost,
not a change of the macroscopic diffusion clock.

**Definition 5.2 (actual command from a specified start).** Compute from
the finite sampled polygon

$$
\tau_n=\inf\{t\in[0,T]:k+a_n(t)\notin I\},\qquad
S_n=\tau_n\wedge T.
\tag{5.3}
$$

Prescribe the actual command

$$
\widehat a_n(t)=a_n(t\wedge S_n),\qquad
\widehat b_n^\lambda(t)=b_n^\lambda(t\wedge S_n).
\tag{5.4}
$$

The cutoff can be calculated before execution from the specified starting
height and the finite list of legs. No online measurement of an unknown
height is asserted. Once prescribed, (5.4) is one numerical relative
command; its domain at any other starting height is still (2.4), without
recomputing a state-dependent cutoff. Existence for every specified
starting state is not existence of one Brownian-like command lawful on
the entire source. N's full-domain restriction $a\equiv0$ remains.

**Proposition 5.3 (literal native lawfulness).** For every finite sample,
(5.4) is an original piecewise $C^1$ relative command. It starts at zero,
has finite phase variation, and obeys the complete source guard. Its
actual lifted history is (2.5) with

$$
\widehat J_n^\lambda(t)
=\int_0^t\widehat a_n\,d\widehat b_n^\lambda
=J_n^\lambda(t\wedge S_n).
\tag{5.5}
$$

Proof. At most one of the finitely many linear legs is cut short; all
remaining velocities are zero. The held height lies in $[l,u]$, so its
actual extrema satisfy

$$
k+\min\widehat a_n\ge l>0,\qquad
k+\max\widehat a_n\le u<H.
\tag{5.6}
$$

Thus these are actual full-support source histories even when they touch
the killing boundary. Their ordinary phase integral stops at the same
time, which proves (5.5). The unexecuted comparison extension can leave
$(0,H)$ and need not have any lawful native interpretation there. Its
post-cutoff costs are not execution costs. The killed observation of the
actual history sends it to $\dagger$ at $\tau_n$, whereas the underlying
source history itself is held at a lawful interior-source state.
$\square$

Because $a_n$ is independent of $\lambda$, the cutoffs $\tau_n$ are
identical across variants under the common sampling (5.1). No variant
is compared with another's conditional survival sample or another clock.

## 6. Direct joint convergence, including the chronological coordinate

**Theorem 6.1 (established joint limit of the sampled extensions).**
Couple (5.1) by setting $\Delta_i^j=W^j_{t_{i+1}}-W^j_{t_i}$ for
two independent Brownian motions $W^1,W^2$, each with variance $2t$.
Let

$$
J^0_t=\int_0^t W^1_s\,dW^2_s,\qquad J^\lambda_t=J^0_t+\lambda t.
\tag{6.1}
$$

The integral is the Itô integral in the joint Brownian filtration.
Along the dyadic stages of Definition 5.1, almost surely

$$
(a_n,b_n^\lambda,J_n^\lambda)
\longrightarrow(W^1,W^2,J^0+\lambda\,\cdot)
\quad\hbox{uniformly on }[0,T].
\tag{6.2}
$$

In particular this is joint process convergence, not an assumption of
an iterated invariance principle or an inference from a characteristic
function. Arbitrary integer stages give convergence in probability by
the same estimates.

Proof. Uniform continuity of each Brownian path controls the straight
chords, including their half-cell timing. The extra coordinate excursions
are at most $\sqrt\delta$ and $|\lambda|\sqrt\delta$. Thus the
first two coordinates converge uniformly almost surely.

On a straight chord its contribution to $\int a\,db$ is
$x_i\Delta_i^2+\tfrac12\Delta_i^1\Delta_i^2$. On a rectangle it is
exactly

$$
(x_{i+1}+s_n)q_n-x_{i+1}q_n=s_nq_n=\lambda\delta.
\tag{6.3}
$$

The latter sign is the ordered rectangle sign of N, Theorem 9.3.
Consequently, at every mesh point,

$$
J_n^\lambda(t_j)
=\sum_{i<j}W^1_{t_i}\Delta_i^2
 +\frac12\sum_{i<j}\Delta_i^1\Delta_i^2
 +\lambda t_j.
\tag{6.4}
$$

Here are the complete probabilistic estimates needed to pass to the
joint limit. Put $\eta_n(s)=t_i$ on $[t_i,t_{i+1})$, and define the
continuous martingale
$M_n(t)=\int_0^tW^1_{\eta_n(s)}\,dW^2_s$.
The integrands are predictable and square integrable: on a finite
horizon $\mathbb E(W^1_s)^2=2s$. Independence of the coordinates and
the Itô isometry with $d[W^2]_s=2ds$, followed by Doob's $L^2$
maximal inequality, give

$$
\begin{aligned}
\mathbb E\sup_{t\le T}|M_n(t)-J^0_t|^2
&\le 8\int_0^T
 \mathbb E|W^1_{\eta_n(s)}-W^1_s|^2ds\\
&=8T\delta.
\end{aligned}
\tag{6.5}
$$

The second sum in (6.4), denoted $R_{n,j}$, is a discrete martingale
for the filtration of the successive pairs of mesh increments. Each
increment is centered, independent of the past, and has variance
$\tfrac14(2\delta)(2\delta)=\delta^2$. Hence

$$
\mathbb E\max_{j\le n}|R_{n,j}|^2\le4n\delta^2=4T\delta.
\tag{6.6}
$$

At mesh points $M_n$ is exactly the first sum. Equations (6.5)–(6.6)
prove uniform mesh convergence in probability. For $n=2^m$, the bounds
are summable in $m$. Markov's inequality and Borel–Cantelli, applied
to each positive rational error threshold, give almost sure uniform
mesh convergence. These estimates use the actual independence and
normalization in (5.1); a covariance table without these hypotheses
would not justify them.

To control the intervals between mesh points, set
$U=\sup_{t\le T}|W^1_t|$ and
$d_n^j=\max_i|\Delta_i^j|$. The absolute change of $J_n^\lambda$
inside one cell, measured from its initial value, is bounded by

$$
U d_n^2+\tfrac12d_n^1d_n^2
 +2(U+\sqrt\delta)|\lambda|\sqrt\delta.
\tag{6.7}
$$

The chord gives the first two terms. During the two vertical rectangle
legs, its partial integral is bounded by the sum of their absolute
integrals, which gives the last term. The other legs contribute zero.
The bound tends to zero almost surely. The continuous martingale $J^0$
is uniformly continuous on this horizon, and the drift changes by at
most $|\lambda|\delta$ in a cell. This upgrades the mesh convergence
to (6.2), proving every claimed joint assertion. $\square$

**Corollary 6.2 (lawful held and killed limits).** Under the same coupling,
let $\tau$ be the first exit of $k+W^1$ from $I$. With finite-horizon
censoring understood as in (4.1), almost surely

$$
\begin{aligned}
\tau_n&\longrightarrow\tau,\\
(\widehat a_n,\widehat b_n^\lambda,\widehat J_n^\lambda)
&\longrightarrow
\bigl(W^1_{\cdot\wedge\tau},W^2_{\cdot\wedge\tau},
       J^0_{\cdot\wedge\tau}+\lambda(\cdot\wedge\tau)\bigr)
\end{aligned}
\tag{6.8}
$$

uniformly for the held triples. Their complete held state paths converge
uniformly and their killed paths converge in $J_1$.

Proof. Proposition 4.5 verifies the hypotheses of Theorem 4.2, including
the absence of a death-time atom at $T$. Apply it to (6.2), then use
(5.5) and Theorem 3.1. All variants have the same $\tau_n$ and $\tau$
on this coupling. $\square$

The actual held controls have a stopped Brownian first-level limit.
The comparison extensions have the full Brownian first-level limit with
covariance $2I_2dt$. Before their common death these are the same
description. Finite piecewise linear controls themselves are not
Brownian motions and are not claimed to have Brownian quadratic
variation. The equality being asserted is the limiting first-level law,
with exact equality of their finite mesh Gaussian inputs.

## 7. Full native laws, the reference process and wrapped separation

**Theorem 7.1 (the selected law and its area variant).** Before death,
the limiting state of the actual commands in Corollary 6.2 is

$$
\begin{aligned}
K_t&=k+W^1_t,\\
\widetilde\alpha_t&=\alpha_0+W^2_t/2,\\
\widetilde\beta_t^\lambda
 &=\beta_0+c_0W^2_t-\frac1rJ^0_t-\frac\lambda r t
  =\beta_0+\int_0^t\left(\frac12-\frac{K_s}{r}\right)dW^2_s
          -\frac\lambda r t.
\end{aligned}
\tag{7.1}
$$

Wrap both phases modulo $2\pi$ and kill at the same $\tau$.
For $\lambda=0$ this is exactly N's $\rho=1,A=I_2$ horizontal
Friedrichs process on $I\times\mathbb T^2$ in its original clock.
For general $\lambda$ its interior generator is

$$
\mathcal G_\lambda=P^2+Q^2-\frac\lambda r\partial_\beta,
\qquad
P=\partial_k,\qquad
Q=\frac12\partial_\alpha+
        \left(\frac12-\frac{k}{r}\right)\partial_\beta.
\tag{7.2}
$$

Proof. Substitute the established joint limit into (2.5). The integration
identity in (7.1) uses $K=k+W^1$. Itô's formula gives (7.2), since each
driver has quadratic variation $2dt$ and their mutual quadratic
variation is zero. In particular $Qk=0$ and the derivative of $Q$ in
its own direction is zero. The Itô–Stratonovich correction for these
fields and this covariance is zero. Since
$[P,Q]=-r^{-1}\partial_\beta$, the extra term is
$\lambda[P,Q]$. It is a different drift and law; it cannot be removed
by calling the same equation Stratonovich instead of Itô.

For $\lambda=0$, put $W^j=\sqrt2B^j$ in N, (10.21)–(10.22).
This matches every coefficient, the unnormalized measure
$dk\,d\alpha\,d\beta$, both circle periods and the height-only exit.
N, Definition 10.6 and Theorem 10.7 supply the identification with the
Dirichlet Friedrichs realization of $-(P^2+Q^2)$. Neither a new
boundary realization nor a new clock is inferred from convergence.
$\square$

**Theorem 7.2 (separation in an original wrapped output).** Fix any
$t\in(0,T]$ and $\lambda$ with $\lambda t/r\notin2\pi\mathbb Z$.
The killed laws with parameters $0$ and $\lambda$ are different, even
though their full first-level Brownian laws, base paths $(K,\alpha)$
and lifetimes agree under the displayed coupling. This difference is
visible in the original middle-reference $02$ coherence pair, without
unwrapping a phase or observing an added central variable.

Proof. Write its two real components as a complex number, including
the arbitrary fixed preparation rotation $\delta_{02}^0$:

$$
Y(K,\beta)=2\sqrt{ZK}\,e^{i(\delta_{02}^0+\beta)},
\qquad Y(\dagger)=0.
\tag{7.3}
$$

This is N, (10.25), with its positive displayed output angle and the
underlying negative amplitude convention unchanged. Conditional on the
entire height path, the integral in (7.1) is centered Gaussian because
$W^2$ is independent of $W^1$. Its conditional variance is
$2\int_0^t(1/2-K_s/r)^2ds$. Thus

$$
\begin{aligned}
\mathbb E Y(q_t^{\lambda,\dagger})
&=e^{-i\lambda t/r}e^{i(\delta_{02}^0+\beta_0)}C_t,\\
C_t&=\mathbb E\left[
 \mathbf1_{\{\tau>t\}}2\sqrt{ZK_t}
 \exp\left\{-\int_0^t(1/2-K_s/r)^2ds\right\}\right]>0.
\end{aligned}
\tag{7.4}
$$

The inequality follows because a Brownian motion started inside an
interval has positive probability to stay inside for any finite time,
and the integrand on survival is strictly positive and bounded. One
elementary justification of that survival fact is to choose
$J=[k-e,k+e]\Subset I$. Uniformly over starting points in $J$, the
probability to end a sufficiently short block inside $J$ is at least
$1/4$, by the Gaussian transition law. If $d$ is the distance from $J$
to the complement of $I$, the reflection bound makes the probability
to exit $I$ during a block of length $h$ at most
$4\exp(-d^2/(4h))$. Choose $N$ so large that $h=t/N$ makes this
bound less than $1/8$. Surviving a block and returning to $J$ then
has conditional probability at least $1/8$. The Markov property
gives a survival probability at least $(1/8)^N>0$.

Multiplication of the nonzero complex number in (7.4) by
$e^{-i\lambda t/r}\ne1$ changes at least one of its two real
components. Those are bounded continuous observables on $E$, so the
killed wrapped laws differ. Corollary 6.2 and the absence of a lifetime
atom at $t$ also imply convergence of these finite-stage expectations.
Consequently sufficiently fine finite-stage actual command laws are
already separated by this observable. Equality of base laws in this
argument is a conclusion about the coupled limits; it does not assert
identical finite-stage $b$ excursions. $\square$

**Remark 7.3 (what is and is not a new direction).** The added central
drift is an accumulated effect of original two-control rectangles. It
is not a new original actuator and uses no third noise. The source ray
dimension is three, the direct control rank is two, the bracket growth
is $(2,3)$, and the local volume exponent for the declared geometry is
four. The bottom-observation base is two-dimensional. These numbers,
task-dependent predictive capacity, and a count of physical spatial
axes are distinct. None of the laws here selects physical three-space.

## 8. Exact costs of the commands which are actually executed

**Proposition 8.1 (literal segment cost accounting).** List the planned
linear segments of Definition 5.1 in time order. A segment $j$ has
duration $d_j>0$ and increment $v_j=(A_j,B_j)$. Let
$\theta_j\in[0,1]$ be the fraction of its duration executed before
$S_n$; completed segments have fraction one, unexecuted segments zero,
and at most one is partial. For (5.4), exactly

$$
\begin{aligned}
\mathsf V_\chi&=\sum_j\theta_j|B_j|,\qquad
\operatorname{Var}(\widehat a_n)=\sum_j\theta_j|A_j|,\\
\mathsf L_{I_2}&=\sum_j\theta_j\sqrt{A_j^2+B_j^2},\\
\mathsf E_{I_2}&=\sum_j\theta_j\frac{A_j^2+B_j^2}{d_j}.
\end{aligned}
\tag{8.1}
$$

The first quantity is the original phase variation N, (10.4). The last
two use precisely the additional identity-matrix norm of N, (10.3);
they are not a physical energy calibration. Every displayed cost is
finite for each finite sample and stage. The constant identity matrix
is defined on a larger interior cylinder containing
$[l,u]\times\mathbb T^2$, so costs at the killing boundary and on
the held source history are well defined. No distance constrained to
the open killing cylinder is being substituted for these path costs.
For a completely executed cell its contributions are

$$
\begin{aligned}
\mathsf V_{\chi,i}&=|\Delta_i^2|+2|\lambda|\sqrt\delta,\\
\operatorname{Var}(a)_i&=|\Delta_i^1|+2\sqrt\delta,\\
\mathsf L_i&=\sqrt{(\Delta_i^1)^2+(\Delta_i^2)^2}
                  +2(1+|\lambda|)\sqrt\delta,\\
\mathsf E_i&=\frac2\delta\{(\Delta_i^1)^2+(\Delta_i^2)^2\}
                  +16(1+\lambda^2).
\end{aligned}
\tag{8.2}
$$

Proof. On a segment the velocity is $v_j/d_j$; integrate its phase
absolute velocity, Euclidean norm and squared norm for time
$\theta_jd_j$. The chord has duration $\delta/2$. The four rectangle
increments are $(\sqrt\delta,0),(0,\lambda\sqrt\delta),
(-\sqrt\delta,0),(0,-\lambda\sqrt\delta)$, each with duration
$\delta/8$. Substitution gives (8.2). Holds after the cutoff have
zero cost. In particular a partial final chord contributes its actual
elapsed fraction, not the full chord cost and not the cost of a
rescaled shorter-time replacement. $\square$

**Proposition 8.2 (finite costs do not furnish a uniform limit budget).**
Under the dyadic Brownian coupling, the actual lengths and declared
energies in (8.1) tend to infinity almost surely as $n\to\infty$.
The actual original phase variations do also, for every fixed
$\lambda$, including zero.

Proof. Almost surely $\tau>0$ and $\tau_n\to\tau$. Choose a positive
dyadic time $t_0<\min(\tau,T)$. For all sufficiently large stages,
all cells up to $t_0$ are completely executed. Their horizontal
rectangles alone contribute $2t_0/\sqrt\delta$ to length and
$16t_0/\delta$ to energy. For $\lambda\ne0$, their phase legs give
at least $2|\lambda|t_0/\sqrt\delta$ of phase variation.

For $\lambda=0$, the executed chords up to $t_0$ give the dyadic
variation sums of $W^2$. They diverge almost surely. To see the needed
fact directly, their sums of squared increments converge to $2t_0$
almost surely along dyadic partitions: the variance of that sum is
$8t_0\delta$, so summability and Borel–Cantelli suffice. Their largest
absolute increment tends to zero by continuity. Since
$\sum|\Delta_i^2|\ge\sum(\Delta_i^2)^2/\max_i|\Delta_i^2|$,
the absolute sums diverge. The property holds simultaneously for the
countably many possible dyadic $t_0$, so choosing one below the random
exit is legitimate. This proves the assertion for the executed prefixes,
not merely for an unexecuted extension. $\square$

No uniform bounded-cost approximation, optimal-rate assertion, acquisition
budget or cost of stochastic sampling follows. Retiming a fixed command
can change its energy but would not preserve the clock required here.

## 9. Sufficient law and weighting data for selecting the reference

**Theorem 9.1 (a sufficient native selection contract).** For a fixed
starting ray and every finite horizon under consideration, the following
additional data suffice to select N's reference killed law:

1. A probability law on finite prescribed original commands, with the
   full native guard, the specified preparation and the actual clock.
2. Joint uniform-path convergence of comparison triples to
   $(W^1,W^2,\int_0^\cdot W^1dW^2)$, where the first two coordinates
   are independent variance-$2t$ Brownian motions in their joint
   filtration; or, equivalently for this purpose, convergence of the
   corresponding held triples and their lifetimes to that stopped law.
3. The height-only first-exit convention for $I$ and lifetime convergence
   jointly with the held path, with no death-time atom at the observation
   horizon. For comparison
   extensions the Brownian crossing condition verifies this item.
4. The stated sampling weights, with no unaccounted conditioning,
   survival renormalization or path-dependent change of measure.

Under these data the limiting killed law exists and is unique. Definition
5.1 with $\lambda=0$ provides an explicit finite-stage existence family
satisfying them. The original deterministic syntax does not select these
data: the same construction with any nonzero $\lambda$ satisfies the
same first-level Brownian law and native guards but gives the distinct
law of Theorem 7.2.

Proof. The continuity and killing theorems give the limit from the joint
data. Given independent $W^1,W^2$, the square-integrable stochastic
integral in (6.1) has a unique continuous version up to indistinguishability,
and (7.1) with $\lambda=0$ determines every state coordinate until
the uniquely specified exit. This proves uniqueness of the resulting
law without any claim that a first-level approximation theorem alone
selects its lift. Existence and the contrasting family were proved in
Sections 5–7. $\square$

**Remark 9.2 (the extra information is joint, not an independent noise).**
Once a Wiener law and its canonical stochastic integral prescription are
specified, $J^0$ can be constructed as a measurable probability limit
of the left sums in (6.4). It is not an independent third source of
randomness. But that prescription is additional to uniform first-level
convergence: the actual rectangles prove that the limiting chronological
coordinate can instead be $J^0+\lambda t$ on the very same Brownian
realization. For this native equation no further iterated levels are
needed. The law up to death and the lifetime suffice; imposing a unique
post-death extension is unnecessary. These are sufficient data and an
explicit separating obstruction, not a globally minimal sampler theorem.

**Proposition 9.3 (what weighting can change).** Let $Z_n$ denote the
entire finite-horizon killed path in $D([0,T],E)$, and let additional
nonnegative sampling weights $w_n$ satisfy $\mathbb Ew_n=1$. Suppose
$(Z_n,w_n)$ converges jointly in distribution to $(Z,w)$ and that the
weights are uniformly integrable. Then the weighted path laws converge
weakly to the probability law characterized by

$$
F\longmapsto\mathbb E[wF(Z)]
\quad\text{for bounded continuous }F.
\tag{9.1}
$$

This law equals the unweighted law of $Z$ if and only if
$\mathbb E[w\mid Z]=1$ almost surely. A simpler sufficient condition
not requiring a separate joint weight limit is
$\mathbb E|w_n-1|\to0$, together with $Z_n\Rightarrow Z$.

Proof. Replace $w_n,w$ first by their truncations at $R$. Joint weak
convergence applies to the resulting bounded continuous product with
$F$. Uniform integrability controls the tails and gives $\mathbb Ew=1$;
let $R\to\infty$ to obtain (9.1). Conditional expectation gives its
Radon–Nikodym density relative to the law of $Z$ as
$\mathbb E[w\mid Z]$. Equality of the two probability measures is
therefore equivalent to that density being one. For the simpler
condition, the difference of weighted and unweighted expectations is
at most $\|F\|_\infty\mathbb E|w_n-1|$. $\square$

The proposition concerns this stated joint-limit setting; arbitrary
weights need not have such a limit. In particular, discarding samples
which die before $T$ and normalizing the survivors selects a conditioned
law rather than the killed subprobability evolution. Definition 5.2
retains every sample and its death event. Selecting a density on a space
of analytic amplitudes, preparing an $L^2$ function, or calibrating
physical sampling costs is a different contract and is not supplied here.

## 10. Classical scope, native contribution and remaining boundaries

**Literature status 10.1 (attested tools and the exact scope used).**

| Source | Status, correspondence and limitation |
| --- | --- |
| N, §§9.1–9.3 and 10.1 | `repo-derived` supplier, reused as ordinary-proof evidence: the exact chronological action, integral order, extrema domain and original/declared costs. Equations (2.3)–(2.7) reuse these results. They do not by themselves specify a random law. |
| N, Definition 10.6 and Theorem 10.7; O, Theorem 2.1 at $\varepsilon=1$ | `repo-derived` suppliers, reused as ordinary-proof evidence: the reference Friedrichs process and its height-killed two-dimensional factor. Equation (7.1) uses exactly covariance $2I_2dt$, density one and the two $2\pi$ circles. Their identification is reused, not deduced from weak convergence of kernels. |
| P. Friz and N. Victoir, *Approximations of the Brownian rough path with applications to stochastic analysis*, Ann. IHP Probab. Statist. 41 (2005), 703–724, [primary text](https://www.numdam.org/item/AIHPB_2005__41_4_703_0.pdf), §5.1, Proposition 26 and Corollary 27 | `literature-attested`: dyadic polygonal Brownian approximations converge jointly with their canonical enhancement. Their Corollary 27 assumes $\varphi\in\Xi_p$ and $\sqrt{-x\log x}/\varphi(x)\to0$. Taking $2<p<3$ and $\varphi(x)=x^{1/p}$ meets these conditions because $\varphi^p=x$ is strictly increasing and convex and $1/2-1/p>0$. The Brownian input here is two-dimensional; time $T$ and amplitude $\sqrt2$ are the deterministic scaling from their unit standard Brownian convention. This attests the classical polygonal supplier. Theorem 6.1 proves directly the narrower uniform joint-coordinate convergence actually needed here, including our added rectangles. |
| P. Friz and H. Oberhauser, *Non-standard approximations of the Itô-map*, [arXiv:0808.0337v1](https://arxiv.org/html/0808.0337v1), §2.1 Theorem 1, §2.2.1 and §4.1 | `literature-attested`: small inserted loops can leave a central correction and hence a bracket drift while preserving the first-level limit. The abstract criterion requires enhanced polygonal convergence, uniform regularity bounds, central mesh discrepancies and their convergence; first-level covariance alone is not its hypothesis. Here the degree-two discrepancy is explicitly $\lambda(t_j-t_i)$ in the $ab$ coordinate, its group size is of order $|t_j-t_i|^{1/2}$, and the within-cell speed is bounded by $2|\Delta_i|/\delta+8\max(1,|\lambda|)\delta^{-1/2}$. The proof used here is (6.3)–(6.7) and the exact native formula, not an invocation of its general RDE theorem or a copied example coefficient. |
| Itô isometry, Doob's $L^2$ maximal inequality, Borel–Cantelli, Brownian strong Markov and reflection principles, continuous mapping theorem | `literature-attested` classical probability tools. Their actual integrability, filtration, covariance, summability and path-continuity hypotheses are stated and checked in (6.5)–(6.7), Proposition 4.5 and Theorem 4.2. No homogenization theorem with an unproved iterated-limit premise is substituted for these checks. |
| The guarded correspondence, lifetime counterexample, executed family and costs, and original-output separation in this volume | `repo-derived`: Sections 3–9 combine the cited classical tools with the pinned native source, with ordinary proofs given here. This classification makes no literature-wide novelty claim. |

The repository search scope is the owning transport source, the native
observation/Green sources and their native-limit terminology; the primary
literature comparison is the two approximation papers above. No claim of
exhaustive literature search or originality is made. Neither an
Ornstein–Uhlenbeck worked coefficient nor an external theorem merely
assuming joint iterated convergence is needed for these proofs.

**Boundary 10.2 (what remains a separate premise).** The native source
provides original finite commands, their chronological effects and their
lawful domains. It does not supply Gaussian sampling, a reason to choose
zero area drift, the sampling weights, a diffusion clock, the added
interior killing interval, or a resource bound for realizing an
approximation sequence. This volume constructs a conditional mathematical
bridge once those items are specified and proves why first-level data
alone leave it underdetermined. A physical origin or preferred selection
of those additions remains unspecified.

The results do not provide analytic-amplitude preparation, a physical
spatial interpretation, an attraction or stability classification, an
optimal-cost theorem, or recovery of an unbounded source. The global
guard, arbitrary fixed phases, native periods and costs remain intact.
Ordinary proofs and the source identifications remain subject to
mathematical review. A finite increment of these results does not
complete a continuous research objective.

## 追加锚（本行以下为增补区）
## 11. Executed approximation classes on the original clock

**Definition 11.1 (source and executed commands).** Retain Definitions
2.1–2.2, the specified ray $q_0=(k,\alpha_0,\beta_0)$, arbitrary fixed
preparation phases, $0<Z<1$, $r=1-Z$, $H=r/2$, and
$0<l<k<u<H$. The probabilities remain $(k,H-k,Z,H-k,k)$ in mode order
$(0,1,2,3,13)$, the amplitude convention remains
$\psi_s=\sqrt{p_s}e^{-i\theta_s}$, and both native phase circles have
period $2\pi$. Fix the original time interval $[0,T]$, with $T>0$.
At each stage choose zero-start absolutely continuous or piecewise $C^1$
comparison controls $(a_n^\circ,b_n^\circ)$ on this interval. Set

$$
\begin{aligned}
\tau_n&=\inf\{t\in[0,T]:k+a_n^\circ(t)\notin(l,u)\},
       &\inf\varnothing&=\infty,\\
S_n&=\tau_n\wedge T,
&a_n(t)&=a_n^\circ(t\wedge S_n),\qquad
b_n(t)=b_n^\circ(t\wedge S_n),\\
J_n(t)&=\int_0^t a_n\,db_n
       =\int_0^{t\wedge S_n}a_n^\circ\,db_n^\circ.
\end{aligned}
\tag{11.1}
$$

Only $(a_n,b_n)$ is executed. It is an original command, with exact
whole-height extrema domain

$$
D_n=(-\min_{[0,T]}a_n,\ H-\max_{[0,T]}a_n).
\tag{11.2}
$$

At the specified start its height lies in $[l,u]\Subset(0,H)$, hence
$k+\min a_n\ge l>0$ and $k+\max a_n\le u<H$. On a compact promise
$[k_-,k_+]$, the very same numerical command is lawful exactly when
$k_-+\min a_n>0$ and $k_++\max a_n<H$; its cutoff is not recomputed
for another starting height. The comparison extension after $S_n$ is
not required to be a source history. The class includes every original
held command obtained this way, without a restriction to a mesh family,
a sampling rule, causality, or a bound on its finite variation.
Random commands, when used, are measurable choices of such commands;
sampling, offline knowledge and conditioning are additional data. A law
assumption below concerns their actual probability measure, without an
implicit change of sampling weights.

Choose common real initial representatives $\alpha_0,\beta_0$ and put
$c_0=1/2-k/r$. The entire executed native state, with these real phase
lifts before wrapping, is

$$
\bar q_n(t)=
\left(k+a_n(t),\,
 [\alpha_0+b_n(t)/2],\,
 [\beta_0+c_0b_n(t)-J_n(t)/r]\right).
\tag{11.3}
$$

Here brackets reduce modulo $2\pi$. This is Proposition 2.3 at every
prefix, including the hold. It uses exactly
$P=\partial_k$ and
$Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta$.
In particular, $J_n$ is the chronological integral of these same
controls, not a separately chosen finite-stage coordinate. The censored
lifetime is $\zeta_n=\tau_n\in[0,T]\sqcup\{\infty\}$, with
$\infty$ an isolated no-death mark. The killed path equals $\bar q_n(t)$
for $t<\zeta_n$ and $\dagger$ for $t\ge\zeta_n$, in the space $E$
of Definition 4.1. Neither the boundary hold nor the cemetery jump is a
new actuator or a reset.

**Definition 11.2 (executed costs).** For the commands in Definition
11.1 write

$$
\begin{aligned}
V_n^a&=\operatorname{TV}_{[0,T]}(a_n)=\int_0^{S_n}|\dot a_n^\circ|\,dt,
&V_n^b&=\mathsf V_{\chi,n}
       =\operatorname{TV}_{[0,T]}(b_n)=\int_0^{S_n}|\dot b_n^\circ|\,dt,\\
L_n&=\int_0^{S_n}\sqrt{(\dot a_n^\circ)^2+(\dot b_n^\circ)^2}\,dt,
&E_n&=\int_0^{S_n}\bigl((\dot a_n^\circ)^2+(\dot b_n^\circ)^2\bigr)\,dt.
\end{aligned}
\tag{11.4}
$$

The energy is allowed to be $+\infty$ for an absolutely continuous
command; finite piecewise linear commands have finite costs. Length and
energy use the additional identity metric of N, (10.3), without a factor
$1/2$ in energy. The original phase variation is N, (10.4), namely
variation of $b$, not of the displayed coordinate $\alpha=b/2+\alpha_0$.
A planned linear leg of duration $d$ and increment $(A,B)$, executed
for a fraction $\theta$, contributes respectively
$\theta|A|$, $\theta|B|$, $\theta\sqrt{A^2+B^2}$ and
$\theta(A^2+B^2)/d$. Its velocity remains $(A,B)/d$ until cutoff.
All later velocities are zero. Thus (11.4) charges neither an unexecuted
extension, a sped-up replacement of the final partial leg, nor a
cemetery jump. Direct integration, the triangle inequality in
$\mathbb R^2$, and Cauchy–Schwarz give

$$
L_n\ge\sqrt{(V_n^a)^2+(V_n^b)^2},\qquad
L_n^2\le S_n E_n\le T E_n.
\tag{11.5}
$$

These are command costs on the declared clock. Acquisition, analytic
amplitude preparation and physical energy require other definitions.

**Assumption 11.3 (target and separate convergence contracts).** Let
$W^1,W^2$ be independent Brownian motions starting at zero with
$[W^i]_t=2t$ and $[W^1,W^2]_t=0$. For an arbitrary fixed
$\lambda\in\mathbb R$, specify jointly

$$
\begin{aligned}
J^\lambda_t&=\int_0^t W^1_s\,dW^2_s+\lambda t,\\
\tau&=\inf\{t\ge0:k+W^1_t\notin(l,u)\},\qquad S=\tau\wedge T,\\
\bar z^\lambda_t&=(W^1_{t\wedge S},W^2_{t\wedge S},J^\lambda_{t\wedge S}),
\qquad
\zeta=\begin{cases}\tau,&\tau\le T,\\\infty,&\tau>T.\end{cases}
\end{aligned}
\tag{11.6}
$$

The integral is in the joint Brownian filtration. The Brownian pair
specifies an additional comparison law; each finite-stage executed
command is still an original absolutely continuous history, with no
physical Brownian input assumed. Define $\bar q^\lambda$
from this triple by (11.3), and $q^{\lambda,\dagger}$ by its censored
lifetime. Proposition 4.5 gives $S>0$ and $\mathbb P(\tau=T)=0$.
This fixes covariance $2I_2\,dt$ before death and the same clock $T$;
the held process has no new fluctuations after $S$.

The qualitative held-law contract is

$$
(\bar q_n,\zeta_n)\ \Rightarrow\ (\bar q^\lambda,\zeta)
\quad\hbox{in }C([0,T],[l,u]\times\mathbb T^2)
             \times([0,T]\sqcup\{\infty\}),
\tag{11.7}
$$

with uniform path topology. The separate cemetery-law contract is
$q_n^\dagger\Rightarrow q^{\lambda,\dagger}$ in $D([0,T],E)$ with
$J_1$ topology. Either may be imposed for the qualitative result below.
A time homeomorphism in $J_1$ compares observations; it never changes a
command's execution clock or its energy. Death information is retained
in (11.7); held uniform convergence alone is not a death convention.

For quantitative statements impose instead the following coupled
pathwise contract. On a space carrying the specified target, the held
triples $(a_n,b_n,J_n)$ converge uniformly to $\bar z^\lambda$ and
$\zeta_n\to\zeta$. Let $\epsilon_n>0$ tend to zero, allowing random,
nonmonotone errors and dependence on the entire target and on extra
randomness. Fix positive constants $d_a,d_b$. For every rational
$0<t<T$ with $t<S$, eventually

$$
t<S_n,\qquad
\sup_{s\le t}|a_n(s)-W^1_s|\le d_a\epsilon_n,
\qquad
\sup_{s\le t}|b_n(s)-W^2_s|\le d_b\epsilon_n.
\tag{11.8}
$$

The eventual index may depend on $t$ and the realization. A uniform
control tube on all of $[0,T]$ around the held target, with these same
radii, is sufficient for (11.8) together with the stated lifetime
convergence. The full chronological and
lifetime convergence remains part of this approximation class even
though the lower bounds use only (11.8). No tube for an unexecuted
comparison extension is assumed. The qualitative contracts do not
include an error variable and do not assert this pathwise coupling.

## 12. Universal executed floors at prescribed control accuracy

**Theorem 12.1 (native executed floors with unequal radii).** There is
one probability-one event determined by the target Brownian pair such
that the following assertion holds for every realization in it: every
sequence of Definition 11.1 satisfying the quantitative contract of
Assumption 11.3, with any positive errors tending to zero, obeys

$$
\begin{aligned}
\liminf_n\epsilon_n V_n^a&\ge S/d_a,&
\liminf_n\epsilon_n V_n^b&\ge S/d_b,\\
\liminf_n\epsilon_n L_n&\ge S\sqrt{d_a^{-2}+d_b^{-2}},&
\liminf_n\epsilon_n^2 E_n&\ge
 \frac{\pi^2 S}{6}(d_a^{-2}+d_b^{-2}).
\end{aligned}
\tag{12.1}
$$

The event is independent of the command sequence, its access to future
information, the errors and $\lambda$. For random commands the assertion
applies wherever their stated pathwise hypotheses hold. In particular
it does not require taking an uncountable intersection of events indexed
by approximation algorithms. It bounds all lawful executed prefixes in
the declared class, rather than only the family of Section 5.

Proof. We use three classical scalar suppliers inside this native
argument. For a continuous real function $f$ on $[0,t]$, write

$$
\operatorname{TV}^{c}(f;[0,t])
 =\sup_{0=t_0<\cdots<t_m=t}
   \sum_{j=1}^m(|f(t_j)-f(t_{j-1})|-c)_+.
\tag{12.2}
$$

Allowing partitions not containing the endpoints gives the same
supremum, since adjoining endpoints cannot reduce it. If
$\|h-f\|_{[0,t]}\le e$, each increment gives
$|h(t_j)-h(t_{j-1})|\ge(|f(t_j)-f(t_{j-1})|-2e)_+$, whence

$$
\operatorname{TV}(h;[0,t])\ge\operatorname{TV}^{2e}(f;[0,t]).
\tag{12.3}
$$

R. M. Łochowski and P. Miłoś, *On truncated variation, upward truncated
variation and downward truncated variation for diffusions*,
[arXiv:1109.0043v2](https://arxiv.org/html/1109.0043v2), Theorem 1
and Remark 2, give, for a continuous semimartingale $X$, the almost
sure uniform-in-time limit $c\operatorname{TV}^c(X;[0,t])\to[X]_t$
as $c\downarrow0$. In particular, on one event for our two coordinates,

$$
\lim_{c\downarrow0}c\operatorname{TV}^c(W^i;[0,t])=2t
\quad(0\le t\le T,\ i=1,2).
\tag{12.4}
$$

The truncation is twice the approximation radius. For a stopped
coordinate the quadratic variation is $2(t\wedge S)$; alternatively,
(12.4) on rational intervals before $S$ supplies all the localization
needed here.

For the stronger energy estimate, let $B$ be standard variance-$t$
Brownian motion and use the scalar free-terminal-end functional

$$
I_B(t,\rho)=\inf\left\{
 \left(\int_0^t|\dot h|^2\,ds\right)^{1/2}:
 h\in AC[0,t],\ h(0)=0,\ \|h-B\|_{[0,t]}\le\rho\right\}.
\tag{12.5}
$$

Its initial value is fixed, and its terminal value is free. This is
precisely the boundary condition needed for a restriction of a native
command. M. Lifshits and E. Setterqvist, *Energy of Taut Strings
Accompanying Wiener Process*,
[arXiv:1405.1651v1](https://arxiv.org/html/1405.1651v1), Theorems
1.1–1.2, prove the same constant $\mathcal C$ for free and pinned
terminal ends, with $\rho I_B(t,\rho)/\sqrt t\to\mathcal C$ in every
$L_q$ as $\rho/\sqrt t\to0$, and almost surely for fixed radius and
long time. Their Proposition 2.2 and (2.17), for any median
$m(t,\rho)$, also give

$$
\mathbb E|I_B(t,\rho)-m(t,\rho)|^2\le1.
\tag{12.6}
$$

The Cameron–Martin Lipschitz constant behind this estimate is one,
independent of $t$ and $\rho$.

M. A. Lifshits and A. A. Podchishchailov, *Asymptotic distribution of
the derivative of the taut string accompanying Wiener process*,
[arXiv:2411.04690v2](https://arxiv.org/html/2411.04690v2), Theorem
1.1, (4), (9) and §7.2, identify $\mathcal C^2=\pi^2/24$. Their
parameter $w$ is the full strip width: their pinned string satisfies
$|h-B|\le w/2$, and its quadratic energy per unit long time tends to
$\pi^2/(6w^2)$. The quadratic function satisfies their power-growth
hypothesis by taking any exponent greater than two. To check the
normalization and the coefficient directly from their density, put
$v=wx$. Then

$$
\begin{aligned}
\int_{\mathbb R}x^2w\frac{wx\coth(wx)-1}{\sinh^2(wx)}\,dx
 &=w^{-2}\int_{\mathbb R}
       \frac{v^2(v\coth v-1)}{\sinh^2v}\,dv\\
 &=\frac{w^{-2}}2\int_{\mathbb R}\frac{v^2}{\sinh^2v}\,dv
  =\frac{\pi^2}{6w^2}.
\end{aligned}
\tag{12.7}
$$

For the integration by parts use
$d(\operatorname{csch}^2v)=-2\coth v\operatorname{csch}^2v\,dv$.
The boundary term $v^3\operatorname{csch}^2v$ vanishes at zero and
at both infinities. On $v>0$,
$\operatorname{csch}^2v=4\sum_{j\ge1}j e^{-2jv}$; termwise integration
of the nonnegative terms gives
$\int_0^\infty v^2\operatorname{csch}^2v\,dv
=\sum_{j\ge1}j^{-2}=\pi^2/6$.
Taking $w=2\rho$ yields $\pi^2/(24\rho^2)$.
The equality of the pinned and free constants is supplied by
Lifshits–Setterqvist; a pinned-end minimum alone would not be a lower
bound for the free-end problem.

Here is the fixed-time, all-radius step needed for native tracking.
Fix $t>0$. The $L_q$ limit implies
$\rho m(t,\rho)\to\mathcal C\sqrt t$: convergence in probability
to a constant forces every median to converge to that constant after
normalization. For $\rho_j=1/j$ and any $v>0$, (12.6) gives

$$
\sum_{j=1}^\infty
\mathbb P\{\rho_j|I_B(t,\rho_j)-m(t,\rho_j)|>v\}
\le v^{-2}\sum_{j=1}^\infty j^{-2}<\infty.
\tag{12.8}
$$

Borel–Cantelli for positive rational $v$ proves
$\rho_jI_B(t,\rho_j)\to\mathcal C\sqrt t$ almost surely.
The function $I_B(t,\rho)$ is nonincreasing in $\rho$. For
$\rho_{j+1}\le\rho\le\rho_j$,

$$
\frac{\rho_{j+1}}{\rho_j}\rho_jI_B(t,\rho_j)
\le\rho I_B(t,\rho)
\le\frac{\rho_j}{\rho_{j+1}}\rho_{j+1}I_B(t,\rho_{j+1}).
\tag{12.9}
$$

Both ratios tend to one, proving the limit over all real radii
$\rho\downarrow0$ on this same fixed-time event. Intersect these
events for all positive rational $t<T$, and for both standard
coordinates $W^i/\sqrt2$. This is a countable intersection. Amplitude
scaling in (12.5) gives
$I_{\sigma B}(t,e)=\sigma I_B(t,e/\sigma)$ for $\sigma>0$, hence,
on the resulting event,

$$
\lim_{e\downarrow0}e^2 I_{W^i}(t,e)^2
 =4\mathcal C^2t=\frac{\pi^2t}{6},
\qquad t\in\mathbb Q\cap(0,T),\quad i=1,2.
\tag{12.10}
$$

This uses the fourth power of the amplitude scale for squared energy,
not its second power. Long-time almost sure convergence has not been
substituted for a fixed-time assertion by an equality in law.

Intersect (12.4), (12.10), Brownian continuity, continuity of the chosen
Itô integral, and the probability-one lifetime properties of Proposition
4.5. This defines the required target-only event. Fix one of its
realizations and a rational $0<t<S$. For all large $n$, (11.8),
(12.3) and (12.4) give

$$
\liminf_n\epsilon_n V_n^a\ge t/d_a,
\qquad
\liminf_n\epsilon_n V_n^b\ge t/d_b.
\tag{12.11}
$$

The same actual restrictions $a_n|_{[0,t]}$ and $b_n|_{[0,t]}$
are competitors for the free-end scalar problems with radii
$d_a\epsilon_n,d_b\epsilon_n$. Therefore

$$
E_n\ge I_{W^1}(t,d_a\epsilon_n)^2
          +I_{W^2}(t,d_b\epsilon_n)^2.
\tag{12.12}
$$

They are restrictions of one jointly realized native history; no two
separately optimized scalar paths have been spliced into a native
history. Equation (12.10) proves the energy bound with $t$ in place
of $S$. Equation (11.5) and (12.11) give the length bound. Finally
take the supremum over rational $t<S$. Since $S>0$, this supremum
is $S$, including when $S=T$. Every cost used up to $t$ is actually
executed. No stopped path is declared to be an unstopped Brownian
motion, and no cost is assigned after its own exit. $\square$

**Corollary 12.2 (equal control tubes and expected costs).** With
$d_a=d_b=1$, on the event of Theorem 12.1,

$$
\liminf_n\epsilon_n V_n^a\ge S,\qquad
\liminf_n\epsilon_n\mathsf V_{\chi,n}\ge S,\qquad
\liminf_n\epsilon_n L_n\ge\sqrt2S,\qquad
\liminf_n\epsilon_n^2E_n\ge\frac{\pi^2S}{3}.
\tag{12.13}
$$

Consequently all four costs tend to infinity on every such coupled
realization. If the quantitative assumptions hold almost surely and
$\epsilon_n$ are deterministic, then

$$
\begin{aligned}
\liminf_n\epsilon_n\mathbb EV_n^a&\ge\mathbb ES,&
\liminf_n\epsilon_n\mathbb EV_n^b&\ge\mathbb ES,\\
\liminf_n\epsilon_n\mathbb EL_n&\ge\sqrt2\mathbb ES,&
\liminf_n\epsilon_n^2\mathbb EE_n&\ge\pi^2\mathbb ES/3.
\end{aligned}
\tag{12.14}
$$

For random errors, the valid statements place the errors inside the
expectations, for example
$\liminf_n\mathbb E[\epsilon_n^2E_n]\ge\pi^2\mathbb ES/3$;
there is no replacement of this expectation by
$(\mathbb E\epsilon_n)^2\mathbb EE_n$ without further hypotheses.

Proof. Specialize (12.1) and use $S>0$, $\epsilon_n\to0$.
Fatou's lemma applies to each nonnegative normalized cost. The stopping
coefficient is $\mathbb ES\in(0,T]$, not $T$ in general. The elementary
variation/length bound $L_n^2\le TE_n$ gives the energy floor $2S^2/T$;
using $L_n^2\le S_nE_n$ and $S_n\to S>0$ improves it to $2S$.
Both are below the stronger coefficient $\pi^2S/3$ supplied by
(12.12). $\square$

## 13. Accuracy of complete wrapped native paths

**Definition 13.1 (maximum-coordinate native path metric).** On the
held cylinder declare

$$
\begin{aligned}
d_{\max}((h,\alpha,\beta),(h',\alpha',\beta'))
 &=\max\{|h-h'|,d_{\mathbb T}(\alpha,\alpha'),
                   d_{\mathbb T}(\beta,\beta')\},\\
d_{\mathbb T}([x],[y])&=\min_{j\in\mathbb Z}|x-y-2\pi j|,\\
D_{\max}(q,q')&=\sup_{0\le t\le T}d_{\max}(q(t),q'(t)).
\end{aligned}
\tag{13.1}
$$

This is an additional, unweighted coordinate error metric, with angles
measured in radians. It is not the horizontal path length (11.4).
A native accuracy contract consists of
$D_{\max}(\bar q_n,\bar q^\lambda)\le\eta_n\to0$ and
$\zeta_n\to\zeta$ on the same coupling, with common fixed initial
phase representatives. Errors $\eta_n>0$ may be random. The metric
tracks the entire held path; the lifetime is retained separately.

**Theorem 13.2 (wrapped-path transfer and native constants).** The
contract of Definition 13.1 implies the quantitative contract of
Assumption 11.3 with $\epsilon_n=\eta_n$, $d_a=1$, $d_b=2$.
On the target-only event of Theorem 12.1 it therefore forces

$$
\begin{aligned}
\liminf_n\eta_n V_n^a&\ge S,&
\liminf_n\eta_n\mathsf V_{\chi,n}&\ge S/2,\\
\liminf_n\eta_n L_n&\ge\frac{\sqrt5}{2}S,&
\liminf_n\eta_n^2E_n&\ge\frac{5\pi^2}{24}S.
\end{aligned}
\tag{13.2}
$$

Proof. Eventually $\eta_n<\pi$. For either circle, the difference of
the two continuous real lifts starts at zero. If its circle distance
is at most $\eta_n$ throughout the connected interval $[0,T]$, that
difference lies in the union of the disjoint closed intervals
$[2\pi j-\eta_n,2\pi j+\eta_n]$. Continuity and its initial value
force it to stay in the interval with $j=0$. Thus the two real phase
differences are uniformly at most $\eta_n$, even if each path has
many windings. Applying the exact inverse of (11.3) gives

$$
\begin{aligned}
\|a_n-W^1_{\cdot\wedge S}\|_\infty&\le\eta_n,\\
\|b_n-W^2_{\cdot\wedge S}\|_\infty&\le2\eta_n,\\
\|J_n-J^\lambda_{\cdot\wedge S}\|_\infty
 &\le r(1+2|c_0|)\eta_n.
\end{aligned}
\tag{13.3}
$$

This also proves the required full chronological convergence. Lifetime
convergence makes each rational $t<S$ an executed pre-death interval
for all sufficiently large $n$. Substitution in (12.1) gives (13.2).
In particular, reusing the equal-control-tube constants for $\eta_n$
would neglect the factor two in $b=2(\widetilde\alpha-\alpha_0)$.
The phase lift uses the original $2\pi$ periods, not a doubled period.

Conversely, on complete held triples, first-level errors $e_a,e_b$
and chronological error $e_J$ imply

$$
D_{\max}(\bar q_n,\bar q^\lambda)
\le\max\{e_a,e_b/2,|c_0|e_b+e_J/r\}.
\tag{13.4}
$$

This follows from (11.3) and the Lipschitz circle projection. A small
first-level error alone gives no bound on $e_J$. Thus the forward
transfer does not omit the full-lift or lifetime obligations. $\square$

## 14. A rate-free obstruction from full native law convergence

**Theorem 14.1 (executed costs escape every bounded budget in law).**
Suppose either qualitative contract in Assumption 11.3 holds for a
sequence of Definition 11.1. Then, for every finite $M$,

$$
\mathbb P(V_n^a\le M)\to0,\qquad
\mathbb P(\mathsf V_{\chi,n}\le M)\to0,\qquad
\mathbb P(L_n\le M)\to0,\qquad
\mathbb P(E_n\le M)\to0.
\tag{14.1}
$$

Thus each cost diverges in probability and its laws are not tight on
$[0,\infty)$. In the extended sense each expected cost tends to
$+\infty$. This statement requires neither a tube radius nor any
specified stage rate. It makes no almost-sure claim on an unspecified
original coupling.

Proof. First consider the held-law contract. Continuous lifting of a
circle path with its fixed initial representative is continuous for
uniform convergence: once two paths are uniformly closer than $\pi$,
the connected-interval argument in Theorem 13.2 applies. Hence the
inverse (2.6) is a continuous map on the held path space with fixed
initial point. In particular

$$
a_n\Rightarrow W^1_{\cdot\wedge S},\qquad
b_n\Rightarrow W^2_{\cdot\wedge S}
\quad\hbox{in the uniform topology}.
\tag{14.2}
$$

On a common probability-one Brownian event, each coordinate has infinite
total variation on every rational interval $[0,t]$ with $t>0$.
For example its dyadic squared-increment sums converge to $2t$ almost
surely, while the largest increment tends to zero; finite total
variation would force those squared sums to tend to zero. Countably
many rational $t$ suffice. Since $S>0$, choose such a $t<S$.
Both stopped coordinates therefore have infinite variation almost
surely, even though they are constant after $S$.

Total variation on continuous real paths is the supremum of continuous
finite-partition sums. Its finite sublevel sets are closed. Portmanteau
applied to (14.2) gives the first two limits in (14.1). No compactness
of those sublevel sets is needed. Equation (11.5) gives the length
and energy limits, since $L_n\ge V_n^b$ and
$E_n\ge(V_n^b)^2/T$.

For the cemetery-law contract use the Skorokhod representation theorem
on the Polish space $D([0,T],E)$ to realize copies converging almost
surely in $J_1$. This representation is only a proof of statements
about the given marginal laws. Fix a limiting realization with $S>0$
and infinite Brownian variation on all positive rational intervals.
For a rational $0<t<S$, the limit is alive and continuous on a
slightly longer interval. $J_1$ convergence, isolation of $\dagger$
and uniform continuity there imply that the copied finite paths are
eventually alive on $[0,t]$ and converge uniformly on this interval.
Their real phase lifts from the common initial value therefore
converge uniformly too. Finite-partition sums then show

$$
\liminf_n\operatorname{TV}_{[0,t]}(a_n)=+\infty,
\qquad
\liminf_n\operatorname{TV}_{[0,t]}(b_n)=+\infty
\tag{14.3}
$$

for the copied controls recovered from these paths. These are lower
bounds for the costs of the actual executed prefixes.
More explicitly, for an actual killed path the phase cost is twice
the supremum of
$\sum_j d_{\mathbb T}(\alpha(t_j),\alpha(t_{j-1}))$ over rational
pre-death partitions starting at zero. On each compact alive interval,
continuity permits refinement until every real lifted increment has
absolute value less than $\pi$; the circle distances then equal those
absolute increments. This proves equality with $\operatorname{TV}(b)$,
including windings. The height variation has the analogous partition
formula with absolute height differences. These are measurable
functions of the killed path. Continuity supplies the terminal value
at a finite death by the left limit, and at $T$ by a limit from below
when there is no death, so their suprema are the actual held variations.
Each such functional has the
same law for the copies as for the original commands. Thus (14.3)
implies the first two limits of (14.1) in the original laws; (11.5)
again handles length and energy. Nothing assigns variation or energy
to the jump into $\dagger$. In particular one has not lifted a circle
path through that jump or used a post-death comparison extension.

For any nonnegative cost $C_n$ in (14.1),
$\mathbb EC_n\ge M\mathbb P(C_n>M)$. Taking the lower limit and
then $M\to\infty$ gives divergence of expectations. A uniformly
bounded expected budget would also contradict (14.1) directly by
Markov's inequality. No uniform integrability premise is needed for
this lower-bound consequence. $\square$

## 15. Exact boundaries of the resource conclusions

**Proposition 15.1 (even a full terminal lift and lifetime do not force
the tracking floors).** With additional offline access to
$(W^1_S,W^2_S,J^\lambda_S,S,\zeta)$, there is a single original
piecewise linear held command having exactly the target's terminal
real lifted state and censored lifetime, and finite costs almost
surely. Repeating this command at every stage refutes any inference
of (12.13) or (13.2) from terminal accuracy alone, even if terminal
chronology and death time are also exact.

Proof. Put $A=W^1_S$, $B=W^2_S$, $C=J^\lambda_S$, and fix
$0<d<u-k$. On $[0,S]$ give each of the following six legs duration
$S/6$, with the displayed vertices in the control plane:

$$
(0,0),\ (d,0),\ (d,C/d),\ (0,C/d),\ (0,0),\ (0,B),\ (A,B).
\tag{15.1}
$$

The rectangle has chronological integral $d(C/d)=C$. The phase leg
at $a=0$ and the final height leg contribute zero to $\int a\,db$.
Thus the terminal control triple is exactly $(A,B,C)$ on this same
realization. Before the last leg, all heights lie in $[k,k+d]\Subset I$.
On the last leg the height moves from $k$ toward $k+A\in[l,u]$.
It first meets the killing boundary at $S$ exactly when $\zeta<\infty$;
otherwise $S=T$ and it remains in $I$. Hold thereafter. Since $S>0$
and $A,B,C$ are finite, all six original-velocity costs are finite.
The whole-height guard holds strictly within $(0,H)$ throughout.
The prescribed command has its ordinary domain (11.2); no operation
is asserted outside it. For any positive tolerances tending to zero,
the repeated command has zero terminal error while every normalized
cost in (12.13) tends to zero. Its entire path is not asserted to
track the target. Access to those terminal random variables is the
explicit additional information used by this witness. $\square$

**Proposition 15.2 (weak law does not force almost-sure cost divergence
on the original coupling).** There are lawful sequences satisfying
both qualitative contracts, and even convergence in probability of
the coupled held paths and lifetimes, whose executed costs are zero
infinitely often almost surely.

Proof. Use the coupled finite dyadic family of Sections 5–6 for the
fixed $\lambda$. Independently sample Bernoulli variables $D_n$ with
$\mathbb P(D_n=1)=1/(n+1)$. At stage $n$, prescribe the zero command
when $D_n=1$, and the dyadic command otherwise. Each choice is a
complete original command starting from the same specified ray; there
is no reset within a command. The zero command has $J=0$, no death,
full native guard and zero costs. The probability of replacing the
dyadic command tends to zero, so the new full held/lifetime and killed
laws have the same limits: for any bounded test their expectation
difference is at most twice its supremum norm divided by $n+1$.
The same probability bound gives coupled convergence in probability.
Independence and $\sum_n1/(n+1)=\infty$ give $D_n=1$ infinitely often
almost surely. Hence almost-sure divergence of costs fails on this
coupling, although Theorem 14.1 still applies. This witness changes
neither the good samples' chronology nor their own death times.
$\square$

**Proposition 15.3 (no universal growth rate in the stage label).** For
any deterministic positive sequence $R_n\to\infty$, there is a lawful
full-native approximation sequence, with the clock still $T$ and the
specified target $\lambda$, whose four executed costs are all
$o(R_n)$ almost surely. It can retain almost-sure convergence of the
held triples and censored lifetimes and $J_1$ convergence of the killed
paths. Thus (12.1) is a rate in the declared accuracy, not in an
unconstrained enumeration of stages.

Proof. Let the dyadic family be indexed by $m$ and put
$C_m=1+V_m^a+V_m^b+L_m+E_m$. Each $C_m$ is finite almost surely.
Choose deterministic $K_m\ge1$ with
$\mathbb P(C_m>K_m)\le2^{-m}$. Select strictly increasing integers
$N_m$ such that $R_n\ge mK_m$ whenever $n\ge N_m$.
For $N_m\le n<N_{m+1}$, use precisely stage $m$'s command and sample
from the original coupling. Borel–Cantelli gives $C_m\le K_m$
eventually almost surely, so $C_m/R_n\le1/m$ throughout all
sufficiently late blocks. Since $m\to\infty$, the asserted cost and
path limits follow. The finitely many initial labels can use the
first command. Repetition changes an index, not the time parametrization
of any executed command; partial segments and their costs are unchanged.
No estimate relating this new label to its path error is implied.
$\square$

**Proposition 15.4 (random lifetime and the absence of a hard samplewise
budget).** For any fixed $T>0$, one has $\mathbb P(S<T)>0$ and
$\mathbb P(S=T)>0$, and $S$ has no deterministic positive lower bound.
Moreover, at any fixed control tube radius $e>0$, no finite deterministic
bound on phase variation, length or identity energy can accommodate
all realizations satisfying the full held control tube around this
Brownian target almost surely.

Proof. A Brownian height can leave $I$ in any positive time with
positive probability, since a sufficiently large Gaussian increment
forces exit by continuity. Survival to $T$ has positive probability
by the argument in Theorem 7.2. These facts prove the assertions about
$S$. On the event $S=T$, a full tube implies
$|b_n(T)-W^2_T|\le e$, and therefore

$$
V_n^b\ge(|W^2_T|-e)_+,\qquad L_n\ge V_n^b,
\qquad E_n\ge(V_n^b)^2/T.
\tag{15.2}
$$

The survival event depends only on $W^1$, and $W^2_T$ is an independent
Gaussian with unbounded support. Every proposed finite deterministic
budget is exceeded with positive probability. For the native metric
radius $e<\pi$, replace $e$ by $2e$ in (15.2), by Theorem 13.2.
This argument also rules out a time-independent hard budget, since it
already rules one out on the specified fixed horizon. It does not
assert that any finite-radius full-lift tracking class is nonempty.
$\square$

**Proposition 15.5 (what the first-level floors leave unselected).**
The necessary bounds (12.1) and (13.2) apply with the same constants
to every fixed area drift $\lambda$. They do not select a native law,
prove full-lift attainment of a lower bound, or turn a scalar
free-end optimizer into a full-native optimizer.

Proof. The Brownian first-level pair, $S$, and the target-only event
in Theorem 12.1 are common to all these drifts. Every scalar inequality
used there holds for a restriction of any admitted native command,
regardless of its chronological integral. The construction in Sections
5–7 provides actual lawful approximating families for every fixed
$\lambda$, with the distinct wrapped laws established in Theorem 7.2.
Thus the resource inequalities cannot single out $\lambda=0$.

The scalar minima in (12.12) relax both the common chronological
constraint $J_n=\int a_n\,db_n$ and the requested accuracy of the
full $\beta$ path and lifetime. Lower bounds for that larger feasible
set imply lower bounds for the native set, but supply no command
in the latter set attaining them. The classical scalar free-end
optimizer may depend on the entire Brownian path. Its existence
therefore gives no causal access rule, finite-bit sampler, or optimal
causal native command. The explicit native families establish
convergence, not a matching upper bound in the error variable of
(12.13) or (13.2). No sharp full-native optimum follows.

The costs and error metrics in these statements have the definitions
(11.4) and (13.1). They add no calibration of physical energy or
acquisition cost, and no preparation of an analytic amplitude. Their
state is the original three-dimensional ray manifold with control
rank two, bracket growth $(2,3)$ and declared local volume exponent
four; the bottom-observation base remains two-dimensional. Those
objects, task-dependent predictive memory, a number of stored
coordinates and a number of physical spatial axes have different
definitions. None is identified with another by a resource inequality.
The statements fix the starting ray, horizon, killing interval and
actual joint target law; they assert no uniform-in-start, all-Borel
or heat-kernel approximation. $\square$

## 追加锚（本行以下为增补区）

## 16. An offline enhanced target and a terminal partition

**Definition 16.1 (sampling information and accuracy range).** Retain
Definitions 2.1, 11.1–11.3 and 13.1. In particular, fix
$0<Z<1$, $r=1-Z$, $H=r/2$, a starting ray
$q_0=(k,\alpha_0,\beta_0)$, $0<l<k<u<H$, $T>0$, and an arbitrary
fixed $\lambda\in\mathbb R$. The probabilities are
$(k,H-k,Z,H-k,k)$ in the original mode order. Preparation phases are
arbitrary and fixed; the negative amplitude convention and both
$2\pi$ periods are unchanged. The fields are precisely

$$
P=\partial_k,\qquad
Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta.
\tag{16.1}
$$

Use one probability space with its original Wiener measure $\mathbb P$,
carrying the independent covariance-$2$ Brownian coordinates $W^1,W^2$
and their jointly specified continuous enhancement
$J^\lambda=\int W^1\,dW^2+\lambda t$. The Brownian motions may be
continued on $[0,\infty)$ for comparison estimates. Put $S=\tau\wedge T$
and retain the censored death mark $\zeta$ of (11.6). All expectations
below are with respect to this same $\mathbb P$.

The information supplied to the command selector is the complete stopped
enhanced path $(W^1,W^2,J^\lambda)_{\cdot\wedge S}$ on $[0,T]$ and
$\zeta$. It includes exact real values, area, and lifetime. There is no
extra randomness, rejection, survival conditioning, or change of measure.
The selector has offline access to these data, including values later
than the time at which a selected leg starts. A finite list of real
commands obtained from this information is not a finite-bit sampling
algorithm or a causal acquisition rule. Acquisition cost is not defined
by the control costs (11.4).
Only the selected absolutely continuous controls are native inputs;
the Wiener sample is mathematical comparison data, not a physical
Brownian actuator or a prepared analytic amplitude.

Set

$$
\begin{aligned}
d_*&=\min\{k-l,u-k\},&
K_*&=\max\{k-l,u-k\},\\
\rho_*&=\min\{r/4,(u-l)/4,d_*/2,\sqrt T\},&
\eta_*&=4\rho_*.
\end{aligned}
\tag{16.2}
$$

For a prescribed deterministic $0<\eta\le\eta_*$, use the auxiliary
spatial scale $\rho=\eta/4$. The error variable in the conclusions is
$\eta$ in the complete native metric (13.1).

**Definition 16.2 (joint increment mesh).** For $s\le t$ define the
relative chronological increment of the one target by

$$
C_{s,t}=J^\lambda_t-J^\lambda_s
             -W^1_s(W^2_t-W^2_s).
\tag{16.3}
$$

Starting with $t_0=0$, recursively put

$$
\begin{aligned}
F_\rho(s,t)&=\max\left\{
 \frac{|W^1_t-W^1_s|}{\rho},\frac{|W^2_t-W^2_s|}{\rho},
 \frac{|C_{s,t}|}{\rho^2}\right\},\\
t_{i+1}&=\min\{t_i+\rho^2,\ \inf\{t>t_i:F_\rho(t_i,t)\ge1\}\},\\
\Delta_i&=t_{i+1}-t_i.
\end{aligned}
\tag{16.4}
$$

The infimum of an empty set is $\infty$. These are stopping times in
the joint Brownian filtration. The mesh is an analytic partition of the
target; it does not itself prescribe any control legs. On each elementary
interval, including its endpoint, continuity gives

$$
\sup_{t_i\le v\le t_{i+1}}|W^j_v-W^j_{t_i}|\le\rho\quad(j=1,2),
\qquad
\sup_{t_i\le v\le t_{i+1}}|C_{t_i,v}|\le\rho^2.
\tag{16.5}
$$

Random spatial knots and energy bounds using inverse interval durations
are classical: see Lifshits–Setterqvist,
[*Energy of Taut Strings Accompanying Wiener Process*,
arXiv:1405.1651v1, §4.2](https://arxiv.org/html/1405.1651v1).
Their scalar construction does not supply the chronological condition
in (16.4), the native guard, or exact native death. Those conditions
are retained in the construction below.

**Proposition 16.3 (finite terminal partition with a duration charge).**
On the event of continuous enhanced target paths, the mesh has only
finitely many points in every bounded time interval. Let

$$
N=\#\{i\ge0:t_i<S\},\qquad t_{N-1}<S\le t_N.
\tag{16.6}
$$

There is the following measurable partition $\mathcal P_\rho$ of
$[0,S]$. If $S=t_N$, use all $N$ elementary intervals ending at $S$.
If $S<t_N$, use the elementary intervals with indices
$0,\ldots,N-3$ and the single final interval $[t_{N-2},S]$.
In the latter case $N\ge2$, and an empty list of earlier intervals is
allowed. Write $M$ for the number of intervals in this partition.
Then $M\le N$. Every partition interval $[s,t]$ satisfies

$$
\begin{aligned}
\sup_{s\le v\le t}|W^j_v-W^j_s|&\le2\rho\quad(j=1,2),\\
\sup_{s\le v\le t}|C_{s,v}|&\le3\rho^2.
\end{aligned}
\tag{16.7}
$$

Moreover its duration $D=t-s$ can be charged to a distinct elementary
index $i$ with $t_i<S$, so that

$$
s=t_i,\qquad D\ge\Delta_i.
\tag{16.8}
$$

All partition starts are strictly before $S$ and hence have target
height in $I$.

Proof. On $[0,L+\rho^2]$, continuity of $W^1,W^2,J^\lambda$
and boundedness of $W^1$ imply uniformly for $s\le L$ that all three
quantities in (16.4) remain below their thresholds when $t-s$ is
sufficiently small. Thus, for fixed $\rho>0$, there is a positive
lower bound on the mesh durations whose starting times lie in $[0,L]$,
after also taking the minimum with $\rho^2$.
This proves nonaccumulation. It proves it simultaneously for every
positive $\rho$ on the same event of continuous target paths.

The first mesh endpoint satisfies $t_1\le\rho^2\le T$.
Before and at $t_1$, $|W^1|\le\rho<d_*$, so the height cannot have
exited $I$ there. Consequently $S\ge t_1$. In particular the case
$S<t_N$ cannot have $N=1$. The stated partition therefore always
exists, without a separate short initial or terminal interval.

For a merged interval let $v$ lie after its middle mesh point $m$.
The same target satisfies the exact chronological identity

$$
C_{s,v}=C_{s,m}+C_{m,v}
              +(W^1_m-W^1_s)(W^2_v-W^2_m).
\tag{16.9}
$$

Equation (16.5) bounds the first two terms by $\rho^2$ and the product
by $\rho^2$. Adding the two first-level increments gives (16.7).
Before $m$ the stronger bounds (16.5) apply. The ordinary intervals
also satisfy (16.7). Charge an ordinary interval to itself and the
merged final interval to its first, complete elementary interval.
These indices are distinct and prove (16.8). In particular the
possibly arbitrarily short remainder $S-t_{N-1}$ is never used
alone as an energy denominator.

Hitting times of the closed threshold sets in (16.4), evaluations of
continuous paths at these times, and the finite comparisons defining
the partition are measurable. The choice can be determined from the
stopped enhanced path and its death mark: no value after $S$ is
needed to tell whether a threshold was reached before or at $S$.
The full endpoint $t_N$ when it exceeds $S$ is needed only for an
integrable dominating quantity in Section 18. $\square$

## 17. A bounded guarded connector at every actual prefix

**Lemma 17.1 (quantitative inward rectangle and final height leg).**
Let a partition interval $[s,t]$ have duration $D>0$, starting height
$h\in I$, and desired relative endpoint $(X,Y,C)$ with

$$
|X|,|Y|\le2\rho,\qquad |C|\le3\rho^2,\qquad h+X\in[l,u].
\tag{17.1}
$$

Assume $\rho\le(u-l)/4$. Choose

$$
d=\begin{cases}\rho,&h\le(l+u)/2,\\-\rho,&h>(l+u)/2,
\end{cases}
\qquad q=C/d.
\tag{17.2}
$$

Use the following relative control vertices, giving each of the six
legs exactly $D/6$ units of the original time:

$$
(0,0),\ (d,0),\ (d,q),\ (0,q),\ (0,0),\ (0,Y),\ (X,Y).
\tag{17.3}
$$

A zero increment is a hold of its assigned duration. Write $(x(v),y(v))$
for this connector and $j(v)=\int_s^v x\,dy$. Its endpoint is
$(X,Y,C)$ and every partial prefix obeys

$$
|x(v)|\le2\rho,\qquad |y(v)|\le3\rho,\qquad |j(v)|\le3\rho^2.
\tag{17.4}
$$

The height $h+x(v)$ is in $I$ for $s\le v<t$. At $t$ it is on
the killing boundary if and only if $h+X$ is there. The interval's
actual variation, length and unhalved identity energy are

$$
\begin{aligned}
V^a_{s,t}&=2\rho+|X|\le4\rho,\\
V^b_{s,t}&=2|q|+|Y|\le8\rho,\\
L_{s,t}&=2\rho+2|q|+|X|+|Y|\le12\rho,\\
E_{s,t}&=\frac6D(2\rho^2+2q^2+X^2+Y^2)
                              \le\frac{168\rho^2}{D}.
\end{aligned}
\tag{17.5}
$$

Proof. The rectangle in (17.3) is the original two-control rectangle
used in Proposition 15.1 and N, Theorem 9.3. Its inward orientation
makes the full excursion lawful: when $d=\rho$, its maximum height
is at most $(l+u)/2+(u-l)/4<u$ and its minimum is $h>l$.
For $d=-\rho$ the symmetric inequalities apply. The next phase leg
has height $h$. The last height leg is the linear segment from the
interior point $h$ to $h+X\in[l,u]$; every point before its terminal
one is interior. Thus no earlier leg reaches the killing boundary.

Only the second leg contributes to the relative integral $\int x\,dy$.
It varies linearly from zero to $dq=C$ there and remains $C$ on all
later legs. This proves the endpoint area and every partial bound in
(17.4), since $|q|\le3\rho$. Translation to an actual control start
$(a_s,b_s)$ gives exactly

$$
\int_s^v a\,db=a_s y(v)+j(v).
\tag{17.6}
$$

Thus the chronological cross term is retained. Every leg is along
one of the two original control axes. Its velocity is its displayed
increment divided by $D/6$. Direct integration gives (17.5), including
$6(2+18+4+4)=168$. These are bounds for the explicit native control,
not an appeal to a steering theorem. $\square$

**Definition 17.2 (the finite command).** On each interval $[s,t]$ of
$\mathcal P_\rho$, use Lemma 17.1 with

$$
\begin{aligned}
h&=k+W^1_s,& X&=W^1_t-W^1_s,\\
Y&=W^2_t-W^2_s,& C&=C_{s,t},
\end{aligned}
\tag{17.7}
$$

and translate the connector by $(W^1_s,W^2_s)$. Concatenate in the
original chronological order and hold the two controls constant from
$S$ to $T$. Denote this command by $(a_\eta,b_\eta)$ and its ordinary
chronological integral by $J_\eta=\int a_\eta\,db_\eta$.
The prescribed control starts at zero and has at most $6N$ linear
legs before its final hold. Its velocities are fixed by (17.3) before
execution; the elementary mesh in (16.4) carries no earlier velocity
prescription to be truncated or accelerated.

The command is a measurable function of the information in Definition
16.1: on each event specifying a finite partition size, the knot values,
positive durations, orientation choice and slopes are Borel functions
of the supplied paths. Piecewise linear interpolation has measurable
evaluations at every rational time; these generate the Borel sigma
algebra of the continuous-path space. Its finite list has real-valued
times and increments. It uses
area-dependent future endpoints and the final partition depending on
$S$, so adaptedness of the analytic mesh does not assert adaptedness
of the command selector. The finite-stage $J_\eta$ is the integral
of these same selected controls, never a separately supplied actuator.

**Proposition 17.3 (complete held accuracy and exact own death).**
The command in Definition 17.2 is an original finite piecewise linear
native history at the specified start. Its own censored exit is exactly
$\zeta_\eta=\zeta$, its execution horizon is $S_\eta=S$, and its
whole-height source guard is

$$
k+\min_{[0,T]}a_\eta\ge l>0,\qquad
k+\max_{[0,T]}a_\eta\le u<H.
\tag{17.8}
$$

Its entire held chronological triple satisfies

$$
\begin{aligned}
\|a_\eta-W^1_{\cdot\wedge S}\|_\infty&\le4\rho,\\
\|b_\eta-W^2_{\cdot\wedge S}\|_\infty&\le5\rho,\\
\|J_\eta-J^\lambda_{\cdot\wedge S}\|_\infty
                                  &\le5K_*\rho+6\rho^2.
\end{aligned}
\tag{17.9}
$$

Every triple agrees exactly with the target at partition endpoints,
including $S$, and therefore throughout the terminal hold. With the
fixed real phase representatives from Section 2, one has the stronger
direct phase estimates

$$
\begin{aligned}
\|\widetilde\alpha_\eta-\widetilde\alpha^\lambda_{\cdot\wedge S}
  \|_\infty&\le\tfrac52\rho,\\
\|\widetilde\beta_\eta-\widetilde\beta^\lambda_{\cdot\wedge S}
  \|_\infty&\le\tfrac52\rho+6\rho^2/r\le4\rho.
\end{aligned}
\tag{17.10}
$$

Consequently

$$
D_{\max}(\bar q_\eta,\bar q^\lambda)\le4\rho=\eta
\quad\text{on the entire }[0,T].
\tag{17.11}
$$

These deterministic estimates hold on one probability-one target event
for every $0<\eta\le\eta_*$. They include every partial leg and the
merged terminal interval, not just the mesh endpoints.

Proof. Equations (16.7) and (17.7) satisfy all the connector hypotheses.
Each target height at a partition start is interior. Only the last
partition endpoint can be on the killing boundary, and it is on that
boundary exactly on $\{\zeta<\infty\}$. Lemma 17.1 proves that the
command first reaches it at $S$, if it reaches it at all. If there
is no target death on the horizon, even the endpoint at $S=T$ is
interior, and the command has no death. A death at $T$ is also
handled exactly. This proves the claimed own-exit and death mark,
without using a limiting crossing argument.

The concatenation is continuous at each join because both first-level
endpoints are exact. Its integral at the next endpoint is the previous
integral plus $W^1_sY+C_{s,t}$, by (17.6). Induction and (16.3) prove
that it is exactly $J^\lambda_t$. In particular the state at every
join is one continuous chronological state, with no reset of phases,
height, or integral. All heights lie in $[l,u]$, proving (17.8) and
original source lawfulness. The exact numerical command domain is still
$(-\min a_\eta,H-\max a_\eta)$. For a different starting-height
promise its extrema must obey (2.4); the construction does not silently
recompute its cutoff for other starts.

Fix any partition interval $[s,t]$ and any $v\in[s,t]$. Let
$x_*(v)=W^1_v-W^1_s$, $y_*(v)=W^2_v-W^2_s$, and
$c_*(v)=C_{s,v}$. Equations (16.7) and (17.4) give

$$
|x(v)-x_*(v)|\le4\rho,\qquad
|y(v)-y_*(v)|\le5\rho,\qquad
|j(v)-c_*(v)|\le6\rho^2.
\tag{17.12}
$$

The exact chronological matching at $s$ then gives

$$
J_\eta(v)-J^\lambda_v
 =W^1_s\{y(v)-y_*(v)\}+j(v)-c_*(v).
\tag{17.13}
$$

Since $|W^1_s|\le K_*$, this proves all of (17.9) before $S$.
After $S$ the errors are zero. It is important that the local integral
in (17.13) is the relative chronological increment, with its cross
term retained; adding merely scalar area endpoints without that term
would not prove this estimate.

To control the actual phases, apply (2.5) on the same interval from
its matched starting state. The $\beta$ difference at $v$ is exactly

$$
\left(\tfrac12-\frac{k+W^1_s}{r}\right)
       \{y(v)-y_*(v)\}
       -\frac{j(v)-c_*(v)}r.
\tag{17.14}
$$

The starting height is in $(0,r/2)$, so the coefficient in parentheses
has absolute value at most $1/2$. This proves (17.10), using
$\rho\le r/4$. The $\alpha$ difference is half the $b$ difference.
Circle projection with period $2\pi$ cannot increase either error;
(17.11) follows together with the height bound. The calculation uses
the actual affine native action, so it controls the complete response
and its chronological coordinate rather than just a scalar projection.
Continuity and the explicit finite formulas establish all these
statements on the common continuous target event. $\square$

**Corollary 17.4 (held, pre-death and cemetery comparisons).**
For every deterministic sequence $\eta_n\to0$ in the stated range,
the commands satisfy the quantitative full-native contract of Definition
13.1, the held-law contract (11.7), and the cemetery-law contract.
There is a deterministic full held tube, exact equality of censored
lifetimes at every stage, and uniform comparison of the cemetery paths
under their common coupling.

Proof. Proposition 17.3 supplies the held tube and $\zeta_\eta=\zeta$;
its triple estimates give uniform chronological convergence. In
particular every interval strictly before the target death is an
executed pre-death interval for every member of this family. For a
concrete metric in Definition 4.1 take $d_E=\min(1,d_{\max})$ on the
held cylinder and distance $2$ to the isolated cemetery. Before the
common death the $d_E$ error is at most $\eta$, and at and after death
both paths equal $\dagger$. Thus

$$
\sup_{t\le T}d_E(q_\eta^\dagger(t),q^{\lambda,\dagger}(t))\le\eta.
\tag{17.15}
$$

The identity time homeomorphism proves the same upper bound for the
corresponding $J_1$ comparison. Other usual product metrics give the
same convergence. This is a consequence of exact common death; it does
not identify general uniform held convergence with lifetime convergence,
or contradict the unequal-death obstruction in Remark 4.3. Coupled
almost sure convergence implies the asserted weak laws. $\square$

## 18. Integrable original-clock executed costs

**Theorem 18.1 (offline full-native upper envelope).** Fix exactly the
data of Definition 16.1. For every deterministic $0<\eta\le\eta_*$,
Definition 17.2 is a measurable, almost surely finite original command
with the full held native tube $D_{\max}\le\eta$, exact censored
lifetime and death, and complete chronological control (17.9).
It has finite expected costs, on the original clock and under the
original target law, satisfying

$$
\begin{aligned}
\mathbb E V_\eta^a&\le\frac4{\mu_\lambda}
                   \left(\frac{\mathbb ES}{\rho}+\rho\right),\\
\mathbb E V_\eta^b&\le\frac8{\mu_\lambda}
                   \left(\frac{\mathbb ES}{\rho}+\rho\right),\\
\mathbb E L_\eta&\le\frac{12}{\mu_\lambda}
                   \left(\frac{\mathbb ES}{\rho}+\rho\right),\\
\mathbb E E_\eta&\le\frac{168\nu_\lambda}{\mu_\lambda}
                   \left(\frac{\mathbb ES}{\rho^2}+1\right),
\qquad \rho=\eta/4.
\end{aligned}
\tag{18.1}
$$

Here $\mu_\lambda,\nu_\lambda$ are finite positive constants defined
from a covariance-$2$ Brownian pair $U$ by

$$
\begin{aligned}
\sigma_\lambda
 &=\min\left\{1,\inf\left\{v>0:
 |U^1_v|\ge1\ \text{or}\ |U^2_v|\ge1\ \text{or}\
 \left|\int_0^v U^1_w\,dU^2_w+\lambda v\right|\ge1
 \right\}\right\},\\
\mu_\lambda&=\mathbb E\sigma_\lambda\in(0,1],\qquad
\nu_\lambda=\mathbb E\sigma_\lambda^{-1}<\infty.
\end{aligned}
\tag{18.2}
$$

The $U$ notation specifies the law of a normalized cell; it is not an
additional random input to the command. For fixed starting state,
interval, horizon and $\lambda$, (18.1) proves expected variation and
length $O(\eta^{-1})$ and expected identity energy $O(\eta^{-2})$.
No deterministic bound on every realization's costs is asserted.

Proof. The geometric and chronological conclusions are Proposition 17.3.
It remains to prove the integrability and actual execution bounds; a
finite pathwise energy alone would not establish (18.1).

First, $0<\sigma_\lambda\le1$ almost surely by continuity at zero.
For $0<v\le v_\lambda=1/(2(1+|\lambda|))$, stop the martingale
$\int U^1\,dU^2$ when either first-level coordinate first reaches
absolute value $1$. Its quadratic variation up to time $v$ is at
most $2v$. If the area threshold is reached by time $v$ before those
coordinate exits, the stopped martingale has reached absolute value
at least $1/2$, since $|\lambda|v\le1/2$. The reflection principle
for the two Brownian coordinates and the exponential martingale
maximal inequality therefore give

$$
\mathbb P(\sigma_\lambda\le v)
 \le8\exp\{-1/(4v)\}+2\exp\{-1/(16v)\}.
\tag{18.3}
$$

For completeness the martingale inequality used here is
$\mathbb P(\sup_{s\le v}|M_s|\ge a)\le
2\exp(-a^2/(2b))$ when $[M]_v\le b$: stop at the first one-sided
crossing and apply the exponential supermartingale
$\exp(\theta M-\theta^2[M]/2)$, choosing $\theta=a/b$; then sum
the two signs. Here $a=1/2$ and $b=2v$. The coordinate bound follows
from reflection and the variance-$2v$ Gaussian tail. These are
classical Brownian and martingale estimates, with their normalizations
shown to fix the covariance factor.

For any $p>0$ the identity

$$
\mathbb E\sigma_\lambda^{-p}
 =1+p\int_0^1 v^{-p-1}\mathbb P(\sigma_\lambda<v)\,dv
 <\infty
\tag{18.4}
$$

follows from (18.3) near zero and the trivial probability bound elsewhere.
In particular (18.2) has the claimed finite constants.

The strong Markov property at $t_i$ and Brownian scaling imply that
$\Delta_i/\rho^2$ has law $\sigma_\lambda$, independently of
$\mathcal F_{t_i}$. Indeed the pair
$\rho^{-1}(W_{t_i+\rho^2v}-W_{t_i})$ has covariance $2I_2dv$,
and (16.3), divided by $\rho^2$, is its own chronological integral
plus $\lambda v$. Thus the normalized drift stays $\lambda$, with
no alteration of the target clock. Define the nonnegative comparison
reward $R_i=\rho^2/\Delta_i$. Then

$$
\mathbb E(\Delta_i\mid\mathcal F_{t_i})=\rho^2\mu_\lambda,
\qquad
\mathbb E(R_i\mid\mathcal F_{t_i})=\nu_\lambda.
\tag{18.5}
$$

The event $\{t_i<S\}$ is in $\mathcal F_{t_i}$ because $S$ is a
stopping time. Consequently Tonelli and (18.5), initially permitting
infinite expectations, yield

$$
\begin{aligned}
\rho^2\mu_\lambda\,\mathbb EN
 &=\mathbb E\sum_{i\ge0}{\bf1}_{\{t_i<S\}}\Delta_i
   =\mathbb E t_N\le\mathbb ES+\rho^2,\\
\mathbb E\sum_{i\ge0}{\bf1}_{\{t_i<S\}}R_i
 &=\nu_\lambda\,\mathbb EN
 \le\frac{\nu_\lambda}{\mu_\lambda}
              \left(\frac{\mathbb ES}{\rho^2}+1\right).
\end{aligned}
\tag{18.6}
$$

The first upper bound is pathwise: the last elementary interval starts
strictly before $S$ and lasts at most $\rho^2$. It also proves the
needed finiteness before the second line is used. This argument does
not assert independence of terminal or surviving selected intervals.
For example the event that an interval ends before death depends on
its own increment and need not be independent of its reward. Only the
start event in (18.6) is used for conditional factorization.

On each actual partition interval, (17.5) bounds the variations and
length by $4\rho,8\rho,12\rho$. There are at most $N$ such intervals.
The injective assignment (16.8) bounds their total energy by

$$
E_\eta\le168\sum_{i\ge0}{\bf1}_{\{t_i<S\}}
                              \frac{\rho^2}{\Delta_i}.
\tag{18.7}
$$

This is where the terminal construction is essential. On a merged
last interval its actual duration is
$\Delta_{N-2}+(S-t_{N-1})$, so its energy is bounded by
$168\rho^2/\Delta_{N-2}$. No reciprocal moment for the selected
remainder $S-t_{N-1}$ has been presumed. The first-cell argument in
Proposition 16.3 eliminates an unpaired short remainder. Taking
expectations in these inequalities and using (18.6) proves (18.1).

All quantities on the left of (18.1) and (18.7) are literal executed
costs from (11.4). A leg of duration $d$ and increment $(A,B)$ has
velocity $(A,B)/d$; a prefix executing fraction $\theta$ costs
$\theta|A|$, $\theta|B|$, $\theta\sqrt{A^2+B^2}$ and
$\theta(A^2+B^2)/d$, respectively. This formula applies at every
intermediate observation. In this family its own death is the endpoint
of its last height leg. The leg is run at its prescribed velocity up
to that endpoint; all later velocities are zero. There is no shortened
time completion of an interrupted leg, and neither the hold nor the
cemetery jump adds a cost.

The right side of (18.7) is only a dominating random variable. It can
include the full analytic mesh interval crossing $S$; that interval
is not thereby executed or billed. If a Brownian continuation beyond
$T$ is used to define its end, it serves only (18.5)–(18.6).
Marginalizing that continuation leaves both the command law and its
expected executed costs unchanged. This completes the original-law
and original-clock upper bound. $\square$

## 19. Attained powers and the remaining resource questions

**Corollary 19.1 (order matching in complete native accuracy).**
For every deterministic sequence $\eta_n\downarrow0$ in the range
of Definition 16.1, the finite commands of Theorem 18.1 attain the
necessary expected cost powers of Theorem 13.2. More explicitly,
writing lower and upper limits along this sequence, one has

$$
\begin{aligned}
\mathbb ES
 &\le\liminf_n\eta_n\mathbb E V_{\eta_n}^a
 \le\limsup_n\eta_n\mathbb E V_{\eta_n}^a
 \le16\mathbb ES/\mu_\lambda,\\
\mathbb ES/2
 &\le\liminf_n\eta_n\mathbb E V_{\eta_n}^b
 \le\limsup_n\eta_n\mathbb E V_{\eta_n}^b
 \le32\mathbb ES/\mu_\lambda,\\
\sqrt5\,\mathbb ES/2
 &\le\liminf_n\eta_n\mathbb E L_{\eta_n}
 \le\limsup_n\eta_n\mathbb E L_{\eta_n}
 \le48\mathbb ES/\mu_\lambda,\\
5\pi^2\mathbb ES/24
 &\le\liminf_n\eta_n^2\mathbb E E_{\eta_n}
 \le\limsup_n\eta_n^2\mathbb E E_{\eta_n}
 \le2688\nu_\lambda\mathbb ES/\mu_\lambda.
\end{aligned}
\tag{19.1}
$$

Here $\mathbb ES>0$. The lower coefficients are necessary native
bounds; the displayed upper coefficients are constructive bounds and
are not claimed sharp. In particular, full-native expected order
attainment in this offline class is established; the sharp full-native
optimization problem remains unresolved.

Proof. The same deterministic native tolerance $\eta_n$ occurs in
(17.11) and (13.2). The lifetime and chronological hypotheses of the
latter hold by Proposition 17.3. Fatou's lemma gives the lower
inequalities from its pathwise bounds. Substitution of
$\rho=\eta_n/4$ into (18.1) gives the upper inequalities. The
terms involving $\rho$ or the additive energy constant vanish under
the displayed normalizations. This comparison uses a proved complete
wrapped-path accuracy, not a mesh count or a free stage label.
$\square$

**Proposition 19.2 (scope of the native upper and of its suppliers).**
The upper theorem establishes full held tracking, joint chronology and
exact death under the offline information contract of Definition 16.1.
It does not determine sharp native constants, causal or finite-bit
acquisition costs, physical energy, a preferred $\lambda$, or a bridge
to three physical spatial dimensions. The scalar approximation and
qualitative enhanced-path suppliers alone do not establish its
executed-cost conclusion.

Proof. The source correspondence is exactly N, §§9.1–9.3 and
Definition 10.1, together with O, Definitions 1.1–1.2 and G,
Definition 4.1, under the fixed supplier convention 1.1. The quantitative
addition is the inward six-leg realization on the common enhanced
increment partition, its terminal duration assignment, and the
original-law stopped reward estimate (18.6). These give the complete
native contract in one realization.

The scalar free-knot construction of Lifshits–Setterqvist, §4.2,
credits the adaptive approximation and inverse-duration method; it
neither prescribes $\int a\,db$ jointly with both controls nor
ensures the native phase and lifetime estimates. Independently
optimizing the two scalar controls therefore leaves those constraints
unproved, as in Proposition 15.5. First-level uniform tracking alone
cannot repair this: the area-drift families of Section 6 have the same
first-level limit and different chronological limits.

P. Friz and H. Oberhauser,
[*Non-standard approximations of the Itô-map*, arXiv:0808.0337v1,
§§1.2, 2.1 and 2.2.1](https://arxiv.org/html/0808.0337v1), supply
classical enhanced-path interpolation and central perturbations,
including loop constructions and their bracket drift. Their §1.2
explicitly distinguishes access to a path and its Lévy area from
approximations using finitely many first-level observations.
P. Friz and N. Victoir,
[*Approximations of the Brownian rough path with applications to
stochastic analysis*, Ann. IHP 41, 703–724,
§5.1](https://doi.org/10.1016/j.anihpb.2004.05.003), in particular
Proposition 26 and Corollaries 27–28, supply enhanced smooth
approximation results, including an adapted approximation.
Those results are credited mathematical suppliers; they do not
assert the deterministic native tube, exact interior death and
actual-prefix expectation bound in (18.1). No general rough-path
continuity theorem or native steering theorem is needed for the
explicit triangular response estimate (17.14).

A uniform control estimate only before a command's own death would
leave a lifetime and held-path gap; Remark 4.3 and Counterexample 4.4
exhibit the relevant distinction. Here exact own death and exact
terminal triples supply the missing comparison, rather than inferring
it from a pre-death estimate. Similarly, forcing a nonzero correction
onto an arbitrary final remainder of duration $d$ would require
control of its energy proportional to $1/d$. A positive random $d$
alone gives no such expectation bound. The duration assignment
(16.8) and the conditional sum (18.6) supply precisely that missing
integrability; they make no assertion that selected terminal
remainders have the original cell law.

The constants on the two sides of (19.1) differ, and the construction
uses future area and lifetime data. Thus it supplies neither a sharp
native optimizer nor a causal acquisition mechanism. Proposition 15.4
continues to exclude hard samplewise budgets. The energy throughout
is exactly the declared unhalved identity quadratic functional;
no calibration of physical energy or amplitude preparation has been
introduced. Every fixed $\lambda$ has the stated construction, while
Theorem 7.2 separates its native law from other choices when the
specified wrapped observable distinguishes them. Accordingly these
cost powers do not select a drift. Finally the source ray dimension,
the rank-two control distribution, its bracket growth and its local
volume exponent remain the distinct objects of Remark 7.3. No
identification with physical spatial axes is an assumption or a
consequence of the upper theorem. The native combination above is a
repository-derived ordinary argument using the cited classical
methods, with no claim of literature priority or uniformity in the
starting state. $\square$

## 追加锚（本行以下为增补区）

## 20. Causal knowledge and finite numerical issuance

**Definition 20.1 (one target and the information ceiling).** Retain
Definitions 2.1, 11.1 and 11.3, including $0<l<k<u<H$, $T>0$,
arbitrary fixed preparation phases and arbitrary fixed $\lambda$.
Thus the probabilities, negative phase convention, both $2\pi$ periods,
fields $P,Q$, covariance $2I_2$ and original clock are unchanged.
Write $Y_t=k+W^1_t$ and
$\tau=\inf\{t\ge0:Y_t\notin(l,u)\}$. The target is the same jointly
specified $(W^1,W^2,J^\lambda)$, not a newly sampled copy. Its natural
completed filtration is $\mathcal F^W$. The enhancement is adapted to
this filtration; giving its past does not give its future.

On any probability space carrying this target, allow an initial random
seed $U$, independent of the entire Brownian pair. Let $\mathcal F_t$
be the usual augmentation of
$\sigma(U,W^1_s,W^2_s:0\le s\le t)$. The issuer's knowledge may be any
usual subfiltration $\mathcal K_t\subseteq\mathcal F_t$. Its issue and
interruption times must be $\mathcal K$ stopping times, and its numerical
choices at a time $\sigma$ must be $\mathcal K_\sigma$ measurable.
The issuer knows the specified start, clock and its own previous
commands. Additional independent randomization can be included in $U$.
The maximal choice $\mathcal K=\mathcal F$ grants exact observation of
the whole target past. A smaller observation interface restricts this
class. No observation of $W$, of its enhancement, or of its death is
supplied by N's command syntax itself: these are explicitly additional
acquisition inputs. In particular $\tau$ is not initially supplied.

Independence of $U$ leaves $W$ Brownian in $\mathcal F$. The classical
strong Markov property therefore applies at its finite stopping times.
One can also obtain this enlargement directly from its usual proof:
future increments are independent of $\sigma(U,W_s:s\le t)$ at
deterministic $t$, and approximation of a stopping time from above by
dyadic stopping times, followed by path continuity, gives the same
independent future Brownian path. The result used here is Mörters–Peres,
*Brownian Motion*, the public draft dated May 25, 2008, Theorem 2.14,
pp. 47–48 ([consulted text](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf)).
This numbering refers to that draft, not to an unverified numbering in
another edition. Multiplying its standard Brownian motion by $\sqrt2$
gives the present covariance convention.

**Definition 20.2 (the complete finite numerical-command class).** A
policy in $\mathcal C_T$ has a sequence of active issue times
$\sigma_0=0,\sigma_1,\ldots$, with unused times set to $\infty$.
Distinct active times increase strictly; finitely many instructions at
one instant may be collapsed, since zero elapsed time cannot move the
state. At $\sigma_j$ the issuer chooses a zero-start numerical pair
$\gamma_j=(a_j,b_j)$ of absolutely continuous functions of elapsed
time on $[0,T]$. Measurability means measurability as a random element
of $C([0,T];\mathbb R^2)$ with its uniform topology, taking values in
the zero-start AC paths. This admits arbitrary AC
profiles, including profiles with infinitely many internal bends; it
does not restrict a command to a constant velocity or a single leg.
A specified shorter duration is represented by constant continuation.

Until interruption or its own height exit, the actual controls are
exactly the issued numerical functions, translated from the controls
already executed. Thus, on an active interval starting at $\sigma_j$,

$$
A_t=A_{\sigma_j}+a_j(t-\sigma_j),\qquad
B_t=B_{\sigma_j}+b_j(t-\sigma_j).
\tag{20.1}
$$

The next issue time may depend on all subsequently available observations;
it need not be known at $\sigma_j$. An interruption with no replacement
means the zero-increment hold, counted as a new segment in this
representation. Resuming, restarting or changing a
profile after a pause counts as another issuance of the resulting
numerical segment. The joins in (20.1) are continuous. A command may
be interrupted at a predictable time, at a target exit, or at any other
admissible stopping time; the interruption itself changes neither height
nor phase and declares no native death. A feedback instruction whose
future numerical values still depend on future observations is not a
numerical profile chosen at issuance, even if the instruction has a
finite description.

Set

$$
\tau^{\rm N}=\inf\{t\in[0,T]:k+A_t\notin(l,u)\},\qquad
\inf\varnothing=\infty.
\tag{20.2}
$$

At this actual own exit, hold both controls for the rest of $[0,T]$.
Only then is the native killed observation sent to $\dagger$.
The recursively executed controls are adapted and continuous, so
their first exit is a stopping time; the automatic boundary hold
needs no access to a future target value.
There are almost surely finitely many active issuances up to
$\tau^{\rm N}\wedge T$, with no deterministic bound on their number.
This is finiteness of executions, not finiteness of distinct command
strings. In particular it excludes infinitely many new issuances
accumulating at the death endpoint, as well as earlier accumulation.
Being finite on every compact interval strictly before death would be
a weaker condition and is not substituted for this one.
All pathwise execution requirements hold almost surely, on one event
for the countable sequence of issued profiles.

This class is the union over all seeds and all knowledge filtrations
in Definition 20.1, all such adaptive issue/interruption rules and all
such numerical profiles. No bound on variation, speed, quadratic cost,
profile complexity, observation precision or observation rate is imposed.
The finite issuance requirement is the declared operational meaning of
executing finitely many numerical commands. N admits individual AC
histories; it does not assert that every adapted random AC history has
such a finite online issuance representation. Section 23 distinguishes
these two classes inside the same original source.

**Definition 20.3 (source legality, cutoff and the two lifetime records).**
Every actually executed profile prefix must obey N's whole-height guard.
There is no loss for the present killed task in prescribing a profile's
constant continuation from its first hit of $l$ or $u$: the current
native height and the entire numerical profile are known at issuance,
so this cutoff is computed from the issued profile, not from future
target data. It leaves every prefix before own death unchanged.
Profiles already lawful on their full stated duration need no such
replacement. The executed held controls satisfy

$$
J^{\rm N}_t=\int_0^t A_s\,dB_s,\qquad
D_{A,B}=(-\min_{[0,T]}A,\ H-\max_{[0,T]}A),
\tag{20.3}
$$

and their heights lie in $[l,u]\Subset(0,H)$. Consequently
$k+\min A\ge l>0$ and $k+\max A\le u<H$. The actual native path is
precisely (11.3), with $(a_n,b_n,J_n)$ replaced by
$(A,B,J^{\rm N})$. This follows by N, Theorems 9.2–9.3, on each
prefix and by its concatenation rule; the chronological cross terms
are already included in the single integral in (20.3). Finite
concatenation with continuous joins is AC. The original probabilities,
arbitrary preparation rotations, signs and periods are therefore
preserved, including at a killing boundary, which is interior to the
original source. For a different promised starting interval
$[k_-,k_+]$, the same realized numerical history is lawful exactly when
$k_-+\min A>0$ and $k_++\max A<H$. Re-running a policy with another
start is not the same numerical command and is not used to enlarge
this domain.

Write $\zeta^{\rm N}=\tau^{\rm N}$ for the native censored death record
and retain $\zeta$ from (11.6): both take values in
$[0,T]\sqcup\{\infty\}$, where $\infty$ means no death on this horizon.
The horizon-only cutoffs are
$S^{\rm N}=\tau^{\rm N}\wedge T$ and $S=\tau\wedge T$.
A command interruption and these horizon cutoffs are not death marks.
In particular $S^{\rm N}=T$ does not distinguish death exactly at $T$
from survival beyond $T$, whereas $\zeta^{\rm N}$ does.

## 21. Exact coupled death for finite numerical issuers

**Theorem 21.1 (finite causal issuance misses target death).** For every
choice of the fixed parameters in Definition 20.1, every allowed seed,
every allowed knowledge filtration and every individual policy
$C\in\mathcal C_T$,

$$
\mathbb P(\tau^{\rm N}=\tau\le T)=0,
\qquad
\mathbb P(\zeta^{\rm N}=\zeta)
 =\mathbb P(\tau>T,\ \zeta^{\rm N}=\infty)
 \le\mathbb P(\tau>T).
\tag{21.1}
$$

The lifetime-only ceiling is sharp:

$$
\sup_{C\in\mathcal C_T}\mathbb P(\zeta^{\rm N}_C=\zeta)
 =\mathbb P(\tau>T).
\tag{21.2}
$$

There is positive probability of target death before $T$. These are
issuer-by-issuer statements. For any countable family of admissible
issuers on the same target coupling, one common probability-one event
excludes exact death for every member on $\{\tau\le T\}$. No common
exceptional set for the uncountable class of all issuers is asserted.

Proof. Work at an issue time on
$\{\sigma_j<T,\ \sigma_j<\tau^{\rm N}\}$, where the native
height $x_j$ is in $(l,u)$. Define the
nominal first-exit delay of the prescribed numerical height by

$$
d_j=\inf\{s\in[0,T-\sigma_j]:x_j+a_j(s)\notin(l,u)\},
\qquad \inf\varnothing=\infty.
\tag{21.3}
$$

Put $d_j=\infty$ off this alive-issuance event. All evaluations at
$\sigma_j+d_j$ below are restricted to the displayed finite-delay
event, so no value at an infinite time is used.
It is $\mathcal F_{\sigma_j}$ measurable. Indeed $x_j$, $\sigma_j$
and the entire continuous profile are measurable there; first hitting
of the closed exterior is a Borel function of the continuous path and
the prescribed horizon. This can be checked by taking the minimum of
distance to the exterior on compact intervals, using rational times
and continuity. Every finite $d_j$ is strictly positive, since
$a_j(0)=0$ and $x_j$ is interior. Infinite $d_j$ cannot produce a death
before the horizon in this segment.

Conditional on $\mathcal F_{\sigma_j}$, the future path
$W^1_{\sigma_j+s}-W^1_{\sigma_j}$ is a fresh covariance-$2$ Brownian
motion. For any fixed positive $d$ and any fixed real $y$,
$y+W^1_d$ has a Gaussian density and hence gives mass zero to
$\{l,u\}$. Since $d_j$ and $Y_{\sigma_j}$ are known at issuance,
the same conclusion applies at the random but already prescribed
delay $d_j$:

$$
\mathbb P\bigl(
 0<d_j\le T-\sigma_j,\
 Y_{\sigma_j+d_j}\in\{l,u\}
 \mid\mathcal F_{\sigma_j}\bigr)=0.
\tag{21.4}
$$

For precision, this conditioning integrates the jointly measurable
evaluation map $(d,y,w)\mapsto y+w(d)$ against the independent future
Wiener path law, with $d,y$ fixed by the conditioning. It does not
treat $d_j$ as independent of the past or condition on a future
interruption event. If an issue time is not finite everywhere, apply
strong Markov to $\sigma_j\wedge T$ and restrict to
$\{\sigma_j<T\}$. An issue at $T$ cannot move an interior state
on the remaining zero-length interval.

Now suppose $0<\tau^{\rm N}=\tau\le T$. Finiteness of the active
issuances gives a last positive-duration executed segment with start
$\sigma_j<\tau^{\rm N}$ and with no intervening interruption before
$\tau^{\rm N}$. Its numerical profile agrees with the actual height
through that endpoint, and its earlier prefixes are interior. Thus

$$
\tau^{\rm N}=\sigma_j+d_j.
\tag{21.5}
$$

If the death coincides with a new issue or an interruption, continuity
charges it to the segment ending there. A zero-start replacement
cannot cause an instantaneous height change. A hold from an interior
point cannot cause death at all. These observations also cover a
death at $T$. On target death, continuity gives $Y_\tau\in\{l,u\}$,
so (21.5) places the event in the probability-zero event (21.4) for
some integer $j$. A countable union proves the first assertion of
(21.1); no bound on the random command count was needed. Both
lifetimes are strictly positive from the fixed interior start.

Equality of death records either means equality of finite deaths or
means both records are $\infty$. This proves the second assertion.
The zero command $A=B=0$ is lawful, causal and never exits $I$, so it
attains (21.2). It is a lifetime-only optimizer, with no native tube
claim. Finally
$\{Y_T>u\}\subseteq\{\tau<T\}$, and the former event has positive
Gaussian probability. Proposition 4.5 supplies
$\mathbb P(\tau=T)=0$ and almost sure finiteness of $\tau$.
Intersecting the individual probability-one events over any countable
family gives the stated family quantifier. $\square$

**Proposition 21.2 (endpoints, predictability and the precise obstruction).**
The obstruction in Theorem 21.1 is compatible with predictable target
exit and does not apply to every adapted AC history. Its operative
conditions are: a numerical continuation fixed by the information at
issuance; a last segment starting strictly before an actual native
death; continuous joins with death determined by height; and the
conditional atomlessness in (21.4).

Proof. Put $d_* =\min(k-l,u-k)>0$ and $e_n=d_*2^{-n}$, and define

$$
\theta_0=0,\qquad
\theta_n=\inf\{t\ge0:\operatorname{dist}(Y_t,\mathbb R\setminus I)
                         \le e_n\}\quad(n\ge1).
\tag{21.6}
$$

These are stopping times in the full target filtration. Continuity
and $\tau<\infty$ give
$\theta_n<\theta_{n+1}<\tau$ and $\theta_n\uparrow\tau$ almost
surely: a finite limit below $\tau$ would have distance both positive
and at most every $e_n$. Thus they announce $\tau$. This is
predictability, not total inaccessibility. It does not supply a
positive exact residual delay at any finite announcement.

The proof of Theorem 21.1 uses only the four stated conditions at a
segment causing death. In particular a class with countably many
segments also satisfies that proof whenever every death has such a
last segment. Merely forbidding accumulation strictly before death
does not guarantee a last segment at death. Section 23 supplies an
AC counterexample at precisely that boundary. A continuously
observation-dependent velocity need not have a future profile
measurable at any earlier issue time, so the proof does not cover
that class either.

On the stated interior-start contract there is no death at zero, and
target death exactly at $T$ is null. If the contract were changed to
start at $l$ or $u$, both own exits could be zero, so the strict
interior premise cannot be dropped. The theorem concerns $T>0$;
at a zero horizon an interior start has no observed death. Equality
of the horizon-only cutoffs has the same probability ceiling as
(21.2), since on $\{\tau<T\}$ it requires exact native death.
However its equality event also allows native death at $T$ on
target survival. This is why the death-record equality in (21.1)
is the stated exact contract.

Finally there cannot be an issuer-uniform null event by this argument.
For every deterministic $s\in(0,T]$, the command that moves linearly
from $k$ to $l$ over time $s$ and then holds is causal and lawful.
Every target path with death at some $s\le T$ matches one member
of this uncountable family. Selecting that member using the realized
future $\tau$ is not a causal issuer. Similarly, an independent
initial seed $R$ with the target exit-time distribution can prescribe
this ramp with duration $R$. It matches the marginal lifetime law
but, by Theorem 21.1, not a positive-probability coupled death event.
Giving the actual $\tau$ at time zero would break Definition 20.1's
information condition and would permit the ramp with duration
$\tau$ to match lifetime. Neither construction tracks the full native
target. $\square$

## 22. Isolated cemetery comparison on the original clock

**Corollary 22.1 (uniform cemetery obstruction in the specified coupling).**
Use exactly $E$ and its metric from Definition 4.1, with distance $2$
from every alive point to $\dagger$. For $C\in\mathcal C_T$ let
$q_C^\dagger$ be its actual killed native path, and compare it with
the same target $q^{\lambda,\dagger}$ at the same clock times. Then

$$
\mathbb P\left(
 \sup_{0\le t\le T}d_E(q_C^\dagger(t),q^{\lambda,\dagger}(t))=2
 \right)\ge\mathbb P(\tau\le T)>0.
\tag{22.1}
$$

For every countable sequence $C_n\in\mathcal C_T$, almost surely on
$\{\tau\le T\}$ the displayed supremum equals $2$ for every $n$.
Consequently such a sequence cannot converge uniformly in probability
or almost surely to this coupled killed target. More generally the
same conclusion holds for any same-clock uniform metric whose
distance between cemetery and all alive points has a positive lower
bound, with that bound replacing $2$ in the lower estimate.

Proof. If the two censored death records differ, there is a time in
$[0,T]$ when exactly one path is dead. This includes distinct finite
deaths, a finite death versus survival, and a mismatch at $T$.
The distance at that time is $2$, which is also the maximum possible
distance in $E$. By Theorem 21.1 this happens almost surely on
$\{\tau\le T\}$ for each issuer, and simultaneously for a countable
family. The positive probability lower bound rules out convergence
in probability; the common event of permanent distance $2$ also
rules out almost sure convergence. The same argument uses only the
positive alive-to-cemetery gap for the stated metric variant.

This proof permits no clock change. It gives no obstruction to
Skorokhod $J_1$ convergence, where a small time change can align nearby
death times as in Theorem 4.2, and no obstruction to uniform convergence
of continuously held paths in the ordinary native state space. Those
contracts require their own path and lifetime estimates. It also
does not assert failure for every possible coupling of marginal laws.
$\square$

## 23. Accumulating causal issuances with an AC native history

**Theorem 23.1 (a lifetime-only boundary witness).** With exact continuous
observation of the stopped target height available, there is a causal
sequence of numerical native commands, countable and accumulating at
$\tau$, whose executed history is absolutely continuous, has finite
variation and obeys the original whole-height guard. Defined on
$[0,\infty)$ and held after death, its uncensored own exit is exactly
$\tau$; its restriction to $[0,T]$ therefore has
$\zeta^{\rm N}=\zeta$ almost surely. Its $b$ control is identically
zero. Thus absolute
continuity and finite variation alone cannot replace finite issuance
in Theorem 21.1. This witness also has almost surely finite quadratic
control energy through death, by the separate estimate below.
No expectation bound or deterministic energy budget is asserted.

Proof. Use the announcing times $\theta_n$ of (21.6), which can be
detected from the stopped height without any target continuation
after death. Write

$$
d=k-l,\qquad v_n=d2^{-3n},\qquad h_n=T2^{-4n}.
\tag{23.1}
$$

At $\theta_0=0$ start at native height $k=l+v_0$. If the current
height at $\theta_n$ is $x_n$, issue the numerical profile

$$
x_n(s)=x_n-(x_n-l-v_{n+1})\min\{s/h_n,1\},
\qquad b_n(s)=0,\qquad s\ge0.
\tag{23.2}
$$

The relative height increment is $a_n(s)=x_n(s)-x_n$. At
$\theta_{n+1}$ interrupt it continuously and issue the next profile.
Inductively $x_n\ge l+v_n$, so every profile is nonincreasing and
stays between its current value and the strictly interior level
$l+v_{n+1}$. A finished ramp simply holds until the next announcement;
that hold is already part of the issued profile. Each profile is
piecewise linear and known at its issuance. There are finitely many
issuances on every $[0,t]$ with $t<\tau$.
In particular $x_n$ is measurable at $\theta_n$ by finite recursion,
and (23.2) is a measurable choice of numerical AC profile there.
Restricting this construction at $T$ uses no observations after $T$.

It remains to prove that the actual native height tends to $l$ at
$\tau$, rather than leaving a positive gap because too many ramps
are interrupted early. The distance function in (21.6) is 1-Lipschitz.
To move from its value $e_n$ to $e_{n+1}$ requires a target height
displacement of at least $e_n/2$. Strong Markov at $\theta_n$ and
the reflection bound for a covariance-$2$ Brownian motion give

$$
\begin{aligned}
\mathbb P(\theta_{n+1}-\theta_n<h_n
                 \mid\mathcal F_{\theta_n})
&\le\mathbb P\left(\sup_{0\le s\le h_n}|W^1_s|
                                      \ge e_n/2\right)\\
&\le4\exp\{-e_n^2/(16h_n)\}
 =4\exp\{-d_*^2 4^n/(16T)\}.
\end{aligned}
\tag{23.3}
$$

Here reflection bounds each one-sided maximum by twice a Gaussian
tail, and a variance-$2h_n$ Gaussian has upper tail at $a>0$ at
most $\exp(-a^2/(4h_n))$. This is the classical reflection principle
(Mörters–Peres, the draft specified in Definition 20.1, Theorems
2.16 and 2.18) with its variance scaled explicitly. The right side
of (23.3) is summable. Borel–Cantelli, with no independence of these
events required, shows that all sufficiently late ramps finish before
the next announcement. Consequently
$x_{n+1}=l+v_{n+1}$ for all sufficiently large $n$, and the native
height tends to $l$ as $t\uparrow\tau$.

Define its value at $\tau$ to be this limit and hold it afterwards.
This is a continuous extension, not a height jump or a declaration
of death. Before $\tau$ every executed piece has height strictly
above $l$ and at most $k<u$; at $\tau$ its height is exactly $l$.
Thus its own first exit is exactly $\tau$, including when this
happens to coincide with the horizon. Its original native height
always lies in $[l,k]\Subset(0,H)$, so (20.3) proves the whole-height
guard; all source phases remain at their initial values and $J=0$.

For completeness, let $f$ be the nonpositive derivative on each
executed ramp and zero on each hold and after $\tau$. For $t<\tau$
only finitely many intervals occur, so
$x(t)=k+\int_0^t f(s)\,ds$. Monotonicity and the limit just proved
give

$$
\int_0^\tau |f(s)|\,ds
 =\sum_{n\ge0}(x_n-x_{n+1})=k-l=d.
\tag{23.4}
$$

Passing to $t=\tau$ in this integral representation and extending by
zero derivative proves absolute continuity on every finite horizon,
including through the accumulation point. This excludes a hidden
singular-variation contribution at death. It also proves total
variation $d$ through death. Eventually consecutive ramps are both
complete, so ramp $n$ then drops $7v_n/8$ over duration $h_n$ and has
quadratic energy

$$
\frac{49v_n^2}{64h_n}=\frac{49d^2}{64T}\,4^{-n}.
\tag{23.5}
$$

This tail is summable. Every earlier, possibly interrupted ramp has
speed at most $d/h_n$ for at most $h_n$ time and thus energy at most
$d^2/h_n<\infty$. There are almost surely only finitely many such
earlier ramps. Therefore $\int_0^\tau |f(s)|^2\,ds<\infty$ almost
surely, which also proves finite energy on $[0,T]$. This is an
additional calculation, not an inference from AC or finite variation;
it gives no expectation estimate for the random initial portion.
The construction is defined
almost surely, as are the Brownian target and its enhancement; its
causal rules use only present announcements and previous commands.
It uses infinitely many issuances when death occurs on the horizon,
so it is outside $\mathcal C_T$ on an event of positive probability.

The native endpoint is always the lower face, even if the target
exits at the upper face, and its phases are fixed. This is exact
lifetime attainment only, not an enhanced-path, exit-face or native
tube construction. $\square$

## 24. Finite causal approximation of lifetime alone

**Theorem 24.1 (observed exit followed by actual native execution).**
Assume the issuer may read the stopped target height
$\bar Y_t=Y_{t\wedge\tau}$ at a deterministic mesh of step $\delta>0$.
Exact real observations are meant; no future path, area or lifetime
value is supplied. For every $\epsilon>0$ there is a policy with at
most two numerical issuances, lawful in the original source, whose
own exit on an extended clock is $\widehat\tau_{\delta,\epsilon}$
satisfying almost surely

$$
\tau<\widehat\tau_{\delta,\epsilon}
 \le\tau+\delta+\epsilon,
\qquad
\widehat\tau_{\delta,\epsilon}-\tau\ge\epsilon.
\tag{24.1}
$$

Restricting this same execution to $[0,T]$ gives a member of
$\mathcal C_T$. Its censored lifetime $\zeta_{\delta,\epsilon}^{\rm N}$
converges almost surely to $\zeta$ as $\delta+\epsilon\to0$ along
any deterministic sequence, in the topology where $\infty$ is an
isolated no-death mark. Its horizon cutoff obeys

$$
0\le S_{\delta,\epsilon}^{\rm N}-S\le\delta+\epsilon.
\tag{24.2}
$$

For the metric $d_\zeta(s,t)=\min(1,|s-t|)$ on finite lifetimes,
$d_\zeta(s,\infty)=1$ for finite $s$, and $d_\zeta(\infty,\infty)=0$,
one also has, when $\delta+\epsilon<1$,

$$
\mathbb P\left(
d_\zeta(\zeta_{\delta,\epsilon}^{\rm N},\zeta)>
       \delta+\epsilon\right)
\le\mathbb P(T-\delta-\epsilon<\tau\le T).
\tag{24.3}
$$

Proof. Issue the zero command at time zero. Let

$$
D_\delta=\min\{j\delta:j\ge1,
                     \bar Y_{j\delta}\in\{l,u\}\}.
\tag{24.4}
$$

Before death the stopped height is interior; at and after death it
is a boundary value. Thus $D_\delta$ is a stopping time determined
by the available mesh observations, and
$\tau\le D_\delta\le\tau+\delta$ almost surely. At $D_\delta$
issue the relative control

$$
a(s)=-(k-l)\min\{s/\epsilon,1\},\qquad b(s)=0.
\tag{24.5}
$$

The native state is still at height $k$ then. The ramp stays in
$(l,k]$ for $s<\epsilon$, reaches $l$ exactly at $s=\epsilon$,
and holds thereafter. Its own exit is therefore
$\widehat\tau_{\delta,\epsilon}=D_\delta+\epsilon$, proving
(24.1). Observing a target boundary in (24.4) does not declare native
death: the positive-duration ramp (24.5) is actually executed.
Both joins are continuous. All executed heights lie in $[l,k]$,
so the exact source guard follows from (20.3); phases and $J$ remain
fixed. There are finitely many observations on $[0,T]$ and at most
two issuances there. If the detected exit or the ramp's completion
lies beyond $T$, the horizon records no native death. The extended
clock only defines that possible later completion; no part of the
command on $[0,T]$ is retimed or compressed.

Taking minima with $T$ proves (24.2). If $\tau>T$, both censored
records equal $\infty$. If $\tau<T$, then eventually
$\delta+\epsilon<T-\tau$, so the native exit occurs before $T$
and its finite record differs from $\tau$ by at most
$\delta+\epsilon$. The remaining event $\tau=T$ is null by
Proposition 4.5. This proves the almost sure convergence with the
death mark retained. A mark mismatch can occur only on
$\{T-\delta-\epsilon<\tau\le T\}$; otherwise the metric error is
at most $\delta+\epsilon$, proving (24.3).

This approximation requires the stated exact observations of the
stopped height. Observing only an unstopped height at mesh times can
miss a boundary excursion that has returned, so those data cannot
be substituted in (24.4) without a different argument. No independent
death flag is given to the native system. The construction uses the
same target sample, but every finite-stage native death is strictly
later than its target death. It neither simulates only a marginal
lifetime law nor satisfies exact coupled lifetime. Its fixed phases
and its hold at $k$ before detection supply no full held-path or
chronological tube estimate. $\square$

## 25. Supplier scope and remaining causal bridges

**Definition 25.1 (attribution and limits of the native conclusions).**
The source correspondence is N, Definitions 3.1 and 9.1, Theorems
9.2–9.3 and Definition 10.1; O, Definitions 1.1–1.3; and G,
Definition 4.1, at the fixed revision in Source convention 1.1.
The whole-height guard is reused exactly, not replaced by an endpoint
test. Brownian strong Markov, Gaussian densities, reflection and
Borel–Cantelli are `literature-attested` suppliers used inside the
native proofs. The finite-issuer obstruction with its interruption
endpoints, its cemetery consequence and the two guarded lifetime
constructions are `repo-derived` ordinary applications. No literature
priority or new general strong Markov theorem is claimed.

Lifshits–Setterqvist, *Energy of Taut Strings Accompanying Wiener
Process*, [arXiv:1405.1651v1](https://arxiv.org/pdf/1405.1651v1), §4.2,
interpolates between random knots using both endpoint values. A knot
being a stopping time does not make that interpolation known at the
previous knot. Its §5 instead studies an observation-dependent
velocity $x'(t)=b(x(t)-W(t))$, a continuous feedback class. The
numerical-profile assumption in Definition 20.2 is not a theorem
excluding that class, and the scalar pursuit result does not supply
native chronological tracking or exact native own death.

Friz–Victoir, *Approximations of the Brownian rough path with
applications to stochastic analysis*, Ann. IHP 41 (2005), 703–724,
[primary text](https://www.numdam.org/item/AIHPB_2005__41_4_703_0.pdf),
§5.1, Proposition 26 and Corollary 27 supply the enhanced polygonal
approximation cited in §§10 and 19. A qualification is needed for
using the literal displayed interpolation in Corollary 28, p. 718:
with mesh $h=2^{-n}$ and $B_0=0$, that display is zero on $[0,h)$
but has value $B_h$ at $h$. Thus it is not a continuous delayed
polygonal path; its proof's description as a time-shift does not
validate that literal display. None of the proofs in §§20–24 uses
it. A continuous one-step delayed polygonal rule would instead be
zero on $[0,h]$ and, for $j\ge1$ and $t\in[jh,(j+1)h]$, be

$$
B_{(j-1)h}+\frac{t-jh}{h}(B_{jh}-B_{(j-1)h}).
\tag{25.1}
$$

The two cell endpoint values are $B_{(j-1)h}$ and $B_{jh}$; the
next cell starts at the latter, and all its numerical data are
known at $jh$. These elementary checks specify which continuous
adapted interpolation is meant. Formula (25.1) alone makes no
stopped-native enhancement, lifetime or tube assertion here.

Friz–Oberhauser, *Non-standard approximations of the Itô-map*,
[arXiv:0808.0337v1](https://arxiv.org/html/0808.0337v1), §1.2 explicitly
distinguishes access to a Brownian path and its Lévy area from
approximations using finitely many first-level observations. Its
§2.1 Theorem 1 and §2.2.1 concern enhanced approximation and central
perturbations. They do not supply the information-at-issuance premise
or an exact native-death conclusion, and no general rough differential
equation theorem is invoked in §§20–24.

Theorem 18.1 and the attained offline cost powers in §19 retain their
original information contract and are not contradicted by (21.1).
The lower bounds in §§12–15 retain their stated approximation
hypotheses, whether or not an approximating policy is causal. Neither
the lifetime-only construction in §23 nor that in §24 satisfies those
full tracking hypotheses. No conclusion here changes the known
offline powers, proves optimal causal powers, or supplies a full
native causal held tube or a $J_1$ approximation of the full killed
state. Such questions require joint control/area estimates and their
own original-clock cost analysis. General continuous feedback,
other classes of accumulating issuances, optimal or expected costs
of the lifetime-only boundary witness, and acquisition cost require
separate analyses. Theorem 23.1 settles existence in its stated
accumulating-issuance class; it does not classify continuous-feedback
laws or other accumulation interfaces. The supplied comparison
observations are not a physical
source sensor or a cost-free physical implementation. Finally no
statement selects $\lambda$, calibrates physical energy, or identifies
the native ray dimension, bracket growth or volume exponent with
three physical spatial directions.

## 追加锚（本行以下为增补区）

## 26. Causal full-state tracking with finite numerical issuances

**Definition 26.1 (fixed target, observations and tolerance).** Retain
exactly Definitions 2.1–2.2, 11.1–11.3, 13.1 and 20.2–20.3. In
particular the fixed data are $0<Z<1$, $r=1-Z$, $H=r/2$,
$0<l<k<u<H$, $T>0$, arbitrary fixed preparation phases, the negative
amplitude convention, probabilities $(k,H-k,Z,H-k,k)$, both $2\pi$
periods, and the original fields
$P=\partial_k$ and
$Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta$.
The target on one fixed original Wiener probability space is the
covariance-$2$ pair $W$ with
$J^\lambda_t=\int_0^t W^1_s\,dW^2_s+\lambda t$, for any fixed real
$\lambda$. Write $z=(W^1,W^2,J^\lambda)$,
$\tau=\inf\{t:k+W^1_t\notin(l,u)\}$, $S=\tau\wedge T$, and use
$\zeta$ and $\bar q^\lambda$ from (11.6). An independent initial seed
may be adjoined to the usual Brownian filtration $\mathcal F$ as in
Definition 20.1; the construction below does not need a seed.

The supplied ideal observation filtration $\mathcal K$ is the usual
augmentation of the history of $z_{t\wedge\tau}$ together with that
seed. Only times at most $T$ are used. The boundary value of its height
reveals whether $\tau\le t$. Thus $\tau$ is an observable stopping
time, without supplying it in advance. This filtration is contained in
$\mathcal F$; before target death it supplies the entire target past,
including its jointly specified chronological integral. Independent
initial enlargement leaves $W$ Brownian in $\mathcal F$. All
conditional estimates below use this Brownian filtration, without
conditioning the underlying law on survival. After $\tau$ the policy
uses only its stopped observation. Exact observations and real
numerical instructions are mathematical premises, not a method of
acquiring the observations or a finite-bit realization of them.

For every deterministic $\eta>0$ put

$$
\begin{aligned}
d_*&=\min(k-l,u-k),&K_*&=\max(k-l,u-k),\\
\rho&=\min\{\eta/8,r/38,(u-l)/8,d_*/2,\sqrt T\},&
\delta&=\rho^2,&c_\lambda&=\frac1{1024(1+|\lambda|)}.
\end{aligned}
\tag{26.1}
$$

In particular $\rho>0$, $\delta\le T$, and $\rho=\eta/8$ for
all sufficiently small $\eta$. The numerical-command class is the
complete class $\mathcal C_T$ of Definition 20.2, with this supplied
observation. Each issuance chooses its entire numerical AC profile
from issuance-time information. Subsequent stopping-time interruptions
may replace only its unexecuted continuation. There is no dwell,
speed, deterministic count, or observation-resolution bound. Continuous
joins, own-height death and the original extrema guard are required.

**Theorem 26.2 (finite causal full-held attainment).** For every fixed
$\eta>0$ there is a policy in this class whose actual zero-start
controls $(a_\eta,b_\eta)$ are almost surely finite piecewise linear
histories. Put $J_\eta=\int a_\eta\,db_\eta$. Its complete held native
path has

$$
D_{\max}(\bar q_\eta,\bar q^\lambda)\le6\rho\le\eta
\quad\hbox{almost surely},
\tag{26.2}
$$

including every interrupted leg, terminal leg and hold. Its own
censored death and cutoff are exactly

$$
\zeta_\eta=
\begin{cases}\tau+\delta,&\tau+\delta\le T,\\
\infty,&\tau+\delta>T,
\end{cases}
\qquad S_\eta=\min(T,\tau+\delta),\qquad
0\le S_\eta-S\le\delta.
\tag{26.3}
$$

Every retained native death is at the target's exit face. The entire
held triples obey

$$
\begin{aligned}
\|a_\eta-W^1_{\cdot\wedge S}\|_\infty&\le4\rho,\\
\|b_\eta-W^2_{\cdot\wedge S}\|_\infty&\le10\rho,\\
\|J_\eta-J^\lambda_{\cdot\wedge S}\|_\infty
 &\le10K_*\rho+7\rho^2.
\end{aligned}
\tag{26.4}
$$

With precisely the actual executed-prefix costs (11.4), its original-law
expectations satisfy

$$
\begin{aligned}
\mathbb E V^a_\eta&\le\frac3{\mu_\lambda}
                  (\mathbb ES/\rho+\rho)+5\rho,\\
\mathbb E V^b_\eta&\le\frac3{\mu_\lambda}
                  (\mathbb ES/\rho+\rho)+17\rho,\\
\mathbb E L_\eta&\le\frac6{\mu_\lambda}
                  (\mathbb ES/\rho+\rho)+22\rho,\\
\mathbb E E_\eta&\le\frac{48}{c_\lambda\mu_\lambda}
                  (\mathbb ES/\rho^2+1)+708.
\end{aligned}
\tag{26.5}
$$

Here $\mu_\lambda$ is exactly (18.2). Energy has no factor $1/2$.
In particular the expected variation and length powers are
$O(\eta^{-1})$ and the expected energy power is $O(\eta^{-2})$,
on the same target, clock, error variable and probability law. The
construction and proof occupy §§27–30; §31 gives its coupled lifetime
and path-space consequences.

## 27. Known connectors and stopping-time execution of their suffixes

**Definition 27.1 (normal connector geometry).** Use the analytic target
mesh $t_i$ of (16.4), with scale $\rho$, on an auxiliary Brownian
continuation if needed. Write
$C_{s,t}=J^\lambda_t-J^\lambda_s-W^1_s(W^2_t-W^2_s)$ as in
(16.3). Each mesh increment satisfies

$$
|X_i|,|Y_i|\le\rho,\quad |C_i|\le\rho^2,\qquad
(X_i,Y_i,C_i)=
(W^1_{t_i}-W^1_{t_{i-1}},W^2_{t_i}-W^2_{t_{i-1}},C_{t_{i-1},t_i})
\tag{27.1}
$$

for $i\ge1$. At an active $t_i<S$, set $h=k+W^1_{t_{i-1}}$,
choose the inward sign $d$ from (17.2), with $|d|=\rho$, and put
$q_i=C_i/d$. Let $g_i:[0,1]\to\mathbb R^2$ be the six-leg
piecewise linear path (17.3) with vertices

$$
(0,0),(d,0),(d,q_i),(0,q_i),(0,0),(0,Y_i),(X_i,Y_i),
\tag{27.2}
$$

and equal parameter durations $1/6$. Its entire numerical geometry is
known at $t_i$. Translated from the native controls at $t_i$, it will
connect the exact target triple at $t_{i-1}$ to that at $t_i$.
It is executed after $t_i$, rather than interpolated before that time.

The connector computation is the explicit rectangle of Lemma 17.1,
with the stronger bounds (27.1). Consequently all its prefixes have
$|x|,|y|\le\rho$, $|j|\le\rho^2$, where $j=\int x\,dy$.
The relative integral runs from $0$ to $C_i$ on its second leg and
is constant thereafter. All heights are strictly interior to $I$
when its two endpoint heights are interior. Its geometric costs are

$$
V^a(g_i)\le3\rho,\qquad V^b(g_i)\le3\rho,\qquad
L(g_i)\le6\rho,\qquad
\int_0^1|g_i'(v)|^2\,dv\le36\rho^2.
\tag{27.3}
$$

Indeed the variations are $2\rho+|X_i|$ and
$2|q_i|+|Y_i|$. All legs are along the original axes, so length is
their sum. The last integral is
$6(2\rho^2+2q_i^2+X_i^2+Y_i^2)$. These are direct uses of the
published connector geometry, with no additional steering premise.

**Definition 27.2 (prescribed suffixes and their interruptions).** Fix a
normal connector starting at $s=t_i$. Initially its progress parameter
is $v_0=0$ and its first issue time is $r_0=s$. On attempt $j\ge0$ put

$$
\epsilon_j=\frac\rho4\,2^{-j},\qquad
h_j=c_\lambda\rho^2 4^{-j}.
\tag{27.4}
$$

At the stopping time $r_j$, with current progress $v_j<1$, prescribe
the complete zero-start numerical profile

$$
\gamma_j(u)=
 g_i\left(v_j+(1-v_j)\min\{u/h_j,1\}\right)-g_i(v_j),
\qquad 0\le u\le T.
\tag{27.5}
$$

It is piecewise linear, completes the remaining geometric suffix in
original time $h_j$, and then holds. No future observation enters
this profile. Define the next target threshold after issuance by

$$
\theta_j=\inf\{u>0:
 |W^1_{r_j+u}-W^1_{r_j}|\ge\epsilon_j\ \hbox{or}\
 |W^2_{r_j+u}-W^2_{r_j}|\ge\epsilon_j\ \hbox{or}\
 |C_{r_j,r_j+u}|\ge\epsilon_j^2\}.
\tag{27.6}
$$

If $\theta_j<h_j$, interrupt at $r_{j+1}=r_j+\theta_j$ and set
$v_{j+1}=v_j+(1-v_j)\theta_j/h_j$; then issue (27.5) for $j+1$.
If $\theta_j\ge h_j$, finish at $r_j+h_j$ and retain its prescribed
hold. Equality is treated as completion. The actual policy also
interrupts at $\tau$ or $T$, as specified in §28. The unrestricted
version of this suffix rule, used for estimates, ignores those two
cutoffs and uses the auxiliary Brownian continuation. It is only a
dominating construction, not extra observed information.

**Lemma 27.3 (finite completion, geometric conservation and conditional
energy).** Conditional on $\mathcal F_s$, the unrestricted rule has
only finitely many attempts almost surely. It finishes strictly before
the next analytic mesh point $t_{i+1}$. It traverses the connector
exactly once, in order, and satisfies

$$
\mathbb E(E_i^{\rm full}\mid\mathcal F_{t_i})
 \le48/c_\lambda.
\tag{27.7}
$$

This bound is uniform over all past connector data satisfying (27.1).
All its numerical choices are measurable at issuance and all its
interruptions are stopping times. Each actually executed prefix has
its original-velocity cost; none is revalued by a later issuance.

Proof. First apply strong Markov at a finite $r_j$, in the independently
enlarged Brownian filtration of Definition 26.1. If
$V_u=W_{r_j+u}-W_{r_j}$, stochastic integration after a stopping time
gives

$$
C_{r_j,r_j+u}=\int_0^u V^1_v\,dV^2_v+\lambda u.
$$

One can obtain this identity first for simple predictable integrands
on the shifted filtration and then by Itô isometry, stopping where
the coordinates are bounded. Removing these bounds gives the
continuous integral identity on every finite interval. Strong Markov
makes the entire future path $V$ an independent covariance-$2$
Brownian pair. Its stochastic integral is a measurable limit of its
own simple-integrand sums, so the joint future enhancement in this
display has the fresh enhanced Brownian law as well. Thus no
independent area process or future area observation has been added.
Scaling space by $\epsilon_j$ and time by $\epsilon_j^2$ leaves the
normalized area drift equal to $\lambda$. The normalized planned time
is independent of $j$:

$$
w=\frac{h_j}{\epsilon_j^2}=16c_\lambda
 =\frac1{64(1+|\lambda|)}.
\tag{27.8}
$$

It is at most $1/[2(1+|\lambda|)]$ and less than $1$. The classical
reflection and exponential-martingale estimate (18.3), with exactly
these coordinates and relative integral, therefore gives

$$
\mathbb P(\theta_j<h_j\mid\mathcal F_{r_j})
 \le8e^{-1/(4w)}+2e^{-1/(16w)}
 \le8e^{-16}+2e^{-4}=:q<1/16.
\tag{27.9}
$$

For example $e^4>40$ already proves the last strict inequality.
The estimate stops the area martingale at first-level exit, where its
quadratic variation is at most $2w$; the drift on this time interval
has magnitude at most $|\lambda|w<1/2$. Thus the bounded-variation
area drift has not been discarded in using (18.3). The classical
strong Markov and reflection suppliers are those specified in
Definitions 20.1 and 25.1; their covariance has been rescaled explicitly.

Let $A_j$ be the event that attempt $j$ is reached in this unrestricted
construction. It means that all previous attempts were interrupted,
and is measurable at $r_j$. Successive conditioning in (27.9) gives

$$
\mathbb P(A_j\mid\mathcal F_s)\le q^j.
\tag{27.10}
$$

This is not an assertion that the surviving attempts or terminal cells
are independent. At every finite attempt the threshold delay is
strictly positive, by continuity at zero and its positive thresholds.
Conditional probability of infinitely many attempts is bounded by
$\lim_jq^j=0$. Thus a last attempt completes the path almost surely.
The sum of all elapsed attempt times through completion is at most
$\sum_{j\ge0}h_j=4c_\lambda\rho^2/3<\rho^2$.

We must also verify that the target mesh cannot overtake this service.
On each executed attempt its target increments, including the final
endpoint, have first-level magnitudes at most $\epsilon_j$ and
relative chronological magnitude at most $\epsilon_j^2$. For any
prefix through finitely many attempts, Chen's identity (16.9) gives

$$
\begin{aligned}
|W^m_t-W^m_s|&\le\sum_{j\ge0}\epsilon_j=\rho/2\quad(m=1,2),\\
|C_{s,t}|&\le\sum_j\epsilon_j^2+
                  \sum_{j<j'}\epsilon_j\epsilon_{j'}
 =\tfrac12\left((\sum_j\epsilon_j)^2+\sum_j\epsilon_j^2\right)
 =\rho^2/6.
\end{aligned}
\tag{27.11}
$$

For a partial last attempt use its corresponding threshold bounds;
the infinite sums only enlarge the finite ones. The same inequalities
hold at completion by continuity. Their bounds are strictly below the
mesh thresholds $\rho,\rho,\rho^2$, and the elapsed time is strictly
below its cap $\rho^2$. Hence $t_{i+1}$ is strictly after completion.
This verifies the service schedule rather than assuming that a short
next cell allows completion at a fixed speed.

During attempt $j$, progress in (27.5) increases affinely from $v_j$
at speed $(1-v_j)/h_j$. If that attempt were run to its planned end,
its quadratic energy would be

$$
\frac{1-v_j}{h_j}\int_{v_j}^1|g_i'(v)|^2\,dv
 \le\frac{36\rho^2}{h_j}=
       \frac{36}{c_\lambda}4^j.
\tag{27.12}
$$

An interrupted prefix has no greater energy, since its integrand is
nonnegative and its velocity is still the one in (27.5). Tonelli and
(27.10) now yield

$$
\mathbb E(E_i^{\rm full}\mid\mathcal F_s)
 \le\frac{36}{c_\lambda}\sum_{j\ge0}(4q)^j
 \le\frac{48}{c_\lambda},
\tag{27.13}
$$

proving (27.7). Progress never decreases and is continuous at every
interruption; the final attempt reaches $1$. Thus its sequence of
suffixes describes the original geometric path once, without repeated
legs. Variation, length and the relative chronological integral are
unchanged by these increasing piecewise linear parametrizations.
In particular (27.3) bounds their total, regardless of the retry count.

Finally the threshold processes in (27.6) are continuous and adapted
after a stopping time. Their first hitting times, and their minima
with the known planned completion times, are stopping times in the
usual filtration. The past $g_i$, current $v_j$, issue time and
$h_j$ determine the entire continuous function (27.5) measurably.
Evaluation at a stopping time and the finite arithmetic/interpolation
operations used here are measurable; a profile's values at rational
elapsed times determine its Borel law in the uniform continuous-path
space. On each finite-count event this is a finite recursion. These
observations apply to $\mathcal K$ before target death, when the needed
target history is supplied. Strong Markov was used in the larger
Brownian filtration only to bound that recursion. $\square$

## 28. The complete causal policy and its own native exit

**Definition 28.1 (normal evolution and the paid terminal connector).**
Issue the zero profile at time zero. Hold until the first mesh knot,
$\tau$, or $T$. At every $t_i<S$, $i\ge1$, execute the normal connector
by Definition 27.2; after completion hold until the next knot or cutoff.
The actual knot computation observes (16.4) only until its next
threshold, its time cap, $\tau$, or $T$, whichever comes first. A
normal issuance occurs only strictly before both cutoffs. Target
death takes priority over a simultaneous knot or retry threshold;
the horizon stops all execution. Thus no later analytic knot or
post-death target increment is queried by the policy. Simultaneous
instructions are represented by this single selected replacement.
At target death $\tau\le T$, interrupt any normal segment or hold
continuously. Write the current actual controls and chronological
integral as $(a_0,b_0,J_0)$ at that time, and prescribe a terminal
six-leg connector (17.3) of duration $\delta$, with

$$
\begin{aligned}
h_0&=k+a_0,\\
X&=W^1_\tau-a_0,\qquad Y=W^2_\tau-b_0,\\
C&=J^\lambda_\tau-J_0-a_0Y,\qquad
 d=\begin{cases}\rho,&h_0\le(l+u)/2,\\-\rho,&h_0>(l+u)/2,
 \end{cases}\qquad q=C/d.
\end{aligned}
\tag{28.1}
$$

Each leg receives time $\delta/6$, followed by a hold. Every quantity
in this complete numerical profile is known at $\tau$. If its planned
completion is later than $T$, execute its original prefix through $T$;
do not accelerate it to finish at the horizon. If $\tau>T$ there is
no terminal connector. At own height exit hold both controls and use
the native cemetery convention, as in Definition 20.3. Target death
alone changes no native height and supplies no native death flag.

**Proposition 28.2 (finite policy, chronology and guards).** This policy
belongs to $\mathcal C_T$. It is almost surely a finite concatenation
of numerical piecewise linear profiles, and its whole original guard is

$$
k+\min_{[0,T]}a_\eta\ge l>0,\qquad
k+\max_{[0,T]}a_\eta\le u<H.
\tag{28.2}
$$

Its own lifetime and exit face satisfy (26.3). In particular it never
dies before target death. All chronological integrals are those of its
actual controls, including every interrupted prefix.

Proof. Proposition 16.3 gives finitely many analytic knots before $S$.
For each knot Lemma 27.3 has only finitely many attempts almost surely;
a countable intersection over knot indices suffices. The same lemma
puts completion before the next knot unless target death or the
horizon interrupts. Initially the native triple is $z_0=(0,0,0)$.
Inductively, just before the normal connector issued at $t_i$, the
native triple is exactly $z_{t_{i-1}}$. Indeed the preceding connector
completed before $t_i$ and held thereafter. The connector endpoint is
$z_{t_i}$ because its ordinary relative integral is $C_i$ and the
translated integral is $W^1_{t_{i-1}}Y_i+C_i$, as in (17.6).
This proves the invariant at every next knot. The initial hold handles
$i=1$. Arbitrary changes of suffix speed preserve these chronological
integrals, since they traverse exactly the same geometric prefixes.
There is no resetting of $J$, height, phase, or controls at an issuance.

The inward excursions in each normal connector are strictly interior,
and its last height leg joins two interior target heights. Hence all
native heights are interior before the terminal connector. This remains
true at a target death that interrupts a leg: the current numerical
normal path has interior endpoints at its issuing knot. The initial
height is also interior. Thus $h_0\in I$ in (28.1).
The terminal inward rectangle and phase leg stay in $I$, since
$\rho\le(u-l)/8$. Its final height leg joins $h_0$ to
$k+W^1_\tau\in\{l,u\}$. Every point before the end of this final
leg is interior. Its endpoint is the same exit face as the target's.
The native first exit is therefore exactly $\tau+\delta$ if that time
is at most $T$, and there is no native exit on the horizon otherwise.
At a death at $T$ the same endpoint rule applies. The formula for
$S_\eta$ and $0\le S_\eta-S\le\delta$ follow directly. If the
terminal connector completes, (28.1) also gives precisely the target
triple $z_\tau$, which is then held.

All executed heights lie in $[l,u]\Subset(0,H)$, proving (28.2).
N, Theorems 9.2–9.3 apply to every actual prefix, with its negative
phase convention and original preparation. Their formula is exactly
(11.3), with $J_\eta=\int a_\eta\,db_\eta$. The numerical domain
of this same realized command remains
$(-\min a_\eta,H-\max a_\eta)$; for another starting-height promise
it must satisfy (2.4). The inward choice does not enlarge that domain.

There is one initial issuance, finitely many normal attempts, and at
most one terminal issuance. Each attempt has at most six nonconstant
linear pieces and its prescribed hold. Its interruptions do not create
jumps, and the terminal join is continuous. Consequently the actual
histories have finite piece and issuance counts, are zero-start AC
and piecewise $C^1$, and have finite variation and energy almost surely.
The possibly unbounded speeds are finite on each of these finitely
many pieces. All normal observations are before target death, and
the terminal profile is a measurable function of the stopped data
and the policy's known past controls. In particular its $J_0$ is
computable from its finite issued profiles and their elapsed prefixes.
An issuance at the zero remaining horizon moves no state. These facts
verify all operation and information requirements of $\mathcal C_T$.
More explicitly, on each event specifying finite knot and attempt
counts, the actual path evaluations are finite compositions of
measurable stopping-time evaluations, arithmetic and interpolation.
These countably many events exhaust probability one. Rational-time
evaluations generate the Borel sigma algebra of the continuous-path
space, and each chronological value is a finite ordinary leg integral.
Thus the complete executed controls and their chronological paths are
measurable random continuous paths. Choices on the exceptional null
set can be fixed arbitrarily in the usual completions; all operational
requirements and estimates here are almost sure statements.
$\square$

## 29. Accuracy at every actual prefix

**Proposition 29.1 (full held tube and chronological estimates).** The
policy of Definition 28.1 satisfies (26.2) and (26.4), with common
initial real phase representatives, before wrapping both phases modulo
$2\pi$.

Proof. Consider first $v< S$. On the initial hold the target increments
satisfy (16.5) relative to $p=0$. On a later cell
$t_i\le v\le t_{i+1}$ before target death, let $p=t_{i-1}$. The
executed normal connector or its hold has relative coordinates
$(x,y,j)$ from $z_p$, with $|x|,|y|\le\rho$ and $|j|\le\rho^2$,
by (27.2). These bounds apply to every interrupted prefix and to every
suffix speed. The target has relative coordinates

$$
x_*=W^1_v-W^1_p,\qquad y_*=W^2_v-W^2_p,\qquad c_*=C_{p,v}.
\tag{29.1}
$$

Two successive mesh intervals and (16.9) give
$|x_*|,|y_*|\le2\rho$ and $|c_*|\le3\rho^2$. At a mesh endpoint
one may use the cell on its right; its connector starts at progress zero.
Consequently

$$
|x-x_*|,|y-y_*|\le3\rho,\qquad |j-c_*|\le4\rho^2.
\tag{29.2}
$$

The initial hold obeys these same bounds with its stronger one-cell
estimates. Since the triples agree at $p$, exact translation gives

$$
J_\eta(v)-J^\lambda_v
 =W^1_p(y-y_*)+j-c_*.
\tag{29.3}
$$

Here $|W^1_p|\le K_*$. More effectively, the direct native phase
error is

$$
\Delta\widetilde\alpha=(y-y_*)/2,\qquad
\Delta\widetilde\beta=
 (\tfrac12-(k+W^1_p)/r)(y-y_*)-(j-c_*)/r.
\tag{29.4}
$$

Its coefficient has absolute value at most $1/2$, because the anchor
height is in $I\subset(0,H)$. Thus before target death the native
height error is at most $3\rho$, the alpha error at most $3\rho/2$,
and the beta error at most $3\rho/2+4\rho^2/r<2\rho$.
Equations (29.2)–(29.3) give the corresponding triple errors
$3\rho,3\rho,3K_*\rho+4\rho^2$. All these bounds pass to $\tau$
from below by continuity when $\tau\le T$.

For the terminal connector use (29.1)–(29.2) at $v=\tau$, so that
the actual and target triples, relative to the same interior anchor
$p$, are $(x,y,j)$ and $(x_*,y_*,c_*)$. Substitution into (28.1)
retains the chronological cross term and gives

$$
X=x_*-x,\quad Y=y_*-y,\quad C=c_*-j-xY,
\qquad |X|,|Y|\le3\rho,\quad |C|\le7\rho^2.
\tag{29.5}
$$

In particular the terminal geometry is quantitatively bounded even
when target death interrupts a normal area leg. Let $(x_0(v),y_0(v),j_0(v))$
be any terminal prefix relative to the actual state at $\tau$.
The rectangle has $|q|\le7\rho$; all its phase coordinates have
$|y_0|\le7\rho$, including the subsequent leg to $Y$. Its relative
integral stays on the line segment between $0$ and $C$ and is then
constant. Therefore

$$
|y_0-Y|\le10\rho,\qquad |j_0-C|\le7\rho^2.
\tag{29.6}
$$

The terminal height differs from its fixed target boundary height by
at most $4\rho$: at the inward excursion its difference is at most
$|X|+\rho$, and the remaining height leg stays between its two
endpoints. This proves the first-level bounds in (26.4).

Comparing this prefix to its prescribed terminal endpoint, which is
the held target triple, the exact phase formulas give

$$
\begin{aligned}
|\Delta\widetilde\alpha|&\le5\rho,\\
|\Delta\widetilde\beta|
 &\le\tfrac12|y_0-Y|+|j_0-C|/r
 \le5\rho+7\rho^2/r<6\rho.
\end{aligned}
\tag{29.7}
$$

The coefficient in the second line is evaluated at the actual
terminal starting height $h_0\in I$, so its absolute value is at
most $1/2$. This computation compares complete chronological states;
it does not treat target area as an independent native actuator.
Moreover

$$
J_\eta(v)-J^\lambda_\tau
 =a_0(y_0-Y)+j_0-C,
\tag{29.8}
$$

and $|a_0|\le K_*$ by (28.2). Equations (29.6)–(29.8) prove the
last bound in (26.4). They hold even if the terminal connector is
cut off at $T$, with its original parametrization. After a completed
terminal connector all triple and phase errors are zero. If the
target survives past $T$, only (29.2)–(29.4) are needed. Thus the
bounds are for the full held histories on $[0,T]$, including all
possible terminal cases. Projection to either original $2\pi$ circle
is 1-Lipschitz. Together with the height bound, (29.7) proves
$D_{\max}\le6\rho\le\eta$. $\square$

## 30. Original-law costs and matching necessary powers

**Proposition 30.1 (integrable actual execution).** The four expectations
in (26.5) hold for the construction, using precisely the original
velocities and Wiener law. Its issuance count has finite expectation
at each fixed $\eta$.

Proof. Let $N=\#\{i:t_i<S\}$, including $i=0$. The normalized
mesh cells have the conditional law (18.5), and $\mu_\lambda>0$
is supplied with its full scope by (18.2)–(18.4). The start event
$\{t_i<S\}$ is $\mathcal F_{t_i}$ measurable. The same Tonelli
and conditional expectation calculation as (18.6) therefore gives

$$
\mathbb EN\le\frac{\mathbb ES+\rho^2}{\rho^2\mu_\lambda}.
\tag{30.1}
$$

For clarity the pathwise sum of durations over these start events is
the first mesh point at or after $S$, at most $S+\rho^2$; conditioning
each full duration on its start gives mean $\rho^2\mu_\lambda$.
No claim that a cell selected by its end or its survival has the
unselected cell law is used.

At each normal start $t_i<S$, $i\ge1$, define its full suffix service
on the auxiliary Brownian continuation, ignoring later target death.
It uses the connector already known at that start. Lemma 27.3 bounds
its conditional energy by $48/c_\lambda$. The actual normal execution
agrees with this service until $\tau$ or $T$ and executes at most
its original prefix. Hence

$$
\begin{aligned}
E_{\rm normal}
 &\le\sum_{i\ge1}{\bf1}_{\{t_i<S\}}E_i^{\rm full},\\
\mathbb E E_{\rm normal}
 &\le\frac{48}{c_\lambda}\mathbb EN
 \le\frac{48}{c_\lambda\mu_\lambda}
                  (\mathbb ES/\rho^2+1).
\end{aligned}
\tag{30.2}
$$

The factorization is conditional on the start, before imposing any
later interruption or survival. The continuation only defines the
nonnegative dominating variable. Neither its future observations nor
its unexecuted motion is charged to the actual native command.
Normal variations and length are bounded pathwise by
$3\rho N,3\rho N,6\rho N$, respectively, because increasing suffix
parametrizations never repeat the geometric path.

For the terminal connector (29.5) and the six equal durations give

$$
\begin{aligned}
V^a_{\rm term}&=2\rho+|X|\le5\rho,\\
V^b_{\rm term}&=2|q|+|Y|\le17\rho,\\
L_{\rm term}&=V^a_{\rm term}+V^b_{\rm term}\le22\rho,\\
E_{\rm term}&=\frac6\delta(2\rho^2+2q^2+X^2+Y^2)
 \le6(2+98+9+9)=708.
\end{aligned}
\tag{30.3}
$$

These are full planned connector costs. If the horizon cuts it short,
its actually executed costs are no greater, by integration of the
same velocities over a smaller prefix. Combining (30.1)–(30.3)
proves exactly (26.5). Every target-death-to-native-death motion is
included; native post-death holds have zero velocity.

More explicitly, within any issued profile a planned straight piece
of duration $d$ and increment $(A,B)$ has fixed velocity $(A,B)/d$.
An executed fraction $\theta$ costs
$\theta|A|$, $\theta|B|$, $\theta\sqrt{A^2+B^2}$ and
$\theta(A^2+B^2)/d$. When a suffix is subsequently accelerated,
this formula for all preceding pieces remains unchanged. The new
profile only prescribes future velocities. Thus (27.12) and (30.3)
are bounds for actual original-time integrals, without compressing a
past partial leg, assigning post-death bills or changing measure.

Finally (27.10) bounds the conditional expected attempt count by
$1/(1-q)\le16/15$ at each normal start. Tonelli on the same start
events bounds the expected total issuance count by
$2+(16/15)\mathbb EN$. The initial and terminal profiles account for
the two additive issuances, and each successful normal attempt already
contains its subsequent hold. There is consequently no countable
accumulation hidden in this construction. $\square$

**Corollary 30.2 (same-tolerance expected power comparison).** Along
any deterministic sequence $\eta_n\to0$, all four costs have the
necessary expected powers of Theorem 13.2, with explicit comparisons

$$
\begin{aligned}
\mathbb ES&\le\liminf_n\eta_n\mathbb EV^a_{\eta_n}
 \le\limsup_n\eta_n\mathbb EV^a_{\eta_n}
 \le24\mathbb ES/\mu_\lambda,\\
\mathbb ES/2&\le\liminf_n\eta_n\mathbb EV^b_{\eta_n}
 \le\limsup_n\eta_n\mathbb EV^b_{\eta_n}
 \le24\mathbb ES/\mu_\lambda,\\
\sqrt5\,\mathbb ES/2&\le\liminf_n\eta_n\mathbb EL_{\eta_n}
 \le\limsup_n\eta_n\mathbb EL_{\eta_n}
 \le48\mathbb ES/\mu_\lambda,\\
5\pi^2\mathbb ES/24&\le\liminf_n\eta_n^2\mathbb EE_{\eta_n}
 \le\limsup_n\eta_n^2\mathbb EE_{\eta_n}
 \le\frac{3072\mathbb ES}{c_\lambda\mu_\lambda}.
\end{aligned}
\tag{30.4}
$$

Proof. Intersect the probability-one events for this countable sequence.
Equations (26.2)–(26.4) give the complete held native accuracy and
chronological convergence, and (26.3) gives censored lifetime
convergence as proved explicitly in §31. Thus Theorem 13.2 applies
with its same $\eta_n$, $d_a=1$ and $d_b=2$. Its lower coefficients
and Fatou's lemma give the lower inequalities in (30.4); no new
lower-bound argument is required. For the uppers, eventually
$\rho_n=\eta_n/8$ in (26.5). Substitute and take the upper limits.
The additive terminal and mesh constants vanish after normalization.
This compares the same actual controls and joint target, rather than
a scalar optimum or an unexecuted enhanced interpolation. $\square$

## 31. Coupled lifetimes, death marks and the three path metrics

**Proposition 31.1 (censored lifetime and death-mark rate).** For the
actual construction, when $\delta\le T/2$ put

$$
C_T=\frac{u-l}{\sqrt{4\pi}(T/2)^{3/2}}.
\tag{31.1}
$$

Its death-mark discrepancy and the lifetime metric of Theorem 24.1
satisfy

$$
\begin{aligned}
\mathbb P({\bf1}_{\{\zeta_\eta<\infty\}}
                \ne{\bf1}_{\{\zeta<\infty\}})
 &=\mathbb P(T-\delta<\tau\le T)\le C_T\delta,\\
\mathbb E d_\zeta(\zeta_\eta,\zeta)&\le(1+C_T)\delta.
\end{aligned}
\tag{31.2}
$$

Along every deterministic $\eta_n\to0$, the complete held triples and
native paths converge uniformly almost surely to the held target;
$\zeta_{\eta_n}\to\zeta$ almost surely, with eventually equal death
marks. In particular the joint held-path/lifetime law contract (11.7)
holds on this actual coupling.

Proof. Formula (26.3) shows that native death is delayed by exactly
$\delta$ when observed, with no native death if the target survives.
The two marks differ exactly on $T-\delta<\tau\le T$.
For a covariance-$2$ Brownian motion the classical one-sided first
passage time to a level at distance $d>0$ has density

$$
f_d(t)=\frac{d}{\sqrt{4\pi}\,t^{3/2}}
               \exp\{-d^2/(4t)\},\qquad t>0.
\tag{31.3}
$$

This follows by differentiating the reflection-principle identity
$\mathbb P(\sup_{s\le t}W^1_s\ge d)=2\mathbb P(W^1_t\ge d)$;
the variance is $2t$. Exit through a particular face in a time
interval is contained in the event that the first one-sided passage
to that face lies in that interval. Sum (31.3) for distances $k-l$
and $u-k$. On $[T-\delta,T]$ their sum is at most $C_T$, proving
the first line of (31.2). On equal finite marks the lifetime metric
is at most $\delta$, on unequal marks it is $1$, and on equal no-death
marks it is zero. This proves its expectation bound.

If $\tau<T$, then for all sufficiently large $n$,
$\tau+\delta_n<T$, so the two marks are finite and their times differ
by $\delta_n\to0$. If $\tau>T$ both marks are always infinite.
The remaining event $\tau=T$ is null by Proposition 4.5. This proves
the almost sure lifetime and eventual mark assertion without an
independence or matching-marginal-law substitution. Equation (26.4)
proves uniform convergence of the same triples; alternatively the
phase-lift transfer (13.3) applies to (26.2). Their exact affine
native images converge uniformly too. Taking these convergences
jointly proves the law assertion. $\square$

**Proposition 31.2 (held uniform, cemetery uniform and $J_1$).** Use
$d_E=\min(1,d_{\max})$ on the held cylinder and distance $2$ from it
to the isolated cemetery. For every fixed $\eta$, almost surely on
$\{\tau\le T\}$,

$$
\sup_{t\le T}d_E(q_\eta^\dagger(t),q^{\lambda,\dagger}(t))=2.
\tag{31.4}
$$

Nevertheless along every deterministic $\eta_n\to0$ the actual killed
paths converge almost surely in $J_1$ on $D([0,T],E)$. If
$0<\tau<\tau+\delta<T$, a comparison homeomorphism has displacement
at most $\delta$ and state error at most
$\eta+\omega_{\bar q^\lambda}(\delta)$, where the latter is the
modulus of continuity in $d_{\max}$ of the complete held target.

Proof. At time $\tau\le T$ the target is already at $\dagger$ but
the native height is strictly interior, and its own death is later
than $\tau$ or absent on the horizon. Their distance there is $2$,
which is maximal. This proves (31.4), consistently with Corollary
22.1. It also proves failure of same-clock uniform convergence in
probability for any countable sequence, because $\mathbb P(\tau\le T)>0$.
It has no implication against the held uniform estimate (26.2).

For $0<\tau<\tau+\delta<T$, take the increasing piecewise linear
homeomorphism $\Lambda:[0,T]\to[0,T]$ sending
$(0,\tau,T)$ to $(0,\tau+\delta,T)$. Then
$\|\Lambda-\mathrm{id}\|_\infty\le\delta$. For $t<\tau$ both
killed paths at their compared times are alive, and (26.2) gives

$$
\begin{aligned}
d_E(q_\eta^\dagger(\Lambda(t)),q^{\lambda,\dagger}(t))
&\le d_{\max}(\bar q_\eta(\Lambda(t)),\bar q^\lambda(\Lambda(t)))
       +d_{\max}(\bar q^\lambda(\Lambda(t)),\bar q^\lambda(t))\\
&\le\eta+\omega_{\bar q^\lambda}(\delta).
\end{aligned}
\tag{31.5}
$$

At and after $\tau$ the compared paths are both at $\dagger$.
When $\tau<T$, for all sufficiently small $\eta_n$ the strict
inequalities needed for this homeomorphism hold. When $\tau>T$ no
path dies and the identity suffices, with the held tube. The case
$\tau=T$ is null. For any fixed stage a coincidence
$\tau+\delta=T$ is also null, by the atomlessness already shown
(or is impossible if $\delta=T$). Thus continuity of the held target
and $\delta_n\to0$ prove $J_1$ convergence. The homeomorphism is a
comparison in path space only. All controls, chronological integrals
and energy calculations keep their original execution times.
$\square$

## 32. Mathematical suppliers and scope of the finite causal conclusion

**Definition 32.1 (supplier correspondence).** N, O and G retain exactly
the immutable convention 1.1. N, Definitions 3.1, 8.1 and 9.1,
Theorems 9.2–9.3 and Definition 10.1 supply lawful original histories,
full extrema domains, chronological composition and the stated costs.
O, Definitions 1.1–1.3 and Theorem 2.1 at $\varepsilon=1$, and
G, Definition 4.1, fix the two actual circles, fields, covariance and
height killing. The normal and terminal rectangles reuse §17, rather
than a general steering claim. The mesh and its stopped start-event
expectation reuse §§16 and 18. The necessary powers reuse §§12–13.
The finite-issuance information and own-death definitions reuse §20;
its exact-lifetime obstruction and the distinct lifetime-only results
in §§21–25 do not supply the full tracking result of Theorem 26.2.

Lifshits–Setterqvist, *Energy of Taut Strings Accompanying Wiener
Process*, [arXiv:1405.1651v1](https://arxiv.org/html/1405.1651v1),
§4.2 supply classical scalar free-knot interpolation and its
inverse-duration energy method. Their §5 studies continuously
observation-dependent Markovian pursuit, a different issuance class.
Friz–Victoir, *Approximations of the Brownian rough path with
applications to stochastic analysis*,
[Ann. IHP 41 (2005), 703–724, §5.1](https://www.numdam.org/item/AIHPB_2005__41_4_703_0.pdf),
supply enhanced Brownian approximation; the literal adapted display
in Corollary 28 has the qualification in §25. Friz–Oberhauser,
*Non-standard approximations of the Itô-map*,
[arXiv:0808.0337v1, §1.2 and §2.1](https://arxiv.org/html/0808.0337v1),
distinguish enhanced path observations from finitely many first-level
values and supply the classical central-perturbation setting.
Brownian strong Markov, reflection and the exponential-martingale
inequality are used with the precise conditional normalization in
(27.8)–(27.9); the first two suppliers are specified in §§20 and 23.
These existing results are intermediate suppliers. None is being
restated as a new generic approximation theorem.

**Proposition 32.2 (attained endpoint and unresolved boundaries).**
Theorem 26.2 attains the deterministic complete held native tube and
the expected necessary cost powers in the finite numerical issuance
class, with ideal supplied enhanced observations and approximate
coupled own lifetime. It does not impose exact lifetime, a deterministic
command-count or speed bound, or an observation acquisition procedure.
Sharp native constants, physical realization of the observations and
commands, physical energy, drift selection and an identification with
three physical spatial directions remain separate questions.

Proof. The added native argument is the delayed inward connector with
stopping-time replacement of its known suffix, its conditional
geometric energy sum, and the paid terminal connector with full
chronological and phase estimates. Equations (27.9)–(27.13) and
(30.1)–(30.3) prove finite issuances and actual-prefix expectation
bounds, while §§28–29 prove the whole held tube in the original
source. Section 31 proves coupled lifetime and $J_1$ convergence
and the same-clock cemetery obstruction. Thus a scalar tube,
endpoint interpolation, continuously specified actuator feedback or
a countably accumulating execution has not replaced the finite
full-state claim. Observation-dependent decisions occur at finitely
many issuances almost surely; every intervening numerical profile
is already fixed when issued.

The retained lifetimes are strictly delayed, as required by (26.3),
and so respect Theorem 21.1. The upper and lower constants in (30.4)
are unequal and establish powers rather than a sharp optimum. The
same construction and estimates hold for every fixed $\lambda$;
this freedom does not select a drift. All costs are the unhalved
identity functional and original phase variation defined in (11.4),
which contain no physical calibration or acquisition cost. The fixed
native ray dimension, direct control rank, bracket growth, volume
exponent and number of physical spatial axes remain the distinct
objects described in Remark 7.3. The finite causal result is a
repository-derived ordinary mathematical combination of the credited
suppliers, without a claim of literature priority or completion of a
continuous why-three objective. $\square$

## 追加锚（本行以下为增补区）

## 33. Independent central noise and necessary executed resources

**Definition 33.1 (one joint target and the finite issuer class).** Keep
all the native data of Definitions 2.1–2.2 and 11.1–11.2: fixed
$0<Z<1$, $r=1-Z$, $H=r/2$, $0<l<k<u<H$, $T>0$, arbitrary fixed
preparation phases, probabilities $(k,H-k,Z,H-k,k)$, negative amplitude
convention, both $2\pi$ periods, the original fields $P,Q$, the extrema
guard, and the four unhalved original-clock costs (11.4). On one Wiener
space let $W^1,W^2,C$ be independent covariance-$2$ Brownian motions,
starting at zero. Fix arbitrary $\lambda\in\mathbb R$ and
$\nu\in\mathbb R\setminus\{0\}$. Define jointly

$$
\begin{aligned}
K_t&=J^{\lambda,\nu}_t
 =\int_0^tW^1_s\,dW^2_s+\lambda t+\nu C_t,\\
\tau&=\inf\{t\ge0:k+W^1_t\notin(l,u)\},\qquad S=\tau\wedge T,\\
\bar z_t&=(W^1_{t\wedge S},W^2_{t\wedge S},K_{t\wedge S}),\\
\bar q_t&=\left(k+W^1_{t\wedge S},
 [\alpha_0+W^2_{t\wedge S}/2],
 [\beta_0+c_0W^2_{t\wedge S}-K_{t\wedge S}/r]\right),
 \qquad c_0=\tfrac12-k/r.
\end{aligned}
\tag{33.1}
$$

All target coordinates are held at the same $S$. Its death mark is
$\zeta=\tau$ if $\tau\le T$ and $\infty$ otherwise. The Brownian
coordinates and the coefficient $\nu$ are additional analytic premises.
They are not native controls or consequences of the finite source.

Let $\mathcal F$ be the usual joint Brownian filtration, optionally
enlarged initially by a seed independent of the entire triple. The ideal
supplied observation is the usual augmentation of the stopped past of
$(W^1,W^2,C,K)$ at $\tau$, together with that seed. Use Definition
20.2's finite numerical-command class with this observation: each entire
numerical AC profile is chosen at a stopping-time issuance, later
stopping-time interruptions replace only its unexecuted continuation,
joins are continuous, and the actual issuance count through own death or
$T$ is almost surely finite. No fixed dwell, speed or deterministic count
bound is imposed. The own exit, held controls $(a,b)$, chronological
integral $J=\int a\,db$, native path $\bar q^{\rm N}$ and censored
mark $\zeta^{\rm N}$ have exactly Definition 20.3's meanings. In
particular own death is actual height exit, not target death or a command
interruption. The required tube is the complete metric of (13.1):

$$
D_{\max}(\bar q^{\rm N},\bar q)\le\eta\quad\hbox{almost surely}
\tag{33.2}
$$

for each deterministic $\eta>0$, on this same joint source. There is no
survival conditioning, target resampling, clock change or measure change.
The observation premise supplies ideal real histories; it makes no
acquisition or finite-bit assertion.

**Theorem 33.2 (full-class expected lower bounds).** Every policy in
Definition 33.1 satisfying (33.2) for deterministic $0<\eta<\pi$
obeys the following bounds, allowing infinite expectations. Put

$$
F_\eta=\left[(2\nu^2-4r|\lambda|\eta)\mathbb ES
                         -4r^2\eta^2\right]_+.
\tag{33.3}
$$

Then its actual executed-prefix resources satisfy

$$
\begin{aligned}
\mathbb EV^a&\ge\frac{F_\eta}{8r\eta^2},&
\mathbb EV^b&\ge\frac{F_\eta}{4r\eta^2},\\
\mathbb EL&\ge\frac{\sqrt5 F_\eta}{8r\eta^2},&
\mathbb EE&\ge\frac{5F_\eta^2}
                         {64r^2\eta^4\mathbb ES}.
\end{aligned}
\tag{33.4}
$$

Here $0<\mathbb ES\le T$. These inequalities require no lifetime
approximation and no special mesh or command shape. In fact they hold
for every continuous adapted AC own-held pair with the same native tube
and guard, a class containing all the finite issuers under consideration.
For any family satisfying these hypotheses as $\eta\downarrow0$,

$$
\begin{aligned}
\liminf_{\eta\downarrow0}\eta^2\mathbb EV^a_\eta
 &\ge\nu^2\mathbb ES/(4r),\\
\liminf_{\eta\downarrow0}\eta^2\mathbb EV^b_\eta
 &\ge\nu^2\mathbb ES/(2r),\\
\liminf_{\eta\downarrow0}\eta^2\mathbb EL_\eta
 &\ge\sqrt5\nu^2\mathbb ES/(4r),\\
\liminf_{\eta\downarrow0}\eta^4\mathbb EE_\eta
 &\ge5\nu^4\mathbb ES/(16r^2).
\end{aligned}
\tag{33.5}
$$

Proof. The continuous-lift argument in Theorem 13.2 uses only the
$2\pi$ periods, common initial lifts and the tube, so applies unchanged
to (33.1). On the entire interval it gives
$|a-W^1_{\cdot\wedge S}|\le\eta$,
$|b-W^2_{\cdot\wedge S}|\le2\eta$, and
$|c_0(b-W^2_{\cdot\wedge S})-(J-K_{\cdot\wedge S})/r|\le\eta$.
This also proves the actual wrapped-to-unwrapped implication here; no
extra unwrapped accuracy or winding convention is assumed.

On $[0,S]$ abbreviate $A=W^1$, $B=W^2$, $e=a-A$, $f=b-B$,
and define two residuals

$$
R_1=J-K-Af,\qquad R_2=J-K-af.
\tag{33.6}
$$

The coefficients $rc_0-A=r/2-(k+A)$ and
$rc_0-a=r/2-(k+a)$ have absolute value at most $r/2$:
target and own held heights both lie in $[l,u]\subset(0,r/2)$.
Consequently $|R_1|,|R_2|\le2r\eta$ on $[0,S]$.
The ordinary controls have finite variation. The semimartingale product
rule, with $[W^1,W^2]=[W^1,C]=[W^2,C]=0$, gives precisely

$$
\begin{aligned}
dR_1&=e\,db-f\,dW^1-\nu\,dC-\lambda\,dt,\\
dR_2&=-f\,da+e\,dW^2-\nu\,dC-\lambda\,dt.
\end{aligned}
\tag{33.7}
$$

All these identities are stopped at $S$. For example
$d(Af)=A\,db-A\,dW^2+f\,dW^1$, because $[A,f]=0$;
$d(af)=a\,db-a\,dW^2+f\,da$, because $a$ has finite variation.
Thus neither central martingale was replaced by its variation, and the
chronological product term has its original sign.

The martingale parts in (33.7) have quadratic variations
$2\int_0^{\cdot\wedge S}(f^2+\nu^2)dt$ and
$2\int_0^{\cdot\wedge S}(e^2+\nu^2)dt$. Their integrands, and the
residuals multiplying them in Itô's formula, are bounded. They therefore
have square-integrable stopped stochastic integrals with expectation
zero. If $v_b=\operatorname{TV}_{[0,S]}b$ has finite expectation,
Itô's formula for $R_1^2$, followed by expectation, gives

$$
\begin{aligned}
2\nu^2\mathbb ES
&\le\mathbb ER_1(S)^2
   +2\mathbb E\int_0^S|R_1e|\,|db|
   +2|\lambda|\mathbb E\int_0^S|R_1|dt\\
&\le4r^2\eta^2+4r\eta^2\mathbb Ev_b
                         +4r|\lambda|\eta\mathbb ES.
\end{aligned}
\tag{33.8}
$$

If its expectation is infinite the resulting variation bound is already
true. The same argument for $R_2$ uses
$|R_2f|\le4r\eta^2$ and yields
$2\nu^2\mathbb ES\le4r^2\eta^2+8r\eta^2\mathbb Ev_a
+4r|\lambda|\eta\mathbb ES$, where
$v_a=\operatorname{TV}_{[0,S]}a$. Equivalently one may first stop
when the relevant variation reaches an integer and then pass to the
limit; bounded residuals and monotone variation give the same bounds.
No expected energy assumption is needed for either application.

Let $\ell_S=\int_0^S\sqrt{\dot a^2+\dot b^2}\,dt$ and
$e_S=\int_0^S(\dot a^2+\dot b^2)dt$, using the own-held controls.
Minkowski's inequality gives
$\mathbb E\ell_S\ge\sqrt{(\mathbb Ev_a)^2+(\mathbb Ev_b)^2}$.
Cauchy–Schwarz on probability times original time gives
$(\mathbb E\ell_S)^2\le\mathbb ES\,\mathbb Ee_S$.
These statements extend to infinite expectations by truncation. They
prove (33.4), since $v_a,v_b,\ell_S,e_S$ do not exceed the corresponding
actual total resources: after own death the controls hold, and all
additional movement after target death is nonnegative cost. Finally
$F_\eta\to2\nu^2\mathbb ES>0$ proves (33.5). $\square$

## 34. Small inward loops with a larger chronological increment

**Definition 34.1 (scales and a numerical connector).** Write
$d_*=\min(k-l,u-k)$, $K_*=\max(k-l,u-k)$ and set

$$
\begin{aligned}
A_r&=8(1+r^{-1}),\\
\rho&=\min\{\eta/A_r,1,(u-l)/8,d_*/2,\sqrt T\},
       \qquad\delta=\rho^2,\\
c&=[4096(1+|\lambda|+\nu^2)]^{-1},\qquad
q=8e^{-64}+2e^{-16}<1/16,\qquad m=15c.
\end{aligned}
\tag{34.1}
$$

For a starting height $h\in I=(l,u)$ and relative endpoint
$(X,Y,D)$ with $h+X\in[l,u]$, choose $d=\rho$ if
$h\le(l+u)/2$ and $d=-\rho$ otherwise. If $D\ne0$, let
$M=\lceil |D|/\rho^2\rceil$ and concatenate $M$ copies of the
closed rectangle

$$
(0,0)\longrightarrow(d,0)\longrightarrow(d,D/(Md))
 \longrightarrow(0,D/(Md))\longrightarrow(0,0).
\tag{34.2}
$$

Then append $(0,0)\to(0,Y)\to(X,Y)$. If $D=0$ use no rectangle.
All coordinates in this definition are relative to the actual starting
controls; the original chronological increment after translation is
$a_{\rm start}Y+D$. Parametrize the concatenation on $[0,1]$ with
constant Euclidean arclength speed, deleting zero-length legs. If its
length is zero use the constant path. Call the resulting numerical
piecewise linear profile $g=(x,y)$ and put $j=\int x\,dy$.

**Lemma 34.2 (native connector bounds).** At every prefix of this
connector,

$$
|x|\le\max(\rho,|X|),\quad |y|\le\max(\rho,|Y|),\quad
j\in[\min(0,D),\max(0,D)].
\tag{34.3}
$$

It ends at $(X,Y,D)$, stays strictly in $I$ until possibly its final
height endpoint, and uses only the two original controls. If
$|X|,|Y|\le A\rho$ and $|D|\le B\rho$, then

$$
\begin{aligned}
V^a(g)&\le2B+(2+A)\rho,&
V^b(g)&\le2B+A\rho,\\
L(g)&\le4B+(2+2A)\rho,&
\int_0^1|g'(v)|^2dv&=L(g)^2.
\end{aligned}
\tag{34.4}
$$

In particular for $(A,B)=(1,1)$ these are bounded by $5,3,8,64$;
for $(A,B)=(3,7)$ they are bounded by $19,17,36,1296$.

Proof. Each rectangle is exactly the native rectangle of Lemma 17.1,
with $|D/(Md)|\le\rho$. Its relative integral increases from the
previous value to that value plus $D/M$ on its second leg and is
constant on the other three legs. All rectangle increments have the
same sign. The two final legs add zero relative integral. This proves
(34.3), the endpoint chronology and the translated cross term, by (17.6).
The inward excursion $h\to h+d$ is strictly interior because
$\rho\le(u-l)/8$. The last height leg joins $h$ to $h+X$ and is
interior before its endpoint. These are whole-height checks, independent
of the number of rectangles.

For $D\ne0$ the exact variations are $2M\rho+|X|$ and
$2|D|/\rho+|Y|$. Since $M\le|D|/\rho^2+1$, they give
(34.4), also when $D=0$. All legs are along control axes, so their
sum is the Euclidean length. Constant arclength speed on the unit
parameter interval proves the last equality. There are finitely many
legs for each finite input, with no new instantaneous central operation.
$\square$

## 35. The joint mesh and its conditional duration charge

**Definition 35.1 (central-noise mesh).** On the same Brownian source
continued for analytic estimates, define

$$
D_{s,t}=K_t-K_s-W^1_s(W^2_t-W^2_s).
\tag{35.1}
$$

Set $t_0=0$ and let $t_{i+1}$ be the earlier of $t_i+\rho^2$ and
the first $t>t_i$ when one of
$|W^1_t-W^1_{t_i}|$, $|W^2_t-W^2_{t_i}|$, $|D_{t_i,t}|$
reaches $\rho$. These are analytic stopping times, not controls.
In particular their complete cells satisfy

$$
|W^j_v-W^j_{t_i}|\le\rho\ (j=1,2),\qquad
|D_{t_i,v}|\le\rho,\qquad t_i\le v\le t_{i+1}.
\tag{35.2}
$$

The identity (16.9) holds for these $D$: the added $\lambda t+\nu C_t$
has additive increments, so introduces no extra cross term.

**Proposition 35.2 (finite mesh and uniform mean duration).** The mesh
has finitely many knots in every bounded interval almost surely. With
$N=\#\{i\ge0:t_i<S\}$, including $t_0$, one has

$$
\mathbb EN\le\frac{\mathbb ES+\rho^2}{m\rho^2}.
\tag{35.3}
$$

Proof. Uniform continuity of $(W^1,W^2,K)$ and boundedness of $W^1$
on a fixed compact interval give a positive lower bound on the
threshold delays for its starting points. Together with the time cap
this proves nonaccumulation, as in Proposition 16.3.

At a finite stopping time $s$, strong Markov in the joint triple and
stochastic integration after $s$ give, for a fresh covariance-$2$
Brownian triple $U$, the conditional normalized cell law

$$
\begin{aligned}
\sigma_\rho=\min\{1,\inf\{v>0:
 |U^1_v|\ge1\ \hbox{or}\ |U^2_v|\ge1\ \hbox{or}\
 |\rho\!\int_0^vU^1_w\,dU^2_w+\lambda\rho v+\nu U^3_v|\ge1\}\},\\
\mathcal L((t_{i+1}-t_i)/\rho^2\mid\mathcal F_{t_i})
 =\mathcal L(\sigma_\rho).
\end{aligned}
\tag{35.4}
$$

The scaling here is central threshold $\rho$, not $\rho^2$.
The independent central Brownian term therefore retains coefficient
$\nu$; no clock change of the actual target has occurred.

For $0<v\le[2(1+|\lambda|)]^{-1}$, stop $U^1$ at its first
absolute level $1$ when estimating the central martingale. Its quadratic
variation before that stop is at most $2(\rho^2+\nu^2)v
\le2(1+\nu^2)v$, while $|\lambda|\rho v\le1/2$.
The reflection and exponential-martingale inequalities used in (18.3)
therefore give

$$
\mathbb P(\sigma_\rho\le v)
 \le8e^{-1/(4v)}+2e^{-1/[16(1+\nu^2)v]}.
\tag{35.5}
$$

For the central event before a first-level exit, the stopped martingale
must reach absolute level $1/2$; this explains the second exponent.
At $v=16c<1$ this upper bound is at most $q$ in (34.1).
Consequently $\mathbb E\sigma_\rho\ge16c(1-q)\ge m$,
uniformly for $0<\rho\le1$.

The event $\{t_i<S\}$ is measurable at the start $t_i$.
Pathwise the sum of complete mesh durations over these events is the
first knot at or after $S$, and is at most $S+\rho^2$.
Tonelli and conditioning at each start, using (35.4), give
$m\rho^2\mathbb EN\le\mathbb ES+\rho^2$.
The cells selected by their ends or by later survival are not assigned
a fresh unconditional law. A continuation beyond $S$ defines only this
nonnegative duration comparison; the actual policy below never queries
that continuation. $\square$

## 36. Finite stopping-time service of the known connector

**Definition 36.1 (numerical suffix rule).** At a knot $s=t_i<S$,
$i\ge1$, the normal connector is Definition 34.1 with

$$
\begin{aligned}
h&=k+W^1_{t_{i-1}},\\
(X,Y,D)&=(W^1_{t_i}-W^1_{t_{i-1}},
 W^2_{t_i}-W^2_{t_{i-1}},D_{t_{i-1},t_i}).
\end{aligned}
\tag{36.1}
$$

Its entire geometry $g$ is already known at $s$. Its endpoint heights
are interior, its prefixes satisfy $|x|,|y|\le\rho$, $|j|\le\rho$,
and its normalized energy is at most $64$ by Lemma 34.2.
Use the suffix mechanism of Definition 27.2 with the following different
central thresholds. Set $r_0=s$, $v_0=0$, and on attempt $j\ge0$ put

$$
\epsilon_j=(\rho/4)2^{-j},\qquad h_j=c\rho^2 4^{-j},\qquad
\gamma_j(u)=g\bigl(v_j+(1-v_j)\min(u/h_j,1)\bigr)-g(v_j).
\tag{36.2}
$$

At $r_j$ issue this entire numerical profile, with its hold after
$h_j$. Interrupt if, strictly before completion, one of
$|W^1_{r_j+u}-W^1_{r_j}|$,
$|W^2_{r_j+u}-W^2_{r_j}|$, $|D_{r_j,r_j+u}|$
first reaches $\epsilon_j$. If this delay is $\theta_j<h_j$,
put $r_{j+1}=r_j+\theta_j$ and
$v_{j+1}=v_j+(1-v_j)\theta_j/h_j$, then issue the next suffix.
Equality means completion. The actual rule also stops at target death
or the horizon; its unrestricted version for estimates uses the same
Brownian continuation and ignores these two cutoffs.

**Lemma 36.2 (finite service, no mesh overtaking and conditional energy).**
Conditional on $\mathcal F_s$, the unrestricted service completes in
finitely many attempts almost surely, before $t_{i+1}$. It traverses
$g$ once in order, preserving its chronology and geometric variations.
Its full original-time energy and attempt count satisfy

$$
\mathbb E(E_i^{\rm full}\mid\mathcal F_s)
 \le\frac{128}{c\rho^2},\qquad
\mathbb E(A_i^{\rm full}\mid\mathcal F_s)\le16/15.
\tag{36.3}
$$

All issuances and interruptions obey Definition 33.1's information
contract.

Proof. At each reached $r_j$, strong Markov supplies a fresh joint
Brownian future. Before the first-level $\epsilon_j$ exits, the
relative central martingale
$\int_0^u(W^1_{r_j+w}-W^1_{r_j})\,dW^2_{r_j+w}
 +\nu(C_{r_j+u}-C_{r_j})$
has quadratic variation at most
$2(\epsilon_j^2+\nu^2)h_j\le2(1+\nu^2)h_j$ up to $h_j$.
Also $|\lambda|h_j\le\epsilon_j/2$, because
$h_j/\epsilon_j=4c\rho2^{-j}\le4c$.
Reflection for the two first-level coordinates and the same stopped
exponential inequality thus yield

$$
\begin{aligned}
\mathbb P(\theta_j<h_j\mid\mathcal F_{r_j})
&\le8e^{-\epsilon_j^2/(4h_j)}
       +2e^{-\epsilon_j^2/[16(1+\nu^2)h_j]}\\
&=8e^{-1/(64c)}+2e^{-1/[256c(1+\nu^2)]}\le q<1/16.
\end{aligned}
\tag{36.4}
$$

Here $\epsilon_j^2/h_j=1/(16c)$ is independent of $j$ and $\rho$.
The independent $C$ term is included in the quadratic variation; an
area-only Brownian estimate would not justify (36.4).

If $A_j$ is the event of reaching attempt $j$, successive conditioning
gives $\mathbb P(A_j\mid\mathcal F_s)\le q^j$. Every finite
threshold delay is positive by continuity. Thus infinitely many attempts
have probability zero and the expected count is at most
$\sum_jq^j\le16/15$. Completion takes at most
$\sum_jh_j=4c\rho^2/3<\rho^2$ units of the original clock.
At any prefix before completion the target's first-level displacement
from $s$ is at most $\sum_j\epsilon_j=\rho/2$. Chen's identity
(16.9), applied to the successive attempt intervals, gives

$$
|D_{s,t}|\le\sum_j\epsilon_j+
                     \sum_{j<j'}\epsilon_j\epsilon_{j'}
 =\rho/2+\rho^2/12\le7\rho/12<\rho.
\tag{36.5}
$$

Use a partial last interval for a partial attempt. The infinite sums
only enlarge the actual finite sums. The same strict bounds hold at
completion. Neither a target threshold nor the time cap for the next
mesh knot can therefore have occurred: service finishes before
$t_{i+1}$. This establishes the schedule without anticipating the next
cell duration.

Progress increases continuously, and the last attempt reaches $1$;
there is no repeat of an already traversed geometric prefix. An attempt
run to its planned end would have energy

$$
\frac{1-v_j}{h_j}\int_{v_j}^1|g'(v)|^2dv
 \le64/h_j=\frac{64}{c\rho^2}4^j.
\tag{36.6}
$$

Its interrupted prefix has no greater energy at its originally issued
velocities. Tonelli with the reach probabilities gives
$\mathbb E(E_i^{\rm full}\mid\mathcal F_s)
\le64(c\rho^2)^{-1}\sum_j(4q)^j
\le128(c\rho^2)^{-1}$, proving (36.3).

Every profile in (36.2) is fixed numerically by its issuance-time
geometry and progress. The threshold processes are continuous and
adapted after $r_j$, so their first hitting times and their minima with
planned completion and cutoffs are stopping times. Up to target death
they use only the supplied past. The unrestricted future is used solely
for a nonnegative cost bound. No command reads it. The construction is
the suffix rule of §27 with the new central scale, repeated native
rectangles and the explicit central-noise probability estimate above.
$\square$

## 37. Complete native execution, guards and the hard tube

**Definition 37.1 (one actual policy).** Issue the zero profile at zero.
Before $S$, hold until a mesh knot and, at every $t_i<S$, $i\ge1$,
serve (36.1) by Definition 36.1; after completion retain its issued hold.
The next mesh threshold is monitored only up to target death or $T$.
Target death takes priority over a simultaneous knot or retry; the
horizon stops all execution. At $\tau\le T$ interrupt continuously
and let $(a_0,b_0,J_0)$ be the actual triple then. Issue Definition
34.1's complete terminal connector from $h_0=k+a_0$, with

$$
X=W^1_\tau-a_0,\quad Y=W^2_\tau-b_0,\quad
D=K_\tau-J_0-a_0Y,
\tag{37.1}
$$

executed in original duration $\delta=\rho^2$, followed by a hold.
If $T$ occurs during this connector, keep exactly its originally
prescribed prefix through $T$. At own actual height exit hold both
controls. Denote this same actual family by $(a_\eta,b_\eta,J_\eta)$,
where $J_\eta=\int a_\eta\,db_\eta$. No terminal acceleration to
meet the horizon is performed.

**Proposition 37.2 (finite numerical membership and exact own exit).**
For every deterministic $\eta>0$ this policy belongs to Definition
33.1's class almost surely, uses only finitely many piecewise linear
numerical issuances, and satisfies

$$
\begin{aligned}
k+\min_{[0,T]}a_\eta&\ge l>0,&
k+\max_{[0,T]}a_\eta&\le u<H,\\
\zeta^{\rm N}_\eta&=
 \begin{cases}\tau+\delta,&\tau+\delta\le T,\\
 \infty,&\tau+\delta>T,\end{cases}&
S^{\rm N}_\eta&=T\wedge(\tau+\delta),\qquad
0\le S^{\rm N}_\eta-S\le\delta.
\end{aligned}
\tag{37.2}
$$

Every retained own death is at the target's exit face.

Proof. Proposition 35.2 gives finitely many knots before $S$.
Lemma 36.2, on a countable intersection over knot indices, gives finite
service at each, completed before the next knot unless a cutoff
intervenes. Inductively the actual triple just before the connector
issued at $t_i$ is exactly $(W^1,W^2,K)_{t_{i-1}}$.
The connector's final ordinary chronological integral, translated by
$W^1_{t_{i-1}}Y$, makes its endpoint exactly the target triple at
$t_i$. The initial hold supplies the first induction anchor. Increasing
suffix parametrizations preserve these integrals. In particular there
is no resetting of any accumulated chronological value.

Normal endpoints are interior target heights and every normal geometric
prefix is interior by Lemma 34.2. Thus no own exit occurs before $\tau$.
At $\tau$ the current height $h_0$ is still interior, even if a
normal rectangle is interrupted. The terminal inward loops and phase
leg are interior. Its final height leg, which has nonzero length,
joins $h_0$ to the target boundary and reaches it only at its endpoint.
Constant arclength parametrization assigns that endpoint the full
prescribed duration $\delta$. Hence own death is exactly $\tau+\delta$
when that lies on the horizon, and otherwise there is no own death on
$[0,T]$. If the target survives to $T$, all normal prefixes stay
interior. These facts prove (37.2) and the exit-face assertion. They
also prove the displayed whole-height extrema guard for the entire
actual command, including terminal movement and holds. For another
starting-height promise the same numerical history still requires
exactly (2.4); the policy does not enlarge its domain.

Each normal connector and terminal connector has finitely many
rectangles, each suffix has finitely many linear pieces, and the
number of actual suffix issuances is finite almost surely. Joins are
continuous, so the actual controls are zero-start AC and piecewise
$C^1$. Their finite positive piece durations give finite pathwise
energy. Numerical profiles include their holds. Simultaneous events
are represented by the single selected replacement, so no multiple
instantaneous instructions or accumulating issue times are required.

All knot data are observed by issuance, and all retry thresholds are
stopping times before the cutoff. The terminal profile uses only the
stopped observations and the actual past command, whose $J_0$ is its
known finite ordinary integral. The integer ceiling, inward choice,
finite concatenation and arclength parameters in Definition 34.1 are
Borel functions of their finite numerical data. Hitting times and
stopping-time evaluations of these continuous adapted processes are
measurable. On each finite-count event, rational-time evaluations of
the issued and executed paths are finite compositions of these maps;
these evaluations generate the continuous-path Borel sigma algebra.
The countable union of the finite-count events has probability one.
This proves the required profile and path measurability as well as
nonanticipation. Exceptional null sets may be assigned the zero history
in the usual completion; the operational assertions are almost sure
for each deterministic tolerance. All commands use the original $P,Q$ and native
chronology (2.5), with the fixed preparations and periods. $\square$

**Proposition 37.3 (complete held wrapped and chronological accuracy).**
The same family, including every interrupted leg, terminal prefix and
hold, satisfies

$$
\begin{aligned}
D_{\max}(\bar q^{\rm N}_\eta,\bar q)&\le A_r\rho\le\eta,\\
\|a_\eta-W^1_{\cdot\wedge S}\|_\infty&\le4\rho,\\
\|b_\eta-W^2_{\cdot\wedge S}\|_\infty&\le4\rho,\\
\|J_\eta-K_{\cdot\wedge S}\|_\infty&\le(4K_*+7)\rho.
\end{aligned}
\tag{37.3}
$$

Proof. Before $S$, during a cell after $t_i$, compare with the common
anchor $p=t_{i-1}$. The actual normal connector or its hold has
relative triple $(x,y,j)$ with $|x|,|y|\le\rho$, $|j|\le\rho$.
The target relative triple
$(x_*,y_*,j_*)=(W^1_v-W^1_p,W^2_v-W^2_p,D_{p,v})$
obeys $|x_*|,|y_*|\le2\rho$ and
$|j_*|\le2\rho+\rho^2\le3\rho$ by the two successive mesh cells
and their Chen cross term. Therefore

$$
|x-x_*|,|y-y_*|\le3\rho,\qquad |j-j_*|\le4\rho.
\tag{37.4}
$$

For the initial hold the stronger one-cell inequalities imply the
same bounds. These inequalities are independent of how many small
rectangles or accelerated suffixes have already been traversed.
Translation from the exact common anchor yields

$$
\begin{aligned}
J_\eta(v)-K_v&=W^1_p(y-y_*)+j-j_*,\\
\Delta\widetilde\alpha&=(y-y_*)/2,\\
\Delta\widetilde\beta&=
 (\tfrac12-(k+W^1_p)/r)(y-y_*)-(j-j_*)/r.
\end{aligned}
\tag{37.5}
$$

The coefficient in the last line has absolute value at most $1/2$.
Thus the pre-target-death height, alpha and beta errors are bounded
by $3\rho$, $3\rho/2$ and $3\rho/2+4\rho/r$ respectively;
the chronological error is at most $(3K_*+4)\rho$.
Continuity gives these inequalities at $\tau\le T$ from below.

At that time write the actual and target relative triples from the
same anchor as $(x,y,j)$ and $(x_*,y_*,j_*)$. Formula (37.1) becomes

$$
X=x_*-x,\qquad Y=y_*-y,\qquad D=j_*-j-xY.
\tag{37.6}
$$

In particular $|X|,|Y|\le3\rho$ and
$|D|\le4\rho+3\rho^2\le7\rho$. Lemma 34.2 therefore applies
with $(A,B)=(3,7)$. At any terminal prefix $(x_0,y_0,j_0)$,
$|y_0-Y|\le4\rho$: during a rectangle $|y_0|\le\rho$,
and on the subsequent phase leg $y_0$ lies between $0$ and $Y$.
Also $|j_0-D|\le|D|\le7\rho$ by the monotone chronological
prefix property, and the height is within $|X|+\rho\le4\rho$
of its fixed terminal target height. The exact endpoint comparison is

$$
\begin{aligned}
|\Delta\widetilde\alpha|&\le2\rho,\\
|\Delta\widetilde\beta|
 &\le\tfrac12|y_0-Y|+|j_0-D|/r
 \le2\rho+7\rho/r,\\
|J_\eta(v)-K_\tau|
 &=|a_0(y_0-Y)+j_0-D|\le(4K_*+7)\rho.
\end{aligned}
\tag{37.7}
$$

The beta coefficient is evaluated at $h_0\in I$, and $|a_0|\le K_*$
by (37.2). After completion all target triple errors are zero. If $T$
interrupts this terminal profile, the same prefix bounds apply without
changing its velocity or comparing it to a different target. If no
target death occurs, (37.4)–(37.5) suffice through $T$.
Finally $\max\{4,2+7/r\}\le A_r$ and projection onto either
original $2\pi$ circle is 1-Lipschitz. This proves (37.3) for the
complete held histories. $\square$

## 38. Matching expected orders for actual original-time execution

**Theorem 38.1 (attained expected resource orders).** For every fixed
native datum, $\lambda\in\mathbb R$ and $\nu\ne0$, the family
of Definition 37.1 satisfies, on the original joint Wiener law,

$$
\begin{aligned}
\mathbb EV^a_\eta&\le5\frac{\mathbb ES+\rho^2}{m\rho^2}+19,\\
\mathbb EV^b_\eta&\le3\frac{\mathbb ES+\rho^2}{m\rho^2}+17,\\
\mathbb EL_\eta&\le8\frac{\mathbb ES+\rho^2}{m\rho^2}+36,\\
\mathbb EE_\eta&\le
 \frac{128}{cm}\frac{\mathbb ES+\rho^2}{\rho^4}
                          +\frac{1296}{\rho^2}.
\end{aligned}
\tag{38.1}
$$

Its expected issuance count is at most
$2+(16/15)(\mathbb ES+\rho^2)/(m\rho^2)$.
Thus the same family attains simultaneously
$\mathbb EV^a_\eta,\mathbb EV^b_\eta,\mathbb EL_\eta
=O(\eta^{-2})$ and $\mathbb EE_\eta=O(\eta^{-4})$.
Combined with Theorem 33.2, each resource's infimum over the entire
finite issuer class satisfying the complete hard tube has matching
order: $\Theta(\eta^{-2})$ for both variations and length, and
$\Theta(\eta^{-4})$ for unhalved identity energy. An infimum need not
be attained exactly; these are power statements, not sharp constants.

Proof. At a normal start $t_i<S$, the already known connector has
geometric variations and length at most $5,3,8$. Suffix acceleration
traverses its geometry once, so every actual prefix has no greater
geometric cost. The unrestricted full service in Lemma 36.2 dominates
the actual service through its possible later target death or horizon
cutoff. Conditioning at this start before imposing any later cutoff
bounds its expected energy by $128/(c\rho^2)$ and its expected
attempt count by $16/15$, uniformly over the known connector data.
Tonelli over the measurable start events, and (35.3), give the normal
parts of (38.1). This calculation uses actual original velocities;
it never charges an inverse arbitrarily short terminal mesh remainder.

The terminal data satisfy $(A,B)=(3,7)$ by (37.6), so their geometric
costs are at most $19,17,36$. A complete terminal connector of duration
$\delta=\rho^2$ has energy at most $1296/\rho^2$ by (34.4).
An interrupted prefix at $T$ integrates the same squared velocities
over a smaller interval. The initial hold has zero cost. These facts
prove every bound in (38.1) and the stated count bound, including all
movement after target death and before own death or $T$.

More explicitly, each originally issued straight leg of duration $d$
and increment $(A,B)$ has velocity $(A,B)/d$ and an executed fraction
$\theta$ contributes the four quantities of Definition 11.2.
A new suffix changes only future velocities. Hence neither (36.6) nor
the terminal estimate revalues a previously executed partial leg;
post-own-death holds have zero cost and the cemetery jump has no control
cost. Almost-sure finite counts and finite geometric piece counts give
finite pathwise costs, while the conditional estimates above establish
finite expectations, which pathwise finiteness alone would not supply.

For all sufficiently small $\eta$, $\rho=\eta/A_r$.
Equation (38.1) gives the asserted upper powers with constants depending
only on the fixed data. Equation (33.5) gives positive lower coefficients
uniform over all eligible policies, without requiring membership in this
particular construction or a lifetime estimate. Consequently the same
upper family also attains those orders when coupled lifetime convergence
is required, by the next theorem. No lower-only inference of existence
is used. $\square$

## 39. Coupled lifetime, death marks and the path-space boundary

**Theorem 39.1 (same-family coupled killing).** For the actual family
above, retain the metric $d_\zeta$ of Theorem 24.1, with $\infty$
an isolated no-death mark, and $C_T$ of (31.1). If $\delta\le T/2$,

$$
\begin{aligned}
\mathbb P({\bf1}_{\{\zeta^{\rm N}_\eta<\infty\}}
       \ne{\bf1}_{\{\zeta<\infty\}})
 &=\mathbb P(T-\delta<\tau\le T)\le C_T\delta,\\
\mathbb E d_\zeta(\zeta^{\rm N}_\eta,\zeta)
 &\le(1+C_T)\delta.
\end{aligned}
\tag{39.1}
$$

Along every deterministic sequence $\eta_n\downarrow0$ the same-source
held triples and full native paths converge uniformly almost surely,
and the censored lifetimes converge almost surely with eventually equal
death marks. The killed paths converge almost surely in $J_1$ in the
space of Definition 4.1. In contrast, for every fixed $\eta$, on
$\{\tau\le T\}$ the same-clock uniform distance between the two
isolated-cemetery paths is exactly $2$.

Proof. Formula (37.2) is an explicit coupled lifetime identity, separate
from the tube. Its mark discrepancy event is exactly the one in (39.1).
The height and its law are unchanged by the central component. The
one-sided first-passage densities (31.3), summed over the two height
faces on $[T-\delta,T]$, therefore give exactly the bound $C_T\delta$
used in Proposition 31.1. On equal finite marks the delay is $\delta$;
on unequal marks the metric is $1$. This proves the second inequality.

For any such deterministic sequence, intersect its probability-one
construction events. When $\tau<T$, eventually $\tau+\delta_n<T$
and the delay tends to zero. When $\tau>T$ both marks are infinite.
The remaining event $\tau=T$ has probability zero by Proposition 4.5.
Equation (37.3) proves uniform convergence of these same held triples
and their native images, jointly with the lifetimes; no independent
coupling or matching marginal law is substituted.

The isolated-cemetery distance is $2$ at time $\tau\le T$, because
only the target has died then. For $0<\tau<\tau+\delta<T$, the
piecewise linear increasing homeomorphism sending $(0,\tau,T)$ to
$(0,\tau+\delta,T)$ has displacement at most $\delta$. Before the
compared death times, the triangle inequality and (37.3) bound the
state error by $\eta+\omega_{\bar q}(\delta)$; afterwards both
paths equal $\dagger$. This is the argument of Proposition 31.2,
which requires only the lifetime identity and continuity of this held
target. Its modulus of continuity tends to zero, also with the added
continuous central component. If $\tau>T$ the identity homeomorphism
suffices. Thus the asserted almost-sure $J_1$ convergence follows.
This homeomorphism compares observations only: it does not retime
execution, chronological integration or any resource in (38.1).
$\square$

## 40. Covariance rank, the zero-noise benchmark and supplier limits

**Proposition 40.1 (the precise dimension and resource distinction).**
Before target death the state dimension remains three and the primitive
native-control rank remains two. The declared independent central
component gives the target direct covariance rank three, with local
covariance tensor

$$
2\left(P\otimes P+Q\otimes Q+
             \frac{\nu^2}{r^2}\partial_\beta\otimes\partial_\beta\right)dt.
\tag{40.1}
$$

For each fixed nonzero $\nu$, the finite nonanticipating hard-tube
resource powers are those of Theorem 38.1. In particular the published
$\nu=0$ offline powers $O(\eta^{-1})$ for variation/length and
$O(\eta^{-2})$ for energy in Theorem 18.1 cannot hold for this new
finite nonanticipating target. This comparison makes no claim about
sharp constants, a uniform crossover as $\nu\to0$, or the best
anticipating costs for the new target.

Proof. The exact native correspondence gives the target differential
$d\kappa=dW^1$, $d\widetilde\alpha=dW^2/2$ and
$d\widetilde\beta=(1/2-\kappa/r)dW^2-\lambda dt/r-\nu dC/r$.
The three Brownian coordinates are independent and each has quadratic
variation $2dt$, proving (40.1). Its noise-column determinant is
$-\nu/(2r)\ne0$. The original two command fields are unchanged;
central noise is an analytic target law, realized approximately by paid
small rectangles and not supplied as a third native actuator.
The positive coefficients (33.5) exclude the old powers for this class,
and (38.1) proves attainment of the larger powers. The lower coefficients
vanish as $\nu\to0$, so this argument asserts no uniform transition
at zero noise. A fixed arbitrary $\lambda$ enters the estimates but
changes no covariance rank or power. These facts distinguish current
state dimension, direct stochastic covariance and primitive control
rank; they identify none of them with physical spatial axes. $\square$

**Definition 40.2 (attribution and applicability).** Native guards,
preparations, signs, periods, chronology and costs retain N, O and G
at the immutable revision of Convention 1.1. The inward rectangle is
Lemma 17.1's original two-control rectangle. Sections 26–32 at published
revision 9bf71444e02e0fac9db11ba42f65b66b27b24d5d supply the finite
numerical suffix mechanism and the paid delayed-exit geometry. Their
$\nu=0$ probability and energy bounds are not premises for the new
noise: (35.4)–(36.6) verify the changed thresholds and all corresponding
conditional estimates. The added mathematical content is the native
full-class residual lower bound, the bounded-control repeated-loop
connector at chronological scale $\rho$, and their complete finite
causal execution with matching expected powers and coupled killing.

The classical stochastic product rule and Itô square identity are used
only for the bounded, stopped residuals (33.6)–(33.8). Strong Markov and
reflection are used for the joint covariance-$2$ Brownian vector, with
the independent initial enlargement of Definition 20.1; Mörters–Peres,
*Brownian Motion*, public draft, Theorem 2.14, supplies the standard
Brownian strong Markov statement. Scaling every coordinate by $\sqrt2$
gives the present normalization. The exponential-martingale estimate is
exactly the one derived in §18, applied with the displayed new quadratic
variations. These standard results are intermediate tools, not new
product or Brownian theorems.

Lifshits–Setterqvist,
[*Energy of Taut Strings Accompanying Wiener Process*,
arXiv:1405.1651v1](https://arxiv.org/html/1405.1651v1), §4.2,
interpolates between random knots using the future endpoint; §5 uses
instantaneous error-dependent pursuit velocity. Those two scalar classes
do not give a finite numerical native issuer with chronological control.
Friz–Victoir,
[*Approximations of the Brownian rough path with applications to
stochastic analysis*, Ann. IHP 41, 703–724, §5.1, pp. 717–718](https://www.numdam.org/item/AIHPB_2005__41_4_703_0.pdf),
give qualitative enhanced approximations, not the hard-tube executed
costs and own-killing estimates here. No use is made of the literal
adapted display in their Corollary 28; its qualification remains §25's.
Friz–Oberhauser,
[*Non-standard approximations of the Itô-map*, arXiv:0808.0337v1,
§§1.2 and 2.1](https://arxiv.org/html/0808.0337v1), require their
central perturbation's group Hölder regularity, the specified lift level
and uniform approximation hypotheses. A Brownian coordinate placed in
degree two has square-root homogeneous size, and cannot simply be
inserted into the usual step-two Brownian Hölder regime. No general
rough differential equation theorem under weaker hypotheses is inferred;
the native equation here depends affinely on precisely the triple.
Łochowski–Miłoś,
[*On truncated variation, upward truncated variation and downward
truncated variation for diffusions*, arXiv:1109.0043v2,
Theorem 1](https://arxiv.org/html/1109.0043v2), concern a fixed continuous
semimartingale as its truncation level decreases. They are not applied
uniformly to the tolerance-dependent residuals of (33.6); (33.8) provides
the needed adapted lower estimate directly.

These results are ordinary mathematical deductions with the stated
analytic and observation premises. They supply no worldwide-priority,
physical-energy, isotropy, preferred-drift, finite-bit acquisition or
physical-space-three assertion. Sharp constants, acquisition mechanisms
and physically calibrated costs remain separate questions.

## 追加锚（本行以下为增补区）

## 41. Paid wrapped current points and the original hard tube

**Definition 41.1 (the added interface and its acquired filtration).**
Retain exactly Definition 33.1's source, coupling, arbitrary preparation
phases, negative amplitude convention, both actual $2\pi$ periods,
$P,Q$, original clock, chronology, guards and four executed costs.
In particular $W^1,W^2,C$ are one persistent independent covariance-$2$
Brownian triple, $\nu\ne0$, and $K,\tau,S,\bar q$ are precisely (33.1).
There is no replacement of the stopped target by a new sample.

Add the following analytic sensor. At a charged time $R_i\in(0,T]$,
$\operatorname{Read}(R_i)$ returns only $\bar q_{R_i}$: its real height
and its two wrapped phases. The preparation $q_0$ is known. Put

$$
\mathcal H_i=\sigma\bigl(U,(R_j,\bar q_{R_j}):1\le j\le i\bigr),
\qquad \mathcal H_0=\sigma(U),
\tag{41.1}
$$

where $U$ is independent of the entire Brownian triple. The next positive
time $R_{i+1}>R_i$, or the decision to make no further call, is chosen
from $\mathcal H_i$, the known own execution and the clock, before the
next unseen interval. Known own execution is a function of these data,
not another target observation. All issued numerical profiles have the
same measurability restriction. Clock events already determined by these
data may end a profile; a subsequent Read may replace only its unexecuted
continuation. No other source-dependent interruption is allowed.
The actual paid count $M$ and the actual numerical issuance count are
almost surely finite through $T$, including own death. Repeated calls
are charged separately. Native death remains actual own height exit,
with the ensuing hold of Definition 20.3.

The continuous-time acquired information consists of the paid records
which have arrived by that time, $U$, and the clock. Its usual augmentation
is contained in the joint Brownian filtration enlarged by $U$. In
particular all recursively chosen Read times are stopping times in that
larger filtration: a time chosen measurably at a stopping time and lying
later is a stopping time. This larger filtration will be used for
probability estimates and converses, never as an acquisition input.

One Read supplies neither continuous past nor an unwrapped phase,
nonzero winding label, bridge, threshold crossing, central coordinate,
nor target death time. A returned height equal to $l$ or $u$ does certify
that this held target has already exited; it does not reveal when it
exited. The sensor is an explicitly added exact-real interface. It is
not a finite-bit, finite-shot or native physical acquisition theorem.

For $0<\delta<1/4$ let $\mathcal C(\eta,\delta)$ be this class with
$\mathbb P(D_{\max}(\bar q^{\rm N},\bar q)\le\eta)\ge1-\delta$,
and define

$$
V(\eta,\delta)=\inf_{\mathcal C(\eta,\delta)}\mathbb E M.
\tag{41.2}
$$

All expectations use the original joint Wiener law and actual execution,
including unsuccessful paths. The infimum of an empty class is infinity.

**Theorem 41.2 (the almost-sure hard tube is impossible).**
For every deterministic $0<\eta<\pi$, no policy of Definition 41.1
satisfies $D_{\max}(\bar q^{\rm N},\bar q)\le\eta$ almost surely.

Proof. Before the first positive Read $R_1$, or through the horizon if
there is none, the entire actual numerical execution is determined by
$U$ and the clock. Its own cutoff is determined by that same numerical
execution. Conditional on $U$, choose a positive time
$t<\min(R_1,T)$, for example half that minimum, interpreting a missing
$R_1$ as infinity. The event $\{\tau>t\}$ has positive conditional
probability and depends only on $W^1$. Independently, $W^2_t$ has a
nondegenerate centered normal distribution with variance $2t$, so
$\mathbb P(|b(t)-W^2_t|>2\eta\mid U)>0$.

On a complete native tube of radius $\eta<\pi$, continuity of the two
phase lifts from their common initial representatives forces
$|b-W^2_{\cdot\wedge S}|\le2\eta$ on the whole interval, by exactly
the connected-lift argument of Theorem 13.2. Hence the intersection of
the two preceding events violates the tube. Its conditional probability
is strictly positive for almost every $U$, and therefore its probability
is positive. Clock-driven bends, arbitrary numerical AC profiles and a
very small first waiting time do not change this argument. $\square$

**Continuation.** Sections 42–49 are in
[Paid-point observation tracking](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md).
The section, theorem and equation numbering continues there: the
[Read converse](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md#42-a-read-converse-for-the-complete-predictable-gap-class),
[chance resource floors](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md#43-chance-class-floors-for-actual-native-execution),
[paid-polling construction](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md#45-one-finite-command-policy-using-only-paid-polling),
[full held accuracy](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md#47-missed-excursions-local-branches-and-complete-held-accuracy),
and [joint orders and lifetime behavior](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md#48-joint-fixed-risk-optimum-and-coupled-own-death-behavior)
use the interface and class of Definition 41.1 above.

## 追加锚（本行以下为增补区）
