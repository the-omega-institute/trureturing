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
