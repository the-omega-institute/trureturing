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
