# Uniform joint noise and tolerance native resource crossover

> This companion uses the `generic-v1` definition/theorem/proof shape.
> Published bytes are preserved; extensions follow the final append anchor.
> The arguments are ordinary mathematical proofs.

## 1. Persistent source, observation and the resource problem

**Convention 1.1 (named suppliers).** Repository references are to
`b42cd0ca83c0936f04dc8890a2ac44d58702642b`. The following assignments
apply throughout this volume, including when a supplier uses different
local abbreviations.

| Symbol | Filename, title and consumed scope |
| --- | --- |
| K | [FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md), *Native guarded lift limits and diffusion selection*: original source and command class in §§2, 11, 20; first-level floors in §§12–13; residual floors in §33; inward geometry and suffix estimates in §§34–37; lifetime comparison in §39. |
| N | [FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md), *Native central-noise full Green propagation and attractive stability*: full killed operator, Green pairing and tail in §1, bounded occupation and singular limits in §§6–7. This N is not K's abbreviation for the original source. |
| O | [FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md), *Native paid-point observation tracking*: the distinct paid filtration, fixed-risk Read laws and scope in Theorems 42.2, 48.1–48.2 and Scope 49.2. |
| V | [FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md), *Native variable-coefficient Green stability on the fixed two-wall cylinder*: the different coefficient-access bridge of Theorem 29.6. |
| G | [FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md](FIB_NATIVE_TWO_CONTROL_GREEN_STABILITY.md), *Native two-control Green attraction, critical stability and periodic binding*: the horizontal Green supplier. |
| S | [FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md](FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md), *Native point-source occupation and finite-command cap limits*: its stated horizontal smooth approximation family only. |

**Definition 1.2 (unchanged native data and joint target).** Fix K,
Definitions 2.1–2.2's native source:
$0<Z<1$, $r=1-Z$, $H=r/2$, $X=Y=H$,
$0<l<k<u<H$, $I=(l,u)$, horizon $T>0$, arbitrary fixed preparation
phases, the negative amplitude convention, probabilities
$(k,H-k,Z,H-k,k)$ and both actual $2\pi$ phase periods. Keep

$$
P=\partial_k,\qquad
Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta,
\qquad c_0=\tfrac12-k/r.
\tag{1.1}
$$

The immutable INITIAL preparation is not reset. If the chosen starting
ray requires a preceding lawful preparation history, that history and
its resources are separate unchanged charges. On one probability space
let $W^1,W^2,C$ be independent Brownian motions, each of quadratic
variation $2t$. Choose a continuous version of
$\mathcal I_t=\int_0^tW^1_s\,dW^2_s$ once, and put

$$
\begin{aligned}
K^\nu_t&=\mathcal I_t+\nu C_t,\qquad |\nu|\le\bar\nu<\infty,\\
\tau&=\inf\{t\ge0:k+W^1_t\notin I\},\qquad S=T\wedge\tau,\\
\bar q^\nu_t&=\left(k+W^1_{t\wedge S},
 [\alpha_0+W^2_{t\wedge S}/2],
 [\beta_0+c_0W^2_{t\wedge S}-K^\nu_{t\wedge S}/r]\right).
\end{aligned}
\tag{1.2}
$$

Here $\lambda=0$. The entire parameter family uses this same Wiener
triple and this same integral; there is no resampling, survival
conditioning or change of clock or probability measure. The target
law is an additional analytic premise, not a consequence of bare FIB.

**Definition 1.3 (one ideal finite numerical-issuer class).** Supply the
usual augmentation of the stopped history
$(W^1,W^2,C,K^\nu)_{\cdot\wedge\tau}$, and optionally a seed independent
of the entire triple. Each issuance, at a stopping time, chooses an
entire zero-start numerical AC control pair, including its prescribed
hold. Later stopping-time interruptions replace only the unexecuted
suffix. Joins are continuous. The number of issuances through own death
or $T$ is almost surely finite, with no fixed dwell, speed or count cap.
The actually executed zero-start controls $(A,B)$ retain their ordinary
chronological integral and full native image:

$$
J_t=\int_0^t A_s\,dB_s,\qquad
q^{\rm N}_t=(k+A_t,[\alpha_0+B_t/2],
 [\beta_0+c_0B_t-J_t/r]).
\tag{1.3}
$$

Every whole numerical command must have its acquired lawful source
domain: for a relative command $(a,b)$ it is exactly
$(-\min a,H-\max a)$, with the compact-promise version of K, (2.4).
No permission is inferred from an endpoint or a limit. In addition,
the actual held height is in $[l,u]$ throughout. Own death is its first
actual exit from $I$; thereafter both controls hold. The censored mark
is $\zeta^{\rm N}=\tau^{\rm N}$ if $\tau^{\rm N}\le T$ and
$\infty$ otherwise; write $S^{\rm N}=T\wedge\tau^{\rm N}$.
Target death is not own death. Rejection executes no movement and
extends no permission. Stop cancels future movement and holds;
neither it, a hold nor an interruption erases the past $J$, incurred
resources or elapsed source time. All past operations and observations
remain one common history.

At $\nu=0$, $C$ remains visible in this same supplied history. Its
coefficient in the target is zero. This visibility and an independent
seed are information/randomization, not a third actuator. The only
actuators at every parameter value are $P,Q$. Exact real stopped-history
access is assumed; it is neither a paid-point nor a finite-bit theorem.

**Definition 1.4 (costs, infima and simultaneous families).** All four
costs are unhalved and integrated over actual original-time prefixes,
including all interrupted and aborted commands and movement after target
death until own death or $T$:

$$
V^a=\int_0^T|\dot A|dt,\quad V^b=\int_0^T|\dot B|dt,\quad
L=\int_0^T\sqrt{\dot A^2+\dot B^2}dt,\quad
E=\int_0^T(\dot A^2+\dot B^2)dt.
\tag{1.4}
$$

Post-own-death holds cost zero. Use K, Definition 13.1's maximum of
height error and the two circle distances, then its supremum over
$[0,T]$, denoted $D_{\max}$. Let $\mathcal A(\eta,\nu)$ consist of
Definition 1.3's issuers such that, almost surely,

$$
D_{\max}(\bar q^{\rm N},\bar q^\nu)\le\eta,
\qquad 0\le S^{\rm N}-S\le\eta.
\tag{1.5}
$$

For $x=a,b,L,E$ put
$\mathsf C_x(\eta,\nu)=\inf_{\pi\in\mathcal A(\eta,\nu)}
\mathbb E C_x(\pi)$, with $C_x=V^a,V^b,L,E$, respectively, and
$\inf\varnothing=+\infty$. Exact minimizers are not asserted.
A simultaneous family is one rule selecting a policy for every
$0<\eta\le\eta_0$, $|\nu|\le\bar\nu$ on the persistent source.
Almost-sure admissibility is asserted for each deterministic pair and
on one common event for any prescribed countable deterministic sequence
of pairs. An uncountable common exceptional-set assertion is unnecessary.
The stronger lifetime and $J_1$ conclusions below refer to these same
policies, not to separately selected cost minimizers.

## 2. A shifted annulus for the complete chronological residual

**Definition 2.1 (error coordinates and barrier).** Fix a small scale
$0<\rho\le1$ and a sign $d/\rho\in\{-1,1\}$, constant during an epoch.
Before target death define

$$
\begin{aligned}
e&=A-W^1-d,\qquad y=B-W^2,\qquad R=(e^2+y^2)^{1/2},\\
z&=J-K^\nu-(W^1+d+e/2)y,\\
\mathcal D_\rho&=\{(e,y,z):\rho/8<R<3\rho/8,\ |z|<\rho\},\\
b&=\nu^2+2\rho^2,\qquad D=\rho^{-2}+b^2\rho^{-4},\qquad
\phi(v)=-\log(1-v^2),\\
f(R)&=64\phi\left(\frac{R-\rho/4}{\rho/8}\right),\quad
g(z)=4096\frac b{\rho^2}\phi(z/\rho),\quad V=f+g.
\end{aligned}
\tag{2.1}
$$

$V$ is nonnegative and tends to infinity at every boundary component.
The offset $d$ places the entire annulus on the inward side of the
height error when its sign is chosen in §3. These are error coordinates,
not new native state variables or actuators.

**Lemma 2.2 (native error dynamics and dissipative numerical velocities).**
For ordinary control velocities $u=(u_a,u_b)$, the exact Itô dynamics are

$$
\begin{aligned}
de&=u_a dt-dW^1,\qquad dy=u_bdt-dW^2,\\
dz&=\tfrac12(eu_b-yu_a)dt
       -\tfrac y2dW^1+(d+\tfrac e2)dW^2-\nu dC.
\end{aligned}
\tag{2.2}
$$

There is an absolute constant $C_0$ such that, on $\mathcal D_\rho$,
writing

$$
G=\frac{f'(R)}R(e,y)+\frac{g'(z)}2(-y,e),\qquad u_*=-G,
\tag{2.3}
$$

the generator with this velocity at that point satisfies

$$
\mathcal L^{u_*}V\le C_0D-\tfrac34|u_*|^2.
\tag{2.4}
$$

The constant is independent of $\rho,\nu,d$.

*Proof.* Put $x=A-W^1=d+e$ and first form
$R_1=J-K^\nu-W^1y$. The semimartingale product rule and zero cross
variations give $dR_1=xu_bdt-y\,dW^1-\nu\,dC$.
Since $z=R_1-d\,y-ey/2$, another application of the product rule gives
(2.2), with $d$ the fixed offset. The chronological cross terms are retained.
The radial drift is $u\cdot(e,y)/R+1/R$, with radial quadratic
variation $2dt$. The half quadratic-variation coefficient of $z$ is

$$
a_z=y^2/4+(d+e/2)^2+\nu^2\le2\rho^2+\nu^2=b.
\tag{2.5}
$$

Since $V=f(R)+g(z)$ has no mixed radial/central derivative,

$$
\mathcal L^uV=f''+f'/R+a_zg''+u\cdot G,
\qquad |G|^2=f'^2+R^2g'^2/4.
\tag{2.6}
$$

These identities also account for the correlation of radial and central
noise; their independence is not assumed.
For $|v|\ge1/\sqrt2$ one has
$\phi''(v)/\phi'(v)^2=(1+v^2)/(2v^2)\le3/2$;
for $|v|\le1/\sqrt2$, both derivatives are bounded.
With $R\ge\rho/8$ and radial half-width $\rho/8$, this gives

$$
f''+|f'|/R\le\tfrac14 f'^2+C\rho^{-2},\qquad
bg''\le\tfrac14(R^2g'^2/4)+Cb^2\rho^{-4}.
\tag{2.7}
$$

For the second inequality, outside the central middle half the ratio
to $R^2g'^2/4$ is at most $384/4096<1/4$; inside it,
$\phi''\le12$. For the first, outside the radial middle half the
corresponding ratios are at most $3/(2\cdot64)$ and
$1/(2\cdot64)$; inside it they contribute $C\rho^{-2}$.
Thus the diffusion part of (2.6) is at most
$|G|^2/4+C_0D$. Substitution of $u_*=-G$ proves (2.4).
$\square$

**Lemma 2.3 (finite numerical sampling of the barrier).** Suppose an
epoch starts at an observed stopping time $s$ in $\mathcal D_\rho$.
For a stopping-time cutoff $s\le\sigma\le T$, there is a finite numerical
issuer, with constant-velocity legs followed by holds, which stays in
$\mathcal D_\rho$ almost surely and obeys

$$
\mathbb E\left[\int_s^\sigma|u_t|^2dt\mid\mathcal F_s\right]
 \le2V_s+4C_0D\,\mathbb E[\sigma-s\mid\mathcal F_s].
\tag{2.8}
$$

The cutoff may depend on the subsequent history. All command prefixes
are charged at their originally issued velocities. Whenever the current
actual height is at least $\rho/2$ from both faces, the whole numerical
profiles below are lawful and stay in $I$.

*Proof.* This construction samples (2.3); it does not issue an
instantaneous feedback law. At a sampled state $p=(e,y,z)$ choose the
numerical vector $u_p=-G(p)$ and $Q_p=|u_p|^2$. Choose the largest radius
in $\{\rho 2^{-j}:j\ge12\}$ whose closed Euclidean ball about $p$ is
inside $\mathcal D_\rho$ and on which

$$
\mathcal L^{u_p}V\le2C_0D-Q_p/2.
\tag{2.9}
$$

Such a radius exists by (2.4) and continuity. The maximal dyadic choice
is Borel, by testing the continuous inequality on a countable dense
set. On every compact subset of the domain these radii have a positive
lower bound: the margin at the center is at least $C_0D+Q_p/4$, and
the relevant functions are uniformly continuous there.
Issue the complete numerical relative profile

$$
\gamma_p(v)=u_p\min(v,h_p),\qquad
h_p=\min\{\rho^2,\rho/[64(1+|u_p|)]\}.
\tag{2.10}
$$

Interrupt at the earlier of this planned completion, exit of the error
state from the chosen ball, and $\sigma$. If still in the epoch, sample
again. Each event is a stopping time; the ball exit uses only the
supplied past and actual $J$. The entire issued height displacement is
at most $\rho/64$, including its hold. Hence the asserted margin makes
its full numerical profile lawful, not merely its executed prefix.

Here are both the hard constraint and the finiteness argument. Stop
first on a compact sublevel of $V$, on a finite sampling count, and at
the external cutoff. Itô's formula and (2.9) give

$$
\mathbb EV_{\rm stop}+\tfrac12\mathbb E\int_s^{\rm stop}|u_t|^2dt
 \le\mathbb EV_s+2C_0D\,\mathbb E({\rm stop}-s).
\tag{2.11}
$$

On such a compact set velocities are bounded, planned durations have
a positive lower bound, and sampling-ball radii have a positive lower
bound. The state paths, including their stopped stochastic integrals,
are uniformly continuous on a compact time interval. Infinitely many
ball exits or completed durations therefore cannot accumulate there.
The probability of reaching level $m$ of $V$ before the cutoff is at
most $(\mathbb EV_s+2C_0DT)/m$, using continuity and (2.11).
Letting $m\to\infty$ rules out a boundary approach or any finite-time
accumulation. More explicitly, (2.11) bounds the total control energy;
Cauchy–Schwarz gives finite control variation, so the state extends
continuously to a putative accumulation time. An interior limit is
excluded by the compact-set argument, and a boundary limit by the
level estimate. The same argument applies when the accumulation time
would equal $\sigma$ or $T$.
Thus the full compact epoch stays in the domain and has finitely many
issuances almost surely. Fatou and localization in (2.11), followed by
conditioning at $s$, prove (2.8). Every previously executed leg keeps
its numerical velocity after replacement. $\square$

## 3. Inward epochs and uniformly priced changes of geometry

**Definition 3.1 (sign epochs and their numerical endpoint).** Put
$m=(l+u)/2$, $g_0=(u-l)/8$ and assume
$\rho\le\min\{1,(u-l)/128,\sqrt T\}$.
Choose $d=\rho$ initially if $k\le m$, and $d=-\rho$ otherwise.
During a positive epoch the next sign trigger is the target height
$m+g_0$; during a negative epoch it is $m-g_0$. At a trigger reverse
the sign. Triggers are monitored only until $S$.
At initialization or a trigger time $s<S$, let the new sign be $d$.
From the actual past triple $(A_0,B_0,J_0)$ prescribe a connector to

$$
(A_*,B_*,J_*)=(W^1_s+d+\rho/4,W^2_s,K^\nu_s),
\tag{3.1}
$$

with relative data $X=A_*-A_0$, $Y=B_*-B_0$,
$D_*=K^\nu_s-J_0-A_0Y$. Use exactly K, Definition 34.1's inward
rectangles of width $\rho$, then its phase leg and final height leg,
with constant arclength parametrization on $[0,1]$. At $s=0$ these
data have $Y=D_*=0$. At a later trigger Lemma 2.3 has kept the preceding
error in its domain, and

$$
|X|\le3\rho,\quad |Y|\le\rho,\quad
D_*=\tfrac12ey-z,\quad |D_*|\le2\rho.
\tag{3.2}
$$

The last identity uses the old epoch coordinates. The new sign changes
no already executed value. The endpoint in (3.1) is interior to $I$.
K, Lemma 34.2 therefore gives inward interior prefixes and
$L(g_s)\le C_1$, $\int_0^1|g_s'|^2\le C_1^2$, uniformly over all these
known data. No source endpoint in the future is used.

**Lemma 3.2 (causal reset service, including every interrupted prefix).**
The connector of Definition 3.1 can be executed in finite numerical
suffixes, before another sign trigger, with conditional expected energy
at most $C_2\rho^{-2}$ and expected issuance count at most $16/15$.
These constants depend on $\bar\nu$ but not on $\rho,\nu$ or the past.
If target death or $T$ intervenes, the actual prefix obeys the same
energy domination. Throughout the service the first-level and complete
chronological errors are at most $C_3\rho$, with $C_3$ depending only
on the fixed native data. At unrestricted completion the new epoch
coordinates satisfy

$$
\rho/5<R<3\rho/10,\qquad |z|<\rho/32,\qquad
V\le C_4(1+\nu^2/\rho^2).
\tag{3.3}
$$

*Proof.* Set $r_0=s$, $v_0=0$. Retain geometric progress $v_j$ without
ever traversing a previous prefix again. At attempt time $r_j$, issue
exactly the zero-start numerical profile

$$
\gamma_j(w)=g_s\bigl(v_j+(1-v_j)\min(w/h_j,1)\bigr)-g_s(v_j),
\qquad w\ge0,
$$

with the following prescribed duration and thresholds:

$$
h_j=c\rho^2 4^{-j},\quad
\epsilon_j=(\rho/1024)2^{-j},\quad
c=[2^{30}(1+\bar\nu^2)]^{-1}.
\tag{3.4}
$$

It holds after completion. Interrupt before completion if either fresh
first-level source increment reaches $\epsilon_j$, or if

$$
D^\nu_{r_j,t}=K^\nu_t-K^\nu_{r_j}
             -W^1_{r_j}(W^2_t-W^2_{r_j})
\tag{3.5}
$$

reaches absolute value $\epsilon_j$. On interruption set
$v_{j+1}=v_j+(1-v_j)(r_{j+1}-r_j)/h_j$ and issue the next remaining
suffix. Equality with completion means completion. The actual rule also
cuts off at $\tau$ or $T$.

For estimates only, ignore those latter cutoffs on the original Brownian
continuation. Strong Markov and the stopped exponential-martingale
inequality give, at each reached attempt,

$$
\mathbb P(\hbox{retry}\mid\mathcal F_{r_j})
 \le8e^{-\epsilon_j^2/(4h_j)}
   +2e^{-\epsilon_j^2/[4(\epsilon_j^2+\nu^2)h_j]}
 \le10e^{-256}=:q<1/16.
\tag{3.6}
$$

Indeed, before first-level exit the central martingale in (3.5) has
quadratic variation at most $2(\epsilon_j^2+\nu^2)h_j$.
The covariance-$2$ normalization is included in both exponents.
The probability of reaching attempt $j$ is at most $q^j$ conditional
on the original start. Thus retries are almost surely finite and their
expected number, including the last attempt, is at most $16/15$.
Each complete planned attempt has energy at most
$C_1^2/h_j$; its actually executed prefix has no greater energy.
Summing $C_1^2(c\rho^2)^{-1}(4q)^j$ proves the energy bound.
This prices the actual velocities, not an inverse unobserved terminal
remainder. The constant arclength geometry is traversed once in order;
all translated chronological integrals remain $A_0\,dy+\int x\,dy$.

At every prefix of service, including the completion time, Chen's
identity and the geometric sums give

$$
|W^i_t-W^i_s|\le\rho/512\ (i=1,2),\qquad
|D^\nu_{s,t}|\le\sum_j\epsilon_j+
 \sum_{j<j'}\epsilon_j\epsilon_{j'}<\rho/256.
\tag{3.7}
$$

Elapsed service time is at most $4c\rho^2/3<\rho^2$.
The next opposite trigger is at least $g_0$ away at its start, so cannot
overtake this service. For the initial epoch the same distance is at
least $g_0$.
At completion (3.1) gives, with $\Delta W^i=W^i_t-W^i_s$,

$$
e=\rho/4-\Delta W^1,\quad y=-\Delta W^2,\quad
z=-D^\nu_{s,t}+(\Delta W^1+d+e/2)\Delta W^2.
\tag{3.8}
$$

Equations (3.7)–(3.8) imply (3.3) directly.
For every earlier geometric prefix K, (34.3) bounds relative $x,y$ by
$3\rho,\rho$ and relative chronology by $2\rho$.
At the start, $|A_0-W^1_s|,|B_0-W^2_s|\le2\rho$ and
$|J_0-K^\nu_s|\le C\rho$ by (2.1), with bounded stopped $W^1_s$.
Translation by $A_0Y$, and then (3.7), give the claimed full errors
$C_3\rho$ at every prefix, without dropping any cross term.
The original numerical connector and all suffixes are lawful by their
whole-height inward geometry. A cutoff changes neither old velocities
nor past chronology, so the domination includes aborted prefixes.
$\square$

**Lemma 3.3 (number of sign epochs).** Their number $M$, counting
initialization, is finite almost surely and satisfies
$\mathbb EM\le C_I(1+T)$, independently of $\rho,\nu$.

*Proof.* The continuous height must travel between alternating fixed
levels separated by $2g_0$; its first trigger is at least $g_0$ from
its starting height. Uniform continuity proves pathwise finiteness.
At each trigger/start before $S$, consider, solely for a duration
comparison, the fresh Brownian delay to displacement $g_0$, capped by
$g_0^2$. It has expectation $m_I>0$ by scaling, uniformly over the
past, and is no longer than the next trigger delay. The sum of these
delays over starts before $S$ is at most $S+g_0^2$, since only the last
one can extend past $S$. Tonelli and conditioning at the starts give
$m_I\mathbb EM\le\mathbb ES+g_0^2$. This also allows a possibly
uncompleted last epoch. $\square$

## 4. Complete finite execution and its original-time price

**Definition 4.1 (the complete issuer).** Fix $\Gamma\ge1$ sufficiently
large depending only on $I,k,r$, and set $\rho=\eta/\Gamma$ for
$0<\eta\le\eta_0$, with $\eta_0$ small enough for §3 and
$\rho^2\le\eta$. Initialize by Lemma 3.2, then run Lemma 2.3's
numerical sampler until the next sign trigger, repeating the reset
there. Cut off any current command at target death or $T$.
At $\tau<T$, from the actual triple $(A_0,B_0,J_0)$ issue K,
Definition 34.1's connector to exactly
$(W^1_\tau,W^2_\tau,K^\nu_\tau)$, with relative data

$$
X=W^1_\tau-A_0,\quad Y=W^2_\tau-B_0,\quad
D_*=K^\nu_\tau-J_0-A_0Y.
\tag{4.1}
$$

Run this known terminal geometry at constant arclength speed for the
original duration $\delta=\rho^2$, followed by a hold. If $T$ interrupts
it, execute exactly that prefix, at its original velocity. At own death
hold both controls. Ties at $T$ are interpreted by this same prefix
rule. No terminal acceleration is used.

**Theorem 4.2 (uniform attained upper envelope).** The same family
belongs to $\mathcal A(\eta,\nu)$ for every deterministic allowed pair,
uses finitely many piecewise linear numerical issuances almost surely,
and obeys, for a constant independent of $\eta,\nu$,

$$
\begin{aligned}
\mathbb EV^a,\ \mathbb EV^b,\ \mathbb EL
 &\le C(\eta^{-1}+\nu^2\eta^{-2}),\\
\mathbb EE&\le C(\eta^{-2}+\nu^4\eta^{-4}).
\end{aligned}
\tag{4.2}
$$

Every actual prefix satisfies $k+A\in[l,u]\Subset(0,H)$, and

$$
\|A-W^1_{\cdot\wedge S}\|_\infty+
\|B-W^2_{\cdot\wedge S}\|_\infty+
\|J-K^\nu_{\cdot\wedge S}\|_\infty\le C_5\rho.
\tag{4.3}
$$

There is no own death before target death; its exact censored cutoff is

$$
S^{\rm N}=T\wedge(\tau+\rho^2),\qquad
\zeta^{\rm N}=\begin{cases}\tau+\rho^2,&\tau+\rho^2\le T,\\
\infty,&\tau+\rho^2>T.\end{cases}
\tag{4.4}
$$

*Proof.* In a positive feedback epoch $A-W^1=d+e$ lies in
$[5\rho/8,11\rho/8]$ and the target height stays below $m+g_0$.
In a negative one the error lies in
$[-11\rho/8,-5\rho/8]$ and the target stays above $m-g_0$.
The choice of scale in §3 puts the actual height at least $\rho/2$
from both faces. Hence each entire numerical profile in (2.10) is lawful.
It remains interior throughout the epoch. During each reset the same
fact follows instead from the inward geometry, including every suffix.
Lemma 3.2 prevents another sign trigger during reset service. Lemmas
2.3 and 3.3 prove finite total issuances, including epochs cut off at
target death or the horizon. All joins are continuous, so the executed
controls are AC and piecewise linear with their original chronological
integral. Their construction is Borel from stopped observations: dyadic
radius tests, finite numerical geometry, stopping-time evaluations and
first hits of continuous adapted paths are measurable. A countable
recursion defines the same rule at every parameter pair; the exceptional
infinite-count event has probability zero for each such pair.

During feedback, (2.1) gives
$|A-W^1|\le11\rho/8$, $|B-W^2|\le3\rho/8$ and
$J-K^\nu=(W^1+d+e/2)y+z$, hence a complete $C\rho$ bound.
During resets use Lemma 3.2. At $\tau$ these bounds hold by continuity,
including if a reset is interrupted. Consequently (4.1) has
$|X|,|Y|\le C\rho$, $|D_*|\le C\rho$. K, Lemma 34.2 bounds every
terminal prefix and all its translated cross terms by another $C\rho$
relative to the fixed terminal target. Its endpoint is the exact triple;
a horizon interruption retains the same prefix bounds. This proves
(4.3). K, (13.4)'s affine phase estimate, with the original periods,
then gives $D_{\max}\le C\rho\le\eta$ by increasing $\Gamma$.

Before $\tau$ all actual heights are interior. At $\tau$ the actual
height is still interior: a feedback epoch has the inward margin, and
a reset has interior geometry and endpoint. The terminal connector's
loops and phase leg remain interior, and its final, nonzero height leg
first reaches the target face at its endpoint. Constant arclength speed
places that endpoint exactly at $\tau+\rho^2$. This proves (4.4),
also when $T$ cuts that leg off. The held whole-height guard and (1.5)
follow. No observation after $\tau$ is used.

For the resource estimate, sum (2.11) over feedback epochs. Their total
elapsed time is at most $T$, and each entry value is bounded by (3.3).
Thus

$$
\mathbb EE_{\rm fb}
 \le C\mathbb EM(1+\nu^2/\rho^2)+4C_0DT.
\tag{4.5}
$$

This conditional Itô estimate permits later stopping-time cutoffs and
charges every interrupted constant-velocity prefix. Lemma 3.2 prices all
reset service by $C\rho^{-2}\mathbb EM$. The final known connector
has length $O(1)$ and energy $O(\rho^{-2})$ on duration $\rho^2$;
a horizon-cut prefix has no greater energy at that velocity. In
particular an area residual $D_*=O(\rho)$ costs $O(1)$ variation,
not $O(\rho)$. Using $b=\nu^2+2\rho^2$, bounded $\nu$, and Lemma 3.3,

$$
\mathbb EE\le C(\rho^{-2}+\nu^4\rho^{-4}).
\tag{4.6}
$$

Finally $V^a,V^b\le L$ and, on the actual original interval $[0,T]$,
$L^2\le TE$. Cauchy–Schwarz in probability yields
$\mathbb EL\le\sqrt{T\mathbb EE}
 \le C(\rho^{-1}+\nu^2\rho^{-2})$.
This includes all reset and terminal movement without revaluing any
aborted leg. Substitution $\rho=\eta/\Gamma$ proves (4.2).
$\square$

**Theorem 4.3 (same-family allowed own-lifetime convergence).** For
any deterministic sequence $\eta_n\downarrow0$, $|\nu_n|\le\bar\nu$,
(4.4) gives almost-sure convergence of the censored own lifetimes in
K, Theorem 24.1's metric $d_\zeta$, with $\infty$ isolated and
eventually equal death marks. If also $\nu_n\to\nu_*$, the held triples
and native paths converge uniformly on the same source to the target
with coefficient $\nu_*$. The killed paths converge in the isolated
cemetery space in $J_1$. At any fixed tolerance, on $\{\tau<T\}$ the
same-clock uniform isolated-cemetery distance is exactly $2$.

*Proof.* Intersect the countably many almost-sure construction events.
The height exit time is independent of $\nu$ and has no atom at $T$.
When $\tau<T$, eventually $\tau+\rho_n^2<T$; when $\tau>T$, both
marks are infinite. This proves the mark assertion and delay convergence.
Moreover
$\sup_{t\le T}|K^{\nu_n}_{t\wedge S}-K^{\nu_*}_{t\wedge S}|
 \le|\nu_n-\nu_*|\sup_{t\le T}|C_{t\wedge S}|$.
Together with (4.3) this proves the held convergence. The increasing
piecewise linear comparison homeomorphism mapping
$(0,\tau,T)$ to $(0,\tau+\rho_n^2,T)$ has displacement at most
$\rho_n^2$. Before the compared deaths the error is bounded by
$\eta_n$ plus the target modulus of continuity at that displacement;
afterwards both paths equal the cemetery. This proves $J_1$ convergence
as in K, Theorem 39.1. The homeomorphism compares observations only;
it changes no execution time or resource. At time $\tau<T$ one path
has died and the other has not, giving distance $2$ under the isolated
cemetery metric. $\square$

## 5. The uniform two-sided infimum law

**Theorem 5.1 (joint noise/tolerance crossover).** For fixed native data,
$T>0$ and finite $\bar\nu\ge0$, there are $\eta_0>0$ and positive
constants $c_x,C_x$, independent of $\eta,\nu$, such that throughout
$0<\eta\le\eta_0$, $|\nu|\le\bar\nu$,

$$
\begin{aligned}
c_x(\eta^{-1}+\nu^2\eta^{-2})
 &\le\mathsf C_x(\eta,\nu)
 \le C_x(\eta^{-1}+\nu^2\eta^{-2}),\qquad x=a,b,L,\\
c_E(\eta^{-2}+\nu^4\eta^{-4})
 &\le\mathsf C_E(\eta,\nu)
 \le C_E(\eta^{-2}+\nu^4\eta^{-4}).
\end{aligned}
\tag{5.1}
$$

One simultaneous family realizes all four upper bounds and Theorem
4.3's lifetime conclusions. This is an order theorem, not attainment
of each exact infimum or a sharp-constant assertion.

*Proof.* The upper bounds are Theorem 4.2. For the central lower bound
retain the full source residual threshold, including at small noise:

$$
F_{\eta,\nu}=[2\nu^2\mathbb ES-4r^2\eta^2]_+.
\tag{5.2}
$$

K, Theorem 33.2's product-rule proof, with $\lambda=0$, applies also
at $\nu=0$ (where its central conclusion is zero). For every individual
admissible issuer it gives

$$
\mathbb EV^a\ge\frac{F_{\eta,\nu}}{8r\eta^2},\quad
\mathbb EV^b\ge\frac{F_{\eta,\nu}}{4r\eta^2},\quad
\mathbb EL\ge\frac{\sqrt5 F_{\eta,\nu}}{8r\eta^2},\quad
\mathbb EE\ge\frac{5F_{\eta,\nu}^2}{64r^2\eta^4\mathbb ES}.
\tag{5.3}
$$

There is no omission of the positive part and no fixed-$\nu$
asymptotic substituted here.
The common phase-lift argument gives
$|A-W^1_{\cdot\wedge S}|\le\eta$ and
$|B-W^2_{\cdot\wedge S}|\le2\eta$ for $\eta<\pi$.
The target-only scalar event in K, Theorems 12.1 and 13.2 therefore
applies to every sequence of these controls, even when $\nu$ varies:

$$
\begin{aligned}
\liminf_n\eta_n\mathbb EV^a_n&\ge\mathbb ES,&
\liminf_n\eta_n\mathbb EV^b_n&\ge\mathbb ES/2,\\
\liminf_n\eta_n\mathbb EL_n&\ge\sqrt5\mathbb ES/2,&
\liminf_n\eta_n^2\mathbb EE_n&\ge5\pi^2\mathbb ES/24.
\end{aligned}
\tag{5.4}
$$

Only the unchanged first levels and eventually live rational prefixes
are needed for this supplier; (1.5) provides the required lifetime
condition. Fatou transfers its pathwise floors to (5.4).
For $\nu^2\le\eta$, the targets in (5.1) are at most twice their
baseline term, so (5.4) supplies a positive uniform lower fraction.
For $\nu^2>\eta$ and $\eta\le\mathbb ES/(4r^2)$, (5.2) is at least
$\nu^2\mathbb ES$. Then (5.3) supplies a fixed lower fraction of the
central term, which dominates the corresponding baseline term.
If no uniform $\eta_0$ and lower fraction existed, one could choose
$\eta_n\downarrow0$, bounded $\nu_n$, and policies within $1$ of the
relevant finite infima that violate these fractions. The preceding two
regimes contradict that sequence. Separate policies may be chosen for
the separate lower infima; no assertion of a common exact minimizer is
used. This proves (5.1). $\square$

## 6. Same-coupling noise removal and the full Green consumer

**Theorem 6.1 (bounded and capped occupation, with the actual limit order).**
Use the same starting pole and raw density $d\mu=dk\,d\alpha\,d\beta$
as N, §1, so the killed target has operator
$L_{|\nu|}=-(P^2+Q^2+\nu^2r^{-2}\partial_\beta^2)_{F,\Omega}$,
$\Omega=I\times\mathbb T^2$, including the horizontal closure at zero.
Let $F\in C(\overline I\times\mathbb T^2)$ be bounded. Along the actual
family of Theorem 4.2 with $\eta_n\to0$, $\nu_n\to\nu_*$,

$$
\mathbb E\int_0^{S_n^{\rm N}}F(q^{\rm N}_n(t))dt
 \longrightarrow\mathbb E\int_0^{T\wedge\tau}F(q^{\nu_*}(t))dt.
\tag{6.1}
$$

For nonnegative $F$, applying a fixed total cap $B<\infty$ to both
integrals gives the same convergence. For signed $F$ one can use the
bounded Lipschitz clipping map or treat its two parts. In particular
$\nu_*=0$ gives simultaneous operational approximation and noise removal
on the original coupling. Taking first this limit and then $T\to\infty$
in the uncapped bounded-integrand expression gives exactly

$$
\lim_{T\to\infty}\lim_{n\to\infty}
 \mathbb E\int_0^{S_{n,T}^{\rm N}}F(q^{\rm N}_{n,T}(t))dt
 =\int_\Omega\Gamma_{|\nu_*|,o}(q)F(q)\,d\mu(q).
\tag{6.2}
$$

For a nonnegative $F$ and a fixed total cap, the $T\to\infty$ limit
instead equals $\mathbb E\min(B,\int_0^\tau F(q^{\nu_*}_t)dt)$.
To recover the linear Green pairing along this capped route requires
$B\to\infty$ after these two limits. No uncapped singular source-field
occupation or paid-point contract is asserted.

*Proof.* Put $M_F=\|F\|_\infty$ and let $\omega_F$ be its modulus.
On the common live interval the same-source target difference is at
most $|\nu_n-\nu_*|\|C_{\cdot\wedge S}\|_\infty/r$ in native phase
distance. Equations (4.3)–(4.4) give the pathwise integral difference
bound

$$
T\omega_F\left(\eta_n+
 |\nu_n-\nu_*|\|C_{\cdot\wedge S}\|_\infty/r\right)
       +M_F\rho_n^2.
\tag{6.3}
$$

It tends to zero almost surely and is bounded by $2M_FT+M_F\rho_n^2$.
Dominated convergence proves (6.1), and a cap is a 1-Lipschitz function
of the total integral. The original-time overlap and lifetime delay,
not continuity of a cemetery evaluation at the exact death time,
justify this estimate.
N, Theorem 1.3 identifies the full killed Green law and gives
$M_F\mathbb E(\tau-T)_+\le C M_F e^{-\pi^2T/(u-l)^2}$.
This proves (6.2) by the stated iterated limit. Each finite-horizon
approximation has its own prescribed horizon; a uniform infinite-time
native tail is not inferred. Monotone convergence in $T$ proves the
fixed-cap statement for nonnegative $F$, and then monotone convergence
in $B$ recovers the linear pairing. These are bounded occupation tests
of the existing full Green model, not a newly supplied propagator or
an unproved point-source realization. $\square$

## 7. Sharpness, degeneracy and observable falsifiers

**Corollary 7.1 (vanishing noise can still dominate execution).** If
$\bar\nu>0$, the sequence $\nu_\eta=\eta^{1/4}$ is eventually allowed
and tends to zero on the same source, while

$$
\mathsf C_{a,b,L}(\eta,\nu_\eta)\asymp\eta^{-3/2},\qquad
\mathsf C_E(\eta,\nu_\eta)\asymp\eta^{-3}.
\tag{7.1}
$$

At zero they are instead $\asymp\eta^{-1}$ and
$\asymp\eta^{-2}$. More generally the exact order crossover is at
$\nu^2\asymp\eta$: below it the baseline terms dominate; above it the
central terms dominate. Thus uniform convergence of these target laws
to the zero-noise target does not imply zero-noise operational prices.

*Proof.* Substitute the sequences in (5.1). Same-source target
convergence follows from $\nu_\eta C\to0$ uniformly on each stopped
compact horizon. The variation ratio to its zero-noise order diverges
as $\eta^{-1/2}$ and the energy ratio as $\eta^{-1}$. This provides
a joint-parameter falsifier for an endpoint-only uniform price claim.
When $\bar\nu=0$ only the zero-noise assertion remains. $\square$

**Proposition 7.2 (fixed total caps do not give a linear Green pairing).**
For $F=1$ and every finite $B>0$,

$$
\mathbb E\min(B,\tau)<\mathbb E\tau
 =\frac{(k-l)(u-k)}2=\int_\Omega\Gamma_{|\nu|,o}\,d\mu.
\tag{7.2}
$$

*Proof.* Brownian motion started in the interior has positive
probability to stay in the interval up to any finite time. Hence
$\mathbb E(\tau-B)_+>0$ (also use a slightly larger time), whereas
$\mathbb E\tau<\infty$ is N, (1.6). Subtracting this strictly positive
quantity proves (7.2). A time limit alone cannot remove a total cap.
$\square$

**Proposition 7.3 (ranks and physical scope).** State dimension remains
three and native control rank two. The target covariance tensor is

$$
2\left(P\otimes P+Q\otimes Q+
 \nu^2r^{-2}\partial_\beta\otimes\partial_\beta\right)dt;
\tag{7.3}
$$

its rank is three for $\nu\ne0$ and two at zero. These ranks, homogeneous
or spectral dimensions, original-clock resource exponents, and a number
of physical spatial axes are different assertions.

*Proof.* The differentials of (1.2) are $d\kappa=dW^1$,
$d\widetilde\alpha=dW^2/2$,
$d\widetilde\beta=(1/2-\kappa/r)dW^2-\nu dC/r$.
Their independent covariance-$2$ drivers give (7.3); the three-column
determinant is nonzero precisely when $\nu\ne0$. All issued numerical
velocities still multiply only $P,Q$. In particular the polar direction
in the proof is a combination of those two actual controls, not an
extra physical direction. No physical axis identification, physical
energy calibration or bare-FIB stochastic selection follows.
$\square$

## 8. Correspondence, mathematical attribution and remaining boundaries

**Convention 8.1 (what is reused and what is joint).** K, Theorem 26.2
already supplies the zero-noise causal endpoint. K, Theorems 33.2 and
38.1 supply the complete residual floors and fixed-nonzero-noise
attainment. Their constants are not relabelled as uniform: (2.2)–(4.6)
supply a different joint construction and all its actual costs.
K, Definition 34.1 and Lemma 34.2 are used with precisely the data
(3.2) and (4.1), with actual translation by $A_0Y$. K's suffix mechanism
is used only with the new thresholds and explicit estimates
(3.4)–(3.8). K, Theorem 39.1's observation time change is used only
after the actual lifetime identity (4.4) is established. N supplies
the full killed law and tail to which the bounded consumer is applied.
V, Theorem 29.6 has a different fixed coefficient-access interface;
G's Green geometry and S's horizontal smooth-family singular rates
are not converted into native execution bounds here.

**Convention 8.2 (primary mathematical sources).** The following
literature supplies scalar or stochastic tools, with the stated scope;
the annular error construction and its finite native sampling are
repo-derived ordinary deductions, without a priority assertion.

| Primary source | Exact correspondence and limit |
| --- | --- |
| Mörters–Peres, *Brownian Motion*, public draft, [Theorem 2.14, pp. 47–48](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf) | Strong Markov in the right-continuous Brownian filtration. Independent initial enlargement is as in K, Definition 20.1; multiplication by $\sqrt2$ gives the covariance here. It is applied to the full original triple at reached stopping times, not to increments selected by future survival. |
| Łochowski–Miłoś, *On truncated variation, upward truncated variation and downward truncated variation for diffusions*, [arXiv:1109.0043v2](https://arxiv.org/html/1109.0043v2), Theorem 1 and Remark 2 | The continuous-semimartingale limit $c\operatorname{TV}^c(X)\to[X]$ uniformly in time, with truncation twice the uniform approximation radius. K, §12 applies it to the fixed $W^1,W^2$ with quadratic variation $2t$, not to a tolerance-dependent central residual. |
| Lifshits–Setterqvist, *Energy of Taut Strings Accompanying Wiener Process*, [arXiv:1405.1651v1](https://arxiv.org/html/1405.1651v1), Theorems 1.1–1.2, Proposition 2.2 and (2.17) | Free/pinned scalar energy has the same positive small-tube constant; its Cameron–Martin Lipschitz and concentration estimates support K, §12's fixed-time all-radius lower floor. Their §5 scalar Markovian pursuit motivates barrier confinement, but is not a finite numerical native issuer or a chronological/guard/resource theorem. The two-control identities and the frozen-profile argument here are required separately. |
| Lifshits–Podchishchailov, *Asymptotic distribution of the derivative of the taut string accompanying Wiener process*, [arXiv:2411.04690v2](https://arxiv.org/html/2411.04690v2), Theorem 1.1 and §7.2 | Its full-strip-width normalization gives scalar quadratic rate $\pi^2/(6w^2)$; K, §12 takes $w$ twice the radius and scales variance by two. This supplies only the stronger baseline coefficient in (5.4), not the new upper construction. |

The stochastic calculations use Itô's product and square formulas,
strong Markov and reflection for the original Brownian triple, and the
stopped continuous-martingale exponential inequality. Their exact
quadratic variations, signs, normalizations and stopping localizations
are displayed in §§2–3 and K, §§18, 27, 33. No rough-path approximation
theorem or scalar pursuit theorem is used to price a native command.

**Scope 8.3 (unresolved source and acquisition obligations).** The
supplied ideal stopped real history is stronger than O's paid-point
filtration. Its fixed-risk results and impossibility of an almost-sure
paid hard tube remain separate. No price, construction or permission
for acquiring ideal histories is deduced here. Uncapped singular
source-field occupations still require their own uniform-integrability
argument; N, §7's positive-hold example prevents deriving them from a
hard tube alone. A bounded truncation with a continuous extension is
covered as a bounded test, but its truncation cannot be removed from
native expectations without that additional argument. Point sources,
second-order propagation, stochastic law selection and physical
realizability remain declared model/implementation premises and
boundaries. The joint theorem concerns only the class in §1 and its
four original-clock costs; it does not resolve those distinct contracts.

## 追加锚（本行以下为增补区）
