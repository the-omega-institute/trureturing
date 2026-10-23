# Native paid-point observation tracking

This volume continues
[Native guarded lift limits and diffusion selection](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md).
Its sections 42–49 retain the continuous section, theorem and equation
numbering of that argument. Unless another source is named, references
numbered 1–41 refer to the preceding volume; references numbered 42–49
refer to this volume.

The fixed native data, executed costs and complete wrapped metric are in
[§2](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#2-the-original-source-its-guard-and-its-entire-chronological-path),
[§11](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#11-executed-approximation-classes-on-the-original-clock)
and [§13](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#13-accuracy-of-complete-wrapped-native-paths).
The causal and held-death conventions are in
[§20](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#20-causal-knowledge-and-finite-numerical-issuance),
the persistent central-noise target and residual identities in
[§33](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#33-independent-central-noise-and-necessary-executed-resources),
and the connector supplier in
[§34](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#34-small-inward-loops-with-a-larger-chronological-increment).
The added paid sensor, acquired filtration, chance class and almost-sure
hard-tube statement are in
[§41](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md#41-paid-wrapped-current-points-and-the-original-hard-tube).

The named comparison volumes in Scope 49.2 are
[Native finite-menu minimal memory](FIB_NATIVE_FINITE_MENU_MINIMAL_MEMORY.md)
and [Growing-state budget renewal tradeoff](FIB_GROWING_STATE_BUDGET_RENEWAL_TRADEOFF.md).

## 42. A Read converse for the complete predictable-gap class

**Lemma 42.1 (Gaussian tests inside a blind interval).**
Let a covariance-$2$ Brownian motion be compared on $[0,t_0]$ with a
continuous numerical path whose next observation time is fixed from the
previous records. Allow arbitrary additional past information at those
observation times, provided fresh Brownian increments retain their usual
law in the enlarged filtration. If there are at most $n$ observations,
then for every $\epsilon>0$ the probability of the complete scalar tube
of radius $\epsilon$ is at most

$$
\left[\mathbb P\left\{|G|\le
              \epsilon\sqrt{(n+1)/t_0}\right\}\right]^{n+1},
\qquad G\sim N(0,1).
\tag{42.1}
$$

Proof. Set $v=t_0/[2(n+1)]$ and
$g=\mathbb P(|N(0,2v)|\le\epsilon)$. Conditional on all past
information at the beginning of an observation-free interval of known
length $h$, the numerical comparison path throughout it is fixed.
Test only at its internal times $v,2v,\ldots,\lfloor h/v\rfloor v$.
At each such time the required endpoint belongs to an interval of length
$2\epsilon$. A centered normal density assigns the largest probability
to an interval of that length when the interval is centered at zero;
this follows by differentiating its integral with respect to the center.
Independent increments and successive conditioning therefore bound the
conditional tube probability on this gap by
$g^{\lfloor h/v\rfloor}\le g^{h/v-1}$.

For completeness, let $A_i$ be survival of the scalar tube through the
first $i$ blind gaps, and $s_i$ their elapsed total time. The preceding
inequality makes
$\mathbf1_{A_i}g^{-s_i/v+i}$ a nonnegative supermartingale at the gap
ends. Pad a policy with fewer than $n+1$ gaps by zero-length gaps at
$t_0$; the same inequality holds for those gaps. Thus
$\mathbb P(A_{n+1})\le g^{t_0/v-(n+1)}=g^{n+1}$.
Since $\sqrt{2v}=\sqrt{t_0/(n+1)}$, this is (42.1).
The internal tests are solely a converse device. They are not sensor
calls, acquired bridges or permitted controller actions. $\square$

**Theorem 42.2 (fixed-risk expected Read lower order).**
For each fixed $0<\delta<1/4$ there are positive constants $c_1,\eta_1$
depending only on the fixed source data such that

$$
V(\eta,\delta)\ge c_1\eta^{-2}\log(1/\eta),
\qquad 0<\eta<\eta_1.
\tag{42.2}
$$

Proof. Choose $0<t_0<T$ so small that
$\mathbb P(\tau\le t_0)\le1/8$; Brownian continuity at the strictly
interior start permits this choice. A successful native tube with
$\eta<\pi$, on $\{\tau>t_0\}$, implies the complete scalar tube
$\sup_{t\le t_0}|b(t)-W^2_t|\le2\eta$. Its probability is at least
$1-\delta-1/8>5/8$.

If $\mathbb EM=\infty$ there is nothing to prove. Otherwise suppress
all calls after $n=\max(1,\lceil8\mathbb EM\rceil)$, retaining the
numerical continuation and any already determined clock operations.
On $\{M\le n\}$ this changes no execution. Markov's inequality loses
at most $1/8$ in probability. Thus the capped policy has scalar success
probability at least $1/2$ on $[0,t_0]$. Its gaps obey Lemma 42.1 in
the full filtration of $(U,W^1,W^2,C)$. In particular the extra area and
central information in previous point records creates no independence
assumption about past Brownian bridges: the argument uses only fresh
increments after the beginning of each gap. It gives

$$
\frac12\le g_{\eta,n}^{\,n+1},\qquad
 g_{\eta,n}=\mathbb P\{|G|\le2\eta\sqrt{(n+1)/t_0}\}.
\tag{42.3}
$$

Here is an explicit check of the logarithmic implication. For $x\ge0$,
integrating the standard normal density over $[x,x+1]$ and its negative
reflection gives
$\mathbb P(|G|>x)\ge c_2e^{-x^2}$, with
$c_2=2e^{-1}/\sqrt{2\pi}>0$, because
$(x+1)^2/2\le x^2+1$. Write $N=n+1$. If $N<\eta^{-1}$, then
$g_{\eta,n}\le C\sqrt\eta\to0$. If

$$
\eta^{-1}\le N\le(t_0/16)\eta^{-2}\log(1/\eta),
\tag{42.4}
$$

then $x^2=4\eta^2N/t_0\le\tfrac14\log(1/\eta)$ and
$N(1-g_{\eta,n})\ge c_2\eta^{-3/4}\to\infty$.
In both cases $g_{\eta,n}^N\to0$, contradicting (42.3).
Since $n\le8\mathbb EM+1$, (42.2) follows after decreasing $\eta_1$.
This proof applies to arbitrary admissible numerical profiles and
adaptive Read schedules, including policies that stop reading on
failure or own death. It has not priced a different scalar sampler.
$\square$

## 43. Chance-class floors for actual native execution

**Theorem 43.1 (central-noise floors at positive risk).**
Use the $t_0$ above and define, for sufficiently small $\eta>0$,

$$
A_\eta=\left[(2\nu^2-4r|\lambda|\eta)t_0/2
                            -4r^2\eta^2\right]_+.
\tag{43.1}
$$

Every policy in $\mathcal C(\eta,\delta)$, $0<\delta<1/4$, obeys

$$
\begin{aligned}
\mathbb EV^a&\ge A_\eta/(8r\eta^2),&
\mathbb EV^b&\ge A_\eta/(4r\eta^2),\\
\mathbb EL&\ge\sqrt5 A_\eta/(8r\eta^2),&
\mathbb EE&\ge5A_\eta^2/(64r^2\eta^4t_0).
\end{aligned}
\tag{43.2}
$$

No lifetime convergence is assumed. All four resources include every
failed, aborted, interrupted and post-target-death executed prefix.

Proof. Let $\sigma$ be the first time the continuous native held error
exceeds $\eta$, with infinity if it never does, and put
$\theta=t_0\wedge S\wedge\sigma$. This is a stopping time in the
full enlarged Brownian filtration, used only in this converse. At a
finite first violation continuity gives error $\eta$. Until $\theta$
the connected-lift argument therefore gives
$|e|\le\eta$, $|f|\le2\eta$ and the same beta residual bound as in
Theorem 33.2. In particular $|R_1|,|R_2|\le2r\eta$ there, with
exactly the residuals (33.6). On success and $\{S\ge t_0\}$,
$\theta=t_0$, so

$$
\mathbb E\theta\ge t_0(1-\delta-\mathbb P(S<t_0))\ge t_0/2.
\tag{43.3}
$$

Apply the exact differential identities (33.7) and Itô's square formula
only through $\theta$. Their independent central martingale still has
quadratic variation $2\nu^2dt$ there. Bounded residuals and integrands
make the stopped stochastic integrals mean zero. As in (33.8),

$$
\begin{aligned}
2\nu^2\mathbb E\theta
 &\le4r^2\eta^2+4r\eta^2\mathbb E\operatorname{TV}_{[0,\theta]}b
                       +4r|\lambda|\eta\mathbb E\theta,\\
2\nu^2\mathbb E\theta
 &\le4r^2\eta^2+8r\eta^2\mathbb E\operatorname{TV}_{[0,\theta]}a
                       +4r|\lambda|\eta\mathbb E\theta.
\end{aligned}
\tag{43.4}
$$

Localization by accumulated variation justifies these inequalities
without finite expected variation; an infinite relevant expectation
already gives its lower bound. For $2\nu^2-4r|\lambda|\eta\ge0$,
(43.3) proves the two variation floors. Minkowski gives the displayed
length floor for the execution through $\theta$, and Cauchy–Schwarz
on probability times $[0,\theta]$ gives
$(\mathbb EL_{[0,\theta]})^2\le\mathbb E\theta\,
\mathbb EE_{[0,\theta]}\le t_0\mathbb EE$.
This proves (43.2). All stopped costs are bounded above by the actual
total costs, rather than by a success-conditioned cost. Since
$A_\eta\to\nu^2t_0>0$, the necessary powers are $\eta^{-2}$ for
both variations and length and $\eta^{-4}$ for unhalved energy.
$\square$

## 44. Local wrapped decoding and estimates used only for probability

**Definition 44.1 (a local coordinate computed from paid points).**
For two acquired points $q=(h,\alpha,\beta)$ and
$q'=(h',\alpha',\beta')$, let $\operatorname{pv}$ be the fixed principal
representative in $(-\pi,\pi]$ and compute

$$
\begin{aligned}
X(q,q')&=h'-h,\\
Y(q,q')&=2\operatorname{pv}(\alpha'-\alpha),\\
D(q,q')&=r\left\{(\tfrac12-h/r)Y(q,q')
                         -\operatorname{pv}(\beta'-\beta)\right\}.
\end{aligned}
\tag{44.1}
$$

These are computed numbers, not acquired deck labels. The connector
of Definition 34.1, at scale $\rho$, starting at $q$ and using these
numbers, ends exactly at the wrapped point $q'$: its real beta increment
is $(1/2-h/r)Y-D/r=\operatorname{pv}(\beta'-\beta)$, with the original
minus sign of the chronology. Its translated ordinary chronological
increment remains $a_{\rm start}Y+D$.

For analytic comparisons put $\bar A=W^1_{\cdot\wedge S}$,
$\bar B=W^2_{\cdot\wedge S}$ and $\bar K=K_{\cdot\wedge S}$, and

$$
D^*_{s,t}=\bar K_t-\bar K_s-\bar A_s(\bar B_t-\bar B_s).
\tag{44.2}
$$

If $|\bar B_t-\bar B_s|/2<\pi$ and
$|(1/2-\bar h_s/r)(\bar B_t-\bar B_s)-D^*_{s,t}/r|<\pi$,
then (44.1), on these two target points, equals
$(\bar A_t-\bar A_s,\bar B_t-\bar B_s,D^*_{s,t})$.
This is a verified local branch condition, not a global phase lift
supplied by a Read. The exact composition rule is

$$
D^*_{s,t}=D^*_{s,v}+D^*_{v,t}
                    +(\bar A_v-\bar A_s)(\bar B_t-\bar B_v).
\tag{44.3}
$$

It follows by subtracting (44.2), including its stopped holds.

**Lemma 44.2 (one conditional oscillation estimate).**
At an acquired stopping time $s$, and for $0<\epsilon\le1$ and a
positive duration $h$ known at $s$, with
$|\lambda|h\le\epsilon/2$, the conditional probability that, for some
$t\in[s,s+h]$, one of

$$
|\bar A_t-\bar A_s|,\quad |\bar B_t-\bar B_s|,\quad |D^*_{s,t}|
\quad\hbox{reaches or exceeds }\epsilon
\tag{44.4}
$$

is at most

$$
\Psi(\epsilon,h)=8e^{-\epsilon^2/(4h)}
          +2e^{-\epsilon^2/[16(1+\nu^2)h]}.
\tag{44.5}
$$

The same bound holds for the unstopped relative Brownian triple.

Proof. Conditional strong Markov gives fresh covariance-$2$ increments
of the three independent Brownian coordinates. Before either first-level
increment reaches $\epsilon$, the relative central martingale
$\int_s^t(W^1_v-W^1_s)dW^2_v+\nu(C_t-C_s)$ has quadratic variation
at most $2(\epsilon^2+\nu^2)h\le2(1+\nu^2)h$.
Its drift has absolute value at most $\epsilon/2$.
Reflection and the normal exponential tail bound give at most
$8e^{-\epsilon^2/(4h)}$ for the two first-level exits. The stopped
exponential-martingale inequality gives at most the second term for
an absolute central excursion of $\epsilon/2$ before those exits.
For example the latter inequality follows by applying
$\exp(zM-z^2[M]/2)$ at the first level crossing, optimizing $z$, and
summing the two signs. Stopping additionally at $S$ only reduces the
quadratic-variation and drift bounds. If $s\ge S$, all three relative
held coordinates vanish. Conditioning on a known random $h$ gives the
same formula. Supremum information here is used only to bound probability;
no threshold in (44.4) is an actual operation. $\square$

**Definition 44.3 (parameters).** For $0<\eta\le1$ set

$$
\begin{aligned}
A_0&=32(1+r^{-1}),\\
\rho&=\min\{\eta/A_0,1,(u-l)/8,\min(k-l,u-k)/2,\sqrt T\},\\
c&=[2^{30}(1+|\lambda|+\nu^2)]^{-1},\qquad
q=1/64,\qquad m=c/2,\\
N_0&=(T+\rho^2)/(m\rho^2),\qquad
b_0=[2^{24}c(1+\nu^2)]^{-1},\\
\mathcal R_\rho(\Lambda)&=
 \frac{T\Lambda}{c\rho^2}+1+
 N_0\left(1+\frac{\Lambda}{1-q}+\frac{q}{(1-q)^2}\right).
\end{aligned}
\tag{44.6}
$$

Choose any integer $\Lambda\ge1$ satisfying

$$
10e^{-b_0\Lambda}\mathcal R_\rho(\Lambda)\le\delta,
\qquad d_0=c\rho^2/\Lambda.
\tag{44.7}
$$

The least such $\Lambda$ exists, and is
$O(\log(e/(\rho\delta)))$ as $\rho\downarrow0$, uniformly for
$0<\delta<1/4$, with fixed source data. Indeed
$\mathcal R_\rho(\Lambda)\le C\rho^{-2}(\Lambda+1)$, while the exponential in
(44.7) dominates that affine factor. Taking a sufficiently large fixed
multiple of $\log(e/(\rho\delta))$ verifies the inequality directly.
All constants below may depend on the fixed native data, $\lambda,\nu,T$;
they do not depend on $\eta,\delta$.

## 45. One finite-command policy using only paid polling

**Definition 45.1 (waiting, service, terminal execution and abort).**
Use the local computation (44.1) and Lemma 34.2's geometric connector,
with the new scale $\rho$. An abort means an immediate continuous
replacement by a hold, with no further Reads or movement. A terminal
connector, once issued, is followed by its hold and uses no further
Reads. At the horizon retain the actual prefix at its issued velocity;
never compress a connector into the remaining time. At own actual
height exit hold both controls, as required by Definition 20.3.

Initially hold at $q_0$ and store its time $p=0$ and point as an anchor.
A completed normal service will again leave the own wrapped point equal
to its stored target anchor. In waiting mode, schedule the next Read at
the minimum of current time plus $d_0$, the known time $p+\rho^2$,
and $T$. Only strictly positive future delays are used. At $T$ make no
new movement. At any earlier returned point with height $l$ or $u$,
use the terminal rule below. Otherwise compute (44.1) from the stored
anchor to this returned point. Continue waiting if all three absolute
coordinates are below $\rho$ and the clock is below $p+\rho^2$.
At the first failure of that test, at time $s$, abort if any of
$|X|,|Y|,|D|$ exceeds $2\rho$. Otherwise store the point at $s$ as
the next anchor and serve the known connector from the previous anchor
to this point. Its geometry $g=(x,y)$ is fixed at $s$.

The normal service is the following paid-poll suffix procedure. Set
$r_0=s$, $v_0=0$. On attempt $j\ge0$ put

$$
\epsilon_j=(\rho/64)2^{-j},\qquad
h_j=c\rho^2 4^{-j},\qquad m_j=\Lambda+j,
\tag{45.1}
$$

and issue the entire numerical profile

$$
\gamma_j(u)=g\left(v_j+(1-v_j)\min(u/h_j,1)\right)-g(v_j),
\tag{45.2}
$$

including its hold after $h_j$. Store the target point just acquired at
$r_j$. Read at the planned times $r_j+\ell h_j/m_j$,
$\ell=1,\ldots,m_j$, or at $T$ if that comes first. At each Read
use the following priority: horizon, target boundary, overshoot abort,
completion, retry, continuation. The target-boundary priority invokes
the terminal rule. For the other priorities compute (44.1) between the
stored target point at $r_j$ and the new target point. Abort if any
absolute coordinate exceeds $2\epsilon_j$. At the planned completion
$r_j+h_j$ finish the service, even if a threshold is just reached.
Strictly before completion, if any absolute coordinate is at least
$\epsilon_j$, interrupt at this paid Read time $r_{j+1}$ and set

$$
v_{j+1}=v_j+(1-v_j)(r_{j+1}-r_j)/h_j.
\tag{45.3}
$$

Start the next suffix attempt there. Otherwise keep executing the
already issued profile and its next planned poll. Unused polls of an
interrupted attempt are canceled and are not charged as calls.

At normal completion, the current own point equals the target anchor
stored at $s$. Compute (44.1) from this anchor to the just-read target
point. Abort if any absolute coordinate is at least $\rho$.
Otherwise enter waiting mode with anchor time $p=s$. Completion occurs
before $s+\rho^2$, so its next waiting delay is positive.

The terminal rule uses the boundary point actually returned by the
Read, and the known current own point. Compute (44.1) between these
two points. Abort unless $|X|,|Y|\le5\rho$ and $|D|\le15\rho$.
If accepted, issue Lemma 34.2's complete connector from the actual own
height to that acquired boundary point in duration $\rho^2$ of the
original clock, then hold. The boundary Read does not interrupt an
unseen past execution or declare native death. Only the final height
leg of this positive-duration connector can produce own death.

Every choice above is a function of already acquired wrapped points,
known numerical progress, and the clock. In particular the tests are
made only at paid Reads. No continuous threshold detector, bridge or
free notification is part of the policy.

## 46. Finiteness and unconditional actual costs

**Lemma 46.1 (retry and anchor charges).** Each normal service completes
or is cut off by a terminal rule, abort or horizon after finitely many
attempts almost surely. Conditional on its start and its known geometry,
the probability of reaching attempt $j$ is at most $q^j$. The expected
number $N$ of normal accepted starts satisfies $\mathbb EN\le N_0$.

Proof. If the true relative coordinates from an attempt start remain
strictly below $\epsilon_j$, their phase differences lie in the
principal branches in (44.1), and no sampled retry threshold can occur.
A retry is therefore contained in the supremum event of Lemma 44.2.
The branch assertion follows from
$\rho\le[32(1+r^{-1})]^{-1}$ and $|1/2-h/r|\le1/2$ for every
sampled target height $h\in[l,u]$. The drift condition holds since
$h_j/\epsilon_j=64c\rho2^{-j}$. Consequently, at each reached start,

$$
\mathbb P(\hbox{retry}\mid\mathcal F_{r_j})
 \le10\exp\{-1/[65536c(1+\nu^2)]\}<q.
\tag{46.1}
$$

A terminal detection, abort or horizon only reduces this probability.
Successive conditioning proves the reach bound $q^j$ and rules out
infinitely many retries. The total service duration is at most
$\sum_jh_j=4c\rho^2/3<\rho^2$. Reparametrization of successive
suffixes traverses each geometric prefix once, in order.

For the anchor charge, consider the initial anchor time zero and every
accepted normal start $p$; each has target height strictly interior and
$p<S$. In the analytically continued, unstopped Brownian source, let
$\vartheta_p$ be the minimum of $\rho^2$ and the first delay at which
one of the true local first-level increments or the true relative
central increment reaches $\rho/4$. This is solely a duration used in
the estimate. Strong Markov and (44.5), with
$\epsilon=\rho/4$, $h=c\rho^2$, give

$$
\mathbb E(\vartheta_p\mid\mathcal F_p)\ge m\rho^2.
\tag{46.2}
$$

Before this analytic delay the local branches are correct and all three
computed coordinates are below $\rho$. The next accepted normal start
cannot yet occur: its waiting test needs a coordinate at least $\rho$
or elapsed time at least $\rho^2$. Normal service itself introduces no
new anchor. Thus $\vartheta_p$ is at most the spacing to the next
accepted normal anchor, if there is one. For any finite initial list of
anchors the sum of these analytic durations is at most $T+\rho^2$;
only the last duration may extend past the last anchor or past $S$.
Start selection is measurable at that start. Conditioning and Tonelli,
first for finite initial lists and then monotonically, prove that the
expected number of these anchors is at most $N_0$. In particular it is
finite almost surely, and $N$, which excludes the initial anchor, obeys
the stated bound. Neither an end-selected cell law nor a survival-
conditioned fresh law was used. $\square$

**Theorem 46.2 (lawful membership and actual expected charges).**
The policy of Definition 45.1 has almost surely finitely many paid calls
and numerical issuances. Every actual held history is a lawful original
zero-start AC, piecewise $C^1$ history, with

$$
k+\min a\ge l>0,\qquad k+\max a\le u<H,
\qquad J=\int a\,db.
\tag{46.3}
$$

For the same actual policy, unconditionally,

$$
\begin{aligned}
\mathbb EM&\le\mathcal R_\rho(\Lambda),\\
\mathbb EV^a&\le8N_0+37,&
\mathbb EV^b&\le6N_0+35,\\
\mathbb EL&\le14N_0+72,&
\mathbb EE&\le
 \frac{196N_0}{c\rho^2(1-4q)}+\frac{5184}{\rho^2}.
\end{aligned}
\tag{46.4}
$$

These bounds include every abort and every terminal or horizon prefix.

Proof. An accepted normal connector has $(A,B)=(2,2)$ in Lemma 34.2,
so its respective geometric costs are at most $8,6,14$ and its unit-time
energy at most $196$. The terminal connector has $(A,B)=(5,15)$,
so the corresponding bounds are $37,35,72,5184$. Both use inward
rectangles followed by the original phase leg and final height leg.
The complete extrema, not merely the endpoints, stay in $[l,u]$;
normal prefixes are interior. A terminal connector reaches its acquired
boundary only at its endpoint. Suffixes and holds retain these guards.
They prove (46.3), and the very same numerical history on a different
starting-height promise still needs exactly (2.4).

If attempt $j$ were executed to completion at its issued velocity,
its original-clock energy would be

$$
\frac{1-v_j}{h_j}\int_{v_j}^1|g'(v)|^2dv
 \le\frac{196}{c\rho^2}4^j.
\tag{46.5}
$$

An interrupted prefix costs no more. Conditional reach probabilities
$q^j$ therefore give at most
$196/[c\rho^2(1-4q)]$ per started normal service. Its geometric
costs are bounded by the costs of one traversal, since no prefix is
repeated. A terminal connector has duration $\rho^2$ and hence energy
at most $5184/\rho^2$, also for its actual horizon prefix. Tonelli over
measurable normal starts and Lemma 46.1 prove all resource bounds.
The squared speeds are those actually issued: there is no revaluation
of a partial leg and no inverse short horizon remainder.

Waiting Reads are at most $T/d_0+N+1$: the disjoint waiting intervals
have total length at most $T$, and each waiting phase contributes at
most one shortened final interval. Conditional on a normal start, the
expected service Reads are at most

$$
\sum_{j\ge0}q^j(\Lambda+j)=\frac{\Lambda}{1-q}+\frac{q}{(1-q)^2}.
\tag{46.6}
$$

A boundary Read is already one of these waiting or service calls; it
is not charged again. There are no terminal or post-abort Reads.
This proves the first line of (46.4), so the actual paid count is finite
almost surely. Lemma 46.1 similarly makes the actual attempt count
finite. Every connector has finitely many rectangles, each suffix is
a numerical finite piecewise linear profile, and there are finitely
many such issued profiles, with continuous joins. Therefore the actual
history is AC and piecewise $C^1$, with finite pathwise energy.

There is no finiteness assumption hidden in these calculations: the
bounds apply to finite initial lists of anchors and attempts and pass
by monotone convergence. Infinite retry strings and infinitely many
anchors have probability zero by the same bounds. They establish the
claimed nonaccumulation and actual membership.

Finally, principal representatives, ceilings in the connector, finite
concatenation, progress and arclength parametrization are Borel functions
of the acquired numerical data. All planned next positive polling times
are chosen before their unseen intervals. A suffix or terminal
replacement occurs only at a paid Read, and a completion or hold is
already a clock event in the issued profile. This proves the required
acquired-filtration and numerical-profile measurability. No action in
this membership proof uses the analytic durations $\vartheta_p$ or a
Brownian supremum. $\square$

## 47. Missed excursions, local branches and complete held accuracy

**Lemma 47.1 (one event controlling every actual polling gap).**
Let $G_{\rho,\Lambda}$ be the event that, throughout each actual waiting gap,
all three true local coordinates (44.4) from its starting time are at
most $\rho/16$, and, throughout each actual polling gap of attempt $j$,
they are at most $\epsilon_j/16$. Then

$$
\mathbb P(G_{\rho,\Lambda}^c)
 \le10e^{-b_0\Lambda}\mathcal R_\rho(\Lambda)\le\delta.
\tag{47.1}
$$

Proof. A waiting gap has duration at most $d_0=c\rho^2/\Lambda$.
An attempt-$j$ polling gap has duration at most $h_j/(\Lambda+j)$.
Lemma 44.2 with the respective radii gives conditional probabilities
at most $10e^{-b_0\Lambda}$ and $10e^{-b_0(\Lambda+j)}$.
Indeed for the latter gap
$(\epsilon_j/16)^2/[16(1+\nu^2)h_j/(\Lambda+j)]
=b_0(\Lambda+j)$; the first-level exponent is no smaller.
The waiting exponents are larger. The drift conditions hold since
$1024c|\lambda|\rho\le1/2$.

Sum these conditional bounds over actual issued gaps, using their
start-measurable selection. The waiting charge from Theorem 46.2 is
$T\Lambda/(c\rho^2)+N_0+1$. For service use
$N_0\sum_jq^j(\Lambda+j)e^{-b_0(\Lambda+j)}$ and discard the extra factors
$e^{-b_0j}\le1$. This gives precisely (47.1).
The count and reach bounds used here were unconditional and did not
assume $G_{\rho,\Lambda}$. Thus the estimate is not circular, nor does it
condition the original source law on successful tracking. The event
itself is a probability-estimate device, never an acquired observation.
$\square$

**Theorem 47.2 (same-source full held tube).**
On $G_{\rho,\Lambda}$ no abort occurs, and the same actual policy satisfies

$$
\begin{aligned}
D_{\max}(\bar q^{\rm N},\bar q)&\le A_0\rho\le\eta,\\
\|a-\bar A\|_\infty,\ \|b-\bar B\|_\infty&\le6\rho,\\
\|J-\bar K\|_\infty&\le(6K_*+15)\rho,
\qquad K_*=\max(k-l,u-k).
\end{aligned}
\tag{47.2}
$$

In particular this is a whole-held, wrapped three-coordinate chance
tube on the prescribed persistent source, not an endpoint or marginal
approximation.

Proof. First check all local branch and overshoot assertions. During a
waiting gap, if the previous anchor-relative true coordinates were
below $\rho$, (44.3) and the gap bound $\rho/16$ keep both first
levels below $2\rho$ and the relative central coordinate below
$\rho+\rho/16+\rho^2/16<2\rho$. These coordinates force the
principal branches in (44.1), by the choice of $A_0$ and $\eta\le1$.
Thus a waiting trigger, including a boundary detection, has genuinely
bounded local data; an accepted normal service starts with true
$|X|,|Y|,|D|\le2\rho$.

Within attempt $j$, before a continuing poll the coordinates relative
to its start are below $\epsilon_j$. The next gap and (44.3) keep
both first levels below $2\epsilon_j$ and the central coordinate
below $\epsilon_j+\epsilon_j/16+\epsilon_j^2/16<2\epsilon_j$,
at every prefix, not just at the Read. Their phase differences again
lie strictly inside the principal branches. Consequently no overshoot
abort occurs. Each interrupted or completed attempt has true local
first-level and central displacements bounded by $2\epsilon_j$.
For any service prefix, summing them with (44.3) gives

$$
\begin{aligned}
|\Delta\bar A|,|\Delta\bar B|
 &\le\sum_{j\ge0}2\epsilon_j=\rho/16,\\
|D^*_{s,t}|&\le\rho/16+
              \tfrac12(\rho/16)^2<\rho/8.
\end{aligned}
\tag{47.3}
$$

The infinite sums only enlarge the actual finite sums. They also apply
if a boundary or horizon Read cuts the last attempt. At completion,
the relative coordinates from the new anchor at $s$ are therefore below
$\rho$; its completion check never aborts. Its elapsed time is less
than $\rho^2$, so waiting resumes with positive delay. The initial
hold gives the first induction anchor. Thus every completed normal
connector has the exact true lifted endpoint
$(\bar A_s,\bar B_s,\bar K_s)$, not merely its wrapped endpoint:
(44.1)'s local branches have just been verified, and its translated
chronology is $a_{\rm start}Y+D$ with no reset.

For the uniform comparison during a normal service, take its previous
completed target anchor $p$. The own relative triple $(x,y,j)$ obeys
$|x|,|y|\le2\rho$, $|j|\le2\rho$ by Lemma 34.2.
At the service start the target triple relative to $p$ has those same
bounds; (47.3) and (44.3) keep its subsequent relative triple
$(x_*,y_*,j_*)$ within $3\rho$ in each coordinate. Here, for the
central cross term, $2\rho(\rho/16)$ together with $\rho/8$ is
at most $\rho/4$ since $\rho\le1$. Therefore

$$
|x-x_*|,|y-y_*|\le5\rho,\qquad |j-j_*|\le5\rho.
\tag{47.4}
$$

With $h_p=k+\bar A_p$, the exact native phase errors are

$$
\Delta\widetilde\alpha=(y-y_*)/2,
\qquad
\Delta\widetilde\beta=
 (\tfrac12-h_p/r)(y-y_*)-(j-j_*)/r.
\tag{47.5}
$$

Thus their absolute values are at most $5\rho/2$ and
$5\rho/2+5\rho/r$. The chronological error is at most
$(5K_*+5)\rho$. While waiting, the own state is exactly its anchor
and the stronger two-$\rho$ estimates above apply. These statements
include every prefix before an as-yet-unseen target exit and every
prefix between that exit and its boundary Read.

At a boundary Read let the actual and target triples relative to the
same last completed anchor be $(x,y,j)$ and $(x_*,y_*,j_*)$.
If currently waiting use $(x,y,j)=(0,0,0)$; the estimates remain valid.
The true terminal data from the actual own point are

$$
X=x_*-x,\qquad Y=y_*-y,\qquad D=j_*-j-xY.
\tag{47.6}
$$

They obey $|X|,|Y|\le5\rho$ and
$|D|\le5\rho+10\rho^2\le15\rho$.
The current own-to-target phase differences in (47.5) are strictly
less than $\pi$, so the terminal computation (44.1) selects exactly
these true data. It is therefore accepted. The boundary observation
proves that the target is now held, without identifying its earlier
death time.

During any terminal connector prefix $(x_0,y_0,j_0)$, Lemma 34.2 gives
height error at most $|X|+\rho\le6\rho$,
$|y_0-Y|\le|Y|+\rho\le6\rho$, and
$|j_0-D|\le|D|\le15\rho$. Comparing with its fixed terminal target,

$$
|\Delta\widetilde\alpha|\le3\rho,\qquad
|\Delta\widetilde\beta|\le3\rho+15\rho/r,
\qquad |J-\bar K|\le(6K_*+15)\rho.
\tag{47.7}
$$

These estimates persist for a horizon-truncated terminal leg at its
original speed. On completion the errors are zero and both paths hold.
Since $\max(6,3+15/r)\le32(1+r^{-1})$, the Lipschitz projection to
the two original circles proves all of (47.2). This induction also
proves that every possible abort test is avoided on $G_{\rho,\Lambda}$.
No nonzero deck label was presumed at a paid point. $\square$

## 48. Joint fixed-risk optimum and coupled own-death behavior

**Theorem 48.1 (one joint attained order statement).**
For each fixed $0<\delta<1/4$, as $\eta\downarrow0$,

$$
V(\eta,\delta)=\Theta(\eta^{-2}\log(1/\eta)).
\tag{48.1}
$$

A single family in precisely $\mathcal C(\eta,\delta)$, on the same
persistent source and original clock, jointly attains

$$
\begin{aligned}
\mathbb EM&=O\!\left(\eta^{-2}\log\frac{e}{\eta\delta}\right),\\
\mathbb EV^a,\ \mathbb EV^b,\ \mathbb EL&=O(\eta^{-2}),\\
\mathbb EE&=O(\eta^{-4}).
\end{aligned}
\tag{48.2}
$$

The constants in the resource upper bounds are independent of
$\delta\in(0,1/4)$. Each resource infimum over this same chance class
has the respective matching power, $\Theta(\eta^{-2})$ for the two
variations and length, and $\Theta(\eta^{-4})$ for unhalved energy.
These are joint order assertions, not sharp leading constants or an
assertion that an infimum is attained exactly.

Proof. Choose $\Lambda$ as in (44.7) and use Definition 45.1, without changing
the source as either parameter changes. Theorems 46.2 and 47.2 give its
actual membership, probability and unconditional joint costs. For small
$\eta$, $\rho=\eta/A_0$, so (44.6)–(44.7) yield (48.2).
Theorem 42.2 supplies the Read lower bound; Theorem 43.1 supplies each
resource lower bound in the actual chance class. A separate scalar
optimum or an ideal-history controller was not combined with an
unrelated actuator. The logarithm prices the polling precision; retry
service durations remain $h_j=c\rho^2 4^{-j}$ and do not shrink by
that logarithm. Their geometric reach probabilities pay for accelerated
suffix energy. This is why all coordinates in (48.2) belong to the same
implementation. Theorem 41.2 still rules out the original almost-sure
hard tube. $\square$

**Theorem 48.2 (coupled censoring and decreasing-risk limits).**
Write $e_\rho=\rho^2+d_0\le2\rho^2$ and let $d$ be the first actual
paid boundary Read, when it occurs. On $G_{\rho,\Lambda}$, if $\tau\le T$,

$$
\tau\le d\le\min(T,\tau+d_0),\qquad
\zeta^{\rm N}=
 \begin{cases}d+\rho^2,&d+\rho^2\le T,\\
 \infty,&d+\rho^2>T,
 \end{cases}
\qquad 0\le S^{\rm N}-S\le e_\rho.
\tag{48.3}
$$

If $\tau>T$, both marks are infinite on this event. Every retained own
death, also on unsuccessful paths, is later than target death and at
its same exit face. There is no premature own death. For
$e_\rho\le T/2$, with $C_T$ of (31.1),

$$
\begin{aligned}
\mathbb P(\mathbf1_{\{\zeta^{\rm N}<\infty\}}
       \ne\mathbf1_{\{\zeta<\infty\}})&\le\delta+C_Te_\rho,\\
\mathbb E d_\zeta(\zeta^{\rm N},\zeta)
 &\le\delta+(1+C_T)e_\rho,\\
\mathbb E(S^{\rm N}-S)&\le e_\rho+T\delta.
\end{aligned}
\tag{48.4}
$$

Consequently, if $\eta_n\to0$ and $\delta_n\to0$, the same-source
held triples and native paths converge uniformly in probability,
the censored lifetimes converge in probability, and the killed paths
converge in probability in $J_1$. If additionally
$\sum_n\delta_n<\infty$, these convergences hold almost surely,
with eventually equal death marks. A fixed positive risk guarantee
alone does not imply these decreasing-risk conclusions.
For each member of this family, on $\{\tau\le T\}$ the same-clock
uniform isolated-cemetery distance is exactly $2$.

Proof. Every waiting or service polling gap is at most $d_0$.
On $G_{\rho,\Lambda}$ there is no abort, and a boundary return has priority
over all service decisions before the horizon. The Read at $T$ needs
no subsequent movement. This proves the bound on $d$. All normal
connectors have interior height endpoints and interior prefixes.
The accepted terminal connector starts at an interior own height,
ends at the acquired boundary, and has a nonzero last height leg;
constant arclength parametrization reaches that boundary exactly after
its prescribed positive duration $\rho^2$. This proves (48.3).
On any path where an abort occurs the own height instead holds in the
interior. On any other path an own exit still requires an actual paid
boundary return and the same final height leg. Thus the no-premature-
death and exit-face statements hold without conditioning on success.

On $G_{\rho,\Lambda}$ a mark mismatch can occur only if
$T-e_\rho<\tau\le T$. The one-sided passage densities (31.3) for
distances $k-l,u-k$ bound its probability by $C_Te_\rho$.
Off $G_{\rho,\Lambda}$ use probability at most $\delta$, lifetime metric
at most one, and cutoff delay at most $T$. On equal finite marks the
time error is at most $e_\rho$. These facts prove (48.4).

For convergence, (47.2), (47.1) and (48.4) prove the stated probability
limits. On $G_{\rho,\Lambda}\cap\{\tau<T-e_\rho\}$ both death times
are strictly below $T$, and the piecewise linear comparison
homeomorphism matching them has displacement at most $e_\rho$ and
live-state error at most $\eta+\omega_{\bar q}(e_\rho)$, as in (31.5).
When $\tau>T$, the identity comparison suffices on $G_{\rho,\Lambda}$.
The remaining window $T-e_\rho\le\tau\le T$ has probability tending
to zero by (31.3). In particular an own death exactly at $T$ can be
excluded with this window; equality of the two finite marks alone is
not used to construct a homeomorphism sending an interior time to $T$.
The continuous held target has modulus tending to zero, proving the
$J_1$ limit in probability. For almost-sure convergence, $\tau\ne T$
almost surely, so the required strict endpoint inequalities eventually
hold on every path with $\tau<T$. If the risks are summable,
Borel–Cantelli makes $G_{\rho_n,\Lambda_n}$ hold
eventually almost surely; the same argument then gives the almost-sure
limits and eventual equality of marks. No independence across stages
is required or claimed. Retiming compares observations only; every
resource still uses its original execution time.

Finally own death in this family is strictly later than $\tau$ whenever
it occurs. At time $\tau\le T$ the target is at the isolated cemetery
and the own state is still alive. Their distance is $2$, proving the
last assertion even on aborted paths. Neither a positive-risk held tube
nor $J_1$ convergence changes this uniform-cemetery boundary. $\square$

## 49. Exact suppliers, bounded overlap and remaining scope

**Definition 49.1 (supplier correspondence).** The native input is the
published source of §§2, 11, 13, 20 and 33–40 at revision
512365bd25688eefaf2aede357a545c40ae5f375; its bytes agree with the same
owner source at 6c88a1ec4802a0d008b2f1106db7638eb0a561df.
Convention 1.1's N, O and G retain their original source meanings.
The exact reusable geometric supplier is Lemma 34.2: inward rectangles,
ordinary chronology, prefix bounds, constant arclength speed and full
height legality. Its $(A,B)=(2,2)$ and $(5,15)$ instances give exactly
the numbers in (46.4). This is reuse of that connector, not a new
primitive central operation. The suffix parametrization is the finite
numerical mechanism of §§27 and 36. Its former continuous interruptions
are replaced here by paid polling, with (46.1), (47.1) and (47.3)
proving the changed operation contract.

The classical strong Markov and reflection suppliers are
Mörters–Peres, *Brownian Motion*, the public draft referenced in
Definition 20.1, Theorems 2.14 and 2.18. Independent initial enlargement
and multiplication by $\sqrt2$ preserve their required hypotheses and
give this covariance-$2$ law. The bounded stopped stochastic product
rule and Itô square formula enter through the exact identities
(33.6)–(33.8); §43 verifies their chance-stopping application.
The Gaussian density and exponential-martingale estimates needed here
are displayed in §§42 and 44. No Brownian bridge independence, offline
interpolation theorem or general rough differential equation supplier
is required for the upper construction.

Pinned mathlib at db584cd6d46c92f209a44c0f1c829460d327499d, v4.33.0,
provides Brownian finite-dimensional laws and increment facts in
Probability/BrownianMotion/Basic and GaussianProjectiveFamily, and
stopped-process infrastructure in Probability/Process/Stopping.
Those are intermediate formal-library scopes, not a supplied paid-point
native tracking endpoint. No exact compiled Lean application or
Lean-kernel verification of §§41–48 is asserted. The ordinary proof
here supplies the additional acquisition-to-command correspondence.

**Scope 49.2 (bounded comparison and unresolved endpoints).**
The relevant operation distinctions are as follows.

| Supplier or comparison | Applicable scope and transfer boundary |
| --- | --- |
| Lemma 34.2 and §§35–39 | Exact native geometry and ideal-history benchmark; their continuously monitored knots, retry thresholds and immediate target-death knowledge are stronger inputs. §§45–47 replace those inputs and prove the new filtration, missed-excursion and cost estimates. |
| Native finite-menu minimal memory, Definition 2.1, and growing-state renewal tradeoff, Definition 3.1 | Literal tree replies and consecutive renewal-bit Reads have different sources, clocks and charges. Neither is an implementation or price for the exact current-point sensor (41.1). |
| Hatzesberger, arXiv:1901.06148v2 | Full-path $L_q$ approximation with nonchronological information does not itself provide this predictable-gap, whole-held chance tube and joint native execution. No such transfer is used. |
| Free-knot comparisons, arXiv:math/0612313v1 and arXiv:1306.4457v1 | Whole-path or exit information is a different observation contract. A knot chosen from an unseen crossing is not a lawful Read time here. |
| Guo–Kostina, arXiv:2002.01581v4 | A continuously observing encoder and mean-square distortion do not price this held supremum-risk point interface. |
| Grushkovskaya–Zuyev, arXiv:1904.07052v1 | A $C^1$ reference with bounded derivative does not supply the present Brownian-reference hypothesis. |

These comparisons delimit the inspected contracts; they are not an
exhaustive absence or priority claim. No claim of personal full-text
verification of the access-limited original Mueller-Gronbach article
is made or needed. Repository and pinned-library overlap does not
supply the whole joint endpoint by a scalar-only specialization.
The native addition here is the paid, locally decoded, sampled suffix
execution with one joint probability and unconditional resource proof,
together with the common-class Read converse and chance resource floors.
It is ordinary, repository-derived mathematical exposition under the
explicit analytic sensor and stochastic-law premises.

Sharp leading constants, the optimal full dependence of $V$ on a risk
$\delta$ varying with $\eta$, a uniform crossover as $\nu\to0$, and
finite-bit or physically implemented sensing remain separate unresolved
questions. The supplied bounds for varying risk are exactly (48.2) and
(48.4); no sharp decreasing-risk Read formula is inferred from the
fixed-risk equivalence (48.1). The original almost-sure task is
impossible in (41.1), rather than proved by its positive-risk alternative.
The result selects neither physical spatial axes nor a preferred drift,
and calibrates no physical energy. It asserts no worldwide novelty,
independent priors or model diversity.

## 追加锚（本行以下为增补区）
