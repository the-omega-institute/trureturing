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

## 50. Native conditional histories from a finite paid skeleton

**Definition 50.1 (fixed source and the zero-noise sensor).** In
§§50–54 write K for
[Native guarded lift limits](FIB_NATIVE_GUARDED_LIFT_LIMITS_AND_DIFFUSION_SELECTION.md),
U for [Uniform joint noise and tolerance crossover](FIB_NATIVE_UNIFORM_JOINT_NOISE_TOLERANCE_RESOURCE_CROSSOVER.md),
and N for [Central-noise Green stability](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md).
Their consumed statements are those at
`cbb0911e578639a7f6869b5c1daee5cc988067e0`, including U, Theorem 4.2's
barrier controller. Keep the fixed native data of K, §2, $T>0$,
$\lambda=0$, arbitrary fixed preparation phases, and a known signed
$\nu\in[-\bar\nu,\bar\nu]$, where $\bar\nu<\infty$ may be zero.
On the same persistent independent covariance-$2$ triple set

$$
\begin{aligned}
A^0_t&=W^1_{t\wedge S},\qquad B^0_t=W^2_{t\wedge S},\\
K^\nu_t&=\int_0^tW^1_s\,dW^2_s+\nu C_t,\qquad
 S=T\wedge\tau,\qquad
 \tau=\inf\{t:k+W^1_t\notin(l,u)\},\\
X^\nu_t&=\left(k+A^0_t,
 [\alpha_0+B^0_t/2],
 [\beta_0+c_0B^0_t-K^\nu_{t\wedge S}/r]\right),
 \qquad c_0=\tfrac12-k/r.
\end{aligned}
\tag{50.1}
$$

The immutable INITIAL preparation, any preceding preparation history,
the probabilities $(k,H-k,Z,H-k,k)$, negative amplitude convention,
original clock, both $2\pi$ periods, two controls $P,Q$, ordinary
chronology and whole-command source domains are unchanged.
Extend K, Definition 41.1 to $\nu=0$ by using exactly the same
$\operatorname{Read}(t)=X^0_t$ interface and independent seed. At zero
this does not reveal $C$; that unused member of the persistent triple
remains unobserved. For every $\nu$, the acquired information is still
only the paid wrapped current points, the initial seed, known law,
clock and known own execution. In particular neither a continuous
actual history nor actual windings, $C$, bridges or the exact $\tau$
are supplied.

Denote this chance class by $\mathcal C_\nu(\eta,\delta)$ and its
expected Read infimum by $V_\nu(\eta,\delta)$. Denote the separate
infima of $V^a,V^b,L,E$ over exactly this class by
$\mathsf C^p_x(\eta,\nu,\delta)$, $x=a,b,L,E$. All charges include
all actually executed prefixes on unsuccessful outcomes. No lifetime
restriction is added to these infimum classes. The family constructed
below has additional lifetime properties. Constants are uniform in
$\eta,\nu,\delta$ at fixed native data, $T$ and $\bar\nu$; a
fixed-risk Read equivalence may have constants depending on that risk.
Almost-sure assertions are for each deterministic parameter choice,
and on one event for any prescribed countable sequence of such choices.
No uncountable intersection of probability-one events is asserted.

**Definition 50.2 (internal histories and numerical replay).** Let
$E_0=[l,u]\times\mathbb T^2$, with K, (13.1)'s metric. Choose a
finite deterministic equal grid
$t_i=ih$, $0\le i\le n$, $h=T/n$. Write $X_i=X^\nu_{t_i}$.
Use the permitted independent seed in its uniform-real realization,
with a fixed Borel splitting into independent uniform coordinates
$U_1,U_2,\ldots$. Equivalently the one initial seed has product-uniform
law; this uses the existing permission for independent initial
randomization, with no new source access or finite-bit assertion. A generated
history $\widetilde X$ is an internal random element, not an
observation of an actual missing segment. Its required skeleton is
$\widetilde X_{t_i}=X_i$. Only its prefix through $t_i$ may be used
when the $i$th paid record has arrived.

**Theorem 50.3 (causal generation with the native marginal law).**
For every such grid and fixed $\nu$, one can generate
$\widetilde X\in C([0,T];E_0)$ sequentially from these records and
seed, so that, almost surely,

$$
\widetilde X_{t_i}=X^\nu_{t_i}\quad(0\le i\le n),\qquad
\mathcal L(\widetilde X)=\mathcal L(X^\nu).
\tag{50.2}
$$

The generated prefix through $t_i$ is measurable with respect to
$\sigma(X_1,\ldots,X_i,U_1,\ldots,U_i)$. Each generated path is
held at its first boundary hit. If the actual target exits on this
horizon, its generated exit $\widetilde\tau$ is in the very same
first boundary grid cell, at the same face. If there is no actual exit
on the horizon, neither generated nor actual path has a boundary hit
there. The equality of laws is a marginal equality; it does not
identify the generated history with the actual history between Reads.

Proof. All path laws in this proof concern the original model (50.1).
The held process is Markov on $E_0$, with absorbing boundary states.
Indeed, at an interior starting state $x=(a,\alpha,\beta)$ its
future is obtained from fresh covariance-$2$ increments $V^1,V^2,C'$:

$$
\left(a+V^1_v,
 [\alpha+V^2_v/2],
 [\beta+(\tfrac12-a/r)V^2_v
       -r^{-1}(\int_0^vV^1_w\,dV^2_w+\nu C'_v)]\right),
\tag{50.3}
$$

stopped and held at height exit. This follows by subtracting the
original integral and retaining its $W^1_s\Delta W^2$ cross term.
It proves both the Markov property and the exact parameter/operation
correspondence. The quotient phases cause no loss of the future law:
changing a starting lift by a period changes no wrapped future state.
At a boundary state the future path is constant.

For each $i$ let $\mu_i$ be the *unconditional* law on
$\mathcal P=C([0,1];E_0)$ of
$v\mapsto X^\nu_{t_{i-1}+hv}$. This is a standard Borel path
space. Disintegrate $\mu_i$ under the continuous map
$\gamma\mapsto(\gamma(0),\gamma(1))$, obtaining a probability
kernel $B_i(x,y;d\gamma)$. For the actual endpoint-pair law it is
concentrated on paths from $x$ to $y$, with the native absorption rule.
Use an outsourced seed coordinate to choose

$$
\gamma_i=F_i(X_{i-1},X_i,U_i),\qquad
\widetilde X_{t_{i-1}+hv}=\gamma_i(v).
\tag{50.4}
$$

The classical facts used here are Tim Austin, *On exchangeable random
variables and the statistics of large graphs and hypergraphs*,
[arXiv:0801.1698v3](https://arxiv.org/pdf/0801.1698v3), Theorem 2.4,
pp. 85–86, and Lemma 4.2, p. 127. The former disintegrates a probability
on a standard Borel space over a measurable factor into an almost
surely unique probability kernel. The latter realizes a probability
kernel between standard Borel spaces as a Borel function of its input
and one independent uniform $[0,1]$ variable, relative to the given
input law. Here the factor is the *pair of wrapped endpoints*, the
probability is $\mu_i$, and the output is the normalized native cell
path. Atoms from boundary absorption and the degenerate $\nu=0$ law
are allowed. No positive density, ellipticity or independent Brownian
bridge assertion is among the hypotheses.

Here is the native consistency argument, which is not supplied just by
the existence of those kernels. Write $\pi_{i-1}$ for the law of
$X_{i-1}$, $P_h(x,dy)$ for the native endpoint transition, and
$Q_h(x,d\gamma)$ for the entire normalized cell law (50.3).
Disintegration, first also with respect to the starting endpoint, gives

$$
Q_h(x,d\gamma)
  =\int P_h(x,dy)B_i(x,y;d\gamma)
   \quad\text{for }\pi_{i-1}\text{-almost every }x.
\tag{50.5}
$$

For example, test against a countable determining class of bounded
Borel functions of $\gamma$, multiply by an arbitrary bounded function
of $x$, and use the defining disintegration identity. Uniqueness of
conditional expectations proves (50.5) on one null-set complement
for that countable class, hence for the measures.

Condition on the actual source past through $t_{i-1}$ and the
*already used* seed coordinates. The conditional law of $X_i$ is
$P_h(X_{i-1},dy)$, by (50.3), while $U_i$ is independent. The
previous generated prefix is measurable in this conditioning
information. Integrating (50.4) and then applying (50.5) therefore
gives $Q_h(\widetilde X_{t_{i-1}},d\gamma)$ for its next cell.
Induction proves that all generated cells together have the native
path law. This proof conditions on used seed coordinates, not on the
whole seed, and does not assert independence of a generated cell from
its conditioning endpoints. The endpoint support of $B_i$ gives the
shared skeleton and continuous joins. A finite union of the cellwise
exceptional sets is null. Correct absorption then puts both first
exits in $(t_{j-1},t_j]$ when $j$ is the first boundary record, with
the same boundary height. It also covers an exit in the last cell.

One can fix these selections as a single rule over the parameters,
without asserting an uncountable common null set. For completeness,
encode $\mathcal P$ by a fixed Borel isomorphism into a Borel subset
$D$ of $[0,1]$, and choose nested finite endpoint partitions generating
the Borel sigma algebra of $E_0^2$. For a parameterized law $\mu_i$,
the conditional encoded measures on each partition atom are ratios
of its restrictions, with a fixed default at zero denominators.
Take their weak limit when it exists and gives mass one to $D$;
otherwise use a fixed default. The weak-limit map is Borel. For each
fixed law, the limit agrees almost everywhere with Austin's conditional
law: martingale convergence applied to a countable dense set in
$C([0,1])$ identifies the weak limit with that law. Its inverse image
in $\mathcal P$ is the required kernel. A quantile on $[0,1]$, followed
by the inverse encoding with a default outside $D$, is a Borel seed
realization. The laws $\mu_i$ depend Borel measurably on the parameters:
use the original Wiener law, its measurable continuous integral version,
the Borel height hitting time, and cell restriction in (50.1).
Thus the same countable prescription gives parameterized versions.
All almost-everywhere identities used in (50.5) remain statements for
each fixed law, which is all the induction needs. $\square$

## 51. One-grid delay without a resource penalty

**Definition 51.1 (the ideal numerical functional being consumed).**
Apply U, Definition 4.1 and Theorem 4.2 at tolerance
$\vartheta=\eta/4$ to the internally generated history. Use U's
fixed constant $\Gamma$ and put

$$
\rho_U=\vartheta/\Gamma,\qquad d_\eta=\rho_U^2.
\tag{51.1}
$$

Denote its zero-start executed controls and chronology by
$(A^*,B^*,J^*)$, its held state by $Y^*$, and its generated-target
exit by $\widetilde\tau$. Only the *existing* U controller and its
proof are used; no new barrier or actuator is postulated.
Its displayed construction uses only the stopped real triple
$(W^1,W^2,K^\nu)$, known parameters and own numerical progress.
A continuous wrapped generated path supplies that triple by continuous
lifting from the fixed initial representatives:

$$
\begin{aligned}
\widetilde A^0&=\widetilde X^{\rm height}-k,\\
\widetilde B^0&=2(\widetilde\alpha-\alpha_0),\\
\widetilde K^\nu&=r\{c_0\widetilde B^0
                         -(\widetilde\beta-\beta_0)\}.
\end{aligned}
\tag{51.2}
$$

Continuous lifting is Borel and uses only the generated prefix. One
can choose the first dyadic partition on which each entire circle
subpath stays within distance $\pi/4$ of its starting value, using
suprema over a countable dense set of times. On each such subpath
use the principal increment continuously from its start, carrying
the preceding endpoint lift to the next subpath. Uniform continuity
ensures a sufficient partition on every compact prefix. Testing only
successive endpoints would not suffice for this construction. Its
output has the stopped triple's native law by
(50.2). At zero noise no $C$ is reconstructed or supplied to the
controller. U's unused extra visibility of $C$ is consequently not
consumed. At nonzero noise there is likewise no use of actual $C$.
The real lifts in (51.2) are generated internal values, not deck labels
returned by the sensor.

For each generated regular history U supplies a nonanticipating Borel
numerical functional, finitely piecewise linear through $T$, with

$$
\begin{aligned}
D_{\max}(Y^*,\widetilde X)&\le\vartheta,\\
\mathbb E V^a_*,\ \mathbb E V^b_*,\ \mathbb E L_*
 &\le C(\eta^{-1}+\nu^2\eta^{-2}),\\
\mathbb E E_*&\le C(\eta^{-2}+\nu^4\eta^{-4}).
\end{aligned}
\tag{51.3}
$$

Before its terminal endpoint its height is strictly interior; its
first own exit is at $\widetilde\tau+d_\eta$ when that time is at
most $T$, at the generated target face, and otherwise it has no own
exit on the horizon. All its controls hold after own death. These are
precisely U, (4.3)–(4.4), with the tolerance substitution above.

**Definition 51.2 (paid replay and its safe extension).** Read at all
$t_1,\ldots,t_n=T$, even if own movement has already stopped. Initially
issue the zero hold. At $t_i<T$, generate the next missing cell by
(50.4), compute the ideal executed controls through $t_i$, and propose
on the next original-time interval the numerical increment profile

$$
\gamma_i(v)=
 \left(A^*_{t_{i-1}+\min(v,h)}-A^*_{t_{i-1}},
       B^*_{t_{i-1}+\min(v,h)}-B^*_{t_{i-1}}\right),
 \qquad 0\le v\le T.
\tag{51.4}
$$

It includes its prescribed hold after $h$. This is a *computed whole
profile* at $t_i$; the inner ideal feedback is evaluated on an already
generated past cell. It is not an instruction to monitor future target
values. At $T$ issue no movement. Each replacement occurs at its
previously fixed paid grid time. Own boundary hold is the numerical
own cutoff of K, Definition 20.3.

Define the rule also on exceptional inputs. Check each generated cell
for its endpoint joins, membership in $E_0$ and boundary absorption.
Use fixed defaults for kernel arguments outside their declared spaces;
a returned point outside $E_0$, or contradicting a previously acquired
absorbing boundary record, causes an irrevocable own hold.
If it fails, or the ideal prefix functional is undefined, enter an
irrevocable own hold. Otherwise accept a proposal only when it is a
finite piecewise affine continuous profile with zero start, consistent
with the already accepted ideal prefix, and its translated whole height
lies in $[l,u]$. If it has a boundary hit, require a previously arrived
boundary Read at that same face, and require that the whole proposed
pair holds after its first hit. Otherwise require interior height
throughout its nonconstant part and hold. A rejection replaces only
the unexecuted suffix by the zero hold. After own death keep the own
hold. Continue the deterministic Reads and internal generation to $T$
for (50.2), without further movement after a rejection.

These are Borel checks. Finite piecewise affine paths form a Borel
subset of continuous-path space: fix a segment count, bound vertex
values and require positive knot spacings bounded below; each such
parameter set is compact, its path image is compact, and a countable
union covers all finite piecewise affine paths. Height extrema,
closed-set first hits, endpoint equality and absorption are Borel;
all chronological integrals of accepted profiles are their finite
ordinary integrals. Partial recursive evaluation of U is assigned an
undefined symbol on its nontermination or explosion set, also a Borel
set by its countable construction. These selections and checks are
analytic Borel operations, not claims of decidability in finite
arithmetic or of bounded internal computation time.

**Theorem 51.3 (finite lawful replay and unconditional execution).**
The rule of Definition 51.2 uses exactly $n$ paid Reads and at most
$n+1$ own numerical issuances, counting an automatic terminal hold if
represented separately. On every input the accepted execution is
continuous, AC, finitely piecewise affine, has the original chronology
$J^{\rm N}=\int A^{\rm N}\,dB^{\rm N}$, and is lawful on its entire
source domain. It has no own exit before an acquired target boundary
certificate, and any own exit is at the certified face. Under the
actual source law, almost surely all nontrivial proposals pass and

$$
(A^{\rm N}_t,B^{\rm N}_t,J^{\rm N}_t)
 =(A^*_{(t-h)_+},B^*_{(t-h)_+},J^*_{(t-h)_+}),
 \qquad 0\le t\le T.
\tag{51.5}
$$

The same family obeys all four unconditional bounds in (51.3), with
its actual own costs on the left. These bounds include all actual
prefixes on failed tracking outcomes and contain no factor depending
on $n$ or $\delta$.

Proof. Each accepted profile, including its hold, has complete height
in $[l,u]\Subset(0,H)$. Its exact relative source domain is
$(-\min a,H-\max a)$ at its own starting height; in global zero-start
coordinates $k+\min A^{\rm N}\ge l>0$ and
$k+\max A^{\rm N}\le u<H$. The compact-promise criterion remains
exactly K, (2.4); a new starting promise is not inferred from replay.
Holds preserve the guard, rejected proposals execute no movement, and
a finite concatenation of the validated profiles is AC with continuous
joins. Source legality is thus pathwise, also on exceptional inputs.
A permitted own boundary hit requires a paid boundary certificate
already in hand. For the actual held target that certificate entails
$\tau\le t_i$ at its issuing grid time, and identifies its face.
This gives no premature death and same-face death even if later
accuracy fails or the internal generation is rejected.

For a fixed parameter choice, intersect the finitely many sampling
support events of Theorem 50.3 and U's regular event for its native-law
generated path. This is an event of probability one, not the tracking
success event. On it the proposed finite profiles have U's full guards
and continuous joins. If an ideal own death is in the replayed cell
$(t_{i-1},t_i]$, its generated target has already exited by $t_i$.
The shared skeleton therefore includes an actual boundary certificate
at or before $t_i$, at the same face. The extra safety test passes.
An ideal own death at a cell endpoint also satisfies this statement.
Induction over grid cells proves that no proposal is rejected and
that the two actual controls equal the delayed ideal controls.
Changing variables in their ordinary chronological integral proves
(51.5); every translated cross term is retained. There is no reset of
$J$, INITIAL or the clock.

In particular, for $x=a,b,L,E$, actual executed charges are exactly

$$
C_x^{\rm N}=C_{x,*}[0,T-h]\le C_{x,*}[0,T]
\quad\text{almost surely}.
\tag{51.6}
$$

This identity uses original numerical velocities, translated in time
without speeding up any leg. It prices an interrupted final leg at its
actual velocity, rather than compressing it into the remaining time.
U's whole unconditioned expectation bounds apply because the generated
path has its original marginal law and the ideal functional uses only
that path. No stopped bridge is treated as fresh Brownian motion
conditional on its endpoints or on the actual filtration. Taking
expectations in (51.6) proves every claimed resource bound. The null
fallback set contributes zero to these expectations and already has a
lawful finite execution by construction. There is one initial hold,
at most $n-1$ grid proposals, and at most one additional own terminal
hold, giving the stated issuance bound. Finiteness does not rely on a
tracking event or on an unpriced sequence of actual internal
interruptions. $\square$

## 52. Deterministic optimal-order Reads and uniform actuator orders

**Definition 52.1 (one grid for the complete joint task).** Set

$$
C_r=1+r^{-1},\qquad
\epsilon=\eta/(8C_r),\qquad
L_{\eta,\delta}=\log\frac{e}{\eta\delta},\qquad
b=\frac1{1024 C_r^2(1+\bar\nu^2)}.
\tag{52.1}
$$

Restrict $\eta\le\eta_0\le1$ sufficiently for U at
$\vartheta=\eta/4$. Choose once a constant $a\ge1$ so large that
$ba>4$ and

$$
20\{a(1+T)+1\}
 \exp\{-(ba-4)\log(4e)\}\le1.
\tag{52.2}
$$

Such a choice exists because its negative exponent grows linearly in
$a$, whereas the prefactor grows linearly. Use Definitions 50.2 and
51.2 with

$$
n=\left\lceil a(1+T)\eta^{-2}L_{\eta,\delta}\right\rceil,
\qquad h=T/n.
\tag{52.3}
$$

All times and the full Read count are fixed before any unseen interval.
The grid may be arbitrarily fine; this analytic contract has no minimum
latency. Refining it changes neither the ideal tolerance nor its
velocities, so it does not change the execution bounds.

**Theorem 52.2 (same-source whole-held chance tube).** The same family
has, for every deterministic allowed $\eta,\nu,\delta$,

$$
\begin{aligned}
M=n&\le C\eta^{-2}\log\frac e{\eta\delta}
                         \quad\text{deterministically},\\
\mathbb P\{D_{\max}(\bar q^{\rm N},X^\nu)\le\eta\}
 &\ge1-\delta,\\
\mathbb EV^a,\ \mathbb EV^b,\ \mathbb EL
 &\le C(\eta^{-1}+\nu^2\eta^{-2}),\\
\mathbb EE&\le C(\eta^{-2}+\nu^4\eta^{-4}).
\end{aligned}
\tag{52.4}
$$

The constants in all four execution bounds are independent of the
risk $0<\delta<1/4$. No source-dependent unseen interruption or
acquisition of an actual continuous history is involved.

Proof. For the actual target, and also separately in law for the
generated target, apply Lemma 44.2 to every deterministic cell with
$\lambda=0$. Its local held coordinates are
$\Delta A^0,\Delta B^0$ and
$D_{s,t}=K^\nu_{t\wedge S}-K^\nu_{s\wedge S}
 -A^0_s(B^0_t-B^0_s)$. The bound, valid also at $\nu=0$ and after
a boundary hold, is uniformly

$$
\mathbb P\{\text{some local coordinate in a cell has
 absolute supremum exceeding }\epsilon\}
 \le10\exp\left\{-\frac{\epsilon^2}
                         {16(1+\bar\nu^2)h}\right\}.
\tag{52.5}
$$

The primary scalar tools for Lemma 44.2 are Mörters–Peres,
*Brownian Motion*, [draft of May 25, 2008](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf),
Theorem 2.14, p. 48 (strong Markov for an almost surely finite stopping
time in the right-continuous Brownian filtration), and Theorem 2.18,
p. 50 ($\mathbb P(\max_{s\le t}B_s>a)=2\mathbb P(B_t>a)$ for
$a>0$). Independent initial enlargement preserves their hypotheses,
and $\sqrt2 B$ gives the present covariance. The remaining central
bound is the stopped exponential-martingale calculation displayed in
Lemma 44.2, with quadratic variation at most
$2(\epsilon^2+\nu^2)h$. It concerns each native marginal, not a
Brownian law conditional on paid endpoints.

Let $G$ be the event that all these cell bounds hold for both target
paths, intersected with their probability-one regular event. A union
bound uses only their marginal laws, not independence between them:

$$
\mathbb P(G^c)\le20n e^{-b\eta^2/h}\le\delta.
\tag{52.6}
$$

To check the second inequality, put $L=L_{\eta,\delta}$ and
$A=a(1+T)+1$. Then $n\le A\eta^{-2}L$,
$b\eta^2/h=b\eta^2n/T\ge baL$ and $L\ge\log(4e)$.
Since $\eta^{-2}\le e^{2L}$, $\delta^{-1}\le e^L$ and
$L\le e^L$, the ratio of the middle expression in (52.6) to
$\delta$ is at most $20A e^{-(ba-4)L}\le1$ by (52.2).
This deliberately nonsharp estimate is uniform even for arbitrarily
small risk; it proves the deterministic Read envelope in (52.4).

If the local coordinates from a cell's start have absolute value at
most $\epsilon$, the exact phase formula gives displacement from
that start at most $C_r\epsilon$ in $d_{\max}$. Indeed its two
real phase differences are $\Delta B^0/2$ and
$(1/2-h_s/r)\Delta B^0-D_{s,t}/r$, with
$0< h_s\le H=r/2$ (and the same bound at a held face), so
$|1/2-h_s/r|\le1/2$. This is an estimate in the covering coordinates
of that *one cell*, followed by the Lipschitz circle projection.
It does not claim that a single wrapped Read selects a real lift.

For $0\le t\le h$, the own state holds at $q_0$, giving error at
most $C_r\epsilon$ on $G$. For
$t\in[t_i,t_{i+1}]$, $i\ge1$, put $v=t-h$. Then
$v\in[t_{i-1},t_i]$, and the shared endpoint $X_i$ gives

$$
\begin{aligned}
d_{\max}(\bar q^{\rm N}_t,X^\nu_t)
&\le d_{\max}(Y^*_v,\widetilde X_v)
 +d_{\max}(\widetilde X_v,\widetilde X_{t_i})
 +d_{\max}(X^\nu_{t_i},X^\nu_t)\\
&\le\vartheta+2C_r\epsilon+C_r\epsilon
 =5\eta/8<\eta.
\end{aligned}
\tag{52.7}
$$

The factor two uses two displacements from the previous cell's start.
This includes a target exit inside either cell, a held boundary,
phase branches, $t=T$, and any horizon-cut terminal leg. Equation
(51.5) identifies the actual held own state at every such time.
Thus it is a complete three-coordinate whole-held tube. There is no
requirement that the actual and generated central noises agree.
The cost bounds are Theorem 51.3, unconditioned on $G$. $\square$

**Theorem 52.3 (matching infima in the same paid chance class).** For
fixed native data, $T>0$ and $\bar\nu<\infty$, there are positive
constants and $\eta_0>0$ such that uniformly for
$0<\eta\le\eta_0$, $|\nu|\le\bar\nu$, $0<\delta<1/4$,

$$
\begin{aligned}
\mathsf C^p_x(\eta,\nu,\delta)
 &\asymp \eta^{-1}+\nu^2\eta^{-2},\qquad x=a,b,L,\\
\mathsf C^p_E(\eta,\nu,\delta)
 &\asymp \eta^{-2}+\nu^4\eta^{-4}.
\end{aligned}
\tag{52.8}
$$

For every fixed $\delta\in(0,1/4)$, uniformly over the same noise
range,

$$
V_\nu(\eta,\delta)\asymp_\delta
                     \eta^{-2}\log(1/\eta).
\tag{52.9}
$$

The one family of Theorem 52.2 attains all five upper orders together.
Separate actuator infima are not asserted to have a common exact
minimizer. No optimal varying-risk Read dependence is claimed.

Proof. The upper bounds are (52.4). The Read converse is Theorem
42.2, applied to the unchanged $W^2$ coordinate. Its proof uses only
fresh $W^2$ increments in the full original filtration enlarged by
the independent seed. Both signs of $\nu$ and $\nu=0$ leave this
fact unchanged, and no noise-dependent constants occur in that proof.
All the present numerical profiles and predictable Read gaps belong
to that converse class. With fixed risk, the deterministic upper
Read bound in (52.4) has the same logarithmic order, proving (52.9).

Here is a positive-risk baseline execution floor; an almost-sure
ideal-history floor alone would not justify it. Choose $0<t_0<T$
with $\mathbb P(\tau\le t_0)\le1/8$. For sufficiently small
$\eta$ put $m=\lfloor t_0/(64\eta^2)\rfloor$ and partition
$[0,t_0]$ into $m$ equal intervals of length $\Delta=t_0/m$.
Then $64\eta^2\le\Delta\le128\eta^2$ and
$m\ge t_0/(128\eta^2)$. For each original unstopped first level let
$Z_j=\sum_{i=1}^m|W^j_{i\Delta}-W^j_{(i-1)\Delta}|$.
Independent covariance-$2$ Gaussian increments give

$$
\mathbb EZ_j=2m\sqrt{\Delta/\pi}
       \ge(16/\sqrt\pi)m\eta,\qquad
\operatorname{Var}(Z_j)=2(1-2/\pi)t_0.
\tag{52.10}
$$

Chebyshev's inequality therefore makes
$\mathbb P(Z_1<6m\eta\text{ or }Z_2<6m\eta)\le1/8$
for all sufficiently small $\eta$, independently of $\nu$ and of
the policy. Intersect this event's complement, target survival to
$t_0$, and a policy's whole-held success event. The intersection has
probability at least $1-1/8-1/8-\delta>1/2$; no independence of
success is used. The connected-lift argument of K, (13.3), applied on
success, gives $|A^{\rm N}-W^1|\le\eta$ and
$|B^{\rm N}-W^2|\le2\eta$ through $t_0$. Consequently on this
intersection

$$
V^a\ge4m\eta,\qquad V^b\ge2m\eta,\qquad
L\ge V^a,\qquad
E\ge\frac{(4m\eta)^2+(2m\eta)^2}{t_0}.
\tag{52.11}
$$

The last inequality is Cauchy–Schwarz on the actual controls through
$t_0$, including any own-death hold. Taking expectations proves
uniform $c\eta^{-1}$ variation/length and $c\eta^{-2}$ energy
floors for every member of the paid chance class, without a lifetime
hypothesis or a success-conditioned charge.

For the central part, Theorem 43.1 at $\lambda=0$ applies verbatim
in this same class with

$$
A_{\eta,\nu}=[\nu^2t_0-4r^2\eta^2]_+.
\tag{52.12}
$$

Its stochastic residual identities remain valid at $\nu=0$, where
this extra floor is zero, and depend on the sign only through
$\nu^2$. If $\nu^2>\eta$ and
$\eta\le t_0/(8r^2)$, then
$A_{\eta,\nu}\ge t_0\nu^2/2$. Equations (43.2) give the
additional $c\nu^2\eta^{-2}$ variation/length and
$c\nu^4\eta^{-4}$ energy floors. If $\nu^2\le\eta$, the
baseline terms already dominate the sums in (52.8). These two regimes
cover equality and all crossover sequences; the maximum of the two
appropriate floors bounds their sum up to a fixed factor. Taking each
infimum separately proves (52.8). It is essential here to use the
chance-stopped residual floor and (52.11), rather than transferring
an infimum from U's stronger observation class. $\square$

## 53. Original-clock lifetime and the bounded Green consumer

**Theorem 53.1 (same-face delay, censoring and coupled limits).** For
the same family, put $e_\eta=2h+d_\eta=O(\eta^2)$, uniformly in
$\nu,\delta$. No own death is premature, and every retained own
death is at the target's same face. On an event of probability one,
if the actual target has a boundary record on this horizon, then

$$
\zeta^{\rm N}=
 \begin{cases}
 \widetilde\tau+h+d_\eta,&
               \widetilde\tau+h+d_\eta\le T,\\
 \infty,&\widetilde\tau+h+d_\eta>T,
 \end{cases}
\qquad
0\le S^{\rm N}-S\le e_\eta.
\tag{53.1}
$$

If $\tau>T$, both death marks are infinite. The delay bound and the
same-face assertion hold also on unsuccessful tracking outcomes,
not merely on the tube event. With $e_\eta\le T/2$ and the
fixed-horizon passage-density constant $C_T$ of K, (31.1),

$$
\begin{aligned}
\mathbb P(\mathbf1_{\{\zeta^{\rm N}<\infty\}}
          \ne\mathbf1_{\{\zeta<\infty\}})&\le C_Te_\eta,\\
\mathbb E d_\zeta(\zeta^{\rm N},\zeta)
 &\le(1+C_T)e_\eta,\qquad
\mathbb E(S^{\rm N}-S)\le e_\eta.
\end{aligned}
\tag{53.2}
$$

Here $d_\zeta$ is K, §24's censored-time metric with infinity
isolated. For any deterministic sequence with
$\eta_n\to0$, $\delta_n\to0$ and $\nu_n\to\nu_*$ in the
allowed interval, held native paths and their real triples converge
uniformly in probability on the persistent source to the target at
$\nu_*$; the lifetimes converge in probability and the killed paths
converge in probability in $J_1$. If $\sum_n\delta_n<\infty$,
all these limits hold almost surely, with eventually equal finite/infinite
indicators. No independence between different family members is required.

Proof. On the regular event, (51.5) shifts the ideal terminal endpoint
by exactly $h$. If $j$ is the first boundary record, Theorem 50.3 puts
both $\tau$ and $\widetilde\tau$ in $(t_{j-1},t_j]$, at the
same face. Hence

$$
\tau<\widetilde\tau+h+d_\eta\le\tau+2h+d_\eta.
\tag{53.3}
$$

The left inequality also follows from
$\widetilde\tau+h>t_j\ge\tau$.
If the displayed endpoint is beyond $T$, the actual interval simply
ends at $T$ with its current original velocity; its unexecuted suffix
is not accelerated and its death mark is infinite. In particular when
$\tau$ lies in the last grid cell, the own death is beyond the
horizon and $T-\tau\le h$. If the endpoint equals $T$, the own
mark is the finite value $T$. These conventions prove (53.1) in every
censoring case. The safety rule already proves no premature or wrong-
face own death even on the exceptional fallback inputs.

A mismatch of the finite/infinite indicators on the regular event requires
$T-e_\eta<\tau\le T$. K, (31.3)'s two one-sided passage densities
bound this probability by $C_Te_\eta$. On equal finite marks the
time difference is at most $e_\eta$, and on mismatched marks the
metric is at most one, yielding (53.2). There is no $\delta$ loss
in these estimates: the shared boundary grid cell did not require
a small-oscillation event. The uniform $O(\eta^2)$ assertion follows
from (51.1), (52.3) and $L_{\eta,\delta}\ge\log(4e)$.

For the sequence, all regular events may be intersected countably.
The target height and $\tau$ are the same for every $\nu$, and
$\tau$ has no atom at $T$. Thus (53.3) alone gives almost-sure
censored-lifetime convergence and eventually equal finite/infinite
indicators. The held
targets satisfy the same-source bound

$$
D_{\max}(X^{\nu_n},X^{\nu_*})
 \le |\nu_n-\nu_*|\|C_{\cdot\wedge S}\|_\infty/r
 \longrightarrow0\quad\text{almost surely}.
\tag{53.4}
$$

Combine (52.4) with this bound for the held convergence in probability.
On the tube event the continuous-lift differences start at zero and,
for $\eta_n<\pi$, cannot switch between disjoint period branches.
K, (13.3) therefore gives the corresponding real triple error at most
$\eta_n$, $2\eta_n$, and $r(1+2|c_0|)\eta_n$.
For the target triples the only noise difference is
$(\nu_n-\nu_*)C_{\cdot\wedge S}$, proving their convergence too.

When $\tau<T-e_{\eta_n}$, both deaths are strictly below $T$.
The increasing piecewise linear comparison homeomorphism matching
$0,\tau,T$ to $0,\zeta_n^{\rm N},T$ has displacement at most
$e_{\eta_n}$. On the tube event its live-state discrepancy is
bounded by $\eta_n$ plus the modulus of the fixed limiting held
target at $e_{\eta_n}$ and the noise difference (53.4). After the
matched deaths both states are the cemetery. If $\tau>T$ the
identity comparison suffices. The remaining terminal window has
probability tending to zero by the passage-density bound. This proves
$J_1$ convergence in probability, including the case of a possible
own endpoint at $T$ by excluding that window. If the risks are summable,
Borel–Cantelli makes the tube events eventual almost surely. The
same argument is then pathwise, since $\tau\ne T$ almost surely.
Only the observation comparison is retimed; all actual costs and
occupations retain their original clocks. $\square$

**Theorem 53.2 (bounded original-clock occupation and noise removal).**
Use the pole $q_0$, density $d\mu=dk\,d\alpha\,d\beta$ and
killed operator of N, Theorem 1.3, including zero noise:

$$
L_{|\nu|}=-(P^2+Q^2+\nu^2r^{-2}\partial_\beta^2)_{F,\Omega},
\qquad \Omega=(l,u)\times\mathbb T^2.
\tag{53.5}
$$

The subscript denotes N's Friedrichs form realization, with the
horizontal form closure at $\nu=0$, rather than an isotropic $H^1$
domain asserted at that endpoint.

For $F\in C(E_0)$, $\eta_n\to0$, $\delta_n\to0$ and
$\nu_n\to\nu_*$, the same paid family satisfies

$$
\mathbb E\int_0^{S_n^{\rm N}}F(\bar q_n^{\rm N}(t))dt
 \longrightarrow
\mathbb E\int_0^{T\wedge\tau}F(X^{\nu_*}_t)dt.
\tag{53.6}
$$

For nonnegative $F$ the same holds with any fixed cap on the *total*
integral; for signed $F$ it holds under bounded Lipschitz clipping.
Taking first the displayed finite-horizon limit and then $T\to\infty$
in the uncapped bounded-integrand expression gives

$$
\lim_{T\to\infty}\lim_{n\to\infty}
 \mathbb E\int_0^{S_{n,T}^{\rm N}}F(\bar q_{n,T}^{\rm N}(t))dt
 =\int_\Omega\Gamma_{|\nu_*|,q_0}(q)F(q)\,d\mu(q).
\tag{53.7}
$$

At $\nu_*=0$ this is simultaneous paid approximation and removal
of central noise on the original coupling.

Proof. Let $M_F=\|F\|_\infty$ and use its uniform modulus
$\omega_F$. The own path remains alive at least as long as the
target, and (53.1) bounds the extra original-clock interval on every
regular outcome. On the tube event compare the integrands through
$S$, and then use (53.4). On its complement use $2M_FT$.
Thus the expected absolute difference of the random integrals in
(53.6) is at most

$$
T\mathbb E\omega_F\left(\eta_n+
       |\nu_n-\nu_*|\|C_{\cdot\wedge S}\|_\infty/r\right)
 +2M_FT\delta_n+M_Fe_{\eta_n}.
\tag{53.8}
$$

Bounded convergence makes this tend to zero. The random integrals
are bounded in absolute value by $M_FT$, so they also converge in
$L^1$ by the same argument, and a total cap or bounded Lipschitz clip
preserves the limit. This proves (53.6) without a same-clock uniform
cemetery claim.

N, Theorem 1.3 identifies the target expectation with its truncated
Green occupation and bounds the remaining target tail by
$C M_F e^{-\pi^2T/(u-l)^2}$. Applying that supplier after the
finite-horizon paid limit proves (53.7). No uniform infinite-time
native tail is inferred. With a fixed total cap $B$ and nonnegative
$F$, the subsequent $T\to\infty$ limit is instead
$\mathbb E\min(B,\int_0^\tau F(X^{\nu_*}_t)dt)$; obtaining the
linear Green pairing along that route additionally requires
$B\to\infty$. Bounded continuous extensions of truncated fields
are covered. Removing an uncapped singular-field truncation still
requires a separate uniform-integrability argument; N, §7's positive-
hold obstruction is unaffected by paid tracking. $\square$

## 54. Exact acquisition boundary and mathematical correspondence

**Proposition 54.1 (positive risk, analytic profiles and the source boundary).**
The construction proves a uniform paid acquisition-to-execution bridge
for the actual source (50.1). Its statements include $\nu=0$, either
sign, $\nu^2\asymp\eta$, arbitrary fixed preparation phases,
failed tracking outcomes and terminal horizon prefixes. They do not
supply an almost-sure hard tube, a finite-arithmetic sampler, or
additional physical transport or axis conclusions.

Proof. The common actual target remains (50.1) for every family member;
only the seed-generated internal random elements vary. Equations
(50.3)–(50.5) show exactly why their endpoint conditioning preserves
the native marginal path law. Equations (51.2)–(51.6) show which
information suffices for the already proved ideal controller and how
its execution is converted to finitely many paid numerical issuances.
The internal path may have a different central noise and different
windings from the actual path. Neither is identified or charged as an
acquired actual bridge. All output profiles depend only on seed,
records, known law and clock. Every actual change is fixed by a prior
paid record or is the known own numerical boundary hold. The proof
therefore grants no hidden source-dependent interruption or exact
target death time. Its Borel selections use the analytic profile class
of K, Definition 20.2; no bound on profile description, arithmetic,
seed bits or physical sensing latency follows from that class.

U, Theorem 4.2 is reused for its existing substantive native control,
including chronological residual, inward guards and original-time
energy. It is not reproduced as a new controller theorem. The new
content is the native endpoint-kernel correspondence, lawful delayed
paid replay, one common deterministic Read envelope, its uniform
chance-class baseline floor, and the consequent same-family lifetime
and bounded consumer. The central floor is exactly Theorem 43.1 at
$\lambda=0$; the fixed-risk Read lower bound is exactly Theorem 42.2
with its unchanged first-level argument. N supplies the existing full
killed Green law, not a Green law selected by sensing. Austin's two
standard-Borel results and Mörters–Peres's scalar Brownian statements
are classical tools used inside these native proofs. No priority or
worldwide absence claim is required for this repository-derived
composition. Offline taut-string and full-path approximation contracts
listed in §49 are not substituted for the present paid causal class.

Finally K, Theorem 41.2's obstruction applies unchanged at $\nu=0$
as well: conditional on the independent seed, the first blind positive
interval has a fixed numerical own path, while $W^2$ at an internal
time has nondegenerate variance independently of height survival.
Connected phase lifting forces scalar error at most $2\eta$ on an
almost-sure native tube, contradicting that Gaussian tail. Thus no
finite positive-gap policy here has a zero-risk tube for
$0<\eta<\pi$. Also, on $\{\tau\le T\}$, strict delayed own
death makes the same-clock isolated-cemetery uniform distance equal
to $2$, even as $J_1$ convergence holds. These are retained boundaries,
not weaker replacement endpoints. State dimension, control rank,
covariance rank, spectral or homogeneous dimension and physical spatial
axes remain distinct. The analytic target law, its second-order
operator and source realization are model premises; the bridge neither
derives them from bare FIB nor supplies uncapped singular occupation
or physical implementation. $\square$

## 追加锚（本行以下为增补区）
