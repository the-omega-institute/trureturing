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

## 55. Finite reports under the installed exact-point interface

**Definition 55.1 (fixed source, calibration and accessible reports).**
In §§55–59, K, U and N denote the volumes named in Definition 50.1,
with their statements as present at
`f798ec9bfccf53ae06465fbad0accff466978c92`.
Fix every datum of K, Definitions 2.1–2.2 and 41.1: $0<Z<1$,
$r=1-Z$, $H=r/2$, $0<l<k<u<H$, arbitrary preparation phases,
$T>0$ and a fixed signed $\nu\ne0$. The actual target is (50.1)
with $\lambda=0$, on the same persistent independent covariance-$2$
triple $(W^1,W^2,C)$. Its held state is $X$, its height exit is
$\tau$, and $S=T\wedge\tau$. Retain the probabilities
$(k,H-k,Z,H-k,k)$, negative amplitude convention, both actual
$2\pi$ periods, original clock and raw measure
$d\mu=dk\,d\alpha\,d\beta$. The only controls are the original
$P,Q$, with their ordinary chronology and extrema guards.
Any history preceding the specified start keeps its separate charges.
All constants below may depend on these fixed data, but not on
$\eta,\delta$.

The sensor remains the installed, paid exact-point
$\operatorname{Read}(t)=X_t$ of K, Definition 41.1.
A finite report means the following restriction on dependence, not a
replacement sensing contract. At each prescribed Read the acquisition
service applies a fixed Borel map $Q_\rho$ to the raw returned point.
Only the resulting symbol is retained or made accessible to the issuer.
No raw height, raw phase, comparison residue, discarded point, bridge,
deck label or other source-dependent variable is accessible to it.
The service has the analytic permission to apply this deterministic
postprocessing to its already paid exact point; no physical coarsener,
comparison tariff or sensing-precision bound is supplied by that
permission. Calibration, clock and prior issued numerical commands
are known. They are fixed data or functions of the report history,
not additional target channels. No independent seed is needed.

**Definition 55.2 (one source-preserving finite quantizer).** Put
$w=u-l$. For $0<\rho\le1$ set

$$
m_h=\lceil w/\rho\rceil,\qquad
m_\theta=\lceil2\pi/\rho\rceil.
\tag{55.1}
$$

Partition $(l,u)$ into the $m_h$ equal height bins, choosing a fixed
half-open convention at internal ties, and send each bin to its
midpoint. Send height $l$ to $l$ and height $u$ to $u$, as two
distinct boundary outcomes; no interior height is sent to a face.
For each phase use the nearest point of its $m_\theta$-point circular
grid, translated respectively by the known $\alpha_0,\beta_0$.
Break any circular tie by the smaller grid index. Let $\mathcal A_\rho$
be the product alphabet of the height and phase indices, and write
$z(a)\in E_0=[l,u]\times\mathbb T^2$ for a symbol's decoded point.
The known initial point $q_0$ may additionally be encoded by one
calibration symbol. Thus, including that symbol,

$$
|\mathcal A_\rho|\le(m_h+2)m_\theta^2+1\le C\rho^{-3},\qquad
 d_{\max}(z(Q_\rho(q)),q)\le\rho.
\tag{55.2}
$$

Indeed the height and phase errors are each at most $\rho/2$;
the weaker displayed bound will suffice. The bin and tie rules are
Borel. The two death-face flags are exact comparisons before rounding,
not inferences from a rounded value. Repeated held target points
produce the same symbol. Every incoming or retained source report
in what follows belongs to this single alphabet. Exact real entries
of its calibrated decoding table are allowed numerical coefficients;
a finite index is not a finite-bit representation of those entries.

## 56. Direct numerical execution, including failed tracking histories

**Definition 56.1 (one-grid service and the terminal fallback).**
Choose any finite equal grid $t_i=ih$, $h=T/n$, $n\ge2$.
Make and charge all $n$ Reads at $t_1,\ldots,t_n=T$, even after
failure, terminal issuance or own death. Initially issue a zero hold
and set the own endpoint $z=q_0$, in normal mode. Every movement
issued at $t_i<T$ has its entire numerical profile fixed there,
executes over duration $h$, and has constant continuation afterwards.
At $T$ issue no new movement. The automatic own boundary hold is
K, Definition 20.3's cutoff.

In normal mode at $t_i<T$, decode $z_i=z(Q_\rho(X_{t_i}))$ and
compute $(X_i^{\rm c},Y_i^{\rm c},D_i^{\rm c})$ from $(z,z_i)$
by (44.1). Accept the local connector exactly when

$$
|X_i^{\rm c}|\le3\rho,\qquad
|Y_i^{\rm c}|\le5\rho,\qquad
|D_i^{\rm c}|\le6\rho.
\tag{56.1}
$$

On acceptance use K, Definition 34.1's finite inward-rectangle
connector, at scale $\rho$, with these three parameters.
Parametrize its geometry $g_i$ by constant Euclidean arclength speed
on $[0,1]$ and issue the numerical pair
$g_i(\min(v/h,1))$ as a function of elapsed time $v\in[0,T]$.
At its completed endpoint replace $z$ by $z_i$.
A live endpoint leaves normal mode unchanged; a boundary endpoint
makes this a terminal command, followed permanently by its hold.

If (56.1) fails at a live report, replace the unexecuted continuation
by a hold at the current own endpoint and enter failed mode.
In failed mode keep that hold while reports are live. At the first
boundary report, or immediately if (56.1) first fails on a boundary
report, issue the straight height leg from the current own height to
that reported face, with zero $b$ increment, over the whole duration
$h$. This is the terminal fallback, followed by its hold.
It uses neither the boundary phases nor an estimate of the unknown
actual death time. A boundary first reported at $T$ causes no movement.
After any terminal issuance only the prescribed Reads and own hold
remain. Thus an abort of ordinary tracking never suppresses later
boundary acquisition. No interruption uses an unseen target event.

**Theorem 56.2 (legal finite factorization and unconditional own death).**
Assume
$\rho\le\min(1,w/8,\min(k-l,u-k)/2,\sqrt T)$.
Definition 56.1 is a causal finite numerical issuer in the original
paid-point class. Its entire issued profiles, their executed prefixes
and their concatenation obey the original numerical domains and
source guards. They preserve the actual chronology

$$
 j_N(t)=\int_0^t a_N(s)\,db_N(s),\qquad
 D_{a_N,b_N}=(-\min a_N,H-\max a_N).
\tag{56.2}
$$

For every realized absorbed target history, including histories on
which (56.1) fails, there is no premature own exit, every own exit
is at the target's actual face, and, with
$S_N=T\wedge\tau_N$,

$$
0\le S_N-S\le2h.
\tag{56.3}
$$

If $j$ is the first boundary Read index, then an own exit on this
horizon occurs exactly at $t_j+h$ when $j<n$, including equality
$t_j+h=T$; if $j=n$ it has no own exit on the horizon.
If there is no boundary Read, it has no own exit on the horizon.
Every issuance and the full executed held path factor exactly through
the finite report word and the fixed calibration. Equal report words
give identical numerical controls, not just equal endpoint laws.

Proof. Before failure or terminal issuance, induction over grid cells
shows that the own point at $t_i$ is $q_0$ for $i=1$ and otherwise
the decoded preceding report. Formula (44.1) uses only this point
and the new decoded point. Its endpoint calculation and K, Lemma 34.2
show that the issued two-control path ends at exactly $z_i$, including
its wrapped phases. No unwrapped own phase is needed: translation
of its relative chronology contributes
$a_N(t_i)Y_i^{\rm c}+D_i^{\rm c}$ to the single ordinary integral
(56.2). K, Proposition 2.3 then supplies the endpoint and every
prefix with the original negative phase convention.

The connector's inward rectangles stay strictly in $(l,u)$.
Its final height leg is strictly interior until its endpoint and
can touch a face only if that report is a boundary report. Live
quantization midpoints are strictly interior. A failed-mode hold
therefore holds at an interior point. Its terminal straight leg is
also interior until its final face endpoint. Every proposed whole
profile includes its computed hold after its endpoint, so its whole
height lies in $[l,u]\Subset(0,H)$, not merely its executed part.
Its own first exit is precisely that endpoint. The concatenation is
continuous and piecewise affine, with finitely many legs, so it is
an AC original numerical history. Consequently
$k+\min a_N\ge l>0$ and $k+\max a_N\le u<H$.
For an individual increment profile starting at height $h_*$ the
same check reads $h_*+\min x>0$, $h_*+\max x<H$.
For another promised start $[k_-,k_+]$, its domain is still exactly
$k_-+\min a_N>0$, $k_++\max a_N<H$; re-running the policy is not
permission to change that realized command's domain.

A first boundary report is possible only after actual target death.
Before it, all own heights remain interior, even after tracking
failure. If it arrives at $t_j<T$, either terminal rule reaches that
same face exactly at $t_j+h$, without an earlier height touch.
Since $t_{j-1}<\tau\le t_j$, this gives
$0<t_j+h-\tau\le2h$. If the first boundary record is at $T$,
then $S_N=T$ and $0\le T-\tau\le h$.
If no boundary record arrives, $\tau>T$ and both horizon cutoffs
are $T$. This proves (56.3), including the cases of death at a grid
point and death or own death exactly at the horizon. Interruption
and the horizon itself have not been counted as death.

For factorization let $a_1,\ldots,a_i$ be a report prefix.
Starting with the fixed calibration symbol, the preceding recursion
chooses its mode, own endpoint, next whole numerical profile and
all its own cutoff times from that word and the known grid.
Each acceptance comparison, principal representative, ceiling in
the rectangle count and arclength parametrization is a deterministic
Borel operation. For this fixed $\rho$ the rectangle counts are
bounded by $\lceil6/\rho\rceil$, so no infinite profile is issued.
There are at most $n$ grid issuances, counting the initial hold and
holds on failed histories. Prescribed own holds are already included;
counting an automatic own hold separately adds at most one issuance.
The operation times are deterministic grid times or computed own
numerical endpoints. Hence there are Borel maps $\Phi_i$ and $\Phi$
such that

$$
\gamma_i=\Phi_i(a_1,\ldots,a_i),\qquad
 (a_N,b_N,j_N,\bar q_N)=
 \Phi(Q_\rho(X_{t_1}),\ldots,Q_\rho(X_{t_n})).
\tag{56.4}
$$

The fixed clock and calibration are implicit arguments, independent
of the report word. The real chronology on the left is derived
from the selected controls. Their accumulated lifts and numerical
coefficients are likewise derived quantities; none is an extra
measurement. Induction proves identical outputs for every two
raw input streams with the same quantized word. In particular raw
values cannot influence failure, a terminal choice, timing or a
coefficient after their symbols are fixed. This verifies both
causality in K, Definition 41.1 and exact finite-report dependence.
The argument used only deterministic properties of each absorbed
continuous target history; it did not discard unsuccessful outcomes.
$\square$

## 57. One finite-report chance tube and its joint original-time prices

**Definition 57.1 (tolerance, risk and predetermined Read budget).**
Let $0<\delta<1/4$, $0<\eta\le\eta_0$, and put

$$
 C_0=32(1+r^{-1}),\qquad \rho=\eta/C_0,\qquad
 \ell=\log\frac{e}{\rho\delta},\qquad
 b=[16(1+\nu^2)]^{-1}.
\tag{57.1}
$$

Choose $\eta_0\le1$ small enough for Theorem 56.2 and for
$(5/2+r^{-1})\rho<\pi$.
Choose once $a\ge1$ so large that $ba>4$ and

$$
10\{a(1+T)+1\}
 \exp\{-(ba-4)\log(4e)\}\le1.
\tag{57.2}
$$

Such a choice exists by exponential domination of a linear prefactor.
Use Definition 56.1 with

$$
 n=\left\lceil a(1+T)\rho^{-2}\ell\right\rceil,\qquad h=T/n.
\tag{57.3}
$$

Decrease $\eta_0$ if necessary so that $n\ge2$.
These are one family and one common grid for sensing, execution,
death and every consumer below.

**Theorem 57.2 (direct finite-message dependence at full held accuracy).**
For every fixed native datum in Definition 55.1, every
$0<\eta\le\eta_0$ and $0<\delta<1/4$, this single lawful family
obeys

$$
\begin{aligned}
\mathbb P\{D_{\max}(\bar q_N,X)\le\eta\}&\ge1-\delta,\\
 M=n&\le C\eta^{-2}L_{\eta,\delta},\qquad
 L_{\eta,\delta}=\log\frac{e}{\eta\delta},\\
 |\mathcal A_\rho|&\le C\eta^{-3}.
\end{aligned}
\tag{57.4}
$$

Its factorization is exactly (56.4), under the original installed
Read, not an exact-endpoint conditional replay theorem.

Proof. Use the held real coordinates $\bar A,\bar B,\bar K$ and
the relative $D^*_{s,t}$ of (44.2). Let $G$ be the event that in
every grid cell $[t_{i-1},t_i]$ all three quantities
$|\bar A_t-\bar A_{t_{i-1}}|$,
$|\bar B_t-\bar B_{t_{i-1}}|$ and
$|D^*_{t_{i-1},t}|$ remain below $\rho$.
These are probability tests only, not observations or permissible
source-dependent interrupt signals. Lemma 44.2 at $\lambda=0$
and a union bound in the original enlarged Brownian filtration give

$$
\mathbb P(G^c)\le10n e^{-b\rho^2/h}\le\delta.
\tag{57.5}
$$

For the last inequality write $C_a=a(1+T)+1$.
Then $n\le C_a\rho^{-2}\ell$ and
$\rho^2/h\ge a\ell$. Also $\ell\ge\log(4e)$ and
$\rho^{-2}\ell/\delta\le e^{4\ell}$, since each of
$\rho^{-1},\delta^{-1},\ell$ is at most $e^\ell$.
Thus (57.5), divided by $\delta$, is at most
$10C_a e^{-(ba-4)\ell}\le1$ by (57.2).
This estimates the persistent, actually stopped target, including
cells containing or following its death.

On $G$, in any one cell, the target alpha increment has absolute
value at most $\rho/2$ in its continuous local lift, while its beta
increment is

$$
 \left(\tfrac12-X_{t_{i-1}}^{\rm height}/r\right)
       (\bar B_t-\bar B_{t_{i-1}})
       -D^*_{t_{i-1},t}/r.
\tag{57.6}
$$

The coefficient lies in $(0,1/2)$, including at either killing face.
Consequently the target's $d_{\max}$ oscillation relative to the
left endpoint is at most $M_r\rho$, $M_r=1+r^{-1}$.
For two successive decoded points, (55.2) adds at most $2\rho$
to each coordinate increment. Starting from $q_0$ only reduces
that error. The decoded height difference is at most $3\rho$;
the decoded principal alpha increment is at most $5\rho/2$;
the decoded principal beta increment is at most
$(5/2+r^{-1})\rho$.
The smallness condition in Definition 57.1 ensures that these
principal representatives are the indicated local differences,
including when a circular grid crosses its coordinate cut.
Since the own decoded height is in $[l,u]$, (44.1) therefore gives

$$
 |X_i^{\rm c}|\le3\rho,\qquad
 |Y_i^{\rm c}|\le5\rho,\qquad
 |D_i^{\rm c}|\le(5r+1)\rho\le6\rho.
\tag{57.7}
$$

Here $0<r<1$ was retained. Hence no local test fails on $G$,
up to and including its terminal boundary connector.

At a prefix of any such connector K, (34.3) gives
$|x|\le3\rho$, $|y|\le5\rho$, $|j|\le6\rho$.
The actual phase increments from its own start are $y/2$ and
$(1/2-h_*/r)y-j/r$, by the original prefix chronology.
Thus the own path stays within $C_r\rho$ of its decoded start,
where $C_r=3+6/r$ is sufficient. During service on
$[t_i,t_{i+1}]$, that start is within $\rho$ of the actual target
at $t_{i-1}$. The actual target at the current time is within
$2M_r\rho$ of that earlier target point, by the triangle inequality
across at most two cells. The complete service error is therefore
at most

$$
 (C_r+1+2M_r)\rho=(6+8/r)\rho<\eta.
\tag{57.8}
$$

The initial hold has error at most $M_r\rho$.
After a completed terminal connector the actual target is already
held at its observed face, and its own quantized endpoint is within
$\rho$ of that held point forever. If the boundary is first reported
at $T$, the preceding service bound already covers the whole last
cell, with no terminal acceleration. Thus (57.8) covers the full
held path, not just grid values, live intervals or a first-level
projection. It proves the first assertion of (57.4).
Finally $\ell=L_{\eta,\delta}+\log C_0\le C L_{\eta,\delta}$,
and (55.2), (57.3) give the other assertions. $\square$

**Theorem 57.3 (pathwise joint charges and the unpriced services).**
For this same family, on every history, with no conditioning on $G$,

$$
\begin{aligned}
 V^a_N,\ V^b_N,\ L_N&\le C n,\\
 E_N=\int_0^{S_N}(\dot a_N^2+\dot b_N^2)dt
       &\le C n^2/T,\\
 B_{\rm rep}=n\lceil\log_2|\mathcal A_\rho|\rceil
       &\le Cn(1+\log(1/\eta)).
\end{aligned}
\tag{57.9}
$$

The bounds count all actually paid Reads and all actual execution,
including failed, aborted, held and horizon-cut profiles. They are
bounds on original analytic actuator resources and fixed-width
report bits; they do not price a complete service or finite device.

Proof. Every accepted connector satisfies K, (34.4) with $A=5$,
$B=6$ and $\rho\le1$. Its two variations are at most $19,17$,
and its Euclidean native length is at most $36$.
Its constant arclength speed on duration $h$ has unhalved energy
at most $36^2/h$. These are bounds for every accepted report pair,
including those on $G^c$. A terminal fallback has length and height
variation at most $w<1$, zero $b$ variation and energy at most
$w^2/h$. Holds have zero actuator costs. At most $n-1$ nonzero
profiles can be issued. Addition gives (57.9).
A prefix executed for a fraction $\theta$ contributes its actual
variation and length and $\theta L_i^2/h$ energy for a constant-speed
profile of full length $L_i$; this also bounds a prefix cut inside
a leg. No unexecuted suffix is charged or sped up. In this aligned
grid construction the last nonconstant service completes at $T$;
its prescribed later hold is cut by the horizon. A first boundary
Read at $T$ is paid and has no executed terminal leg. A rejection
aborts only future ordinary tracking: earlier completed services,
the later fallback and every subsequent Read remain in the above
count. This accounts for all censoring and failure cases rather
than reporting a success-conditioned cost.

The report alphabet includes both face outcomes and any calibration
symbol. A fixed-width encoding, with padding, uses precisely the
displayed $B_{\rm rep}$ bits for the $n$ incoming words. Storing
all those words uses no more report bits; streaming is also possible.
Equation (55.2) proves its upper bound. Any fixed finite mode flags
change it by at most $Cn$.

The price and permission coordinates are distinct. Sensing uses
exactly $n$ units of the installed paid Read service, even though
its raw replies are exact reals. Raw-to-finite acquisition uses the
analytic $Q_\rho$ permission of Definition 55.1; its comparison and
discard operations have no supplied physical tariff. Exact face
equality, bin and principal-branch comparisons, integer ceilings and
arclength parametrization are allowed analytic calculations; their
physical execution cost is not zero by implication. Numerical
coefficients use the fixed exact calibration and decoded table,
not a source-dependent analog supplement. Installation of that
table, exact coefficient access and actuation precision have no
supplied bit or service bound. The report-storage count above
bounds stored report indices only; clock state, working arithmetic,
calibration and numerical own-control state are separate.
Observation rights, source access, installation rights and their
prices are precisely additional permissions required to provide
the installed Read and its coarsening; the original two-control
syntax alone supplies none of them. Storage access and arithmetic
likewise have no given total-service tariff. Only the four
actuator coordinates have the declared identity metric and
original-time prices in K, (11.4). Without a specified joint tariff
these different coordinates cannot be summed into a scalar optimum.
In particular (56.4) supplies no finite-bit raw sensor, finite
arithmetic, finite physical memory, computability for arbitrary
noncomputable calibration constants or total controller-state bound.
The positive logarithmic overhead in (57.9) also gives no new
actuator optimum; the distinct exact-real replay family's established
optimal statements remain those of §§50–54. $\square$

## 58. The same finite-report family's bounded and fixed-cap consumers

**Theorem 58.1 (bounded occupation on the actual killed coupling).**
For $F\in C(E_0)$ let $M_F=\|F\|_\infty$ and
$\omega_F(s)=\sup\{|F(x)-F(y)|:d_{\max}(x,y)\le s\}$.
For precisely Definition 57.1's execution and its actual target,

$$
\begin{aligned}
\mathbb E\left|\int_0^{S_N}F(\bar q_N(t))dt
                    -\int_0^S F(X_t)dt\right|
 &\le T\omega_F(\eta)+2hM_F+2T\delta M_F.
\end{aligned}
\tag{58.1}
$$

Consequently $\eta\to0$, $\delta\to0$ at fixed $T$ gives
$L^1$ convergence of these occupations, also after any fixed
Lipschitz clipping of the total integral. For nonnegative $F$ this
includes a fixed total cap. Taking first that finite-horizon limit
and then $T\to\infty$ in the unclipped bounded-integrand expectation
gives exactly N, (1.6)'s full killed Green pairing
$\int_\Omega\Gamma_{|\nu|,q_0}F\,d\mu$.
A fixed total cap instead retains the expectation of the capped
random total and is not that linear pairing.

Proof. By Theorem 56.2 the common live interval is $[0,S]$ and
the remaining own interval has length at most $2h$ on every
outcome. On $G$ compare the integrands through $S$ by
$\omega_F(\eta)$; on $G^c$ bound their absolute difference by
$2M_F$. Integrating on the original clock, then taking expectations,
proves (58.1) using (57.5). Lipschitz clipping follows by applying
its Lipschitz constant to this $L^1$ bound. The target tail after
$T$ is at most $C M_F e^{-\pi^2T/w^2}$ by N, Theorem 1.3.
This proves the claimed iterated limit without a uniform infinite-
time tail assumption on the native executions. Monotone convergence
for a nonnegative capped total gives its stated different limit.
No exact equality of shared two-time marginal laws was used.
$\square$

**Theorem 58.2 (fixed field cap and its original-clock response).**
Fix the same source, pole $q_0$, $\epsilon=|\nu|>0$, $g>0$ and
finite $B>0$. Let $V=\Gamma_{\epsilon,q_0}$ and let $V_B=V\wedge B$
have value $B$ at the pole and zero at both absorbing faces.
By N, Proposition 7.1 this is continuous on $E_0$.
Set, for this family's actual execution,

$$
\begin{aligned}
 A_{NB}&=\int_0^{S_N}V_B(\bar q_N(t))dt,&
 A_B&=\int_0^S V_B(X_t)dt,\\
 W_{NB}&=e^{gA_{NB}},& W_B&=e^{gA_B},\\
 d_B&=T\omega_{V_B}(\eta)+2Bh+2BT\delta.
\end{aligned}
\tag{58.2}
$$

For any real Lipschitz $f$ on $E_0$ which vanishes on both faces,
put $f(\dagger)=0$, $M_f=\|f\|_\infty$ and
$K_f=\operatorname{Lip}_{d_{\max}}f$. Then

$$
\begin{aligned}
 \mathbb E|A_{NB}-A_B|&\le d_B,\\
 \mathbb E|W_{NB}-W_B|&\le g e^{gBT}d_B,\\
 \left|\mathbb E[W_{NB}f(q_N^\dagger(T))]
             -\mathbb E[W_B f(X^\dagger_T)]\right|
 &\le e^{gBT}\{gM_f d_B+K_f\eta+2M_f\delta\}.
\end{aligned}
\tag{58.3}
$$

The limiting response as $\eta,\delta\to0$ at fixed $B,T$ is the
continuous zero-boundary representative at $q_0$ of
$e^{-T\mathsf H_B}f$, where $\mathsf H_B$ is the form operator
of $T_\epsilon-g\int V_B|u|^2d\mu$ on N's actual
$\mathcal F_\epsilon$. This is a bounded-potential response of
the free killed target, not a native attractive-process sampler.

Proof. The first inequality is (58.1), now proved for the present
family. Both occupations lie in $[0,BT]$, so the exponential has
Lipschitz constant $g e^{gBT}$ on their range, proving the second.
Because $f$ vanishes on both faces, each killed terminal value equals
$f$ of its held endpoint, even if exactly one process has died.
The whole-held tube therefore bounds the terminal difference by
$K_f\eta$ on $G$ and by $2M_f$ on $G^c$.
Split the response difference into the weight difference times one
terminal value and $W_B$ times the terminal difference; use
$W_B\le e^{gBT}$. This gives the last inequality. All expectations
include failed outcomes, terminal fallback executions and extra own
lifetimes. For fixed $B$, uniform continuity of $V_B$ makes
$d_B\to0$, proving the response limit.

For the analytic identification use N, (12.17), which is proved for
this actual killed operator and bounded potential by the ordered-time
Duhamel expansion. The target, sign, raw measure, pole, two Dirichlet
faces and clock here are exactly its parameters. In particular its
operator is $L_\epsilon-gV_B$, not a retimed or normalized operator.
The acquisition family in N, Definition 12.1 is different; its
family-specific (12.6) and resource schedule are not transferred.
Here their needed tracking, own lifetime and capped integrability
hypotheses were supplied directly by Theorems 56.2, 57.2 and (58.1).
N, §§15–20's unit-cell coefficients, threshold and universal profiles
are likewise unchanged analytic consumers, not new realization claims.

There is an explicit obstruction to deleting the field cap for this
producer. The initial own hold lasts $h>0$ at the pole and occurs
strictly before own exit. Since $V(q_0)=+\infty$,
$\int_0^{S_N}V(\bar q_N(t))dt=+\infty$ for every family member.
Thus (58.3) asserts only the fixed-field-cap response just stated;
it implies neither uncapped native occupation nor uniform
integrability of that uncapped exposure. A separate analytic cap
limit for the target is not a change of this native obstruction.
$\square$

## 59. Mathematical correspondence and the remaining source bridge

**Definition 59.1 (attributed intermediates and exact scope).**
The new composition in §§55–58 is repository-derived: absolute finite
reports of this specific wrapped source, direct guarded execution,
unconditional same-face delayed death, joint pathwise prices and
the consequent bounded and fixed-cap consumer for that execution.
K, Definitions 2.1–2.2, 11.1–11.2, 20.2–20.3 and 41.1 supply its
source, numerical class, guards, sensor and prices; K, Lemma 34.2
supplies its existing finite legal connector. Equations (44.1)–(44.5)
supply the local wrapped decoding and stopped oscillation estimate.
The elementary finite grid quantization, union bound and Lipschitz
calculations are intermediates in these proofs, not separate new
classical theorem claims. N, Theorem 1.3, Proposition 7.1 and
(12.17) are respectively the exact raw-measure killed Green,
continuous field-cap and bounded-potential response correspondences.
U's ideal-history actuator theorem and §§50–54's exact endpoint
conditional-history theorem have different information hypotheses;
neither is substituted for the present finite-report construction.

The primary stochastic approximation comparisons are
Creutzig–Müller-Gronbach–Ritter,
[Free-Knot Spline Approximation of Stochastic Processes,
§§1–2, Theorems 2–3](https://arxiv.org/pdf/math/0612313v1), and Slassi,
[Free knot linear interpolation and the Milstein scheme for stochastic
differential equations, §§1–2](https://arxiv.org/pdf/1306.4457v1).
The former optimizes measurable free-knot spline approximants and
their averaged errors. The latter explicitly grants complete
individual-path information in §1 and uses the supremum-based
free-knot times (13) in §2. Neither contract installs a sensor for
this two-period source, supplies its actual area chronology, or
prices guarded commands with its own absorbing faces. Their
approximation results are literature-attested comparisons, not
native sensor or control suppliers. The claimed content here is the
explicit source-specific composition above; no worldwide novelty or
formal certification is asserted.

Finite reports do not identify source dimension, control rank,
covariance rank, homogeneous dimension and three physical spatial
axes. The native law, geometry, source, clock, operations and paid
observation permissions remain premises. A common-source spatial
realization and recursive gluing still require their own maps and
joint compatibility conditions. Different qutrit, atomic-port or
transport sources do not acquire these permissions from equality of
dimensions. This finite-horizon finite-message bridge closes only
the declared dependence obligation under the installed exact Read;
it supplies no new preparation, reset, third control, law change,
attractive sampler or unpriced total-service optimum.

## 追加锚（本行以下为增补区）

## 60. A fixed finite acquisition and its exact certificate task

**Definition 60.1 (the unchanged joint experiment and finite records).**
In §§60–65, K, U and N have Definition 50.1's source meanings.
Use their statements and this volume's §§55–59 at
`5664567cef22b0cbcd6ab70ab480acf36d5800ff`.
Retain every datum of Definition 55.1: the actual five-mode ray,
its arbitrary fixed preparation phases and negative amplitude convention,
both $2\pi$ periods, $r=1-Z$, $H=r/2$,
$0<l<k<u<H$, raw $d\mu=dh\,d\alpha\,d\beta$, $T>0$,
$\lambda=0$ and fixed signed $\nu\ne0$.
At height $h$ the probabilities in mode order $(0,1,2,3,13)$ are
$(h,H-h,Z,H-h,h)$. Write the original control fields as
$P=\partial_h$ and
$Q_{\rm ctl}=\tfrac12\partial_\alpha+(\tfrac12-h/r)\partial_\beta$;
$Q_{\rm ctl}$ denotes K's control $Q$, distinct from the report map below.
The target is precisely (50.1) on the original persistent independent
covariance-$2$ triple $(W^1,W^2,C)$, held at its first height exit
$\tau$; $S=T\wedge\tau$. Its live region and faces are

$$
 \Omega=(l,u)\times\mathbb T^2,\qquad
 F_f=\{f\}\times\mathbb T^2\quad(f=l,u),\qquad
 E_0=\Omega\cup F_l\cup F_u.
\tag{60.1}
$$

Surface measure on either face means the unnormalized
$d\sigma_f=d\alpha\,d\beta$, not a conditional exit probability.
Fix once a finite alphabet $\mathcal A$ and a Borel map
$Q:E_0\to\mathcal A$. At each paid exact Read only
$A_i=Q(X_{R_i})$ is accessible. The same $Q$ is used at every call,
including after target or own death. No raw residue, crossing signal,
source-dependent timing, refreshed sample or new sensor is supplied.
Write

$$
 I_a=Q^{-1}(a)\cap\Omega,\quad B_{f,a}=Q^{-1}(a)\cap F_f,
 \qquad v_a=\mu(I_a),\quad b_{f,a}=\sigma_f(B_{f,a}).
\tag{60.2}
$$

A symbol is boundary-active when $b_{l,a}+b_{u,a}>0$.
Zero mass and an empty set are different conditions.

Allow any independent initial randomization $U$, with no finite-state
or finite-entropy restriction. Replace K, (41.1)'s raw replies by $A_i$;
retain its entire report-predictable positive-gap class.
Thus the next Read time or cessation of calls is chosen from the
complete acquired record, seed, clock and known own execution before
the unseen gap. Gaps are strictly positive but need no common lower
bound. Read and numerical issuance counts through $T$ are almost surely
finite; they need no deterministic or expected bound. A decision can be
made at a Read or at a clock time determined from previous records,
including between Reads. Null-event completions do not change a
law-almost-sure claim. Known own execution, all previous declarations,
interruptions, rejections and failure flags are retained; they are
functions of this acquired information, not further target observations.

An issuer still uses exactly K, Definitions 2.2, 20.2–20.3 and 41.1's
numerical $P,Q_{\rm ctl}$ commands, chronological $j_N=\int a_N\,db_N$,
whole-command domain $D_{a_N,b_N}=(-\min a_N,H-\max a_N)$
and its extrema guards, and actual own first exit $\tau_N$ from
$(l,u)$, followed by its hold. Neither a declaration nor an interrupted
profile is an own exit. All four charges remain the variations $V^a,V^b$,
Euclidean native length $L$ and unhalved energy
$E=\int_0^{T\wedge\tau_N}(\dot a_N^2+\dot b_N^2)dt$ of K, (11.4),
on their actually executed prefixes, including unsuccessful histories.
Theorems below neither reprice them nor condition them on success.

**Definition 60.2 (certification and a positive horizon margin).**
A death certificate is a declaration at a permitted acquired-information
time $D\le T$ such that
$\mathbb P(D\le T,\tau>D)=0$; $D=\infty$ means no declaration.
A labelled-face certificate additionally gives $f\in\{l,u\}$ and has
zero probability of declaring any $f$ other than the actual absorbing
face $X_\tau\in F_f$. These are zero-error statements under the original
joint law, including the independent seed. They do not reveal $\tau$.
Completeness with margin $d\in(0,T)$ means

$$
 \mathbb P\{\tau\le T-d,\ D>T\}=0.
\tag{60.3}
$$

The procedure may depend on $d$, with finite paid acquisition, and must
have zero error also outside the completeness event. The same definition
applies without a face label. Certification is an information task;
it supplies no new native motion or full tracking controller.

## 61. Native support and the maximal finite-record certificates

**Theorem 61.1 (complete-record certificate characterization).**
For every fixed $Q$ in Definition 60.1, the following holds throughout
its full positive-gap class. At any permitted decision time $\sigma\le T$
let $m$ be the finite number of acquired Reads and, if $m>0$, let $a=A_m$.
Define accessible events

$$
\begin{aligned}
 C_0(\sigma)&=\{m>0,\ v_a=0,\ b_{l,a}+b_{u,a}>0\},\\
 C_f(\sigma)&=\{m>0,\ v_a=0,\ b_{f,a}>0,\ b_{g,a}=0\},
                    \qquad \{f,g\}=\{l,u\}.
\end{aligned}
\tag{61.1}
$$

For every event $E$ determined by the acquired information at $\sigma$,

$$
\begin{aligned}
 \mathbb P(E\cap\{\tau>\sigma\})=0
 &\quad\Longleftrightarrow\quad
 \mathbb P(E\setminus C_0(\sigma))=0,\\
 \mathbb P(E\setminus\{\tau\le\sigma,X_\tau\in F_f\})=0
 &\quad\Longleftrightarrow\quad
 \mathbb P(E\setminus C_f(\sigma))=0.
\end{aligned}
\tag{61.2}
$$

Here a decision can include a declaration or the actual own exit between
Reads. In particular the complete finite history, random schedule,
arbitrary independent seed and prior own execution cannot enlarge the
zero-error certificate events beyond (61.1), up to law-null events.

Proof. We first establish the transition and exit correspondence for
this actual source, rather than postulating full support for an abstract
observed process. Started from $x=(h,\alpha,\beta)\in\Omega$, use fresh
covariance-$2$ Brownian increments $B^1,B^2,D$, and set
$c(h)=1/2-h/r$. Until height exit the native lifts are

$$
 h_s=h+B^1_s,\qquad
 \alpha_s=\alpha+B^2_s/2,\qquad
 \beta_s=\beta+\int_0^s c(h_z)\,dB^2_z-\nu D_s/r.
\tag{61.3}
$$

This is (50.1), since $B^1$ and $B^2$ have zero mutual quadratic
covariation. At a stopping-time restart, splitting the original area
integral at that time gives exactly (61.3), with the current height and
wrapped phases. No discarded winding or earlier bridge enters its
coefficients. Independent initial enlargement preserves the Brownian
strong Markov property. This use of strong Markov is the classical
supplier in Mörters–Peres, *Brownian Motion*,
[Chapter 2, Theorem 2.14](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf),
rescaled by $\sqrt2$; the larger Brownian filtration is used only in
this proof. It is not an acquisition input.

For a positive deterministic lag $t$, condition on the whole height
path. On either survival to $t$ or exit by $t$, put $s=t\wedge\tau_x$,
where $\tau_x$ is the fresh height exit. Then $s>0$ almost surely.
The two phase increments in (61.3) are jointly Gaussian. For any real
$(\xi,\zeta)\ne(0,0)$ their linear combination has conditional variance

$$
 2\int_0^s\left\{(\xi/2+\zeta c(h_z))^2
                         +\zeta^2\nu^2/r^2\right\}dz>0.
\tag{61.4}
$$

Its wrapped two-dimensional Gaussian law therefore has a strictly
positive density with respect to $d\alpha\,d\beta$. This statement
uses the fixed $\nu\ne0$ and asserts no uniform lower bound as
$\nu\to0$, $s\to0$ or the start approaches a face.

For the height, killed Brownian transition measure at lag $t$ is
equivalent to Lebesgue measure on $(l,u)$. One direct justification is
to condition on its Gaussian endpoint $h'\in(l,u)$. The Brownian bridge
about the segment from $h$ to $h'$ has positive probability of a uniform
norm less than the segment's positive distance from the two faces.
The usual Brownian small-ball fact here can be obtained from the
independent Gaussian dyadic construction in Mörters–Peres, Chapter 1,
§1: a sufficiently late independent tail has small uniform norm with
positive probability, and finitely many earlier coefficients can each
be restricted to an open interval of positive Gaussian probability.
This also proves a positive-probability tube about every polygonal path.
The centered bridge is $B_z-(z/t)B_t$; independence from $B_t$ follows
from zero Gaussian covariance, and its small-ball event follows from
$\sup|B_z-(z/t)B_t|\le2\sup|B_z|$.
Consequently the conditional bridge survives with positive probability
for every interior endpoint. Either face has positive probability of
being the first face reached by time $t$: choose a polygonal height
path that crosses that face before $t$ and stays separated from the
opposite face, and use its Brownian tube. This last assertion does not
assume an unobserved crossing is acquired.

Together with (61.4) and Fubini these facts give, for every Borel set,
the measure equivalences

$$
\begin{aligned}
 \mathbb P_x\{t<\tau_x,\ X_t\in\cdot\}&\sim\mu|_\Omega,\\
 \mathbb P_x\{\tau_x\le t,\ X_{\tau_x}\in\cdot\cap F_f\}
                                      &\sim\sigma_f,\qquad f=l,u.
\end{aligned}
\tag{61.5}
$$

For example, for an interior set of positive volume its phase section
has positive area for a positive-measure set of height endpoints;
conditional wrapped Gaussian positivity and the killed height density
make its probability positive. Null sections have probability zero.
For a face set, conditional on any height path exiting at that face,
the wrapped Gaussian at $s=\tau_x>0$ has the same two implications.
There is positive height probability of that face exit by $t$.
These arguments prove both directions of each equivalence, including
Borel sets with no interior. A target already on a face instead stays
at its exact point, so all its later reports are the same symbol.

We now pass from positive deterministic lags to the actual admissible
histories. Freeze a seed value and a finite report word
$w=(a_1,\ldots,a_m)$. The recursively chosen Read times on that word
are fixed numbers $0<r_1<\cdots<r_m\le T$; a decision time in the next
blind gap is likewise fixed by that word and the clock. Discard only
words on which the policy does not schedule these events.
At each actual Read time the fresh triple is strong Markov, and its
next lag is already measurable from the past. Conditional on that past,
(61.5) applies at that lag, however small it is. It follows successively
that the native live and face supports on the word are exactly

$$
\begin{aligned}
 \mathbb P_x\{w,\ \tau>r_m\}>0
 &\quad\Longleftrightarrow\quad
                  v_{a_i}>0\text{ for every }1\le i\le m,\\
 \mathbb P_x\{w,\ \tau\le r_m,\ X_\tau\in F_f\}>0
 &\quad\Longleftrightarrow\quad
 \exists j\in\{1,\ldots,m\}:\quad
 \begin{cases}
 v_{a_i}>0 & (i<j),\\
 a_j=a_{j+1}=\cdots=a_m,\\
 b_{f,a_j}>0.
 \end{cases}
\end{aligned}
\tag{61.6}
$$

Here probabilities refer to the policy at that fixed seed and the fixed
word's schedule. The initial live state is the specified $q_0$; the
same statement holds from any interior state. The first line follows
by integrating a positive live transition at each step. For the second,
partition by the first Read at or after death. Its earlier Reads must
all be live, that transition must exit at the indicated face with its
indicated symbol, and every later symbol must repeat. Each transition
has positive probability by (61.5), so these conditions are also
sufficient. If all earlier symbols have positive volume, the conditional
interior law after the earlier prefix is equivalent to $\mu$ restricted
to its last cell; integrating any of (61.5)'s strictly positive kernels
preserves positivity. The same integration proves that both face
possibilities in (61.6) remain positive when both face masses are
positive. Thus support of a nonempty topological neighborhood has not
been substituted for support of an arbitrary Borel report cell.

If every $v_{a_i}>0$, there remains positive probability of being live
also at any scheduled finite decision time $\sigma\ge r_m$: append
survival for its remaining lag to (61.6). This includes zero remaining
lag. With no Reads the corresponding probability is simply
$\mathbb P_{q_0}(\tau>\sigma)>0$. Waiting a finite time or choosing a
numerical own trajectory cannot remove this live alternative.
If some $v_{a_j}=0$ on a positive-probability word, let $j$ be its
first occurrence. The target cannot have been live at $r_j$; its report
must be boundary-active and it is held thereafter. In particular every
later symbol equals $a_j$, including $a_m$. At each face with
$b_{f,a_j}>0$, (61.6) gives positive probability of this same entire
word, and the held face is unchanged at every later decision time.
This proves the classification at a fixed seed and word.

To justify its use with arbitrary randomization, no individual exact
seed or exact timestamp is asserted to have positive probability.
Use the independent product law for the seed and Brownian triple, and
integrate the finite-word transition kernels over the seed. For a fixed
word the kernel for a live alternative is strictly positive at every
feasible seed whenever all its cell volumes are positive. A measurable
seed subset supporting a positive-probability declaration on that word
therefore also gives positive live error probability. If the first
zero-volume symbol has both face masses positive, the analogous two
face kernels are both strictly positive on the same feasible seed
subset; declaring only one face cannot have zero error there.
Tonelli gives these implications even for a nonatomic or arbitrarily
rich seed. This is a statement about equivalence of the induced record
measures, not a comparison of singleton records.

Finally partition by the finite number of arrived Reads, their finite
word, and, when needed, the finite issuance index. These form countable
partitions; no deterministic count cap, mean count or fixed minimum gap
is required. Before the next Read, clock events, whole numerical
profiles, their joins and their own height hitting times are determined
by the preceding record and seed. Their outcomes and failure flags
cannot add a target-dependent condition to that partition.
This includes an own exit between Reads; a simultaneous Read can be
included in the acquired word, which only grants more information.
One may equivalently apply the same argument to any first declaration
time in the acquired filtration: on a fixed word its time before the
next Read depends only on the clock and that word. The almost-sure
finite-count hypothesis covers every actual declaration and own exit;
completed null events change none of these probabilities.

On $C_0$ the target is already dead, and on $C_f$ it is dead at face
$f$, proving the reverse implications of (61.2). Outside those events
the live or opposite-face record measure just constructed is positive
on any accessible event of positive probability. This proves the
forward implications and the theorem. $\square$

## 62. Sharp death and labelled-face completeness frontiers

**Theorem 62.1 (the two finite-acquisition criteria).**
Under Definition 60.1, zero-error death certification complete on deaths
with every fixed positive horizon margin is possible if and only if

$$
 b_{l,a}+b_{u,a}>0\quad\Longrightarrow\quad v_a=0
                  \qquad(a\in\mathcal A).
\tag{62.1}
$$

Zero-error labelled-face certification with that completeness is
possible if and only if

$$
 b_{l,a}+b_{u,a}>0\quad\Longrightarrow\quad
            v_a=0\ \text{ and }\ b_{l,a}b_{u,a}=0
                  \qquad(a\in\mathcal A).
\tag{62.2}
$$

Each criterion is necessary already for completeness at any one margin
$d\in(0,T)$. These are law-almost-sure criteria on positive masses,
not pointwise all-history claims or algorithms for deciding arbitrary
Borel masses.

Proof. Suppose (62.1). For a fixed margin $d$, use a deterministic finite
grid through $T$ of mesh $h<d$. Declare death at the first report with
$v_a=0$ and $b_{l,a}+b_{u,a}>0$, and never otherwise.
Theorem 61.1 gives zero error on all outcomes outside its null set.
The boundary cells of zero surface mass have zero exit probability by
(61.5); the alphabet is finite. Thus almost every held exit point has
a boundary-active symbol. For that point (62.1) gives $v_a=0$.
The first grid Read after death therefore declares by $\tau+h$, whenever
that time is in the horizon. In particular it declares by $T$ on
$\{\tau\le T-d\}$. If (62.2) holds, its unique positive face mass
also supplies the correct face label at the same declaration. These
are finite paid declarations under the installed Read and fixed $Q$;
they prescribe no new actuator policy.

For necessity choose a boundary-active symbol $a$ and a face $f$ with
$b_{f,a}>0$. The exact original-law event

$$
 H_{f,a,d}=\{\tau\le T-d,\ X_\tau\in B_{f,a}\}
\tag{62.3}
$$

has strictly positive probability by (61.5) at the positive lag $T-d$.
Before death all acquired symbols have positive live volume almost
surely, by (61.5), conditioning at each positive gap and a countable
union over Reads. After death all acquired symbols equal $a$.
If $v_a>0$, the latest symbol at every possible post-death declaration
still has positive live volume, or there has been no post-death Read.
Theorem 61.1 precludes every positive-probability zero-error death
declaration on (62.3). A pre-death declaration is also forbidden by
zero error. Hence (60.3) is impossible. This proves (62.1)'s necessity
and the volume part of (62.2).
If $v_a=0$ but $b_{l,a}b_{u,a}>0$, a post-death record either still
has only pre-death Reads, or ends in the same face-ambiguous symbol
$a$. In the former case a live alternative remains; in the latter
both faces remain possible on that complete record. The face part of
(61.2) forbids a zero-error face declaration on (62.3). Its probability
is positive for each face. This proves the remaining necessity.
All errors and completeness failures are measured on the same original
joint law; no alternative realization is substituted for it. $\square$

**Theorem 62.2 (null fibres and the stronger pointwise task).**
For the stronger task of certification on every absorbed continuous
input path in $E_0$ starting at $q_0$, requiring a finite acquired record
at each declaration also on paths of native-law probability zero,
conditions (62.1)–(62.2) become respectively

$$
\begin{aligned}
 B_{l,a}\cup B_{u,a}\ne\varnothing
    &\ \Longrightarrow\ I_a=\varnothing,\\
 B_{l,a}\cup B_{u,a}\ne\varnothing
    &\ \Longrightarrow\ I_a=\varnothing
                   \text{ and at most one }B_{f,a}\ne\varnothing.
\end{aligned}
\tag{62.4}
$$

This pathwise requirement is strictly stronger than the native-law
requirements. Death alone is also strictly weaker than labelled-face
certification, even under the native law.

Proof. Empty live fibres and separated nonempty face fibres give direct
pointwise certificates, and the finite grid argument of Theorem 62.1
works for every such absorbed path. Conversely take a boundary point
with symbol $a$ and a continuous path reaching it before $T-d$.
Pointwise completeness requires a declaration with a finite acquired
record on that path. If $I_a$ is nonempty,
a live path can visit an interior point of that cell at every later
Read. Earlier live report points can be matched. Connect successive
interior waypoints within the connected $\Omega$ during the strictly
positive gaps; this preserves the complete acquired record and all
its scheduled times, commands and declarations. It stays live through
the proposed declaration. If instead both face fibres are nonempty,
a path to the opposite face with the same boundary symbol can match
the live prefix and every later report. The final approach to either
face fits inside the gap before its first boundary report.
These finite waypoint constructions include a first boundary report
coincident with a declaration; no crossing time is itself reported.
They prove the necessity of (62.4) for pointwise certificates. The
alternative continuous histories need not have positive native-law
probability, which is exactly why they cannot prove (62.1)'s converse.

For a strict example modify Definition 55.2's installed $Q_\rho$ at one
interior point $q_*\ne q_0$ only, assigning to it an existing lower-face
symbol. Every mass in (60.2) is unchanged. Thus (62.2) still holds,
whereas that symbol now has a nonempty live fibre and fails (62.4).
A positive-gap Read hits $q_*$ while live with probability zero by
(61.5); the countable union over adaptive Reads remains null.
Pointwise an interior path through $q_*$ gives the alias just described.
For the distinction between the two law criteria, assign all interior
points one symbol and both whole faces a second symbol. The second
symbol has $v_a=0$ and $b_{l,a}=b_{u,a}=4\pi^2$.
It certifies death completely but can never certify its label with
zero error and complete coverage. $\square$

## 63. Own-exit and bounded-occupation consequences on the original law

**Theorem 63.1 (no-premature death forces no finite-horizon own death).**
Suppose that every boundary-active symbol of the fixed $Q$ has positive
live volume:

$$
 b_{l,a}+b_{u,a}>0\quad\Longrightarrow\quad v_a>0.
\tag{63.1}
$$

Every admissible native issuer in Definition 60.1 satisfying
$\mathbb P\{\tau_N\le T,\ \tau_N<\tau\}=0$ then satisfies

$$
 \mathbb P\{\tau_N\le T\}=0,\qquad S_N=T\wedge\tau_N=T
                                      \quad\text{almost surely}.
\tag{63.2}
$$

For every $0\le e<T$, the bounded-delay lifetime requirement
$0\le S_N-S\le e$ almost surely is impossible in this class.
For the bounded occupation test $F\equiv1$ its unavoidable loss is

$$
\begin{aligned}
 \mathbb E\left|\int_0^{S_N}1\,dt-\int_0^S1\,dt\right|
 &=\mathbb E(T-S)=\int_0^T\mathbb P(\tau\le t)dt\\
 &\ge T\Phi\left(-\frac{d_0}{\sqrt T}\right)>0,
       \qquad d_0=\min(k-l,u-k),
\end{aligned}
\tag{63.3}
$$

where $\Phi$ is the standard normal distribution function. In particular
this loss cannot tend to zero in any family of such no-premature issuers
at the fixed original $T$ and source.

Proof. An actual own exit is a permitted acquired-information event:
the numerical controls and their original chronological path determine
its height, and before the next Read their hitting time of $l$ or $u$
is determined by the existing record and clock. Interruptions and new
issuances are themselves subject to that same information restriction.
Partition an exit through $T$ by its finite issuance index, finite Read
count and complete report word, as in Theorem 61.1. No-premature own
death makes this event a zero-error certificate that the target has
already died at that time, whether or not the issuer explicitly declares
anything. Equation (61.2) places it inside $C_0$ up to a null event.
Under (63.1), $C_0$ has probability zero. This proves (63.2), including
own exits between Reads, random finite counts, failures and an own exit
exactly at $T$.

Consequently $S_N-S=T-(T\wedge\tau)$. Its being at most $e<T$
fails on $\{\tau<T-e\}$, an event of strictly positive probability:
height Brownian motion can reach either face in every positive time.
Thus in particular Theorem 56.2's $e=2h<T$ lifetime conclusion cannot
hold after replacing its face flags by such a $Q$.
Tonelli proves the first line of (63.3). Reflection for the nearest
face, with covariance-$2$ height increments, gives

$$
 \mathbb P(\tau\le T/2)
       \ge2\Phi(-d_0/\sqrt T).
\tag{63.4}
$$

Indeed crossing that single face in the unrestricted Brownian path
implies an interval exit by then, even if the opposite face was reached
first. Reflection is Mörters–Peres, Chapter 2, Theorems 2.16 and 2.18,
with the same $\sqrt2$ rescaling. Integrate the nondecreasing exit
probability over $[T/2,T]$ to obtain (63.3). Its upper bound is $T$,
so the positive loss is finite. This is a conclusion for the actual
joint occupation, not a comparison with a separately sampled lifetime
or a survival-normalized law. It is independent of the four actuator
charges; allowing them to be arbitrarily large does not acquire a
missing zero-error certificate. $\square$

## 64. Wrapped point accuracy can erase the exact death information

**Theorem 64.1 (a boundary-merged variant at the same report order).**
Let $w=u-l$ and $0<\rho\le\min(1,w/8)$. Use Definition 55.2's
$m_h=\lceil w/\rho\rceil$ equal interior bins and
$m_\theta=\lceil2\pi/\rho\rceil$ translated circular phase grids.
Form $\widetilde Q_\rho$ by merging its lower-face height index into
the first live-bin index and its upper-face height index into the last
live-bin index, leaving the phase indices unchanged. If the separate
$q_0$ calibration symbol is used, leave it separate.
Decode all ordinary height indices to their live-bin midpoints and
all phase indices to their old grid points. This fixed Borel
postprocessing of the installed Read satisfies

$$
\begin{aligned}
 d_{\max}(z(\widetilde Q_\rho(q)),q)&\le\rho/2
                                   \qquad(q\in E_0),\\
 |\widetilde{\mathcal A}_\rho|
 &\le m_hm_\theta^2+1\le C_*\rho^{-3},\\
 C_*&=(w+1)(2\pi+1)^2+1.
\end{aligned}
\tag{64.1}
$$

Yet it satisfies (63.1), and therefore fails even the zero-error death
completeness contract, before requiring a face label. In contrast the
installed unmerged $Q_\rho$ satisfies the sufficient labelled-face
condition (62.2), including its pointwise version (62.4).

Proof. Each height bin has width $\Delta_h=w/m_h\le\rho$.
A face is at distance $\Delta_h/2$ from its adjacent midpoint;
ordinary height errors have the same bound. The phase error on each
actual $2\pi$ circle is at most $\pi/m_\theta\le\rho/2$.
The calibration point, when separate, has zero error. These are exactly
K, Definition 13.1's maximum-coordinate errors, proving the first line
of (64.1), including points on the two faces and circular cuts.
For $\rho\le1$, $m_h\le(w+1)/\rho$ and
$m_\theta\le(2\pi+1)/\rho$, proving its declared alphabet constant.
The map is the old finite quantizer followed by one fixed map of its
height labels; it installs no extra observation or timing service.

Every angular cell has raw area
$\Delta_\theta^2=(2\pi/m_\theta)^2>0$, including the cells crossing
a phase cut. For an ordinary symbol of the first height bin,

$$
 v_a=\Delta_h\Delta_\theta^2>0,\quad
 b_{l,a}=\Delta_\theta^2>0,\quad b_{u,a}=0;
\tag{64.2}
$$

for a last-bin symbol the two face masses are reversed. Since
$m_h\ge8$, these bins are distinct. All other ordinary symbols have
both face masses zero. Removing the possible calibration singleton
changes none of these volumes, and its own boundary masses are zero.
Thus every boundary-active symbol has positive live volume; (63.1),
Theorem 62.1 and Theorem 63.1 apply. The failure is exact certification
despite the deterministic point-error bound, not a failure of its
$c\rho^{-3}$ report-size estimate.

For the original $Q_\rho$, a face symbol instead has $v_a=0$,
$b_{f,a}=\Delta_\theta^2$ and $b_{g,a}=0$ for the opposite face;
no live point is assigned any face symbol. All its live and calibration
symbols have zero face masses. This verifies (62.2) and (62.4) directly.
For precisely that unmerged quantizer the existing numerical issuer,
terminal connector and failure fallback remain Definition 56.1 and
Theorem 56.2, with $0\le S_N-S\le2h$ on every history. Its original
chance tube and unconditional executed-prefix prices are Theorems 57.2
and 57.3. Theorem 58.1 supplies the bounded occupation estimate for
that same execution and original joint target; $F=1$ is one of its
bounded tests. These statements are reused, not rederived for
$\widetilde Q_\rho$. For general $Q$, (62.2) certifies faces only;
it supplies neither a wrapped decoder of the needed accuracy nor the
local acceptance estimates used by the installed tracking controller.
Thus face certification alone is not a generic tracking theorem.
$\square$

## 65. Suppliers, exact consumers and the unclosed source bridge

**Definition 65.1 (attribution and applicability).**
The new native composition in §§60–64 is the complete finite-record
certificate frontier for (50.1), its actual no-premature-own-exit
consequence and the original-law bounded-occupation loss, with the
explicit boundary-merged counterexample. Classical positivity, Gaussian
conditioning, strong Markov and finite-observation diagnosis reasoning
are intermediates, not new general support or diagnosis theorems.
The native positive-volume and face-surface equivalences were derived
inside Theorem 61.1 with the original phase wrapping, height killing,
raw measure and signed central coefficient; a theorem for an unrelated
hidden-state model is not an assumed access or source correspondence.
The mathematical attribution is repo-derived for this composition,
with the following literature-attested suppliers and comparisons.

Mörters–Peres, *Brownian Motion*,
[the linked public draft](https://www.stat.berkeley.edu/~aldous/205B/bmbook.pdf),
Chapter 1, §1 supplies the independent Gaussian dyadic construction;
Chapter 2, Theorems 2.14, 2.16 and 2.18 supply Brownian strong Markov
and reflection. These concern Brownian motion, not the installed
finite-report issuer. Equation (61.3), conditioning (61.4), the
face/live equivalences (61.5), and the acquired-record integration are
the required native correspondence before using those intermediates.

Polyanskiy–Poor–Verdú, *Feedback in the non-asymptotic regime*,
[§II, Definitions 1–2](https://people.lids.mit.edu/yp/homepage/data/vbf_journal.pdf),
distinguish an output-filtration stopping rule for variable-length
feedback from termination allowed to depend also on the transmitted
message. The latter includes an additional reliable termination method;
it is a different information contract. This is a comparison of
observation rights only. Its channel capacity and coding theorems are
not used, and neither termination permission is added to (60.1).
The seed in Definition 60.1 retains its given arbitrary independent
law; no finite-common-randomness cardinality conclusion from a coding
model is transferred.

Slassi, *Free knot linear interpolation and the Milstein scheme for
stochastic differential equations*,
[§1 and §2, equation (13)](https://arxiv.org/pdf/1306.4457v1),
allows complete individual-path information for its free knots and
uses a supremum over an interval to define the next knot. Its
approximation estimates do not certify an unobserved absorbing event
in the present positive-gap class. An extra crossing signal or an
encoder-selected source-dependent termination time would change that
class, even if its endpoint report alphabet were unchanged.

The direct repository consumers are Definition 55.1's accessible
reports, Definition 55.2's separated flags, Theorem 56.2's actual
own-death delay and Theorem 58.1's common-clock occupation. K,
Definition 41.1 supplies exactly their acquired filtration and numerical
issuer class. N, Theorem 1.3 supplies the raw-measure killed law and
Green pairing; no survival-normalized or different-clock law is used
in (63.3). N, §§21–25's measurable Hilbert chord-distance floors have
a separate metric contract and select no dimension. An injective
distorted readout can retain all source information; here the explicit
$\widetilde Q_\rho$ instead identifies a face with a live positive-volume
cell, and (61.5)–(61.6) prove the resulting operational ambiguity.

These statements concern a fixed classical finite report of the actual
source on its original clock. Finite real coordinate count, exact real
memory values, paid acquisition and a coherent future contract are
different data. Nothing here changes the source law or operation syntax,
supplies reset or copies, a physical coarsening/comparison/retention
price, a new approximation producer or a uniform $\nu\to0$ result.
No worldwide novelty or Lean certification is asserted.
A common-source physical spatial or transport realization still needs
its geometry and preserved law, clock, operations and resource maps;
actual acquisition, retention and actuation prices and compatible
recursive spectral gluing remain separate mathematical obligations.
Neither (62.2) nor a chord-distance equality identifies three physical
spatial directions.

## 追加锚（本行以下为增补区）
