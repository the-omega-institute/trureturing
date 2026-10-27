# Recursive relational observation: sharp tasks and retained environment memory II

This continuation uses [STR] for the original source, tasks and all
supplied theorems in §§1–19, including its complete full-$H$ stability
results. Sections 20–23 are in this volume. Unqualified theorem,
definition, section and equation numbers below 20 refer to [STR];
numbers 20–23 refer here. Literature references are separately named.
The input, chronology,
old record and late-decoder timing are unchanged. [ERM] denotes the
original environment-instrument source used by STR.

## 20. Nine known preparations controlling joint retained use

The source, horizon and unknown-input domain remain Definitions
1.1–1.2 and 11.1. In particular $H=\mathbb C^5$, the input is the
whole complex qutrit, $B$ is the original isometry, $n\ge0$, and
$r(a\mid h)$ is the original complete input-independent finite or
countable kernel. Write $v=(\xi+e)/\sqrt2$, $E=vv^\dagger$,
$p=Bv$, $P=pp^\dagger=\widehat E_e$ and $P_0=I_5-P$.
Every $A_j$ below is the actual full-$H$ operator (11.1). The
decoder $\mathcal D_a:M_5\to M_5$ is common before the late task
choice and can have arbitrary full-$H$ output. No fairness law is
imposed on that output.

The per-Kraus estimate (13.35)–(13.38), including the complementary
full-$H$ events, is used as a supplier here. Theorem 13.3 already
proves average reference stability, and Theorem 17.1 already supplies
the optimal worst-case uniform local exponent $1/2$. The application
below specifies actual known preparations for that positive residual
and controls the joint channel that keeps the old record. It asserts
no new rigidity, exponent, exact modulus or optimal test count.

Theorem 18.1 already supplies the global all-angle bound
$\|T-\operatorname{Ad}_B\|_\diamond\le216578\delta_\theta(T)$
under its exact output-support hypothesis
$T(X)=P_RT(X)P_R$ for every $X$, where $P_R=BB^\dagger$.
Its input domain is still the whole complex qutrit, with every finite
untouched reference; its extra restriction is on the output. That
hypothesis permits the CPTP compression $X\mapsto B^\dagger T(X)B$
and the square-channel argument of (18.7)–(18.23). It is not imposed
here on $T$ or on any $\Phi_{h,a}$. In particular the allowed
$n=0$, one-record decoder $\operatorname{Ad}_{U_t}$ of Theorem
17.1 realizes $T_t=\operatorname{Ad}_{U_tB}$, and (18.24) proves
that this allowed output is outside $R$ for $0<t\le1/25$.
The supported-output theorem therefore does not replace the full-$H$
residual supplier used below. Its defect is the uniform effect norm
(18.4); the following application instead provides a finite set of
known preparation/event probabilities and controls the complete
weighted record/quantum endpoint from their positive sum. The task
complement $P_0$ here is distinct from the support projection $P_R$
(denoted $Q$ in §18).

Theorem 19.1 of [STR] also applies on precisely this unrestricted
complex $M_3\to M_5$ domain, at every real angle and including
$n=0$. Its different defect $\delta_{2,\theta}$ in (19.3)
retains the immediate effect, all four one-step effects and all eight
actual depth-two effects, uniformly over **all** complex qutrit density
inputs. For the average $T$ defined below its supplied conclusion is
$\|T-\operatorname{Ad}_B\|_\diamond\le
418231548\,\delta_{2,\theta}(T)$ globally, with no output-support
or small-defect premise. The depth-two product is $A_kA_j$, first
$j$ then $k$, and its ideal joint weight is $1/4$, not a normalized
branch probability. Its (19.8) also supplies persistence of this
average estimate for every tested depth $m\ge2$.

These are existing average/reference conclusions, not contributions
of this continuation. Their applicability requires their actual
augmented defect; a later callable two-acquisition experiment is not
already an acquired uniform defect bound. The nine configurations
below instead measure the positive residual using immediate and
one-step joint events. Equations (13.35)–(13.38) of [STR], also
retained in its (19.21)–(19.23), supply their coercivity without
requiring depth-two measurements. No depth-two acquisition, uniform
input oracle or new preparation right is added to that panel, campaign
or later unknown-input contract. Proposition 23.3 gives explicit
same-domain reasons why the average linear estimate cannot replace
the retained-record conclusion or make that residual's modulus linear.

**Definition 20.1 (the nine preparation/event configurations).**
For every real $\theta$ set $\sigma_j=(-1)^j$ and define

$$
\begin{aligned}
d_j&=-e/2+\sigma_j(\sqrt3/2)e^{2i\theta}f,&
w_j&=(\xi+d_j)/\sqrt2,\\
x_1&=(\xi-e)/\sqrt2,&x_2&=f,\\
z_{j1}&=(\xi-d_j)/\sqrt2,&
z_{j2}&=(\sqrt3/2)e+\sigma_j e^{2i\theta}f/2.
\end{aligned}
\tag{20.1}
$$

Here $w_j$ is exactly (13.26), not a different probe. Each
configuration prepares $B\chi\chi^\dagger B^\dagger$ **before**
the original $n$ acquisitions, processes their actual labels with
$r$, and invokes the installed $\mathcal D_a$. Only then does it
perform the indicated terminal experiment. Its designated bad event
is as follows:

| Configuration | Initial qutrit vector $\chi$ | Terminal experiment and designated event |
| --- | --- | --- |
| $1$ | $v$ | Immediate binary test $(P,P_0)$; event $y=0$, effect $P_0$ |
| $2,3$ | $x_1,x_2$, respectively | Immediate binary test; event $y=1$, effect $P$ |
| $4+2j,5+2j$, $j=0,1$ | $z_{j1},z_{j2}$, respectively | One actual acquisition, then the binary test; joint event $(j,1)$ |
| $8+j$, $j=0,1$ | $w_j$ | One actual acquisition, then the binary test; joint event $(j,0)$ |

All outcomes of each experiment occur in its complete instrument.
A different acquisition label is an ordinary outcome with bad-event
indicator zero; it is not discarded or used to renormalize the
trial. The last six configurations use six actual additional
acquisitions, one per configuration, rather than six postselected
branches of a single acquisition.

For a corrected channel $T:M_3\to M_5$, define its nine event
probabilities and their sum by

$$
\begin{aligned}
f_1(T)&=\operatorname{Tr}(P_0\,T(vv^\dagger)),\\
f_{1+r}(T)&=\operatorname{Tr}(P\,T(x_rx_r^\dagger)),
                       &&r=1,2,\\
f_{3+2j+r}(T)&=\operatorname{Tr}
 (A_j^\dagger PA_j\,T(z_{jr}z_{jr}^\dagger)),
                       &&j=0,1,\quad r=1,2,\\
f_{8+j}(T)&=\operatorname{Tr}
 (A_j^\dagger P_0A_j\,T(w_jw_j^\dagger)),&&j=0,1,\\
\mathcal R(T)&=\sum_{i=1}^9 f_i(T).
\end{aligned}
\tag{20.2}
$$

All $f_i$ are probabilities in $[0,1]$. They need not add to one,
since they refer to different preparations. The analytical definitions
do not themselves grant the ability to prepare those states.

**Proposition 20.2 (operational correspondence to the supplied residual).**
The vectors $(x_1,x_2)$ form an orthonormal basis of $v^\perp$,
and $(z_{j1},z_{j2})$ one of $w_j^\perp$. Every event (20.2)
has probability zero for $T=\operatorname{Ad}_B$. For any finite
Kraus family $T(X)=\sum_\nu L_\nu XL_\nu^\dagger$, let
$q_\nu$ be precisely the residual (13.33), with
$t_j=A_j^\dagger p$ and $F_j=w_jw_j^\dagger$. Then

$$
\begin{aligned}
\mathcal R(T)&=\sum_\nu q_\nu,\\
\max_i f_i(T)&\le\mathcal R(T)\le9\max_i f_i(T),\\
\max_i f_i(T)&\le\delta_\theta(T),
\qquad \mathcal R(T)\le9\delta_\theta(T).
\end{aligned}
\tag{20.3}
$$

Proof. The frame $(\xi,e,f)$ is orthonormal. The vector $d_j$
has norm one, is perpendicular to $\xi$, and is perpendicular to
$z_{j2}$ because
$-\sqrt3/4+\sqrt3/4=0$. Thus (20.1) gives the claimed two
orthogonal-complement bases, also when $\sin\theta$ or
$\cos\theta$ vanishes. For the ideal channel use exactly
(13.27): the immediate effect compresses to $E$, the joint
$(j,1)$ effect to $F_j/2$, and the joint $(j,0)$ effect to
$(I_3-F_j)/2$. These annihilate the stated inputs. Inserting
the Kraus expansion in (20.2) gives, in order, the sums of
$\|P_0L_\nu v\|^2$, the two basis terms of
$\|p^\dagger L_\nu(I_3-E)\|_{\rm HS}^2$, the two basis
terms of each $\|t_j^\dagger L_\nu(I_3-F_j)\|_{\rm HS}^2$,
and each $\|P_0A_jL_\nu w_j\|^2$. Their sum is (13.33).
The middle line of (20.3) is positivity. Each event expectation
is a zero-ideal expectation of one of (13.23)'s Hermitian effect
differences; the immediate $P_0$ difference is the negative of the
$P$ difference by trace preservation. Its absolute expectation is
bounded by that difference's operator norm. This proves the last
line without replacing any full-$H$ effect by its input-corner
compression on a leaked state. $\square$

**Definition 20.3 (joint comparison with the original chronological law).**
For the actual scheme put, with $h_1$ still acting first,

$$
\begin{aligned}
p_{h,a}&=2^{-n}r(a\mid h),&
\Phi_{h,a}&=\mathcal D_a\circ\operatorname{Ad}_{BQ_h},\\
T&=\sum_{h,a}p_{h,a}\Phi_{h,a},&
\Gamma_{ha}(X)&=\bigoplus_{h,a}p_{h,a}\Phi_{h,a}(X),\\
\Gamma^0_{ha}(X)&=\bigoplus_{h,a}p_{h,a}BXB^\dagger,&
\Gamma_a(X)&=\bigoplus_a\sum_h p_{h,a}\Phi_{h,a}(X),\\
\Gamma^0_a(X)&=\bigoplus_a\left(\sum_h p_{h,a}\right)BXB^\dagger.
\end{aligned}
\tag{20.4}
$$

The actual retained endpoint is $a$ together with decoded $H$;
$\Gamma_a$ is its channel. The index $h$ in $\Gamma_{ha}$
resolves actual events for comparison and supplies no installed
history port. A kept subrecord of $h$ must already be in the complete
$a$, with its acquired backing. At $n=0$ the only history is the
empty word, of weight one before the kernel. The countable direct
sums are trace-class $\ell^1$ sums: for $Y=\bigoplus_bY_b$,
$\|Y\|_1=\sum_b\|Y_b\|_1$. Every channel in (20.4) is
normalized, since $\sum_{h,a}p_{h,a}=1$ and each unweighted
$\Phi_{h,a}$ is CPTP.

For all these maps the diamond norm is **unhalved**, with the same
convention as (13.25):

$$
\|\Lambda\|_\diamond=
\sup_{d\ge1}\ \sup_{0\ne X\in M_3\otimes M_d}
\frac{\|(\Lambda\otimes\operatorname{id}_{M_d})(X)\|_1}{\|X\|_1}.
\tag{20.5}
$$

The supremum includes arbitrary complex matrices, not just densities.
Vector norms are Euclidean; $\|L\|_{\rm HS}^2=
\operatorname{Tr}(L^\dagger L)$; $\|L\|_{\rm op}$ is the
largest singular value. A finite inaccessible reference is untouched
throughout the actual implementation.

**Theorem 20.4 (finite-event control of the complete weighted endpoint).**
For every $\theta\in\mathbb R$, $n\ge0$, complete kernel of
Definition 1.2, and common full-$H$ decoder family of Definition
11.1, set $\mathcal R=\mathcal R(T)$ using (20.2) and (20.4).
Then

$$
\begin{aligned}
\|\Gamma_{ha}-\Gamma^0_{ha}\|_\diamond
&\le\min\{2,250\sqrt{\mathcal R}\},\\
\|\Gamma_a-\Gamma^0_a\|_\diamond
&\le\min\{2,250\sqrt{\mathcal R}\}
 \le\min\{2,750\sqrt{\max_i f_i(T)}\}.
\end{aligned}
\tag{20.6}
$$

The first inequality also controls any actually retained subrecord,
and all the inequalities hold with every finite untouched reference.
No branch is reweighted; no lower bound on a positive $p_{h,a}$
is required. The numerical constants are conservative evaluated
constants, with no optimality assertion.

Proof. First fix any CPTP $\Phi:M_3\to M_5$ and a finite Kraus
family $L_\nu$. Put $c_\nu=p^\dagger L_\nu v$ and
$\mathbf c=\sum_\nu c_\nu|\nu\rangle$. The **single-Kraus**
inequality of [STR] (13.35)–(13.38), also used in its
(19.21)–(19.23), before its summation
against $\delta$, says

$$
\sum_\nu\|L_\nu-c_\nu B\|_{\rm HS}^2
 \le15000\sum_\nu q_\nu=15000\mathcal R(\Phi).
\tag{20.7}
$$

This directly reuses that proof's full-$H$ coercivity; it does not
infer a per-branch estimate from an averaged defect. Define the
isometric dilation $Wx=\sum_\nu L_\nu x\otimes|\nu\rangle$.
Trace preservation at $v$ gives, exactly,

$$
r^2:=\|\mathbf c\|^2=1-f_1(\Phi),\qquad0\le r\le1.
\tag{20.8}
$$

For $r>0$ take $\eta=\mathbf c/r$; for $r=0$ choose any unit
vector in that environment. Let $Ux=Bx\otimes\eta$. Both
$U,W$ are isometries. Applying (20.7) to $W-B\otimes\mathbf c$
and using $1-r\le\sqrt{1-r^2}$ gives

$$
\begin{aligned}
\|W-U\|_{\rm op}
&\le\sqrt{15000\mathcal R(\Phi)}+1-r\\
&\le(\sqrt{15000}+1)\sqrt{\mathcal R(\Phi)}.
\end{aligned}
\tag{20.9}
$$

The zero-$r$ case obeys the same inequality since then $f_1=1$.
The dilation trace-norm estimate used in (13.40)–(13.42) applies
to every complex $X$ and every finite reference: expand
$W_ZXW_Z^\dagger-U_ZXU_Z^\dagger$ as
$(W_Z-U_Z)XW_Z^\dagger+U_ZX(W_Z-U_Z)^\dagger$, use
$\|AXB\|_1\le\|A\|_{\rm op}\|X\|_1\|B\|_{\rm op}$,
and discard only the dilation environment by the completely
trace-norm contractive partial trace. Hence

$$
\|\Phi-\operatorname{Ad}_B\|_\diamond
 \le2(\sqrt{15000}+1)\sqrt{\mathcal R(\Phi)}
 \le250\sqrt{\mathcal R(\Phi)}.
\tag{20.10}
$$

Here $\sqrt{15000}<124$, so the displayed coefficient is
strictly smaller than $250$. This is the supplied stability mechanism
applied to the measured residual, rather than a new exponent result.

Apply (20.10) separately to each actual $\Phi_{h,a}$. Linearity
and positivity of (20.2) give

$$
\mathcal R(T)=\sum_{h,a}p_{h,a}\mathcal R(\Phi_{h,a}).
\tag{20.11}
$$

Triangle inequality in the direct-sum norm and Cauchy–Schwarz for
these **original** probability weights now yield

$$
\begin{aligned}
\|\Gamma_{ha}-\Gamma^0_{ha}\|_\diamond
&\le\sum_{h,a}p_{h,a}
      \|\Phi_{h,a}-\operatorname{Ad}_B\|_\diamond\\
&\le250\sum_{h,a}p_{h,a}\sqrt{\mathcal R(\Phi_{h,a})}
 \le250\sqrt{\mathcal R(T)}.
\end{aligned}
\tag{20.12}
$$

For a countable kernel the sums converge absolutely; the last
inequality follows first on finite subsets and then by their increasing
union. Every channel has diamond norm one, giving the independent
cap two for their difference. Summing over $h$, or applying the actual
classical subrecord map, is CPTP and cannot increase the norm.
Finally use (20.3). This proves (20.6). $\square$

The weighted statement includes correlations of the old record with
the decoded specimen and the inaccessible reference. It does not give
a uniform normalized guarantee on each rare record. For example the
direct-sum bound gives for an individual positive fine block only
$p_{h,a}\|\Phi_{h,a}-\operatorname{Ad}_B\|_\diamond\le
250\sqrt{\mathcal R}$, which loses its force as that weight tends
to zero. Conditioning on a later success event has the same
normalization problem. Exact equality at $\mathcal R=0$ follows
from the estimate and agrees with the already supplied Theorem 13.1;
finite experimental acceptance will not establish that equality.

## 21. Common legal successors and a credited low-port floor

**Definition 21.1 (admitted common finite continuation).** A continuation
has a fixed finite maximum number of stages. At each stage its next
CP instrument can depend on its actually retained old record, selector
and earlier continuation outcomes. The very same maps and physical
call rights must be available on the actual and comparison routes.
They act on accessible systems only and leave the inaccessible reference
untouched. Each instrument is complete: its sum is trace preserving,
with every success, failure, stop and other relevant outcome and its
remaining quantum successor included in the output. Finite or
countable outcome instruments must define normal trace-class maps.
Terminated branches can be padded by identity steps.

Legality includes the supplied control domains on all states that the
two routes can reach, readable record backing, addresses, clocks and
permissions through every use. It cannot be inferred from small trace
distance. An operation defined only on $R$ is not automatically a
legal operation on a leaked actual state; its full-$H$ implementation
or appropriate admitted interface must be supplied. A selector chosen
after decoding does not select a different recovery decoder. The
comparison index $h$ grants no continuation access to an unavailable
history. Consumed storage flags are not added to the old record.
The original decoder's declared output is $H$; its discarded local
environment is unavailable for later calls. An additional retained
quantum output or a retained specimen-dependent flag requires its
own specified joint comparison and is not silently appended to (20.4).

**Proposition 21.2 (preservation of the joint guarantee).** Every
continuation of Definition 21.1, including zero stages, defines a CPTP
map $\mathcal C$ on the actual retained interface. For every such
$\mathcal C$ and every finite inaccessible reference,

$$
\|\mathcal C\Gamma_a-\mathcal C\Gamma^0_a\|_\diamond
 \le\min\{2,250\sqrt{\mathcal R(T)}\}.
\tag{21.1}
$$

An accessible external finite selector or ancilla supplied in the same
state on the two routes is allowed as well, with arbitrary input
correlations covered by (20.5). No action on the inaccessible reference
is needed. Every specified final event therefore differs in probability
by at most $\min\{1,125\sqrt{\mathcal R(T)}\}$ on any joint
input density. This last assertion concerns unnormalized event laws,
not states normalized on that event.

Proof. A complete instrument, with its outcome label and quantum
successor, is CPTP into its direct sum. Controlling its next stage by
an already present classical outcome preserves that property.
Induction over the finite number of stages gives $\mathcal C$;
normality handles the countable direct sums. Complete trace-norm
contraction and (20.6) give (21.1), also after adjoining an accessible
selector to the input reference space and then acting on that selector.
For a joint density the final difference is Hermitian of trace zero.
The supremum of its expectation against an effect in $[0,I]$ is
half its trace norm, giving the event bound. Completeness is essential:
normalizing a selected successful block is nonlinear and is not the
map just proved contractive. $\square$

For example, if the terminal binary readout is installed as its
Lüders instrument, the immediate implementation retains
$\bigoplus_yP_yYP_y$, with $P_1=P$ and $P_0=I_5-P$. The one-step
implementation with the actual acquisition operators then retains

$$
Y\longmapsto\bigoplus_{j,y}P_yA_jYA_j^\dagger P_y,
\qquad\sum_{j,y}(P_yA_j)^\dagger(P_yA_j)=I_5.
\tag{21.2}
$$

Thus (21.1) keeps $a,j,y$ and the residual specimen as well as its
reference. It does not substitute a fair coin for $j$ on leaked states.
The readout's effects alone do not prescribe its quantum successor;
another installed complete readout uses its own common CP blocks
instead and obeys the same (21.1).
Repeating common legal stages preserves the same bound, rather than
adding a new error allowance at every stage; the comparison is the
composition of the same channels with the two initial endpoints.
Different implementations at later stages would require additional
error hypotheses and are not covered by that statement.

**Corollary 21.3 (an explicit full-H low-port error floor).** Impose
exactly the storage restriction of Definition 14.1: each old record
selects a finite specimen-dependent classical flag alphabet, encoding
through $M_q$, and a complete whole-block decoder to $M_5$; the
same actual flag is used on both sides and is consumed by decoding.
All input-dependent quantum information crosses that bottleneck, with
no specimen, environment, reference or entanglement bypass. The old
record remains the original complete $a$, with no bound on its finite
or countable alphabet. For $q=1$ or $q=2$, every such scheme obeys

$$
\begin{aligned}
\mathcal R(T)&\ge\frac{3-q}{15000+3-q},\\
\max_i f_i(T),\ \delta_\theta(T)
 &\ge\frac{3-q}{9(15000+3-q)}.
\end{aligned}
\tag{21.3}
$$

For $q=2$ these lower bounds are $1/15001$ and $1/135009$;
for $q=1$ they are $1/7501$ and $1/67509$, respectively.
They hold at every real angle and at $n=0$. They are not optimal
coefficients or new coherent-dimension classifications.

Proof. Reuse the same-flag product (14.3), supplied by
[CoherentFlagPort][CFP] (including its `flagged_kraus_product`
step) and [FiniteKrausRepresentation][KRAUS]. For each actual
branch its Kraus matrices have the form
$L=D_{a\ell\beta}E_{a\ell\alpha}BQ_h$ and rank at most $q$.
For $c=p^\dagger Lv$, choose $3-q$ orthonormal vectors in
$\ker L$. On each such vector $x$, $(L-cB)x=-cBx$, whence

$$
(3-q)|c|^2\le\|L-cB\|_{\rm HS}^2\le15000q_L.
\tag{21.4}
$$

The second inequality is the already supplied per-Kraus estimate,
not a new compression-rigidity argument. Sum first over this actual
Kraus family and then over the unchanged $p_{h,a}$. Equation
(20.8) and linearity give
$(3-q)(1-f_1(T))\le15000\mathcal R(T)$.
Since $f_1(T)\le\mathcal R(T)$, rearrangement gives the first
line of (21.3); (20.3) gives the second. $\square$

Bluhm–Rauber–Wolf [arXiv:1708.04898v4][BRW], Definition 4.1
and Lemma 5.2, supply the classical-quantum port model and composite
Kraus rank bound; their Theorem 5.1 already proves a qualitative
positive approximate-compression floor by compactness. Corollary
21.3 is a short evaluated consequence for this source's rectangular
corner and actual labelled tests. It does not claim a new qualitative
incompressibility principle. A holding channel can be absorbed in
the codecs only if the whole holding interval satisfies the same
complete bottleneck and flag conditions. Merely naming a nominal
$q$-level subsystem while another quantum carrier survives does
not satisfy the hypothesis.

## 22. A paid finite campaign and subsequent unknown-input calls

**Definition 22.1 (calibrated repeatable fixed installation).** The
following are additional operational premises, not conclusions from
the event data. A model instance supplies a known $n$, a specified
real $\theta$, the actual original preparation/interaction/environment
measurement of Definition 1.1, the binary terminal instrument, a
complete input-independent $r$, and one installed full-$H$ recovery
service $a\mapsto\mathcal D_a$. The actual recovery service may be
imperfect. If it includes encoding, storage and decoding, their chosen
holding duration and whole interface are fixed and included in this
service. Its map is the same CPTP map on each invocation and on later
unknown-input use. It receives no configuration tag or terminal-choice
input. The source instrument, preparation and terminal measurement are
calibrated as specified, including their action outside $R$ where
required. The calibration and the fixed-device premise are supplied,
not tested by this campaign.

There are trusted callable preparations of all nine initial states in
Definition 20.1 on expendable campaign specimens, and reset services
for the apparatus and its control/environment workspaces. Fresh ready
environments, preparations, private randomness and resets make the
completed trial laws independent, with no retained hidden campaign
memory, drift, or campaign/later-use switch. These requirements concern
the entire same installed acquisition/record/recovery apparatus, not
only its visible $H$ register. The event experiment is chosen after
the common recovery and cannot alter that recovery. Preparing an
input state remains an allowed quantum input to the same channel;
no classical label identifying it is passed to the channel.

The installation also supplies actual call rights and backing: source
and reset access, a terminating callable record processor, full-$H$
decoder/codec controls, readable addresses and record capacity, control
code, clock, holding service and continuation permissions for their
required lifetimes. Countable records have specified finite encodings
on each returned call; the ideal untruncated service must realize the
given complete kernel and terminate with finite charged resources
almost surely. No uniform cost bound for it is inferred from its
finite description. A campaign controller has a supplied interruptible
finite resource cap, using integer metered operation units, finite
record capacity and finite elapsed-time limits, and rejects if any
limit would be exceeded. The cap includes its own schedule/event
bookkeeping and all trial services. This supplies a finite campaign
even for a countable service without a uniform completion bound.
The cap is a rejection rule, not a truncated replacement for $r$ or
$\mathcal D_a$ in (20.4).
Metering and any reported service-failure status refer to this faithful
untruncated implementation: they can interrupt and reject its run,
but do not substitute a different map on accepted transcripts. This
permits coupling the capped campaign to independent untruncated trials.

All setup, calibration, code, known-state preparation, source calls,
record work, resetting, storage and later use are charged on this
same installation. The known preparation/reset rights concern only
the expendable campaign specimens. A later unknown specimen, and its
inaccessible reference, have no supplied clone, reset, state-read or
reference-access operation. They arrive with the original embedded
input contract and are used once through the installed process.

For arbitrary real $\theta$, an exact calibrated control service in
this model is an analytical supplied-control premise. It is not an
algorithm for learning a real calibration, comparing exact-real
words or synthesizing these controls. An effective specialization
must specify its finite control library and encodings separately.

**Theorem 22.2 (exact finite decision rule and uniform false acceptance).**
Input a model instance of Definition 22.1, a rational
$0<\eta<2$, a positive integer $k$, and a finite resource cap.
Compute the integer

$$
m=\left\lceil\frac{62500k}{\eta^2}\right\rceil.
\tag{22.1}
$$

In the fixed order $1,\ldots,9$, execute exactly $m$ trials of
each configuration, with fresh known specimens and the required
resets, at the fixed holding duration when storage is tested. Keep
the complete actual outcome/record during each trial. Reset after
each trial, including the last trial before subsequent use. The
controller accepts if and only if all $9m$ trials complete within
the cap and no designated bad event occurs. A missing outcome,
service failure, cap exhaustion or failed reset rejects. Its event
decision uses only the exact discrete outcomes and an accumulated
Boolean conjunction; it makes no real-valued frequency comparison.

For every fixed installed device satisfying the model, write
$\mathcal E=\|\Gamma_{ha}-\Gamma^0_{ha}\|_\diamond$ for its
untruncated service. If $\mathcal E>\eta$, then

$$
\Pr(\mathrm{accept})\le e^{-k}\le2^{-k}.
\tag{22.2}
$$

The bound is uniform over all such full-complex devices, record
kernels, finite references, real angles and horizons, with the model's
fixed supplied apparatus and controls. In particular it bounds false
acceptance of the claim that the actual retained endpoint and every
admitted common finite legal continuation have diamond error at most
$\eta$. It is a frequentist false-acceptance bound, not a conditional
probability that an accepted device is good.

Proof. For the untruncated independent trials the all-pass probability
is exactly

$$
\prod_{i=1}^9(1-f_i(T))^m
 \le\exp\left(-m\sum_{i=1}^9f_i(T)\right)
 =e^{-m\mathcal R(T)}.
\tag{22.3}
$$

This uses the elementary $1-x\le e^{-x}$ for $0\le x\le1$.
The cap/reset/failure rule can only remove accepting transcripts.
Equivalently couple it to the full independent sequence and reject
on the first interrupted prefix; every accepted transcript is still
an all-pass transcript. Theorem 20.4 implies that
$\mathcal E>\eta$ requires
$\mathcal R(T)>\eta^2/62500$. Equation (22.1) then makes
(22.3) at most $e^{-k}$. Since $e>2$, this is at most $2^{-k}$.
If a retained endpoint or an admitted continuation violates its
$\eta$ claim, (20.6) or (21.1) implies $\mathcal E>\eta$,
so the same bound covers the entire asserted family at once.
There is no union over reference dimensions or continuation choices.
$\square$

The trusted-preparation/testing and independent all-pass mechanism
are mature gate-verification ingredients: Zhu–Zhang,
[arXiv:1910.14032v2](https://arxiv.org/abs/1910.14032v2),
§III.A–B, equations (6)–(20). Here (22.3) is its elementary
balanced deterministic-schedule version. Their square unitary target,
process-fidelity and balanced/local-measurement optimality results
are not applied to this rectangular retained-record channel. Neither
the sample count (22.1), nine configurations nor the resource cap is
claimed optimal. An ideal zero-residual device passes all event tests;
a cap may still reject it for resources. For positive residual even
a device within the desired tolerance need not accept often.

For the low-port models of Corollary 21.3, the same campaign gives
the separate direct consequence

$$
\Pr(\mathrm{accept})
 \le\exp\left(-\frac{m(3-q)}{15000+3-q}\right),
\qquad q=1,2.
\tag{22.4}
$$

This rejects those bottlenecks through the measured residual; it is
not an assertion that (21.3) is a lower bound on every chosen
continuation's diamond error. A continuation can erase all outputs.

**Proposition 22.3 (what an accepted campaign permits one to call).**
Keep the same installation, holding duration, channel, record
processor, backing and rights after the campaign. Supply a new
arbitrary density $\rho$ on $\mathbb C^3\otimes Z$, with
finite inaccessible $Z$, initialized as
$(B\otimes I_Z)\rho(B^\dagger\otimes I_Z)$. Run the original
$n$ actual acquisitions, retain their actual complete record $a$,
invoke the same common recovery once, then select and execute any
admitted common finite legal continuation. The resulting joint law
is exactly $((\mathcal C\Gamma_a)\otimes\operatorname{id}_Z)
(\rho)$. If this device's $\mathcal E\le\eta$, its trace-norm
distance to the corresponding ideal joint law is at most $\eta$.
The evidence rule's chance of accepting a device for which this
uniform certificate fails is at most $2^{-k}$ under Definition 22.1.

Proof. The original restricted branch is
$2^{-n/2}BQ_h$ also on one tensor factor of an entangled input.
Thus the original chronological weights are exactly $p_{h,a}$,
and the physical composition is (20.4) followed by $\mathcal C$.
The norm assertion is (21.1) and (20.5). With a fixed memoryless
installation, conditioning on earlier campaign acceptance does not
change its later map. Theorem 22.2 supplies the stated error-control
interpretation of the decision rule. No campaign state or reference
is substituted for the newly arriving unknown input. $\square$

Acceptance does not logically prove $\mathcal E\le\eta$, exact
equality, stationarity or calibration. It does not give
$\Pr(\mathcal E>\eta\mid\mathrm{accept})\le2^{-k}$ without
additional prior and acceptance-probability assumptions. It also
does not certify normalized rare branches or permit access to $Z$.
Reuse after changing the device, holding duration, kernel, decoder,
calibration or its repeatability conditions falls outside the certificate.
Actual call rights are premises with lifetimes, not consequences of a
norm estimate or of retaining the word “accept”.

## 23. Same-installation resources and the remaining source boundary

**Definition 23.1 (costs of this campaign and its retained use).**
Setup is a paid finite resource vector: apparatus preparation and
calibration, source/terminal controls, the known-state library,
decoder and any encoder/holding service, record memory and addresses,
reset facility, controller/code, clocks, workspace and service rights.
These are installed once for this particular campaign and later call;
their physical capacities and lifetimes remain charged while retained.
No evidence trial creates or synthesizes them for free.

On a complete $9m$-trial campaign, before any later unknown use,
the exact operation counts in this interface are

| Paid operation | Count |
| --- | --- |
| Known initial $H$ preparations from (20.1) | $9m$ |
| Original acquisitions before recovery | $9mn$ |
| Common recovery invocations | $9m$ |
| Additional actual acquisitions for configurations $4$ through $9$ | $6m$ |
| Terminal binary task measurements | $9m$ |
| Completed post-trial resets, including the last | $9m$ |

Each of the $9mn+6m$ acquisitions pays one fresh environment
preparation, interaction, environment measurement and actual label
acquisition. Complete old-record processing, writes, reads, buffers,
random seeds, table selection and any archive are charged at their
actual sizes and lifetimes. The additional $j$ and $y$ outcomes and
the controller's trial counters and conjunction bit are charged too.
One may release a trial's records after its event has been evaluated
and its reset completed; retaining them longer incurs that retention.
An online conjunction does not erase the old-record resources needed
by that trial's actual decoder.

If the recovery service includes a codec, there are $9m$ encoder
and $9m$ decoder calls and $9m$ tested holding intervals of the
specified duration. The coherent $q$-port capacity, physical carrier,
consumed flag capacity and flag lifetime are separate from the old
record's memory. The consumed flags are not retained as a free extra
output or side channel. The campaign's cap bounds the charged trial
resources and gives rejection on overflow; an early rejection pays
its incurred setup and prefix costs even if fewer operations complete.

After acceptance the one later unknown-input use pays a further $n$
original acquisitions, actual record work, one invocation of the same
recovery and, if present, its encoder, holding interval and decoder.
It then pays every stage, outcome, control and retained successor of
the chosen continuation. The immediate task adds one binary test;
the original labelled one-step task adds one actual acquisition and
one binary test. Unknown input arrival supplies no known-state
preparation right for that input. Its inaccessible reference is not
an installed memory or a usable bypass. Setup resources that remain
available for these calls retain their actual capacity, service fees
and lifetime costs. The sum of setup, campaign and later-use resource
vectors is the cost of this construction; no scalar optimum or
combination of separately optimal resources is asserted.

**Proposition 23.2 (a finite effective supplied-control specialization).**
At $\theta=0$ or $\theta=\pi/6$, fix any finite known $n$.
Supply exact callable algebraic preparations (20.1), the calibrated
original instrument and terminal test, a reset library, and the
inverse-letter/full-$H$ extensions of the acquired controls in
ERM Theorem 16.1 and §15. With the full chronological record
$r(a\mid h)=\mathbf1_{a=h}$ and finite backing for its $n$
bits, the campaign controller and later unknown-input call have a
finite explicit interface. If these primitive services have supplied
finite per-call bounds, a finite cap can accommodate every trial.
An exact recovery instance exists with zero residual; testing arbitrary
fixed imperfect instances uses Theorem 22.2 rather than an assumed
ideal decoder.

Proof. The full-history service records the $n$ labels actually
obtained. It selects the existing inverse $Q_h^\dagger$ on $R$,
with the complete full-$H$ extension already used in §§14–15.
Execution uses $n$ inverse-letter invocations in reverse chronological
order and then the supplied common output interface; $n=0$ uses
no inverse or history bits. The existing acquired upper restores
$B\rho B^\dagger$ with every finite inaccessible reference, so
(20.2) has zero residual. All preparations (20.1) have algebraic
coordinates at these two angles. The finite **supplied** library
includes their physical preparation maps and the inverse letters;
this is not a claim to synthesize arbitrary algebraic unitaries from
an unspecified gate set. Integer counters for $m$, the finite record
and discrete event rule complete the controller. Summing the supplied
finite bounds for the counts of Definition 23.1 gives a finite cap.
$\square$

This specialization uses one actual record/control scheme on every
trial and on later use. It does not combine the smaller single-task
effect record with a full-word inverse after that record has lost
information. The six-state full-word permutation accumulator at zero
angle and the $n$-label implementation at $\pi/6$ are the existing
ERM/§15 suppliers, not new acquisitions. For other real angles the
analytical theorem still covers **all** original kernels. Operational
use requires an actually callable implementation of the chosen one;
the existence of a finite table at a fixed horizon does not implement
an arbitrary exact-real table or make an arbitrary countable kernel
computable. A campaign cap does not give the untruncated later
service a uniform time or memory bound. Faithful later calls and
adequate backing remain additional obligations in that case.

**Proposition 23.3 (source subtraction with the actual observation and record domains).**
For the original mixture (20.4), the supplied STR19.1 applies to
$T$ and separately to every CPTP $\Phi_{h,a}$. Consequently it gives

$$
\begin{aligned}
\|T-\operatorname{Ad}_B\|_\diamond
 &\le418231548\,\delta_{2,\theta}(T),\\
\|\Gamma_{ha}-\Gamma^0_{ha}\|_\diamond
 &\le\min\left\{2,418231548\sum_{h,a}p_{h,a}
                       \delta_{2,\theta}(\Phi_{h,a})\right\}.
\end{aligned}
\tag{23.1}
$$

These are direct supplied consequences, not new stability claims.
In contrast, neither a uniform linear bound of the original endpoint
error by $\mathcal R(T)$ nor a uniform linear bound of its retained
endpoint error by the **average** $\delta_{2,\theta}(T)$ holds,
even locally on the admitted original domain. Thus replacing the
hypothesis or forgetting the old record would change the task.

Proof. The complete original weights sum to one, including for a
countable old record and $n=0$. Each $\Phi_{h,a}$ is CPTP, and
its norm-convergent weighted sum $T$ is CPTP on precisely $M_3$ to
$M_5$. Apply STR19.1 with those identical $B,P,A_j,\theta$.
The trace-class direct-sum triangle inequality gives the second line
of (23.1); each defect is at most one, so its weighted sum converges.
Convexity gives $\delta_{2,\theta}(T)\le
\sum p_{h,a}\delta_{2,\theta}(\Phi_{h,a})$, in the direction
that does **not** permit replacing this sum by the average defect.

For the residual distinction, take exactly STR17.1's $G,U_t,T_t$
at $\theta=0$, $0<t\le1/25$, with $n=0$, one old record and
full-$H$ decoder $\operatorname{Ad}_{U_t}$. This is an original
allowed scheme. By (20.3) and STR(17.5),
$\mathcal R(T_t)\le9\delta_0(T_t)\le450t^2$, whereas
$\|T_t-\operatorname{Ad}_B\|_\diamond\ge t$.
For any proposed finite linear coefficient choose sufficiently small
positive $t$; these inequalities contradict that coefficient, also
inside any positive residual threshold. This reuses the published
family and does not assert a new optimal-exponent theorem.

For the retained-record distinction use the same $G$, but take the
complete input-independent kernel $r(\pm\mid\varnothing)=1/2$
and the two common pre-choice full-$H$ decoders
$\operatorname{Ad}_{U_t},\operatorname{Ad}_{U_{-t}}$.
Then $T=(T_t+T_{-t})/2$ and
$\Gamma_a=\frac12T_t\oplus\frac12T_{-t}$, with ideal blocks
$\frac12\operatorname{Ad}_B$. The lawful density $xx^\dagger$
from STR(17.18) already gives
$\|\Gamma_a-\Gamma_a^0\|_\diamond\ge t/2$ from its plus block.
On the other hand, at every finite amplification the second derivative
of $X\mapsto U_sBXB^\dagger U_s^\dagger$ has trace norm at most
$4\|G\|^2\|X\|_1$. Taylor's integral remainder and cancellation
of the two first derivatives imply
$\|T-\operatorname{Ad}_B\|_\diamond\le
2\|G\|^2t^2\le50t^2$, using STR(17.11).
Every augmented effect is a positive contraction, so trace/operator
norm duality gives $\delta_{2,0}(T)\le
\|T-\operatorname{Ad}_B\|_\diamond\le50t^2$.
Again any proposed finite linear coefficient fails for small positive
$t$. This example uses an independently randomized **old** record,
not a retained specimen-dependent storage flag, and adds no output
support restriction. It is compatible with STR19.1's average estimate.
$\square$

The common finite continuations of §21 remain applicable to the full
weighted endpoint of Theorem 20.4. Forgetting $a$ would instead permit
only an average comparison unless its required joint guarantee were
proved separately. Neither (23.1) nor STR19.1 installs call rights,
preparations, calibrated instruments, resets, independent trials or a
fixed campaign/later-use channel. Those remain exactly Definition 22.1's
added premises. Its false-acceptance control and later calls retain
Theorem 22.2 and Proposition 22.3 with their original nine configurations,
$9m$ trials, $m=\lceil62500k/\eta^2\rceil$, and all costs of §23.
The credited low-port bound of Corollary 21.3 still uses STR13.38's
per-Kraus residual and the same consumed-flag product; STR19.1 asserts
no new port or old-record resource minimum. The finite panel, weighted
endpoint, campaign and installed-use conclusions here have the stated
residual and operational premises; the average theorem instead uses its
augmented uniform defect.

Mayer–Knill [arXiv:1805.04491v1](https://arxiv.org/abs/1805.04491v1),
Theorems 1–3, concerns square channel survival of spanning connected
pure states and its process-fidelity estimates. Its exact result and
the private `dual_fixed`, `kraus_commutes_projection` and
`overlap_scalar` steps of [ProbeComponentRigidity][PCR] are existing
square suppliers; neither is silently applied to leaked rectangular
outputs. The rectangular coercivity used here is precisely §13.3.
The exact full-word/port classification and attained reference law
are already §§11, 13–15. Theorem 17.1 supplies the optimal uniform
local exponent on unrestricted full-$H$ outputs, including its lawful
zero-angle examples; Theorem 18.1 supplies the global linear estimate
under exact output support in $R$. STR19.1 supplies the global
unrestricted-output average bound for its augmented depth-two defect,
with constants and persistence as stated above. All these source results
are supplied, not open obligations or new contributions here.
Sections 20–23 retain the original unrestricted output, old-record
and observation domains. Their source-relative increment is the positive residual's
finite laboratory interface, its complete weighted retained-record use
and common legal successors, and the paid independent fixed-device
campaign with later calls. These are `repo-derived` conditional theory
synthesis from those suppliers, not a replacement proof of their claims
or a worldwide novelty claim.

The distinct published source [FIB native paid-point observation
tracking](FIB_NATIVE_PAID_POINT_OBSERVATION_TRACKING.md),
§§60–65, keeps its native $\lambda=0$, fixed signed $\nu\ne0$
diffusion, finite fixed Borel report, independent seed and positive-gap
history. Its live-volume/face-mass certificates and original-law
occupation-loss boundary do not supply quantum preparations, resets
or fixed-device stationarity for Definition 22.1. Conversely this
campaign proves none of those native-source acquisition questions.
Its known preparations are explicitly added rights on expendable
specimens, rather than an inverse inferred from documentary agreement.
The analytic seam and one-face results of
[FIB native central-noise Green stability](FIB_NATIVE_CENTRAL_NOISE_GREEN_STABILITY.md),
§§26–35, already give their uniform modal energy/rank estimates,
raw unit-pole Green and exit-flux correspondences, and original-clock
resolvent/semigroup recovery on the declared cylinder. Their boundary
input is a complex $L^2$ forcing family, with bounded complex-linear
operator-norm approximation; it is not this finite collection of
quantum preparation/event trials. The original killed realization and
the one-face mixed realization also retain their stated distinction.
Those analytic identities install no forcing, sensing or reset service
and supply neither the fixed repeatable quantum channel nor the paid
calibrated controls of Definition 22.1.

The contribution relates finite actual observations to the usability
of one acquired memory interface of the original source. Chronology
is still its actual acquisition word; the boundary is its complete
late instrument; retained memory is the old record and the decoded
quantum specimen with its preserved reference correlations. These
objects come from one process with the original weights, not separate
marginal optima. No hidden full-history copy is supplied by the
comparison index in (20.4). There is no new independent spatial metric
or incidence view, duration recovery, unknown-calibration acquisition,
general physical installation or universal alpha/beta reduction here.
The fixed-apparatus/original-Q, parked-consumer, unchanged-initialization,
atomic/quantum common-source and unbounded-horizon obligations retain
their original scopes, as does the original critical causal-memory
estimate. Their resolution, calibration/retention
robustness beyond the stipulated model, and practical or total-resource
parsimony remain outside this finite application. These are analytical
theory statements; no Lean certification or completion of the continuing
four-expression programme is asserted.


[STR]: RECURSIVE_RELATIONAL_OBSERVATION_SHARP_TASK_RETAINED_ENVIRONMENT_MEMORY.md
[ERM]: AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[BRW]: https://arxiv.org/abs/1708.04898v4
[CFP]: ../../../D5/S3/Quantum/Reduction/CoherentFlagPort.lean
[KRAUS]: ../../../D5/S3/Quantum/Foundation/FiniteKrausRepresentation.lean
[PCR]: ../../../D5/S3/Quantum/Reduction/ProbeComponentRigidity.lean

## 追加锚（本行以下为增补区）

## 27. Uniform square-root stability of the original erased successor

**Theorem 27.1 (Unrestricted erased-successor stability).**
Keep exactly $B,E,P$ of [STR], Definitions 1.1–1.2 and (19.1),
and the actual full-$H$ operators $A_j(\theta)$ of [STR],
Definition 11.1 and (19.2), on $H=\mathbb C^5$. For every fixed
known real $\theta$, define

$$
\begin{aligned}
\Phi_\theta(Y)&=\sum_{j=0}^1 A_j(\theta)YA_j(\theta)^{\dagger},\\
J_0&=P,\qquad J_1=\sum_{j=0}^1 A_j^{\dagger} PA_j,\\
J_2&=\sum_{j,k=0}^1(A_kA_j)^{\dagger} P(A_kA_j).
\end{aligned}
\tag{27.1}
$$

These are exactly the three completely unlabelled raw success
effects of [STR], (25.1), with chronological products $A_kA_j$
and the original joint weights. For every complex-linear
completely positive trace-preserving map
$T:M_3(\mathbb C)\to M_5(\mathbb C)$ with unrestricted output, put

$$
\delta_\theta(T)=\max_{r=0,1,2}
\bigl\|T^{\dagger}(J_r)-B^{\dagger} J_rB\bigr\|_{\mathrm{op}}.
\tag{27.2}
$$

Here a dagger on a map denotes its trace adjoint and
$\operatorname{Ad}_B(X)=BXB^{\dagger}$. For a complex-linear map
$\Lambda:M_3(\mathbb C)\to M_5(\mathbb C)$, use the full,
unhalved diamond norm

$$
\|\Lambda\|_\diamond=
\sup_{d\ge1}\ \sup_{0\ne Z\in M_d(\mathbb C)\otimes M_3(\mathbb C)}
\frac{\|(\operatorname{id}_{M_d}\otimes\Lambda)(Z)\|_1}{\|Z\|_1},
\qquad \|Z\|_1=\operatorname{Tr}\sqrt{Z^{\dagger} Z}.
\tag{27.3}
$$

Every finite untouched reference and every complex amplified input,
without positivity or Hermiticity restrictions, occurs in this
supremum. Uniformly in $\theta$ and $T$,

$$
\delta_\theta(T)\le1
\quad\Longrightarrow\quad
\bigl\|\Phi_\theta\circ T-
\Phi_\theta\circ\operatorname{Ad}_B\bigr\|_\diamond
\le1200\sqrt{\delta_\theta(T)}.
\tag{27.4}
$$

Thus $C=1200$ and $\eta=1$ are valid. There is no extra observation,
label or control, conditioning, output-support promise or reference
access in the hypotheses.

Proof. All inner products and matrices below are complex. Reuse the full-$H$ reduction
and exact matrices of [STR], Theorem 26.1, equations (26.4)–(26.9). The unitary
coefficient matrix mixing $(K_0,K_1)$ into $(A_0,A_1)$ gives, on the entire
$M_5(\mathbb C)$,

$$
\Phi_\theta(Y)=\mathcal G(Y)=K_0YK_0^{\dagger}+K_1YK_1^{\dagger}.
$$

Consequently both chronological effects are independent of $\theta$:
$J_1=\mathcal G^{\dagger}(P)$ and $J_2=(\mathcal G^{\dagger})^2(P)$. A dagger on a map
denotes its trace adjoint. Put

$$
D_+=B^{\dagger}(K_0+K_1)/\sqrt2,\qquad D_-=B^{\dagger}(K_0-K_1)/\sqrt2.
$$

The full-$H$ matrices, without input restriction, are

$$
D_+=\frac1{\sqrt2}\begin{pmatrix}1&1&0&0&0\\0&0&\sqrt2&0&0\\0&0&0&1&1\end{pmatrix},\quad
D_-=\frac1{\sqrt2}\begin{pmatrix}1&-1&0&0&0\\0&0&0&0&0\\0&0&0&-1&1\end{pmatrix}.
$$

Thus $D_+^{\dagger} D_++D_-^{\dagger} D_-=I_5$ and
$\operatorname{ran}D_-=N=\operatorname{span}\{(1,0,0)^{\mathsf T},(0,0,1)^{\mathsf
T}\}$, and

$$
\mathcal G(Y)=B(D_+YD_+^{\dagger}+D_-YD_-^{\dagger})B^{\dagger}.
\tag{27.5}
$$

Let $q=(\xi+e)/\sqrt2$, $r=(\xi-e)/\sqrt2$ and $f=(1,-1,0)^{\mathsf T}/\sqrt2$.
Define $a=D_+Bq$, $h=D_+Br$ and $g=D_-Bf=(1,0,-1)^{\mathsf T}/\sqrt2$. Then
$(q,r,f)$ and $(a,h,g)$ are orthonormal bases, and

$$
D_+Bq=a,\ D_-Bq=0,\ D_+Br=h,\ D_-Br=0,\ D_+Bf=0,\ D_-Bf=g.
\tag{27.6}
$$

In particular the target qutrit channel $R_0(X)=B^{\dagger}\mathcal
G(BXB^{\dagger})B$ maps $qq^{\dagger},qr^{\dagger},rq^{\dagger},rr^{\dagger}$ to
$aa^{\dagger},ah^{\dagger},ha^{\dagger},hh^{\dagger}$, respectively, maps $ff^{\dagger}$ to
$gg^{\dagger}$, and annihilates the four cross units involving $f$.

We reuse [STR], equations (26.5)–(26.9). Write $F=B^{\dagger} J_1B$, a positive
contraction. In the output basis $(a,h,g)$, the positive contractions $E,F$ are

$$
E=\frac1{16}\begin{pmatrix}1&3&\sqrt6\\3&9&3\sqrt6\\\sqrt6&3\sqrt6&6\end{pmatrix},\quad
F=\frac1{32}\begin{pmatrix}17&3&-\sqrt6\\3&9&-3\sqrt6\\-\sqrt6&-3\sqrt6&6\end{pmatrix}.
\tag{27.7}
$$

Moreover

$$
J_1=D_+^{\dagger}ED_++D_-^{\dagger}ED_-,\qquad
J_2=D_+^{\dagger}FD_++D_-^{\dagger}FD_-.
\tag{27.8}
$$

For the two target compressions $B^{\dagger} J_1B$ and $B^{\dagger} J_2B$, their $qr$
entries are $3/16$ and $3/32$, their $qf,rf$ entries are zero, and their $ff$
entries are $3/8$ and $3/16$, respectively. Their $q,r$ principal blocks are
respectively

$$
\begin{pmatrix}1/16&3/16\\3/16&9/16\end{pmatrix},\qquad
\begin{pmatrix}17/32&3/32\\3/32&9/32\end{pmatrix}.
\tag{27.9}
$$

These identities concern the original raw chronological sums, not conditional or
labelled effects.

Take a finite rectangular Kraus representation $T(X)=\sum_l L_lXL_l^{\dagger}$, with
$\sum_l L_l^{\dagger} L_l=I_3$. This is the standard finite-dimensional Kraus
representation: see M.-D. Choi, “Completely positive linear maps on complex
matrices,” *Linear Algebra and its Applications* **10** (1975), 285–290,
[doi:10.1016/0024-3795(75)90075-0](https://doi.org/10.1016/0024-3795(75)90075-0).
For this representation and the trace-norm facts used below, see also John
Watrous, *The Theory of Quantum Information*, Cambridge University Press (2018),
[Chapters 1–3](https://cs.uwaterloo.ca/~watrous/TQI/). Set $X_l=D_+L_l$ and
$Y_l=D_-L_l$. Then

$$
\sum_l(X_l^{\dagger}X_l+Y_l^{\dagger}Y_l)=I_3,\qquad \operatorname{ran}Y_l\subset N,
\tag{27.10}
$$

and the channel $R(X)=\sum_l(X_lXX_l^{\dagger}+Y_lXY_l^{\dagger})$ satisfies
$\mathcal G\circ T=\operatorname{Ad}_B\circ R$. By (27.6), $P$ corresponds under
the isometry $x\mapsto(D_+x,D_-x)$ to the projection onto $(a,0)$. All estimates
below therefore apply to every original $T$.

Write $\delta=\delta_\theta(T)$ and $\epsilon=\sqrt\delta$, with $0\le\delta\le1$.
For a sequence of vectors, its norm means the square root of the sum of squared
norms. In particular (27.10) says that the combined sequence $(X_lz,Y_lz)_l$ has
norm one for each unit $z$. We repeatedly use

$$
\left\|\sum_l v_lw_l^{\dagger}\right\|_1\le
\left(\sum_l\|v_l\|^2\right)^{1/2}
\left(\sum_l\|w_l\|^2\right)^{1/2}.
\tag{27.11}
$$

This follows from the trace norm of a rank-one matrix, the triangle inequality
and Cauchy–Schwarz.

First put $\alpha_l=a^{\dagger} X_lq$, $A=\sum_l|\alpha_l|^2$ and
$e_l=X_lq-\alpha_la$. Positivity, trace preservation and the $J_0$ defect give

$$
1-\delta\le A\le1,\qquad
\sum_l(\|e_l\|^2+\|Y_lq\|^2)=1-A\le\delta,
\qquad
\sum_l|a^{\dagger}X_l z|^2\le\delta\quad(z=r,f).
\tag{27.12}
$$

Here the last inequality uses the zero target $J_0$ expectation on $r,f$.

We next extract two spectral estimates using only $J_1+2J_2$. Put $Q=E+2F$,
$b=(a+h)/\sqrt2$ and $k=(1,0,1)^{\mathsf T}/\sqrt2$; $b$ here is a local proof
vector. Formula (27.7) gives on the whole plus output space and on $N$,
respectively,

$$
Q=\tfrac34 I_3+\tfrac34 bb^{\dagger},\qquad
Q|_N=\tfrac34 I_N+\tfrac12 kk^{\dagger}.
\tag{27.13}
$$

Here $Q|_N$ denotes compression to $N$. The block operator $H_Q=Q\oplus Q|_N$ has
minimum $3/4$ and maximum $3/2$, attained only on the line $(b,0)$. Its
restriction to the orthogonal complement of that line has eigenvalues at most
$5/4$. If $s=(q+r)/\sqrt2$, (27.9) gives the target expectations

$$
s^{\dagger}B^{\dagger}(J_1+2J_2)Bs=\tfrac32,\qquad
f^{\dagger}B^{\dagger}(J_1+2J_2)Bf=\tfrac34.
\tag{27.14}
$$

The operator defect for this combination is at most $3\delta$. The maximum in
(27.14), the gap $1/4$ and (27.10) imply

$$
\|(Y_l s)_l\|\le\sqrt{12}\,\epsilon,
\qquad
\|(Y_l r)_l\|\le\sqrt2\|(Y_l s)_l\|+\|(Y_l q)_l\|
\le(\sqrt{24}+1)\epsilon\le6\epsilon.
\tag{27.15}
$$

The minimum in (27.14) instead gives

$$
\tfrac34\sum_l|b^{\dagger}X_l f|^2+
\tfrac12\sum_l|k^{\dagger}Y_l f|^2\le3\delta.
\tag{27.16}
$$

Together with (27.12) and $h=\sqrt2b-a$, this yields sequence bounds

$$
\|(a^{\dagger}X_lf)_l\|\le\epsilon,\quad
\|(h^{\dagger}X_lf)_l\|\le(2\sqrt2+1)\epsilon\le4\epsilon,\quad
\|(k^{\dagger}Y_lf)_l\|\le\sqrt6\epsilon\le3\epsilon.
$$

Define $\beta_l=g^{\dagger} X_lf$, $\gamma_l=g^{\dagger} Y_lf$, $u_l=X_lf-\beta_lg$
and $v_l=Y_lf-\gamma_lg$. The bases $(a,h,g)$ of $\mathbb C^3$ and $(k,g)$ of $N$
are orthonormal, so the preceding inequalities imply

$$
\sum_l(\|u_l\|^2+\|v_l\|^2)\le36\delta,
\quad n:=\sum_l(|\beta_l|^2+|\gamma_l|^2)\le1,
\quad 1-n\le36\delta.
\tag{27.17}
$$

The displayed component bounds already give $1+16+9<36$.

For $z=r,f$, let $M_z=\sum_l\overline{\alpha_l}X_lz$. By (27.12), $|a^{\dagger}
M_z|\le\epsilon$. Replacing the $q$ column by $(\alpha_la,0)$ in each of the
$J_1,J_2$ cross moments costs at most $\epsilon$, by (27.11), (27.12), (27.10) and
the contraction norms of $E,F$. The original operator defects cost at most
$\delta\le\epsilon$. Thus, with $d_r=1$ and $d_f=0$,

$$
|a^{\dagger}EM_z-3d_z/16|\le2\epsilon,\qquad
|a^{\dagger}FM_z-3d_z/32|\le2\epsilon.
\tag{27.18}
$$

Write $M_z=xa+yh+tg$. Multiplication by $16$ and $32$ in (27.18) gives

$$
|x+3y+\sqrt6t-3d_z|\le32\epsilon,\quad
|17x+3y-\sqrt6t-3d_z|\le64\epsilon,\quad |x|\le\epsilon.
$$

Adding and subtracting these complex equations proves

$$
|y-d_z|\le19\epsilon,\qquad
|t|\le(56/\sqrt6)\epsilon\le23\epsilon.
$$

Consequently

$$
\|M_r-h\|\le30\epsilon,\qquad \|M_f\|\le30\epsilon,
\tag{27.19}
$$

since $\sqrt{1+19^2+23^2}<30$. There is no reality restriction on $x,y,t$.

We now bound all nine complex matrix units. Equations (27.11), (27.12), and
(27.19) directly give

$$
\|R(qq^{\dagger})-aa^{\dagger}\|_1\le2\delta+2\epsilon\le4\epsilon,
\quad
\|R(qr^{\dagger})-ah^{\dagger}\|_1\le31\epsilon,
\quad
\|R(qf^{\dagger})\|_1\le31\epsilon.
\tag{27.20}
$$

For the second and third inequalities, $R(qz^{\dagger})=aM_z^{\dagger}$ plus an error
of trace norm at most $\epsilon$. For the first, expand $X_lq=\alpha_la+e_l$; the
coefficient error is at most $\delta$, the two cross terms total at most
$2\epsilon$, and the remaining positive terms have trace at most $\delta$.

Set $d_l=X_lr-\alpha_lh$. Then (27.10), (27.12) and (27.19) yield

$$
\sum_l(\|d_l\|^2+\|Y_l r\|^2)
=1+A-2\operatorname{Re}(h^{\dagger}M_r)\le60\epsilon.
\tag{27.21}
$$

Also the vector $\sum_l\overline{\alpha_l}d_l=M_r-Ah$ has norm at most
$31\epsilon$. Expanding the $rr$ output as its $Ahh^{\dagger}$ term, its two cross
terms and its positive remainder, and using (27.21), proves

$$
\|R(rr^{\dagger})-hh^{\dagger}\|_1\le\delta+62\epsilon+60\epsilon
\le123\epsilon.
\tag{27.22}
$$

Similarly, expanding (27.17), the two cross terms for $ff$ have total trace norm
at most $2\sqrt{n(1-n)}\le12\epsilon$, and its coefficient error and positive
remainder total $2(1-n)\le72\delta$. Hence

$$
\|R(ff^{\dagger})-gg^{\dagger}\|_1\le84\epsilon.
\tag{27.23}
$$

For completeness, the $rf$ unit requires the leakage estimate (27.15). Write

$$
R(rf^{\dagger})=w g^{\dagger}+H_0,\qquad
w=\sum_l(\overline{\beta_l}X_l r+\overline{\gamma_l}Y_l r).
$$

By (27.11) and (27.17), $\|H_0\|_1\le6\epsilon$. Write $w=xa+yh+tg$. Equations
(27.12), (27.15) and $n\le1$ give $|x|\le7\epsilon$. Trace preservation on
$rf^{\dagger}$ gives $\operatorname{Tr}R(rf^{\dagger})=0$, so $|t|=|g^{\dagger}
w|\le6\epsilon$. The original $J_1$ cross defect and (27.8) imply

$$
|\operatorname{Tr}(E R(rf^{\dagger}))|\le\delta,
\qquad |g^{\dagger}Ew|\le\delta+6\epsilon\le7\epsilon.
$$

Using the $g$ row of (27.7),

$$
3\sqrt6\,|y|\le112\epsilon+\sqrt6|x|+6|t|
\le(148+7\sqrt6)\epsilon\le23(3\sqrt6)\epsilon.
$$

Thus $\|w\|\le\sqrt{7^2+23^2+6^2}\epsilon\le25\epsilon$ and

$$
\|R(rf^{\dagger})\|_1\le31\epsilon.
\tag{27.24}
$$

The three reversed cross units obey the same bounds because $R,R_0$ preserve
adjoints. Equations (27.20), (27.22)–(27.24) therefore prove, for every $i,j$ in
the orthonormal basis $(q,r,f)$,

$$
\|(R-R_0)(|i\rangle\langle j|)\|_1\le123\epsilon.
\tag{27.25}
$$

Finally, fix any finite reference dimension $d$ and any complex matrix $Z\in
M_d(\mathbb C)\otimes M_3(\mathbb C)$, with no positivity or Hermiticity
restriction. Expand

$$
Z=\sum_{i,j}Z_{ij}\otimes|i\rangle\langle j|.
$$

Each block is a left and right compression by operators of norm one, so the
trace-norm ideal inequality gives $\|Z_{ij}\|_1\le\|Z\|_1$. Trace-norm
multiplicativity on tensor products and (27.25) imply

$$
\| (\mathrm{id}_{M_d}\otimes(R-R_0))(Z)\|_1
\le\sum_{i,j}\|Z_{ij}\|_1\,
\|(R-R_0)(|i\rangle\langle j|)\|_1
\le1107\epsilon\|Z\|_1.
$$

This bound holds simultaneously for every $d$ and every nonzero complex $Z$.
Postcomposition by the isometry $B$ preserves trace norms at every reference
dimension: conjugation by $I_d\otimes B$ preserves the nonzero singular values of
every matrix. Equations (27.5)–(27.6) and the full-$H$ $\theta$ cancellation
therefore give the claimed unhalved diamond bound, with $1107\le1200$. The
argument also includes $\delta=0$. This proves the theorem. $\square$

The full-$H$ reduction and exact matrices in (27.5)–(27.9) are
reused from [STR], Theorem 26.1. The new quantitative inference
is the simultaneous use of the global minimum and maximum in
(27.13)–(27.16), followed by the nine matrix-unit estimates and
the explicit reference-independent amplification. The zero-defect
source alone does not supply this inference. The two Kraus
summands and their linear combinations are internal proof
coordinates, not accessible additional detectors or branch labels.
The conclusion concerns the erased successor; [STR], Theorem 25.1,
retains its distinct preceding-channel counterexample. There is no
claim of optimal constant or exponent, minimum resources, physical
realization or worldwide novelty.

## 追加锚（本行以下为增补区）

## 28. Sharp exponent for the original erased successor

**Definition 28.1 (Original complex model, raw defect and successor distance).**
Use the physical orthonormal basis $(e_0,\ldots,e_4)$ of
$H=\mathbb C^5$. The following are exactly the matrices of [STR],
Definitions 1.1–1.2 and 11.1, (19.1)–(19.2), (26.3):

$$
\begin{gathered}
u=(e_0+e_3)/\sqrt2,\qquad
v_H=(e_1+e_4)/\sqrt2,\qquad z_H=e_2,\qquad
B=(u,v_H,z_H),\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
e=(1,1,-2)^{\mathsf T}/\sqrt6,\qquad
f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
q=(\xi+e)/\sqrt2,\qquad r=(\xi-e)/\sqrt2,\qquad
p=Bq,\qquad E=qq^\dagger,\qquad P=pp^\dagger,\\
U=U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},
\qquad
W=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},
\qquad P_+=(I_3+W)/2,\qquad P_-=ff^\dagger,\\
\Delta_W(X)=P_+XP_++P_-XP_-.
\end{gathered}
\tag{28.1}
$$

In particular $(q,r,f)$ is an orthonormal basis, and
$\operatorname{ran}P_+=\operatorname{span}\{q,r\}$. For every fixed
known real angle $\theta$, retain the full-$H$ operators

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|
 +2^{-1/2}|v_H\rangle\langle e_2|+|z_H\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|
 +2^{-1/2}|v_H\rangle\langle e_2|+|z_H\rangle\langle e_3|,\\
A_0(\theta)&=\cos\theta K_0+i\sin\theta K_1,\qquad
A_1(\theta)=i\sin\theta K_0+\cos\theta K_1,\\
\Phi_\theta(Y)&=\sum_{j=0}^1 A_j(\theta)Y A_j(\theta)^\dagger,\\
J_0&=P,\qquad J_1=\sum_{j=0}^1 A_j^\dagger P A_j,\qquad
J_2=\sum_{j,k=0}^1(A_kA_j)^\dagger P(A_kA_j).
\end{aligned}
\tag{28.2}
$$

Thus the products are chronological, with $A_j$ acting first in
$A_kA_j$. These are the original completely unlabelled raw effects
of [STR], (25.1), with their original joint weights. For every
complex-linear CPTP map $T:M_3(\mathbb C)\to M_5(\mathbb C)$,
without an output-support restriction, set

$$
\begin{aligned}
\delta_\theta(T)&=\max_{s=0,1,2}
 \|T^\dagger(J_s)-B^\dagger J_sB\|_{\mathrm{op}},\\
d_\theta(T)&=\|\Phi_\theta\circ T
 -\Phi_\theta\circ\operatorname{Ad}_B\|_\diamond,\qquad
\operatorname{Ad}_B(X)=BXB^\dagger,\\
\|\Lambda\|_\diamond
 &=\sup_{d\in\mathbb N,\ d\ge1}\ \sup_{\substack{0\ne Z\in
 M_d(\mathbb C)\otimes M_3(\mathbb C)}}
 \frac{\|(\operatorname{id}_{M_d}\otimes\Lambda)(Z)\|_1}{\|Z\|_1},
 \qquad \|Z\|_1=\operatorname{Tr}\sqrt{Z^\dagger Z}.
\end{aligned}
\tag{28.3}
$$

The dagger on a map is its trace adjoint. The norm is full and
unhalved, over all complex amplified matrices, without positivity
or Hermiticity promises, and every finite untouched reference.
There is no additional observation, label, control, conditioning
or reference access in this definition.

**Theorem 28.2 (Coherent leakage and the optimal uniform exponent).**
With exactly Definition 28.1, put

$$
\begin{gathered}
c=(e_0+e_1-e_3-e_4)/2,\qquad
a=Uq,\qquad g=Uf=(1,0,-1)^{\mathsf T}/\sqrt2,\\
w_t=\sqrt{1-t^2}\,c+itp,\qquad
L_0=BP_+,\qquad L_{1,t}=w_tf^\dagger,\\
T_t(X)=L_0XL_0^\dagger+L_{1,t}XL_{1,t}^\dagger
\qquad(0<t<1).
\end{gathered}
\tag{28.4}
$$

For every such $t$, this is a complex-linear CPTP map on the full
stated domain, independent of $\theta$, and for every real
$\theta$ it satisfies the exact identities

$$
\delta_\theta(T_t)=t^2,\qquad d_\theta(T_t)=2t.
\tag{28.5}
$$

Consequently, for every real $\alpha>1/2$ and every $C,\eta>0$,
there exist a real $\theta$ and a complex-linear CPTP map
$T:M_3(\mathbb C)\to M_5(\mathbb C)$ such that

$$
0<\delta_\theta(T)\le\min\{\eta,1\},
\qquad d_\theta(T)>C\,\delta_\theta(T)^\alpha.
\tag{28.6}
$$

Together with Theorem 27.1, this makes exponent $1/2$ uniformly
optimal on the unrestricted original domain. The particular
two-Kraus witness is not an additional hypothesis on arbitrary $T$.

Proof. The coefficient matrix
$\left(\begin{smallmatrix}\cos\theta&i\sin\theta\\
i\sin\theta&\cos\theta\end{smallmatrix}\right)$ is unitary for
every real $\theta$. Hence, on every complex full-$H$ matrix,

$$
\Phi_\theta(Y)=\mathcal G(Y)
 :=K_0YK_0^\dagger+K_1YK_1^\dagger,\qquad
J_s=(\mathcal G^\dagger)^s(P)\quad(s=0,1,2).
\tag{28.7}
$$

This is the full-$H$ reduction of [STR], (25.4), (26.4)–(26.7);
in particular it applies to leaked outputs. Since $B,K_0,K_1,p$
are real in the physical basis, all three $J_s$ are real symmetric.

The original matrices in (28.1)–(28.2) give

$$
\begin{gathered}
c^\dagger c=1,\qquad B^\dagger c=0,\qquad
a^\dagger a=g^\dagger g=1,\qquad a^\dagger g=0,\\
K_0B=BU/\sqrt2,\qquad K_1B=BUW/\sqrt2,\\
K_0c=K_1c=Bg/\sqrt2,\qquad
K_0p=K_1p=Ba/\sqrt2.
\end{gathered}
\tag{28.8}
$$

Thus $\mathcal G\circ\operatorname{Ad}_B
=\operatorname{Ad}_{BU}\circ\Delta_W$. Put
$F=\Delta_W(U^\dagger EU)$ and $H_s=B^\dagger J_sB$.
The target compressions, as in [STR], (26.7)–(26.9) and
(27.7)–(27.9) above, are

$$
\begin{gathered}
H_0=E,\qquad H_1=F,\qquad H_2=\Delta_W(U^\dagger FU),\\
[H_0]_{(q,r,f)}=
 \begin{pmatrix}1&0&0\\0&0&0\\0&0&0\end{pmatrix},\\
[H_1]_{(q,r,f)}=
 \begin{pmatrix}1/16&3/16&0\\3/16&9/16&0\\0&0&3/8\end{pmatrix},
\qquad
[H_2]_{(q,r,f)}=
 \begin{pmatrix}17/32&3/32&0\\3/32&9/32&0\\0&0&3/16\end{pmatrix}.
\end{gathered}
\tag{28.9}
$$

These matrices are block diagonal for
$\operatorname{ran}P_+\oplus\mathbb C f$. The scalar entries needed
for the leaked preparation are

$$
\begin{array}{c|ccc}
s&0&1&2\\ \hline
c^\dagger J_sc&0&3/8&3/16\\
p^\dagger J_sp&1&1/16&17/32\\
f^\dagger H_sf&0&3/8&3/16
\end{array}.
\tag{28.10}
$$

For explicit scalar evaluation from the original coordinates,
write $q=(x,x,y)^{\mathsf T}$, where
$x=(\sqrt2+1)/\sqrt{12}$ and $y=(\sqrt2-2)/\sqrt{12}$.
Then $q^\dagger a=1/4$, $q^\dagger g=\sqrt6/4$; for every $z\in\mathbb C^3$,

$$
z^\dagger Fz=
 \frac{|q^\dagger Uz|^2+|q^\dagger UWz|^2}{2},
\qquad
a^\dagger Fa=17/32,\qquad g^\dagger Fg=3/16.
\tag{28.11}
$$

Together with (28.8), these identities give every entry of
(28.10): after one erased acquisition $cc^\dagger$ and
$pp^\dagger$ become $Bgg^\dagger B^\dagger$ and
$Baa^\dagger B^\dagger$, respectively.

Because $c\perp p$, the vector $w_t$ is unit, and

$$
L_0^\dagger L_0+L_{1,t}^\dagger L_{1,t}
 =P_++ff^\dagger=I_3.
\tag{28.12}
$$

The standard finite-dimensional Kraus criterion proves complete
positivity and trace preservation; the displayed formula is
complex-linear on every input matrix. This criterion is used
only as an intermediate ingredient; see John Watrous,
[The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/),
Chapters 2–3.

Since $c,p,J_s$ are real, the imaginary cross terms cancel exactly:

$$
w_t^\dagger J_sw_t
 =(1-t^2)c^\dagger J_sc+t^2p^\dagger J_sp.
\tag{28.13}
$$

The Kraus formula therefore gives
$T_t^\dagger(J_s)=P_+H_sP_+
 +(w_t^\dagger J_sw_t)ff^\dagger$. Using (28.9)–(28.10),

$$
\begin{aligned}
T_t^\dagger(J_0)-H_0&=t^2ff^\dagger,\\
T_t^\dagger(J_1)-H_1&=-\frac5{16}t^2ff^\dagger,\\
T_t^\dagger(J_2)-H_2&=\frac{11}{32}t^2ff^\dagger,
\qquad
ff^\dagger=\frac12
 \begin{pmatrix}1&-1&0\\-1&1&0\\0&0&0\end{pmatrix}.
\end{aligned}
\tag{28.14}
$$

Thus all entries of the three original raw operator defects,
including off-diagonal entries, are accounted for. As
$\|ff^\dagger\|_{\mathrm{op}}=1$, their maximum is exactly $t^2$.
No individually labelled or conditionally normalized effect is
used.

For the successor, set
$v_t=\sqrt{1-t^2}\,g+ita$. Equation (28.8) gives
$\mathcal G(w_tw_t^\dagger)=Bv_tv_t^\dagger B^\dagger$.
For every complex input $X$, the plus blocks of the two successors
coincide and both maps kill the cross blocks between $P_+$ and
$f$. Their difference is therefore the exact complex-linear map

$$
\begin{aligned}
\Lambda_t(X)
 &:=(\Phi_\theta\circ T_t
       -\Phi_\theta\circ\operatorname{Ad}_B)(X)\\
 &=(f^\dagger Xf)BD_tB^\dagger,\qquad
D_t=v_tv_t^\dagger-gg^\dagger.
\end{aligned}
\tag{28.15}
$$

In the orthonormal basis $(g,a)$ the only nonzero block of $D_t$ is

$$
\begin{pmatrix}
-t^2&-it\sqrt{1-t^2}\\
it\sqrt{1-t^2}&t^2
\end{pmatrix}.
\tag{28.16}
$$

Its trace is zero and its determinant is $-t^2$, so its eigenvalues
are $t,-t$. Isometric embedding by $B$ preserves the nonzero
singular values; hence $\|BD_tB^\dagger\|_1=2t$.
The legal density input $ff^\dagger$ with reference dimension one
already gives $\|\Lambda_t\|_\diamond\ge2t$.

To bound every allowed amplification, take any finite $d\ge1$
and any $Z\in M_d(\mathbb C)\otimes M_3(\mathbb C)$, without a
positivity or Hermiticity assumption. Define

$$
\begin{gathered}
Z_{ff}=(I_d\otimes f^\dagger)Z(I_d\otimes f),\\
(\operatorname{id}_{M_d}\otimes\Lambda_t)(Z)
 =Z_{ff}\otimes BD_tB^\dagger,\\
\|Z_{ff}\|_1\le\|Z\|_1,\qquad
\|(\operatorname{id}_{M_d}\otimes\Lambda_t)(Z)\|_1
 \le2t\|Z\|_1.
\end{gathered}
\tag{28.17}
$$

The compression inequality is the trace-norm ideal property,
since both compression factors have operator norm one; the last
inequality also uses multiplicativity of the trace norm on
tensor products. These standard facts may be found in Watrous,
Chapters 1–3. They apply to arbitrary complex $Z$. Taking both
suprema in (28.3) proves $d_\theta(T_t)=2t$, completing (28.5)
with the full unhalved convention and every finite untouched
reference.

Finally, given $\alpha>1/2$ and $C,\eta>0$, choose

$$
t=\frac12\min\left\{1,\sqrt\eta,
       (2/C)^{1/(2\alpha-1)}\right\},\qquad \theta=0.
\tag{28.18}
$$

Then $0<t<1$, $0<t^2\le\min\{\eta,1\}$ and
$t^{2\alpha-1}<2/C$. Equation (28.5) yields
$2t>C(t^2)^\alpha$, proving every quantifier of (28.6).
The same family in fact satisfies (28.5) for every real angle;
only the existence of one angle is needed for the uniform
optimality statement. Theorem 27.1 applies to all unrestricted
complex CPTP maps and supplies
$d_\theta(T)\le1200\sqrt{\delta_\theta(T)}$ when
$\delta_\theta(T)\le1$. Combining that upper bound with (28.6)
establishes the matched exponent, without determining the optimal
uniform coefficient. $\square$

Source correspondence for Theorem 28.2. The original model and raw
effects are [STR], Definitions 1.1–1.2 and 11.1, (19.1), (19.2),
(25.1). The real leaked vector $c$ and the $t=0$ channel come from
[STR], Theorem 25.1, (25.3)–(25.9). That channel has the same erased
successor as $\operatorname{Ad}_B$, so its preceding-channel
separation is not a successor lower bound. The full-$H$ reduction
and compressions are [STR], Theorem 26.1, (26.4)–(26.9);
its exact zero-defect rigidity is preserved. Theorem 27.1 supplies
the unrestricted upper bound only. [STR], Theorem 17.1, has
labelled defects and a preceding-channel distance, so its
lower-rate conclusion is not applied to (28.3). Relative to these
source statements, the additional inference is the imaginary
coherent perturbation in (28.4), its exact original raw defect
(28.14), the erased-successor norm (28.15)–(28.17), and the uniform
quantifier bridge (28.18). The Kraus and trace-norm facts are
mature intermediate ingredients. The witness Kraus summands are
proof coordinates, not newly accessible branch labels. This is
an analytic statement about the stipulated complex channels; it
does not assert physical realization, empirical validation,
minimum resources, an optimal global coefficient, worldwide
novelty or Lean verification.

## 追加锚（本行以下为增补区）
