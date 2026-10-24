# Recursive relational observation: sharp tasks, retained environment records and actual continuation

## 1. One measured source and three terminal contracts

This volume concerns the fixed known-horizon measured instrument of
[Environment instruments and terminal record memory][ERM], abbreviated ERM.
It keeps its actual labels, input domain and prohibition on intermediate
quantum feedback. Its terminal task is the existing
$E_e=|(\xi+e)/\sqrt2\rangle\langle(\xi+e)/\sqrt2|$ of ERM §27 and
[ERM II, Theorem 29.2][ERMII]. Retaining some of the labels changes the
available information; it does not change the erased-history minimax
problem of those sections. The fixed horizon here is distinct from the
autonomous first-STOP contracts of [Stopped environment memory][STOP].
All spaces are finite-dimensional over $\mathbb C$. Channels are
complex-linear CPTP maps, $\operatorname{Ad}_L(X)=LXL^\dagger$, and
the dagger of a channel denotes its trace adjoint.

**Definition 1.1 (Actual preparation, instrument and inputs).** Use the
five-dimensional $H$, embedding $B$ and range $R$ of ERM Definition 1.3.
Explicitly, for the fixed orthonormal basis $(e_0,\ldots,e_4)$ of $H$,

$$
u=(e_0+e_3)/\sqrt2,\qquad v=(e_1+e_4)/\sqrt2,\qquad z=e_2,
\qquad B(x_0,x_1,x_2)=x_0u+x_1v+x_2z,
\qquad P_R=BB^\dagger.
\tag{1.1}
$$

The environment has orthonormal basis $(f_0,f_1)$, ready state $f_0$,
and the fixed isometry of ERM Definition 2.1:

$$
\begin{aligned}
\mathcal V e_0&=u\otimes f_0,&
\mathcal V e_1&=u\otimes f_1,&
\mathcal V e_2&=v\otimes(f_0+f_1)/\sqrt2,\\
\mathcal V e_3&=z\otimes f_1,&
\mathcal V e_4&=z\otimes f_0.
\end{aligned}
\tag{1.2}
$$

Fix a real calibration angle $\theta$ and one unitary completion of
$\mathcal V$. Each acquisition freshly prepares this environment,
applies that interaction to the current $H$, measures in the basis

$$
g_0=\cos\theta f_0-i\sin\theta f_1,\qquad
g_1=-i\sin\theta f_0+\cos\theta f_1,
\tag{1.3}
$$

supplies the actual label $j\in\{0,1\}$, and discards the environment.
There is no retained quantum environment. Initial inputs are all density
matrices on the qutrit, embedded as $B\rho B^\dagger$; no smaller input
code or known input state is promised. An untouched reference may be
present but is inaccessible. ERM Theorem 2.2 gives the restricted branch
$2^{-1/2}BV_j$, with

$$
\begin{gathered}
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
W=\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\qquad U_1=U_0W,\\
V_0=U_0e^{i\theta W},\qquad V_1=V_0W,\qquad
Q_h=V_{h_n}\cdots V_{h_1},\qquad Q_\varnothing=I_3.
\end{gathered}
\tag{1.4}
$$

The time word $h=(h_1,\ldots,h_n)$ is the actual chronological sequence,
with $h_1$ acting first. Every word has probability $2^{-n}$ on every
allowed input, and the normalized terminal state is
$BQ_h\rho Q_h^\dagger B^\dagger$. This is the actual joint label/state
law, not just an equality of averaged channels. The horizon $n\ge0$ and
deterministic prefix schedule are known independently of the history.

**Definition 1.2 (Tasks and complete classical retention).** In qutrit
coordinates set

$$
\begin{gathered}
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
e=(1,1,-2)^{\mathsf T}/\sqrt6,\qquad
f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
v_e=(\xi+e)/\sqrt2,\qquad v_f=(\xi+f)/\sqrt2,\qquad
E_e=|v_e\rangle\langle v_e|,\qquad E_f=|v_f\rangle\langle v_f|,
\qquad \widehat E_q=BE_qB^\dagger.
\end{gathered}
\tag{1.5}
$$

These tasks expose the Born probabilities of two specified binary
measurements of the original unknown input. They do not ask for its
whole density matrix or for the word. Their physical terminal tests are
$(\widehat E_q,I_5-\widehat E_q)$ when the output is in $H$.

Only classical processing of the supplied labels occurs during the $n$
steps. Every finite or countable complete terminal record is represented
by an input-independent stochastic kernel

$$
r(a\mid h)\ge0,\qquad \sum_a r(a\mid h)=1.
\tag{1.6}
$$

A record value is positive when $\sum_h r(a\mid h)>0$.

The counted record includes every history-dependent classical carrier
available at use: program selection, buffers, seed, table selection,
archive and clock variations. Decoder-local randomness is absorbed into
the decoder's CPTP map; discarded private randomness is already averaged
in $r$. There is no extra history oracle, unknown-input copy,
postselection or reference read. Fixed calibrated controls, descriptions,
the independently scheduled clock and the retained live $H$ are separate
resources, not additional uncounted history ports.

For the single task $E_e$, an allowed decoder is any CPTP
$\mathcal D_a:M_5\to M_5$, selected by the complete record, and exactness
means only the averaged condition

$$
\sum_{h,a}2^{-n}r(a\mid h)
 \operatorname{Tr}\!\left(\widehat E_e\,
 \mathcal D_a(BQ_h\rho Q_h^\dagger B^\dagger)\right)
=\operatorname{Tr}(E_e\rho)
\quad\text{for every }\rho\in\mathsf D(\mathbb C^3).
\tag{1.7}
$$

The decoder can depend on $\theta,n$ and the task, but not on $\rho$ or
an unavailable history. A full-$H$ decoder need not preserve $R$.
Sections 2–3 use precisely this decoder domain. Section 4 distinguishes
two late-choice timings. Section 5 explicitly requires qutrit output
before its late choice.

## 2. The exact single-task terminal record

Write $\mathcal P_n=\{[Q_h]:|h|=n\}$ and $m_n(\theta)=|\mathcal P_n|$
as in ERM Definitions 3.1 and 11.1. No new word-count theorem is needed.
At each fixed horizon, projective equality is equality of matrices:
both letters send $\xi$ to $e^{i\theta}\xi$, so
$Q_h\xi=e^{in\theta}\xi$ excludes a nontrivial relative scalar.
On $T=\xi^\perp$, ERM (6.2) gives

$$
\det(V_0|_T)=-1,\qquad \det(V_1|_T)=1,
\qquad W\xi=\xi,\quad We=e,\quad Wf=-f.
\tag{2.1}
$$

**Theorem 2.1 (Sharp-task fibers and the exact retained alphabet).**
For every real $\theta$, integer $n\ge1$ and words $h,g\in\{0,1\}^n$,

$$
\begin{aligned}
Q_hE_eQ_h^\dagger=Q_gE_eQ_g^\dagger
&\ \Longleftrightarrow\ Q_h=Q_g\ \text{or}\ Q_h=Q_gW.
\end{aligned}
\tag{2.2}
$$

A kernel (1.6) admits decoders satisfying (1.7) if and only if, at every
positive record value $a$, all histories with $r(a\mid h)>0$ have the
same effect $Q_hE_eQ_h^\dagger$. Consequently the exact minimum finite
terminal alphabet and fixed binary payload are

$$
\min|\mathcal A_n|=\frac{m_n(\theta)}2,\qquad
\min b_n=\left\lceil\log_2\frac{m_n(\theta)}2\right\rceil
\quad(n\ge1).
\tag{2.3}
$$

At $n=0$ these minima are one value and zero bits. The necessity includes
stochastic records, all allowed full-$H$ CPTP decoders and correctness
required only after averaging as in (1.7).

Proof. First calculate the source-specific fiber. Put
$L=Q_g^\dagger Q_h$. It fixes $\xi$ and preserves $T$. Equality of the
two rank-one effects says $Lv_e=\lambda v_e$ with $|\lambda|=1$.
The nonzero $\xi$ coordinate forces $\lambda=1$, so $Le=e$.
A unitary on $T=\operatorname{span}\{e,f\}$ fixing $e$ acts by a scalar
$\mu$ on $f$. By (2.1), $\det(L|_T)\in\{1,-1\}$, hence $\mu=\pm1$.
Thus $L=I_3$ or $L=W$, proving necessity in (2.2). Both possibilities
fix $v_e$, proving sufficiency. This argument retains the spectator
phase; a projective quotient on $T$ alone would not suffice.

For the decoder condition use the standard sharp-effect extremality
argument in the observable-correction interface. For each record let

$$
F_a=B^\dagger\mathcal D_a^\dagger(\widehat E_e)B,
\qquad 0\le F_a\le I_3.
\tag{2.4}
$$

The inequalities follow from positivity and unitality of the adjoint,
including when the decoder leaks outside $R$. All-density separation
turns (1.7) into

$$
\sum_{h,a}2^{-n}r(a\mid h)Q_h^\dagger F_aQ_h=E_e.
\tag{2.5}
$$

An average of effects equal to a projection has every positively
weighted effect equal to that projection. Indeed, on a vector in its
kernel all the nonnegative expectations vanish; on a vector in its
range the expectations of the complementary effects vanish. Positivity
then annihilates those respective vectors, and together the two
subspaces give equality of operators. This also applies to a countable
average. Therefore (2.5) implies
$Q_h^\dagger F_aQ_h=E_e$ whenever $r(a\mid h)>0$.
For a fixed $a$ this is exactly constancy of $Q_hE_eQ_h^\dagger$.
It uses averaged correctness directly, without assuming branchwise
correctness in advance.

Conversely choose a representative $Q_a$ of the effect at each reached
record. Use the existing unitary extension of ERM (16.2),

$$
D_a=BQ_a^\dagger B^\dagger+(I_5-P_R),\qquad
\mathcal D_a=\operatorname{Ad}_{D_a}.
\tag{2.6}
$$

Its two orthogonal blocks are unitary. By (2.2), for every compatible
history $D_aBQ_h$ is either $B$ or $BW$. Both corrected branches have
the prescribed $E_e$ probability for every input. Thus (1.7) holds.

Finally, right multiplication by $W$ acts freely on the finite set of
distinct length-$n$ word matrices: it toggles the first chronological
label because $V_{1-j}=V_jW$. It stays within that set, and $QW=Q$
would imply $W=I_3$, which is false. Equation (2.2) identifies exactly
its two-element orbits. Hence there are exactly $m_n/2$ task fibers.
Every history has positive probability. Different fibers must have
disjoint nonempty sets of record values by (2.5), which proves the
lower bound even for stochastic $r$. Storing the fiber and using (2.6)
attains it. A $b$-bit register has at most $2^b$ values, giving the bit
formula. The sole empty word is treated by identity, not by dividing
$m_0=1$ by two. $\square$

For a standard Borel complete view, let $\nu_h$ be its conditional law
and $\lambda=\sum_h\nu_h$. Set $f_h=d\nu_h/d\lambda$; these are
measurable and sum to one almost everywhere. The criterion is then that,
for $\lambda$-almost every view $a$, all $h$ with $f_h(a)>0$ have one
task fiber. To prove necessity, replace the sum in (2.5) by its integral
and test the nonnegative quadratic forms on a basis of
$\operatorname{ran}E_e$ and $\ker E_e$. Zero integral makes each
vanish almost everywhere. There are finitely many histories and basis
vectors, so one common full-measure set works. On it the preceding
effect argument applies. Conversely choose the first representative
of the unique fiber with positive density; the choice is measurable
because there are finitely many histories, and (2.6) works almost
everywhere. Thus a measurable exact view determines the finite task
fiber. A continuum of views is not a finite alphabet merely because
its individual points have probability zero. The same argument applied
to the finitely many queried effects in §4 gives its corresponding
almost-everywhere criterion. In §5 it applies to the positive Choi
quadratic forms once identity is established. An explicitly free shared
seed independent of the labels cannot lower the finite-alphabet bounds:
the same nonnegative-form argument first forces conditional exactness
for almost every seed, and independence leaves every history with its
positive fair probability there. A history-correlated visible seed is
already part of the complete record.

**Proposition 2.2 (Online accumulation and its exact-real boundary).**
For each fixed real $\theta$ and integer $n\ge1$ there are prefix transition tables and
a deterministic clock accumulating the task fiber using at most the
terminal minimum (2.3) values at every prefix after its classical update.
This existential statement does not specify an algorithm taking an arbitrary exact real $\theta$
as input and deciding all word equalities.

Proof. The intrinsic boundary value at prefix $h$ is the transported
effect

$$
X_h=Q_hE_eQ_h^\dagger,
\qquad X_\varnothing=E_e,
\qquad X_{hj}=V_jX_hV_j^\dagger.
\tag{2.7}
$$

Thus equality of boundary values is preserved on appending the same
actual label. Conjugation by $V_0^{n-t}$ injects the set at depth $t$
into the set at depth $n$. The empty-depth set has size one. For
$t\ge1$ the size is $m_t/2$ by Theorem 2.1, and never exceeds $m_n/2$.
Choose finite encodings at each depth into that many slots and use
(2.7) for the two transitions from each reachable slot. This proves
existence of the tables. It can require up to $2n(m_n/2)$ transition
entries and $m_n/2$ terminal representative controls. Equality of exact
real matrix entries is not a supplied effective test; the finite-table
existence proof supplies no uniform acquisition or compilation procedure
for an unspecified real calibration. The two explicit calibrations in
§3 avoid this missing test. $\square$

The paid-parity completion in [Approximate online recovery memory,
Theorem 17.2][ONLINE] is an existing supplier. Its exact specialization
here has a particularly transparent interpretation: the task fiber plus
the actual label parity determines the full word class. In fact
$\det(Q_h|_T)=(-1)^{n-\sum_kh_k}$, and the two matrices $Q,QW$ in
(2.2) have opposite determinants on $T$. Updating parity by
$\eta\leftarrow\eta\mathbin\oplus j$ therefore selects one of them.
This is use of that completion mechanism, not a new general parity
principle. Theorem 2.1 supplies the exact task-specific factor of two.

## 3. Acquired records and paid use at two exact calibrations

**Theorem 3.1 (The acquired suffix at $\theta=\pi/6$).** At this fixed
calibration, the minimum terminal record for $E_e$ has $2^{n-1}$ values
and $n-1$ bits for every $n\ge1$. It is attained by actually discarding
the first supplied label and retaining the subsequent labels in order.
The record supports a terminal inverse control on the same retained
specimen followed by the fixed $E_e$ test. It loses precisely the first
label among chronological words of this fixed length.

Proof. ERM Theorem 8.2 proves injectivity of all full word classes at
this calibration; its finite-horizon consequence is $m_n=2^n$.
Theorem 2.1 then gives the lower bound. For acquisition start with an
empty suffix. The first actual label is read and discarded. Each later
actual label is appended. For $n\ge1$ let

$$
s(h)=(h_2,\ldots,h_n),\qquad
\widetilde h=(0,h_2,\ldots,h_n).
\tag{3.1}
$$

Because the first label acts on the right,

$$
Q_h=Q_{\widetilde h}W^{h_1},\qquad
Q_{\widetilde h}^\dagger Q_h=W^{h_1}.
\tag{3.2}
$$

Use (2.6) with $Q_a=Q_{\widetilde h}$. Each actual corrected branch
is $B W^{h_1}\rho W^{h_1}B^\dagger$, so it has the original $E_e$
probability. Conditional on the suffix, the first label remains fair;
the corrected conditional qutrit channel is exactly

$$
\Delta_W(\rho)=\tfrac12(\rho+W\rho W).
\tag{3.3}
$$

Conversely, (2.2) and full-word injectivity imply that two histories have
the same task fiber precisely when their suffixes in (3.1) agree.
Each such fiber consists of the two choices of $h_1$. This proves both
optimality and the exact lost distinction. At prefix $t\ge1$ the suffix
has $t-1$ bits, so the peak history payload for this known horizon is
$n-1$ bits at returned acquisition cuts, after the classical update,
with no archived first label. The incoming label wire and its
measurement/communication apparatus are supplied acquisition resources.
For $n=1$ the suffix is empty,
and the sole decoder is the known inverse of $V_0$.

These are acquired labels from (1.2)–(1.3), not fair labels resampled
independently to synthesize a different joint process. There are exactly
$n$ fresh environment preparations, $n$ interactions, $n$ environment
measurements and $n$ supplied-label acquisitions. The suffix uses $n-1$
label writes and stores all the retained bits on the same run. The
known prefix schedule supplies the write position; any material clock
and addressing workspace must be supplied in addition to the payload.

A finite control scheme for use reads the stored suffix backwards,
applies the full-$H$ extensions of
$V_{h_n}^\dagger,\ldots,V_{h_2}^\dagger,V_0^\dagger$ in that order,
and then performs the single binary task measurement. This uses $n$
inverse-letter invocations when $n\ge1$, $n-1$ suffix accesses and
one task measurement; it keeps the suffix unchanged. The composition is
exactly (2.6), since multiplication is in the reverse order of physical
application. A reverse scan or a retained cursor and its control states
are additional implementation resources. For fixed $n$ a deterministic
schedule can select these positions without a history-dependent clock.
If the prefix counter and reverse-scan index are material registers,
each ranges over at most $n+1$ positions and can be stored in
$\lceil\log_2(n+1)\rceil$ bits, with a fixed finite set of phase flags.
Their deterministic scheduling does not encode a discarded label.
No exponentially large terminal matrix table is required for this
particular construction. There is no assertion that the inverse-call
count or other apparatus costs are optimal. At $n=0$ there is no
acquisition or inverse call and the original task can be measured
directly. $\square$

**Theorem 3.2 (The acquired three-value boundary at $\theta=0$).**
At zero angle the exact terminal alphabet for $E_e$ is

$$
\begin{array}{c|cccc}
n&0&1&2&n\ge3\\\hline
\min|\mathcal A_n|&1&1&2&3\\
\min b_n&0&0&1&2
\end{array}
\tag{3.4}
$$

A homogeneous three-value accumulator realizes all horizons. At each
known horizon, time-dependent encodings also attain the displayed
terminal cardinality as the peak history-register cardinality.

Proof. Reuse the full-word counts $1,2,4,6$ of ERM Theorem 5.1 in
Theorem 2.1, treating $n=0$ separately. An explicit actual accumulator
also identifies the retained distinction. The qutrit letters are now
the permutations $U_0,U_1$. The vector $e$ has its unique coordinate
$-2/\sqrt6$ at position $2$, with the other two coordinates equal.
Let $r\in\{0,1,2\}$ be the position of this coordinate in $Q_he$.
Start at $r=2$ and update on the actual label by

| Current $r$ | On $0$ | On $1$ |
| --- | --- | --- |
| $0$ | $0$ | $2$ |
| $1$ | $2$ | $0$ |
| $2$ | $1$ | $1$ |

These are the column-image permutations of the very matrices (1.4).
Induction proves that the accumulator equals the position in $Q_he$.
At depths $0,1,2$ the reachable sets are respectively
$\{2\},\{1\},\{0,2\}$. At depth three all three positions occur,
and their union of successor images remains all three thereafter.
They correspond bijectively to the effects in (2.7), since every
permutation fixes $\xi$ and the three possible images of $e$ are
different. The small-depth counts and the stable tail are therefore
also obtained directly from the actual updates.

Choose fixed permutation matrices $P_r$ taking $e$ to the vector with
its negative coordinate at $r$: take $P_2=I_3$, $P_1=U_0$, and $P_0$
the transposition of coordinates $0,2$. Each fixes $\xi$. For any
history ending at $r$, the permutation $P_r^\dagger Q_h$ fixes $e$
and is exactly $I_3$ or $W$. Thus the full-$H$ unitary
$BP_r^\dagger B^\dagger+(I_5-P_R)$ followed by the $E_e$ test
is exact. This is a constant list of three terminal controls, not a
history oracle. The homogeneous table has six entries and performs
one classical update per acquisition. There are the same $n$ fresh
preparations, interactions, environment measurements and label
acquisitions as before, then one selected inverse-permutation
invocation and one task measurement. Identity controls may be omitted.
Calibration and implementation of those controls remain supplied
resources. The homogeneous carrier has three values even at startup;
re-encoding each reached set using the deterministic prefix schedule,
as in Proposition 2.2, gives the smaller peak counts for $n=0,1,2$.
$\square$

Both constructions retain callable control data, not an estimate of
$\rho$. The record remains readable through selection and invocation
of the terminal control. The live quantum carrier is indispensable to
these uses: $\operatorname{Tr}(E_e\rho)$ is not encoded in the
input-independent record law. A destructive task read does not leave
unlimited fresh copies or independent future trials. Even at $\pi/6$,
a finite program for reading and reversing a suffix requires an
unbounded record capacity as $n$ grows, by Theorem 3.1. A finite static
description, history payload, addressing workspace, retained quantum
carrier and exact-control precision are distinct resources.

The lost first label cannot generally be reconstructed using the live
carrier. On the permitted input $\rho_*=I_3/3$, every word leaves the
same qutrit state. At $\pi/6$, conditional on a fixed suffix the two
first labels therefore give identical joint accessible data and equal
probabilities, so their optimal guessing success is $1/2$. At zero
angle the position register merges distinct permutations differing by
$W$; words with the same full permutation are merged as well. In
particular the two histories differing only in their first label always
have the same $r$ and different full permutations. The position record
is not a recovery of chronological time or of the full accumulated
permutation, even though it supports the prescribed terminal task.

## 4. A late choice of two tasks requires the full word class

**Definition 4.1 (Choice timing and correctness quantifiers).** Acquire
one kernel $r(a\mid h)$ before a query $q\in\{e,f\}$ is supplied.
The required guarantee is for each of the two possible queries and
every input, with the same acquisition kernel:

$$
\begin{gathered}
\text{for every }q\in\{e,f\}\text{ and every }\rho\in\mathsf D(\mathbb C^3),\\
\sum_{h,a}2^{-n}r(a\mid h)
 \operatorname{Tr}\!\left(\widehat E_q\,
 \mathcal D_{a,q}(BQ_h\rho Q_h^\dagger B^\dagger)\right)
 =\operatorname{Tr}(E_q\rho).
\end{gathered}
\tag{4.1}
$$

In the common terminal decoder contract, $\mathcal D_{a,e}=
\mathcal D_{a,f}=\mathcal D_a$ is fixed and applied before the late
choice; the choice only selects which fixed binary measurement to
perform. In the query-dependent contract, the choice is supplied after
acquisition but before decoding, so two families $\mathcal D_{a,q}$
are allowed. Both act on all of $H$. The choice is an external task
input, not a source of missing history or unknown-input information.
Equation (4.1) requires either query to be supported, rather than
success averaged only under one prescribed record-dependent choice law.
A selector carrying additional history is part of the complete view
under Definition 1.2, and has a different resource account.

**Theorem 4.2 (Exact full-word requirement for either timing).**
For every real $\theta$ and $n\ge0$, a complete record supports the
common terminal decoder contract exactly when, at each positive record,
all compatible histories have the same full word class $[Q_h]$.
The same condition is necessary and sufficient for the query-dependent
contract (4.1). For both contracts the exact minimum is

$$
\min|\mathcal A_n|=m_n(\theta),\qquad
\min b_n=\lceil\log_2m_n(\theta)\rceil.
\tag{4.2}
$$

In particular it is $n$ bits and the full chronological word at
$\theta=\pi/6$, whereas at zero angle the alphabet counts are
$1,2,4,6$ for $n=0,1,2,\ge3$. A full word class is not generally a
full chronological word at angles with word collisions.

Proof. Allow the larger, query-dependent decoder class first. Apply
the sharp-effect argument (2.4)–(2.5) separately to each of the two
equations in (4.1), using $F_{a,q}=B^\dagger
\mathcal D_{a,q}^\dagger(\widehat E_q)B$. Because the kernel is the
same, histories $h,g$ with positive weight at one $a$ must satisfy

$$
Q_hE_eQ_h^\dagger=Q_gE_eQ_g^\dagger,\qquad
Q_hE_fQ_h^\dagger=Q_gE_fQ_g^\dagger.
\tag{4.3}
$$

Their relative unitary $L=Q_g^\dagger Q_h$ fixes $\xi$. The first
equality forces $Le=e$, and the second forces $Lf=f$: in each case
the nonzero spectator coordinate removes the ray phase, exactly as
in Theorem 2.1. Thus $L=I_3$. At $n=0$ there is only the empty word.
For every fixed horizon this is exactly equality of full projective
word classes. The argument does not require a common decoder, and
therefore proves necessity for both timings.

Conversely, the existing full-state recovery ERM Theorem 16.1 supplies
(2.6) for each retained word class. It recovers the original qutrit,
also with an untouched reference, before any choice. It therefore
satisfies the stronger common terminal decoder contract. The same
disjoint-support counting as in Theorem 2.1 proves (4.2), and the
existing word counts give the two calibrations. $\square$

The record lower bound does not force every common corrected channel
in this theorem to be identity. Here is an explicit counterexample
even with the optimal word-class record. Let
$S=\operatorname{span}\{v_e,v_f\}$, let $P_S$ be its projection,
and define the qutrit pinching

$$
\mathcal L(X)=P_SXP_S+(I_3-P_S)X(I_3-P_S).
\tag{4.4}
$$

It is CPTP and its adjoint fixes $E_e,E_f$. On $H$ use the unitary
inverse (2.6), followed by pinching onto $BS$ and its orthogonal
complement in $H$. On every actual branch the corrected qutrit channel
is $\mathcal L$, so both tasks are exact. Nevertheless $\mathcal L$
kills every cross operator from $S$ to $S^\perp$ and is not identity.
This example applies also at $n=0$ and requires no decoder response to
the late choice. Its two fixed tasks are alternative measurements on
one output, not a claim that their noncommuting sharp tests can be
jointly measured with both sharp marginals. The compatibility result
in [SharpMeasurementCompatibility][SHARP] retains that distinction.

## 5. One actual labelled continuation forces qutrit identity

**Definition 5.1 (Common qutrit output before a late continuation choice).**
Keep the same actual acquisition (1.2)–(1.6), but require that the
terminal decoder output is a qutrit, physically re-embedded in $R$
before any subsequent ERM step. Write its effective action on the
actual terminal qutrit as a CPTP map $\mathcal C_a:M_3\to M_3$.
This includes restriction of a physical decoder with arbitrary behavior
off $R$ and output confined to $R$; no output in $H\setminus R$
is passed to the next step. The common corrected average is

$$
\mathcal T(X)=\sum_{h,a}2^{-n}r(a\mid h)
                 \mathcal C_a(Q_hXQ_h^\dagger).
\tag{5.1}
$$

Only after this same decoder has been applied, choose between measuring
$E_e$ immediately and performing one further actual acquisition of
(1.2)–(1.3), keeping its label $j$, followed by measuring $E_e$ on
its actual successor. The latter has the restricted instrument

$$
\mathcal J_j(X)=\tfrac12 V_jXV_j^\dagger.
\tag{5.2}
$$

There is no intervening correction after that step. Let $E_e^{(1)}=E_e$
and $E_e^{(0)}=I_3-E_e$. The required equalities are, for every qutrit
density $\rho$,

$$
\begin{aligned}
\operatorname{Tr}(E_e\mathcal T(\rho))&=\operatorname{Tr}(E_e\rho),\\
\operatorname{Tr}(E_e^{(y)}\mathcal J_j(\mathcal T(\rho)))
 &=\operatorname{Tr}(E_e^{(y)}\mathcal J_j(\rho))
 \quad(j,y\in\{0,1\}).
\end{aligned}
\tag{5.3}
$$

Thus the target future label and result are the joint outcomes of
the same specified instrument acting on the original input, compared
with its actual action on the decoded current specimen. They are not
two separately optimized successor marginals. The choice is a task
input with both alternatives required, as in Definition 4.1. It does
not select a new decoder or supply an unrecorded history.

**Theorem 5.2 (Labelled one-step closure and exact record requirement).**
For every real $\theta$ and integer $n\ge0$, (5.3) holds if and only
if $\mathcal T=\operatorname{id}_3$. For a given complete kernel $r$,
such common decoders exist exactly when its positive record fibers
refine the full word class $[Q_h]$. The exact alphabet and fixed-bit
minima are therefore (4.2).

Moreover every successful scheme has
$\mathcal C_a\circ\operatorname{Ad}_{Q_h}=\operatorname{id}_3$
whenever $r(a\mid h)>0$. This is identity of the corrected channel on
the whole qutrit; the raw terminal decoder is the inverse word channel,
not in general identity. All these identity conclusions also preserve
every untouched finite reference.

Proof. By the actual instrument formula (5.2), the $y=1$ equalities
in (5.3), together with the immediate equality, say exactly

$$
\mathcal T^\dagger(E_e)=E_e,\qquad
\mathcal T^\dagger(F_j)=F_j\quad(j=0,1),\qquad
F_j=V_j^\dagger E_eV_j.
\tag{5.4}
$$

The factor $1/2$ in each joint effect cancels because both branches
are actual fair qutrit branches. The $y=0$ equations then follow from
trace preservation and $\mathcal J_j^\dagger(I_3)=I_3/2$.
Keeping $j$ is essential to obtain the two separate equations in
(5.4).

Now evaluate these very effects. In the ordered basis $(\xi,e,f)$,

$$
W=\operatorname{diag}(1,1,-1),\qquad
U_0=1\oplus
 \begin{pmatrix}-1/2&\sqrt3/2\\\sqrt3/2&1/2\end{pmatrix}.
\tag{5.5}
$$

Consequently $F_0=|w_+\rangle\langle w_+|$ and
$F_1=|w_-\rangle\langle w_-|$, where the harmless whole-vector
phase $e^{-i\theta}$ in $V_j^\dagger v_e$ has been removed and

$$
w_\pm=\frac{\xi-e/2\ \pm\ (\sqrt3/2)e^{2i\theta}f}{\sqrt2}.
\tag{5.6}
$$

All three vectors $v_e,w_+,w_-$ are unit vectors. Their overlaps are

$$
\langle v_e,w_+\rangle=\langle v_e,w_-\rangle=
\langle w_+,w_-\rangle=\frac14.
\tag{5.7}
$$

They span $\mathbb C^3$: the difference $w_+-w_-$ is a nonzero
multiple of $f$, their sum is a nonzero multiple of $\xi-e/2$,
and $v_e$ supplies the independent direction $\xi+e$. This argument
holds for every real angle, since $e^{2i\theta}$ never vanishes.

Apply the existing connected-probe rigidity principle to (5.4) with
exactly these three probes, output dimension three, and all density
inputs. Its repository owner is
[ProbeComponentRigidity.connected_probability_preserving_identity][PCR],
with its [owning Scribe][PCRB], including the private
`dual_fixed`, `kraus_commutes_projection` and `overlap_scalar`
steps. For completeness, the finite argument is short. If $L_\ell$
are Kraus operators of $\mathcal T$, any fixed projection $P$ satisfies

$$
\begin{aligned}
\sum_\ell(PL_\ell-L_\ell P)^\dagger(PL_\ell-L_\ell P)
&=\mathcal T^\dagger(P)
 -\mathcal T^\dagger(P)P-P\mathcal T^\dagger(P)+P=0.
\end{aligned}
\tag{5.8}
$$

Every summand is positive, so each Kraus matrix commutes with $P$.
For a rank-one $P$ its vector is therefore a Kraus eigenvector.
Commuting with two such projections whose vectors have nonzero
overlap forces their eigenvalues to agree: apply
$PL_\ell=L_\ell P$ to the second vector. Equations (5.7) equate
all three eigenvalues, and their spanning property makes
$L_\ell=c_\ell I_3$. Trace preservation gives
$\sum_\ell|c_\ell|^2=1$, hence $\mathcal T(X)=X$ on every
complex matrix. This is the mature rigidity argument applied after
the source-specific calculation (5.5)–(5.7), not a new general
rigidity theorem. Identity plainly implies all of (5.3).

Since (5.1) is now identity, the existing full-state record theorem
ERM 16.1 applies on this very qutrit. One can also see the individual
branch assertion directly from its rank-one Choi argument. The Choi
matrix of identity is a positive rank-one matrix, and it is the
weighted sum of the positive Choi matrices of
$\mathcal C_a\circ\operatorname{Ad}_{Q_h}$.
Every positive summand has support in that line; its trace is three,
so each positively weighted channel is itself identity. If $h,g$
share a positive record $a$, then
$\mathcal C_a=\operatorname{Ad}_{Q_h^\dagger}
=\operatorname{Ad}_{Q_g^\dagger}$, forcing the two unitaries to
differ only by a scalar. They therefore have the same full word
class. Conversely the word-class inverse supplied by ERM (16.2)
gives identity and all the required successor statistics. This proves
the criterion and the minima. Equality on every complex matrix
tensor-extends to every untouched finite reference. $\square$

The upper construction is physically successive on the same retained
carrier: acquire the $n$ original labels, retain their full word class,
apply its calibrated inverse, and, only if the continuation alternative
is selected, freshly prepare one more environment, use the same
interaction and basis, retain its label and measure its actual successor.
The continuation alternative adds one preparation, interaction,
environment measurement and label acquisition, plus one terminal task
measurement. The immediate alternative adds only the task measurement
after correction. The record-selecting control must stay readable until
correction has been invoked. At $\pi/6$ the $n$ retained labels permit
$n$ inverse-letter invocations; at zero angle the existing homogeneous
six-state permutation accumulator and six inverse controls of ERM
Theorem 5.1 suffice. These costs concern this upper construction; no
optimality of total actuation cost follows from the alphabet minimum.

Theorem 5.2 does not replace its qutrit-output condition by arbitrary
leakage into $H$. On such leaked states the actual full instrument need
not have branch effect $I_5/2$, and (5.4) is not the same reduction.
Nor does forgetting the future label give the two equations in (5.4):
it gives only the sum involving $(F_0+F_1)/2$. No identity or record
minimum for that different continuation contract is asserted here.

## 6. Chronology, task boundary and memory on the same run

**Proposition 6.1 (Attained routes and update agreement).** At every
fixed prefix depth $t$, chronological accumulation of the actual word,
forward update of $X_h$ in (2.7), and either explicit record of §3
give the same transported task effect. Any terminal representative
chosen from that effect fiber gives the same pulled-back $E_e$ task.
For the stronger contracts of §§4–5, retaining the full word class
instead makes correction and every subsequent physical instrument
step agree with the corresponding ideal-input route. The latter is a
state-channel conclusion and is stronger than single-task agreement.

Proof. The chronological law gives $Q_{hj}=V_jQ_h$, whence
$Q_{hj}E_eQ_{hj}^\dagger=V_jX_hV_j^\dagger$ at every actual
acquisition. Starting at $E_e$ proves (2.7) by induction, without
substituting an independently generated word. At $\pi/6$, (3.2)
shows that the recorded suffix has that same effect. At zero angle,
the coordinate-position induction in Theorem 3.2 identifies that effect
with the three-value accumulator. Thus both acquisition routes reach
the actual boundary. Conversely on the attained finite effect set,
the suffix at $\pi/6$ and the position at zero are uniquely determined
by the effect, by Theorems 3.1 and 3.2. These two inverse descriptions
give the same task record and effect on their respective attained
domains. They do not acquire that record from an unmeasured copy of
an abstract matrix.

For representatives $Q_a,Q'_a$ in one effect fiber, each satisfies
$Q_aE_eQ_a^\dagger=Q'_aE_e(Q'_a)^\dagger=X_h$. Pulling that
effect back through the actual $Q_h$ gives $E_e$. The controls may
differ on other observables, but their specified task laws agree on
every density. Finally if the full word class is retained, its inverse
gives $Q_a^\dagger Q_h$ scalar and hence the identity channel on
the original input. Composing this exact channel identity with
$\mathcal J_j$ gives exactly the same subnormalized successor,
label probability and terminal result as applying $\mathcal J_j$
directly to that input. The same reasoning holds successively for
any specified finite sequence of actual steps and tests. Their fresh
preparations, retained labels, controls and additional outputs must
still be supplied and counted. $\square$

The three observations in this proposition have independent operational
meanings. Chronology is the ordered series of actual measured labels,
with $t$ counting acquisitions rather than physical duration. The task
boundary is the physical effect at the terminal specimen that can be
pulled back to the specified original-input probability. Memory is the
actually written complete classical view available to select an allowed
operation, together with the separately retained specimen on which that
operation acts. Equation (2.2) proves the exact distinction discarded
by this boundary; (2.7) proves its compatibility with actual accumulation.
It is not necessary to put the whole chronology in each of these
observations. At $\pi/6$ one bit is dispensable for the single task
at every $n\ge1$, but indispensable when the allowed terminal task family is enlarged
as in §§4–5. At zero angle three values suffice for that single task
while six full-word values suffice for the stronger contracts at
$n\ge3$. At horizons with more than one task fiber, the fixed time
count alone cannot select its run-dependent value.

The single-task boundary is not a claim of autonomous closed prediction
for all future experiments after correction. The residual (3.3) is
already a concrete distinction from identity. The future labelled
effects in (5.6), or the second task in §4, detect information that
the single-task record may erase. Theorems 4.2 and 5.2 specify exactly
when the required enlargement forces retention of the full word class.
They preserve the different acquisition and STOP domains of [STOP].

## 7. Source correspondence and unresolved realization bridges

The source-specific deductions here are the all-angle task fiber (2.2)
and its exact half-word terminal record, its actual acquired
implementations at the two stated calibrations, the late-query record
condition with both decoder timings, and the evaluation of the labelled
one-step effects (5.5)–(5.7) that makes existing rigidity applicable.
These are `repo-derived` conclusions with ordinary proofs. The general
observable-correction, sharp-effect, parity, Kraus and rigidity tools
are suppliers. No global novelty or additional Lean certification is
asserted.

| Source | Correspondence and exact limit of use |
| --- | --- |
| [ERM][ERM] Definitions 1.3–1.5,2.1,3.1–3.2,11.1; Theorems 2.2,3.3,5.1,8.2,16.1–16.2 | The same $H,B,R$, ready state, basis measurement, chronological multiplication, complete classical view and all-qutrit source. The full-state optimum $m_n$ and counts are reused. Only the terminal correctness task is changed in §§2–4; §5 derives full-state correctness from its specified future tests. |
| ERM §26, Definition 27.1 and (27.4)–(27.5); [observable-correction note][NOTE] | All-density expectation separation and positive effect lifts. Our $E_e$ is its $v=(\xi+e)/\sqrt2$, and $E_f$ uses the same fixed $f$. The history-erased channels and their minimax losses retain their original no-record assumptions. |
| [ERM II][ERMII], Theorem 29.2 | The sixth-horizon obstruction to projective optimality is for discarded history and fixed qutrit effect domain. Our retained-record theorem changes neither that assertion nor its counterexample and does not determine its unrestricted minimax optimum. |
| [Actual erased-history terminal recovery][ERASED], §§103–104 | Existing common-decoder argmin intersections and their three-task obstruction concern nonzero taskwise optima after erasure. Our exact tasks with an acquired record do not replace that problem. |
| [Approximate online recovery memory][ONLINE], Theorem 17.2 and Proposition 17.3 | Existing actual determinant-parity refinement, with the spectator phase retained. It supplies no new proof of the sharp-task fiber count; the count and the two actual acquisitions are proved here. |
| [ProbeComponentRigidity][PCR] and [Scribe][PCRB] | Universal all-density probability preservation, finite Kraus normalization and connected spanning probes imply identity. The new applicability calculation is the actual three-vector family (5.6), not a generic rigidity claim. SparseProbeCoercivity and its Scribe instead give quantitative scalar-defect estimates for a coordinate basis plus a full-support vector; their different probe assumptions are not substituted for (5.7). |
| [KrausLeftInverseNecessity][KLI] and [Scribe][KLIB]; [FiniteKrausRepresentation][KRAUS] and [Scribe][KRAUSB] | The actual all-matrix left inverse and finite rectangular CP representation interfaces, including private helper proofs. A generic CPTP map has a finite Kraus representation, but a word-class record lower bound alone does not imply identity, as (4.4) demonstrates. |
| [ContinuationEffectClosure][CEC] and [Scribe][CECB] | The real Hermitian effect spaces close under branch duals in at most $d^2-r$ steps. For (5.2) those duals are $X\mapsto V_j^\dagger XV_j/2$. The exact one-step matrix and connectedness calculation is supplied in §5; no closure bound itself produces acquisition, rights or an inverse control. |
| [OrthogonalSyndromeChannel][SYN] and [Scribe][SYNB] | Existing full-space CPTP completion and logical-observable principles. The present single-task construction uses the explicit block unitary (2.6); it does not assume that different actual histories occupy orthogonal quantum syndrome subspaces. |

For the primary-literature correspondence, Bény–Kempf–Kribs,
*Quantum Error Correction of Observables*, [arXiv:0705.1574v1][BKK],
Definition 8, equation (7), Theorem 9 and Corollary 10, supplies the
Heisenberg correction framework and the compressed-Kraus-product
criterion for algebras. Here the input code projection is $I_3$;
the spectator $|\xi\rangle\langle\xi|$ is not that code projection.
For a positive record $a$, the actual conditional errors are
$\sqrt{r(a\mid h)/\sum_g r(a\mid g)}\,Q_h$. The single sharp
task uses the algebra generated by $I_3,E_e$; the common-task condition
uses one decoder, not two independently attainable optima. The
elementary effect argument in Theorem 2.1 handles the original
full-$H$ output domain directly.

Gregoratti–Werner, *Quantum Lost and Found*,
[quant-ph/0209025v1][GW], Proposition 2 and §II.C.1, supplies
conditional inversion of $t_j=V_j/\sqrt2$ with
$t_j^\dagger t_j=I_3/2$. Their system is identified here with the
qutrit, not all of $H$. Their *On quantum error-correction by classical
feedback in discrete time*, [quant-ph/0403092v1][GW2], Proposition 2,
equations (10)–(12), permits the deferred-correction specialization
in which all earlier corrections are identity. These literature
results do not supply the count of coarsened task records.
Choi–Johnston–Kribs, *The Multiplicative Domain in Quantum Error
Correction*, [arXiv:0811.0947v1][CJK], Theorem 8, supplies the
unital-CP Schwarz-equality principle behind the fixed-projection
argument. Applied to the adjoint of a CPTP qutrit channel, it is
consistent with the explicit positive defect (5.8). None of these
papers is being credited with the source-specific counts or actual
probe family proved here.

An independent spatial view of this qutrit process has not been
constructed. The three-dimensional Hilbert space and the physical
five-level carrier are supplied system structure; they are not an
acquired metric, incidence geometry or native spatial realization.
The binary measured labels in (1.3) have not been identified with native
$\alpha/\beta$ constructors. In particular the independently published
[global-port acquisition and odd-offset continuation][GPO] concerns a
free ordered tree, literal presence queries, authentic size advice and
installed Read/update grants. Its recovery routes do not provide a map
from that actual tree process to (1.2), nor does (1.2) install its
tree service. Such a bridge must specify the shared initialization,
joint source, action correspondence, readouts, resources and independent
spatial meaning and prove their transport laws.

Unknown-angle acquisition, uniform effective exact-real table synthesis,
finite-precision robustness, minimum total control cost, leaked-output
labelled continuation and unlabelled-continuation minima remain outside
the proved contracts. The exact terminal classical minima do not bound
quantum carrier size or indefinite retained capacity. The original
fixed-apparatus/original-Q/parked-consumer/unchanged-initialization
problems and the signed P/Q tasks retain their original assumptions
and unresolved obligations. The NCR/PVC/PR57/PG/Atlas results retain
their own source and acquisition hypotheses. No mutually recoverable
four-expression structure for the full programme follows from this
bounded task-relative contribution.

[ERM]: AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[ERMII]: AURIC_FIB_ENVIRONMENT_RECORD_MEMORY_II.md
[ERASED]: AURIC_FIB_ACTUAL_ERASED_HISTORY_TERMINAL_RECOVERY.md
[ONLINE]: AURIC_FIB_APPROXIMATE_ONLINE_RECOVERY_MEMORY.md
[STOP]: RECURSIVE_RELATIONAL_OBSERVATION_AUTONOMOUS_STOPPED_ENVIRONMENT_MEMORY.md
[NOTE]: ../../../Library/Quantum/benykempfkribs2007observables.md
[PCR]: ../../../D5/S3/Quantum/Reduction/ProbeComponentRigidity.lean
[PCRB]: ../../../Blueprint/D5/S3/Quantum/Reduction/ProbeComponentRigidity.scribe.cs
[SHARP]: ../../../D5/S3/Quantum/Measurement/SharpMeasurementCompatibility.lean
[KLI]: ../../../D5/S3/Quantum/Recovery/KrausLeftInverseNecessity.lean
[KLIB]: ../../../Blueprint/D5/S3/Quantum/Recovery/KrausLeftInverseNecessity.scribe.cs
[KRAUS]: ../../../D5/S3/Quantum/Foundation/FiniteKrausRepresentation.lean
[KRAUSB]: ../../../Blueprint/D5/S3/Quantum/Foundation/FiniteKrausRepresentation.scribe.cs
[CEC]: ../../../D5/S3/Quantum/Measurement/ContinuationEffectClosure.lean
[CECB]: ../../../Blueprint/D5/S3/Quantum/Measurement/ContinuationEffectClosure.scribe.cs
[SYN]: ../../../D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel.lean
[SYNB]: ../../../Blueprint/D5/S3/Quantum/Recovery/OrthogonalSyndromeChannel.scribe.cs
[BKK]: https://arxiv.org/abs/0705.1574v1
[GW]: https://arxiv.org/abs/quant-ph/0209025v1
[GW2]: https://arxiv.org/abs/quant-ph/0403092v1
[CJK]: https://arxiv.org/abs/0811.0947v1
[GPO]: https://github.com/the-omega-institute/trureturing/blob/d7305509a5999f9c6cd596ae3312d6d07bf2aaa3/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md

## 追加锚（本行以下为增补区）

## 8. The immediate task and the actual erased-label continuation

**Definition 8.1 (Two alternative tests of one corrected qutrit).**
Keep Definitions 1.1–1.2, including every real calibration $\theta$,
all qutrit density inputs, the actual measured environment, and the
absence of intermediate quantum feedback. In this section coordinates
are in the ordered basis $(\xi,e,f)$, so that the same reflection is
$W=\operatorname{diag}(1,1,-1)$. Put

$$
\begin{gathered}
P_+=(I_3+W)/2,\qquad P_-=(I_3-W)/2,\qquad
\Delta_W(X)=P_+XP_++P_-XP_-,\\
\mathcal F(X)=\sum_{j=0}^1\mathcal J_j(X)
 =\tfrac12(V_0XV_0^\dagger+V_1XV_1^\dagger)
 =V_0\Delta_W(X)V_0^\dagger.
\tag{8.1}
\end{gathered}
$$

Thus $\mathcal F$ is the actual one-acquisition successor channel
when its measured label is discarded; its physical output is
$B\mathcal F(X)B^\dagger$ in $H$. The environment is still freshly
prepared, interacted with and measured; discarding its label does not
replace this operation by a different dilation or a resampled label.
Since $e^{i\theta W}$ acts by a scalar on each diagonal block,
$\mathcal F=\operatorname{Ad}_{U_0}\circ\Delta_W$.

Let $E=E_e$, $E^{(1)}=E$, and $E^{(0)}=I_3-E$. A single CPTP
correction $\mathcal T:M_3\to M_3$ is applied before a late choice
between two alternatives. The first measures $E$ immediately. The
second performs the actual acquisition, discards $j$, and then measures
$E$. Correctness requires both alternatives for every density $\rho$:

$$
\begin{aligned}
\operatorname{Tr}(E\mathcal T(\rho))&=\operatorname{Tr}(E\rho),\\
\operatorname{Tr}(E\mathcal F(\mathcal T(\rho)))
 &=\operatorname{Tr}(E\mathcal F(\rho)).
\tag{8.2}
\end{aligned}
$$

The complementary result probabilities follow by trace preservation.
These are alternative tests of the same corrected specimen, not two
measurements performed successively on fresh copies. The decoder does
not depend on the late choice. A stronger, initially distinct contract
requires the first equality and $\mathcal F\circ\mathcal T=\mathcal F$
on all matrices.

For $z\in\mathbb C$ define the block multiplier

$$
\mathcal D_z(X)=P_+XP_++P_-XP_-
       +zP_+XP_-+\overline zP_-XP_+.
\tag{8.3}
$$

The scalar parameter $z$ in (8.3) is distinct from the physical basis
vector $z=e_2$ in (1.1).

**Theorem 8.2 (Exact erased-continuation correction family).**
For every real $\theta$ and every CPTP $\mathcal T:M_3\to M_3$,
the following conditions are equivalent:

1. Both actual task equalities (8.2) hold for every qutrit density.
2. The immediate task is preserved and
   $\mathcal F\circ\mathcal T=\mathcal F$ on $M_3$.
3. $\mathcal T=\mathcal D_z$ for a unique $z$ with $|z|\le1$.

In particular the two probability requirements already imply equality
of the entire erased successor channel, with every untouched finite
reference. This conclusion concerns the successor after the erased
acquisition; it does not assert preservation of the state left by the
immediate task measurement.

Proof. Write $v=v_e$ and $r=(\xi-e)/\sqrt2$. The vectors $(v,r,f)$
are an orthonormal basis, with $P_+=|v\rangle\langle v|+
|r\rangle\langle r|$. Use the actual one-step effects (5.6), rather
than treating the two discarded labels as two separately accessible
tests. Their average is

$$
\begin{aligned}
G:=\mathcal F^\dagger(E)
 &=\tfrac12(F_0+F_1)
   =|a\rangle\langle a|+\tfrac38|f\rangle\langle f|,\\
a&=(\xi-e/2)/\sqrt2=\tfrac14v+\tfrac34r,\\
G\big|_{(v,r,f)}
 &=\begin{pmatrix}
 1/16&3/16&0\\3/16&9/16&0\\0&0&3/8
 \end{pmatrix}.
\tag{8.4}
\end{aligned}
$$

This is independent of $\theta$, as is (8.1). All-density separation
turns (8.2) into $\Phi(E)=E$ and $\Phi(G)=G$, where
$\Phi=\mathcal T^\dagger$ is unital and completely positive.

Use the fixed-projection implication in (5.8), equivalently the
conserved-algebra argument of [Bény–Kempf–Kribs, Theorem 5][BKK]
with input code projection $I_3$. For a normalized Kraus family
$L_\ell$ of $\mathcal T$, fixing $E$ forces
$EL_\ell=L_\ell E$ for every $\ell$. In particular

$$
\Phi(EX)=E\Phi(X),\qquad
\Phi(XE)=\Phi(X)E
\quad(X\in M_3).
\tag{8.5}
$$

Apply (8.5) to $G$. Set $R_0=|r\rangle\langle r|$ and
$N_0=|f\rangle\langle f|$. Both $I_3-E=R_0+N_0$ and

$$
(I_3-E)G(I_3-E)=\tfrac9{16}R_0+\tfrac38N_0
\tag{8.6}
$$

are fixed by $\Phi$. Subtracting $3/8$ times the first fixed
operator from the second gives $\Phi(R_0)=R_0$, because
$9/16-3/8=3/16\ne0$. Hence $\Phi(N_0)=N_0$. Moreover

$$
EG(I_3-E)=\tfrac3{16}|v\rangle\langle r|
\tag{8.7}
$$

is fixed, as is its adjoint. These four plus-block matrix units and
$N_0$ span exactly

$$
\mathcal A=P_+M_3P_+\oplus\mathbb CP_-\simeq M_2\oplus\mathbb C.
\tag{8.8}
$$

Thus $\Phi$ fixes this whole algebra. The same fixed-projection
implication now makes every $L_\ell$ commute with all projections
of $\mathcal A$. Commutation with $P_+,P_-$ removes cross blocks;
commutation with the rank-one projections in the plus block makes
that restriction scalar. Consequently

$$
L_\ell=\alpha_\ell P_++\beta_\ell P_-,\qquad
\sum_\ell|\alpha_\ell|^2=\sum_\ell|\beta_\ell|^2=1.
\tag{8.9}
$$

This is the component-scalar supplier of [ProbeComponentRigidity][PCR]
applied to the evaluated algebra (8.8). Substitution in the Kraus sum
gives (8.3), with
$z=\sum_\ell\alpha_\ell\overline{\beta_\ell}$ and $|z|\le1$ by
Cauchy–Schwarz. Its value is unique by testing any nonzero operator
from the minus block to the plus block. This proves $1\Rightarrow3$.

Conversely, for every $|z|\le1$ the two Kraus matrices

$$
K_1=P_++\overline zP_-,\qquad
K_2=\sqrt{1-|z|^2}\,P_-
\tag{8.10}
$$

have adjoint-Gram sum $I_3$ and give exactly $\mathcal D_z$.
It is therefore CPTP. It preserves $E\in\mathcal A$ and satisfies
$\Delta_W\mathcal D_z=\Delta_W$, so (8.1) gives
$\mathcal F\mathcal D_z=\mathcal F$. Hence $3\Rightarrow2$;
$2\Rightarrow1$ follows by taking the $E$ expectation of the successor.
The successor identity is an identity of complex-linear maps, so it
tensor-extends to every finite reference. $\square$

The source-specific part of this theorem is the evaluated erased
effect (8.4) and its implication (8.6)–(8.8) for this actual pair of
tasks. The conserved-algebra and component-scalar implications are
literature-attested suppliers, not new general nondisturbance results.
The theorem is a `repo-derived` deduction at the stated task interface.

## 9. Erasure with retained classical records and subsequent use

**Definition 9.1 (Joint history interface).** Let $\lambda$ denote a
finite or countable complete classical record obtained before the
qutrit correction, with input-independent probabilities $p_\lambda$.
Conditional on $\lambda$, let $\mathcal S_\lambda:M_3\to M_3$ be
CPTP, and put $\mathcal T=\sum_\lambda p_\lambda\mathcal S_\lambda$.
For the actual history acquisition one may take

$$
\lambda=(h,a),\qquad p_{h,a}=2^{-n}r(a\mid h),\qquad
\mathcal S_{h,a}=\mathcal C_a\circ\operatorname{Ad}_{Q_h}.
\tag{9.1}
$$

An actually retained subrecord is any classical postprocessing of
$\lambda$; including the whole pair in a mathematical comparison
does not install an unavailable history port. Reference inputs in
this interface are arbitrary densities $\rho$ on $\mathbb C^3\otimes Z$,
independent of the initial classical randomness. Actual fairness on
the embedded qutrit gives the same $p_{h,a}$ also for these inputs.

**Theorem 9.2 (Joint erased successor from averaged task correctness).**
In Definition 9.1, if the average channel satisfies (8.2), then every
$\mathcal S_\lambda$ with $p_\lambda>0$ is some
$\mathcal D_{z_\lambda}$. Thus for every finite reference $Z$,

$$
\begin{aligned}
\sum_\lambda p_\lambda|\lambda\rangle\langle\lambda|\otimes
 ((\mathcal F\circ\mathcal S_\lambda)\otimes\operatorname{id}_Z)(\rho)
 =\sum_\lambda p_\lambda|\lambda\rangle\langle\lambda|\otimes
 (\mathcal F\otimes\operatorname{id}_Z)(\rho).
\tag{9.2}
\end{aligned}
$$

The corresponding joint immediate record/result probabilities also
agree. After the erased acquisition, any common finite continuation
instrument controlled by the actually retained subrecord has the same
joint output and successor law on both sides of (9.2), including all
its retained labels and the untouched reference.

Proof. By Theorem 8.2, $\mathcal T=\mathcal D_z$, and its adjoint
fixes every projection $P$ of $\mathcal A$. The effects
$\mathcal S_\lambda^\dagger(P)$ have the projection $P$ as their
$p_\lambda$-weighted average. Sharp-effect extremality, exactly as in
the proof of Theorem 2.1, forces
$\mathcal S_\lambda^\dagger(P)=P$ for each positive $p_\lambda$.
One can apply this to a finite spanning set of projections of
$\mathcal A$, so there is no issue of incompatible exceptional sets
in a countable mixture. With $v=v_e$ and $r=(\xi-e)/\sqrt2$, the
projections of $v,r,f$ and of $(v+r)/\sqrt2,(v+ir)/\sqrt2$ span its
Hermitian part.
The component-scalar argument (8.9) therefore applies to each
$\mathcal S_\lambda$. In particular it preserves $E$ and its erased
successor is exactly $\mathcal F$.

Tensor-extension gives each summand of (9.2), proving the joint
identity before any classical record is discarded. The immediate
result equality follows from the same summandwise $E$ preservation;
as a quantum-to-classical channel identity it also preserves the
joint outcome/reference state. Classical postprocessing preserves
these equalities. A record-controlled future instrument is one CP
map on each classical block, with total trace-preserving sum.
Composing those very maps with the equal blocks in (9.2) proves
equality of their subnormalized outputs. Iteration proves the claim
for every specified finite adaptive continuation. All added
preparations, measurements, selectors, legal controls and records
are still resources of that continuation. $\square$

The erased first label is absent from (9.2). If it is retained, the
relevant interface instead has blocks $\mathcal J_j\mathcal T$;
equality of their sum is insufficient. Theorem 5.2 supplies the
qutrit-output classification for that labelled task. Likewise (9.2)
does not assert that an immediate destructive task read leaves the
original state available for arbitrary further use.

## 10. Coherent storage after correction

**Definition 10.1 (Finite flag, one coherent port, no quantum bypass).**
Use the finite classical-flag model of
[Measurement-relative quantum boundary, Definition 1.3][MRQB], with
system dimension three. For an integer $q\ge1$ and a finite alphabet
$\mathsf L$, a storage implementation consists of CPTP maps

$$
\operatorname{Enc}:M_3\longrightarrow\bigoplus_{\ell\in\mathsf L}M_q,
\qquad
\operatorname{Dec}((Y_\ell)_\ell)=
 \sum_\ell\operatorname{Dec}_\ell(Y_\ell),
\qquad \mathcal T=\operatorname{Dec}\circ\operatorname{Enc}.
\tag{10.1}
$$

Each $\operatorname{Dec}_\ell:M_q\to M_3$ is CPTP on the entire
block. The maps are fixed before the unknown input and late task
choice. Every input-dependent quantum carrier during the storage
interval is included in the $q$-dimensional port; the original carrier,
a quantum environment and preshared entanglement cannot bypass it.
The flag can depend on the input. Its finite classical size is
counted separately from $q$ and from the earlier input-independent
history record. As in the supplier model, it is consumed or discarded
by decoding before the future task unless a joint flag interface is
explicitly retained.

**Theorem 10.2 (Erased-task minimum and prescribed block multiplier).**
In Definition 10.1, the minimum coherent dimension of a channel
satisfying (8.2) is two. For a prescribed $\mathcal D_z$, $|z|\le1$,
the exact minimum is

$$
q_{\min}(\mathcal D_z)=
\begin{cases}
2,&z=0,\\
3,&z\ne0.
\end{cases}
\tag{10.2}
$$

Both values are attained by actual encoders and whole-block CPTP
decoders. The two-dimensional construction has a two-value classical
flag. If that flag is also retained at use, its joint successor is
the flagged instrument described below, rather than an independent
flag appended to $\mathcal F$.

Proof. Use the rectangular Kraus factorization of the existing
[CoherentFlagPort][CFP] and its [owning Scribe][CFPB]. Encoder
operators $B_{\ell a}:\mathbb C^3\to\mathbb C^q$ obey
$\sum_{\ell,a}B_{\ell a}^\dagger B_{\ell a}=I_3$; decoder operators
$C_{\ell b}:\mathbb C^q\to\mathbb C^3$ obey
$\sum_b C_{\ell b}^\dagger C_{\ell b}=I_q$ for each $\ell$.
Every composite Kraus matrix
$L_{\ell ba}=C_{\ell b}B_{\ell a}$ has rank at most $q$.
This factorization applies to arbitrary CPTP maps in (10.1), by the
finite rectangular Kraus supplier [FiniteKrausRepresentation][KRAUS].

Theorem 8.2 and its fixed-algebra argument apply to this particular
composite Kraus family, not only to the convenient representation
(8.10). Thus every member has form (8.9). Normalization requires
some $\alpha_{\ell ba}\ne0$, whose scalar restriction to the
two-dimensional plus block gives rank at least two. Hence $q\ge2$.
If the prescribed $z$ is nonzero, the identity

$$
z=\sum_{\ell,b,a}\alpha_{\ell ba}\overline{\beta_{\ell ba}}
\tag{10.3}
$$

requires a term with both coefficients nonzero. That member is
invertible on the direct sum of the two blocks and has rank three.
Therefore $q\ge3$ for $z\ne0$, irrespective of the number of finite
flags or Kraus operators.

For attainment at $z=0$, take an orthonormal basis $(b_0,b_1)$ of
$\mathbb C^2$ and the isometry $J:\mathbb C^2\to\mathbb C^3$
given by $Jb_0=\xi$, $Jb_1=e$. With flag alphabet $\{+,-\}$ set

$$
\begin{aligned}
\operatorname{Enc}_+(X)&=J^\dagger XJ,&
\operatorname{Enc}_-(X)&=\langle f,Xf\rangle
                              |b_0\rangle\langle b_0|,\\
\operatorname{Dec}_+(Y)&=JYJ^\dagger,&
\operatorname{Dec}_-(Y)&=\operatorname{Tr}(Y)|f\rangle\langle f|.
\tag{10.4}
\end{aligned}
$$

The encoder has branch Kraus matrices $J^\dagger$ and
$|b_0\rangle\langle f|$ with adjoint-Gram sum $P_++P_-=I_3$.
The plus decoder is trace preserving because $J^\dagger J=I_2$;
the minus decoder has Kraus matrices $|f\rangle\langle b_i|$,
$i=0,1$, whose adjoint-Gram sum is $I_2$. In particular it is a
legal decoder also on the unused $b_1$ direction. Their composite
is exactly $\Delta_W=\mathcal D_0$. This is the explicit
orthogonal-component coding and complete padding construction of
[OrthogonalCoherentEmbedding][OCE] and its [Scribe][OCEB] on the
actual blocks of dimensions two and one.

For every $z\ne0$ in the disk, take $q=3$, a single flag, the
identity encoder, and decoder $\mathcal D_z$ with the normalized
Kraus family (8.10). These maps attain the prescribed channel.
Together with the lower bounds they prove (10.2), and allowing
the choice $z=0$ gives the task minimum two.

For completeness, retaining the flag of an arbitrary implementation
of $\mathcal D_z$ gives CP subchannels
$\mathcal K_\ell=\operatorname{Dec}_\ell\circ\operatorname{Enc}_\ell$.
By the same composite Kraus formula put

$$
\begin{gathered}
a_\ell=\sum_{b,a}|\alpha_{\ell ba}|^2,\quad
b_\ell=\sum_{b,a}|\beta_{\ell ba}|^2,\quad
c_\ell=\sum_{b,a}\alpha_{\ell ba}\overline{\beta_{\ell ba}},\\
\mathcal K_\ell(X)=a_\ell P_+XP_++b_\ell P_-XP_-
       +c_\ell P_+XP_-+\overline{c_\ell}P_-XP_+,\\
\sum_\ell a_\ell=\sum_\ell b_\ell=1,\qquad
\sum_\ell c_\ell=z.
\tag{10.5}
\end{gathered}
$$

Its actual flagged erased successor, on every matrix, is therefore

$$
\sum_\ell|\ell\rangle\langle\ell|\otimes
 \mathcal F\bigl(a_\ell P_+XP_++b_\ell P_-XP_-\bigr).
\tag{10.6}
$$

All these identities tensor-extend to a reference. The flag law is
$\operatorname{Tr}((a_\ell P_++b_\ell P_-)X)$ on a density $X$;
it need not be input independent. In (10.4), (10.6) is exactly

$$
\sum_{s\in\{+,-\}}|s\rangle\langle s|\otimes
                       \mathcal F(P_sXP_s).
\tag{10.7}
$$

Thus the joint comparison retaining this flag uses the same initial
block measurement on the ideal route. Tracing out the flag gives
$\mathcal F(X)$, but it does not justify replacing (10.7) by a
product of that marginal and an independent classical flag. Subsequent
flag-controlled use composes with (10.6) or (10.7), as appropriate.
$\square$

The finite-flag model and rank factorization are literature-attested
suppliers: Bluhm–Rauber–Wolf,
[Quantum compression relative to a set of measurements][BRW],
Definition 4.1 and the proof of Lemma 5.2. Their Theorem 7.1 supplies
the maximal-block upper construction; here the relevant algebra is
the explicitly forced $M_2\oplus\mathbb C$ in (8.8). That theorem
is an upper bound for general observable families, not a general
assertion that a generated algebra always gives the exact minimum.
The lower bounds here use (8.9) on every actual composite Kraus
matrix, including the extra rank-three obstruction when $z\ne0$.
This evaluated continuation and prescribed-channel resource cut is
`repo-derived`; the generic coding construction is not a new result.

**Definition 10.3 (Acquisition cut and storage cut).** The history
record is retained through the required terminal inverse control.
Only after that control is invoked does the storage interval of
Definition 10.1 begin. At this interval the old record can be released
if no later task requires it. The flag in (10.4) is new, is obtained
from the actual specimen, and occupies a separate two-value classical
carrier throughout storage and decoding. The discarded original
quantum carrier is not an additional storage channel.

For the immediate and erased tasks, use the effect-fiber record,
its exact iff criterion and its minimum $m_n/2$ for $n\ge1$ from
Theorem 2.1, with one value at $n=0$. No new record-count theorem is
needed: the immediate task already supplies necessity. For sufficiency
its existing representative inverse leaves each compatible history
as $\rho$ or $W\rho W$. The two residual channels are
$\mathcal D_1$ and $\mathcal D_{-1}$; (8.2) and
the full joint successor (9.2) follow. Inserting (10.4) after that
inverse leaves exactly $\Delta_W(\rho)$ on every history, since
$\Delta_W\operatorname{Ad}_W=\Delta_W$. Hence the supplied minimum
history record and the two-dimensional storage upper are attained
on the same run under their respective control permissions. If both
the old record and the new flag are retained, their actual erased
successor is, with the weights of (9.1),

$$
\sum_{h,a,s}2^{-n}r(a\mid h)
 |h,a,s\rangle\langle h,a,s|\otimes\mathcal F(P_s\rho P_s),
\tag{10.8}
$$

with tensor-extension when a reference is present. Any accessible
subrecord is obtained by the actual classical postprocessing.

The acquired implementations and costs are the suppliers in
Theorems 3.1–3.2. At $\theta=\pi/6$ they retain the actual suffix
of $n-1$ bits and use $n$ inverse-letter invocations for $n\ge1$;
at $\theta=0$ they use the three-position task accumulator and one
selected inverse-permutation invocation, with the smaller reached
alphabets at $n=0,1,2$ as in (3.4). These invocations precede the
storage encoder. Every original run has $n$ fresh environment
preparations, interactions, environment measurements and actual
label acquisitions. The erased continuation adds one of each and
discards its new label; its terminal task adds one binary measurement.
The encoder and decoder in (10.4), their calibration, the storage
flag and any physical addressing or timing apparatus are additional
resources. No optimality of the combined actuation cost is implied.

To implement a prescribed nonzero $z$ on the original unknown input,
a valid same-run upper instead first uses the full-word-class inverse
of ERM Theorem 16.1, and then the three-dimensional implementation
of $\mathcal D_z$. The old class record remains readable until that
inverse has been applied and may then be released. At $\pi/6$ the
supplier retains $n$ labels and uses $n$ inverse-letter invocations;
at zero angle its six-state permutation accumulator and selected
inverse suffice. This is a supplied upper with the full-word record,
not a claim that a nonzero $z$ can be installed after the minimum
effect-fiber record has already erased the missing coherence. At
$n=0$ no history acquisition or inverse is needed in either route.

For an arbitrary fixed real calibration, Proposition 2.2 and ERM
Theorem 16.1 supply existential finite tables on their respective
record domains. They do not supply unknown-angle acquisition or a
uniform effective procedure for exact-real word comparison or control
synthesis. The storage cut does not remove those prerequisites.

The following comparison credits its first and third entries to the
existing sharp readout and labelled rigidity suppliers:

| Qutrit-output task after the storage decoder | Minimum coherent dimension | Supplier or deduction |
| --- | --- | --- |
| Immediate sharp $E$ probability only | $1$ | Sharp measure-and-prepare readout, as in the observable-correction note [NOTE] and the commutative case of [BRW] Theorem 7.1 |
| Immediate $E$ and the actual erased-label continuation (8.2) | $2$ | Theorems 8.2 and 10.2 on this actual source |
| Immediate $E$ and the recorded joint $j,y$ continuation with qutrit output | $3$ | Theorem 5.2 forces identity; the existing coherent-port rank bound and the identity port attain dimension three |

In the first entry the encoder measures $E$ and retains its binary
result classically; the decoder prepares $v_e$ or $f$ according to
that result. The one-dimensional coherent block carries no unknown
quantum information. In the third entry identity has only scalar
identity Kraus matrices, so a nonzero one has rank three. These are
applications of the cited suppliers, not additional new dimension
theorems. None of these three qutrit-output cuts classifies storage
with unrestricted full-$H$ decoder output.

## 11. A late actual full-H acquisition after unrestricted decoding

**Definition 11.1 (Full-H output, common decoder, recorded future).**
Keep exactly the original acquisition and complete finite or countable
kernel (1.6). In particular the $n$ original histories are fair on
all qutrit inputs, and the kernel is independent of that input.
Allow arbitrary CPTP $\mathcal D_a:M_5\to M_5$, without requiring
their outputs to lie in $R$. Apply this common decoder before a late
choice. The two alternatives are the immediate binary test
$(\widehat E,I_5-\widehat E)$ and one further actual full-$H$
acquisition followed by that test, retaining its joint outcomes
$(j,y)$. There is no new correction after the acquisition.

The full-$H$ acquisition operators are exactly those of ERM
Theorem 2.2. To fix their action also on leaked states, write

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+
       2^{-1/2}|v\rangle\langle e_2|+|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+
       2^{-1/2}|v\rangle\langle e_2|+|z\rangle\langle e_3|,\\
A_0&=\cos\theta K_0+i\sin\theta K_1,\qquad
A_1=i\sin\theta K_0+\cos\theta K_1,\\
\mathcal A_j(X)&=A_jXA_j^\dagger,\qquad
\widehat E^{(1)}=\widehat E=BE B^\dagger,\quad
\widehat E^{(0)}=I_5-\widehat E.
\tag{11.1}
\end{aligned}
$$

Here the ket $v$ in the $K_j$ formulas is the physical vector of
(1.1), not $v_e$. On $R$ the restricted formula is still
$A_jB=BV_j/\sqrt2$; it is not substituted for (11.1) on other states.
The complete task requires, for every qutrit density $\rho$,

$$
\begin{aligned}
\sum_{h,a}p_{h,a}\operatorname{Tr}\bigl(
 \widehat E\,\mathcal D_a(BQ_h\rho Q_h^\dagger B^\dagger)\bigr)
 &=\operatorname{Tr}(E\rho),\\
\sum_{h,a}p_{h,a}\operatorname{Tr}\bigl(
 \widehat E^{(y)}\mathcal A_j(
 \mathcal D_a(BQ_h\rho Q_h^\dagger B^\dagger))\bigr)
 &=\operatorname{Tr}\bigl(
 \widehat E^{(y)}\mathcal A_j(B\rho B^\dagger)\bigr)
 \quad(j,y\in\{0,1\}),\\
p_{h,a}&=2^{-n}r(a\mid h).
\tag{11.2}
\end{aligned}
$$

Thus the target is the joint law of the original actual acquisition
on the original embedded input. Correctness is required for each late
alternative, not only for an average over a chosen distribution of
queries. Equation (11.2) assumes no conditional correctness in advance.

**Theorem 11.2 (Full-word record necessity with arbitrary full-H decoding).**
For every real $\theta$ and integer $n\ge0$, CPTP decoders satisfying
(11.2) exist if and only if every positive record fiber refines
$[Q_h]$:

$$
r(a\mid h)r(a\mid g)>0
\quad\Longrightarrow\quad [Q_h]=[Q_g].
\tag{11.3}
$$

Consequently the exact finite alphabet and fixed binary payload are
the supplied full-word quantities
$m_n(\theta)$ and $\lceil\log_2m_n(\theta)\rceil$ of ERM
Theorem 16.1. They include one value and zero bits at $n=0$.
Its actual class accumulation and inverse controls attain this
existence statement on the same specimen. Including the actually
retained old record in the required joint output leaves this
existence criterion unchanged. This theorem makes no
classification assertion about every successful rectangular
corrected map $M_3\to M_5$.

Proof. At $n=0$ the sole empty word makes (11.3) automatic, and
identity decoding attains (11.2). For necessity at $n\ge1$, set
$p=Bv_e$, $P=|p\rangle\langle p|=\widehat E$ and
$t_j=A_j^\dagger p$. The actual full-$H$ effects for the future
$y=1$ event are

$$
G_j^{H}=A_j^\dagger P A_j=|t_j\rangle\langle t_j|,
\qquad B^\dagger G_j^{H}B=\tfrac12F_j.
\tag{11.4}
$$

These are positive effects, not projections rescaled by an asserted
full-$H$ fairness law. The complementary joint effect is
$A_j^\dagger A_j-G_j^{H}$, and the two sum to the actual
$A_j^\dagger A_j$ on all of $H$.

For a fixed record $a$, take finite rectangular Kraus matrices
$L_{a\nu}:\mathbb C^3\to H$ for
$X\mapsto\mathcal D_a(BXB^\dagger)$. They obey
$\sum_\nu L_{a\nu}^\dagger L_{a\nu}=I_3$. Define

$$
H_a=\sum_\nu L_{a\nu}^\dagger P L_{a\nu},\qquad
M_{a,j}=\sum_\nu L_{a\nu}^\dagger G_j^{H}L_{a\nu}.
\tag{11.5}
$$

Then $0\le H_a\le I_3$ and $M_{a,j}\ge0$. The first equality
of (11.2) gives
$\sum_{h,a}p_{h,a}Q_h^\dagger H_aQ_h=E$.
By the existing sharp-effect argument of Theorem 2.1, every
positive summand has $H_a=Q_hEQ_h^\dagger$. Its source-specific
fiber calculation (2.2) says that histories sharing $a$ obey

$$
Q_h=Q_g\quad\hbox{or}\quad Q_h=Q_gW.
\tag{11.6}
$$

The spectator phase in that calculation is retained; all these
histories have the same known length. This use of Theorem 2.1
already includes arbitrary full-$H$ output.

The future equation for $j=0,y=1$ gives the positive-operator identity

$$
\sum_{h,a}p_{h,a}Q_h^\dagger M_{a,0}Q_h
                   =\tfrac12F_0
                   =\tfrac12|w_+\rangle\langle w_+|.
\tag{11.7}
$$

Every positive summand on the left is supported in the line
$\mathbb Cw_+$. Indeed its quadratic form on $w_+^\perp$ is
nonnegative and has sum zero there, so it vanishes there; positivity
then annihilates that subspace. This argument is valid for a
countable record alphabet. In the Kraus expansion (11.5) it implies

$$
L_{a\nu}^\dagger t_0\in\mathbb C Q_hw_+
\quad\text{for every }\nu\text{ whenever }r(a\mid h)>0.
\tag{11.8}
$$

Suppose the second, unequal possibility of (11.6) occurs at one
positive $a$. Since $Ww_+=w_-$, (11.8) puts each vector
$L_{a\nu}^\dagger t_0$ in both $\mathbb C Q_gw_+$ and
$\mathbb C Q_gw_-$. These are distinct lines: $w_+,w_-$ are
unit vectors with overlap $1/4$, by (5.7). Their intersection is
zero. Hence $L_{a\nu}^\dagger t_0=0$ for all $\nu$, and
$M_{a,0}=0$.

On the other hand $H_a=Q_gEQ_g^\dagger$ gives

$$
\operatorname{Tr}\bigl(P\,
 \mathcal D_a(BQ_gEQ_g^\dagger B^\dagger)\bigr)=1.
\tag{11.9}
$$

The argument of this $P$ expectation is a positive trace-one
matrix. A rank-one projection has expectation one only on its
own pure state: its orthogonal-complement trace is zero, positivity
annihilates that complement, and trace one fixes the remaining
coefficient. Thus the decoded state in (11.9) is exactly $P$.
But the actual source supplies the nonzero overlap

$$
\begin{aligned}
\langle t_0,p\rangle
 &=\langle p,A_0p\rangle
   =\frac{\langle v_e,V_0v_e\rangle}{\sqrt2}
   =\frac{e^{i\theta}}{4\sqrt2},\\
\operatorname{Tr}(G_0^{H}P)&=\frac1{32}>0.
\tag{11.10}
\end{aligned}
$$

Here the last equality follows from
$V_0^\dagger v_e=e^{-i\theta}w_+$ and (5.7), with the
conjugate-linear-first convention of ERM. Equations (11.9)–(11.10)
make the future $G_0^{H}$ probability of that decoded state positive,
whereas $M_{a,0}=0$ makes the same probability zero. This contradiction
excludes $Q_h=Q_gW$. Therefore (11.3) is necessary. The proof uses
only a positive support consequence of the future effect; it does
not promote the unsharp equation (11.7) to branchwise equality
with $F_0/2$.

Conversely suppose (11.3). Choose a representative $Q_a$ for each
positive record and use the supplied full-$H$ unitary inverse

$$
D_a=BQ_a^\dagger B^\dagger+(I_5-P_R),\qquad
\mathcal D_a=\operatorname{Ad}_{D_a}.
\tag{11.11}
$$

Its two orthogonal blocks are unitary. For every compatible history,
$Q_a^\dagger Q_h$ is scalar, so it recovers $B\rho B^\dagger$
on that very branch, also jointly with any untouched reference.
Applying the actual maps $\mathcal A_j$ and the specified binary
test proves all four future equations of (11.2), including the
complementary outcomes, and the immediate equality. This is the
same common decoder before either possible late choice.

Every history has positive original probability. Different full
word classes therefore require disjoint nonempty sets of positive
record values, and recording the class attains that bound. The
cardinality, fixed payload and acquired inverse uppers are precisely
the suppliers of ERM Theorem 16.1; only their necessity for the
present full-$H$ future task has been established here. When $n=0$
there is only the empty class, and identity is the inverse in
(11.11). No division of $m_0=1$ by two is involved. $\square$

For this upper construction the full retained joint interface is
explicit. For any finite reference density $\rho$ and every positive
$(h,a)$, the state after correction is
$(B\otimes I_Z)\rho(B^\dagger\otimes I_Z)$. The joint record and
subnormalized successor after the new acquisition is consequently

$$
\sum_{h,a,j}2^{-n}r(a\mid h)|h,a,j\rangle\langle h,a,j|
 \otimes\tfrac12(BV_j\otimes I_Z)\rho
                              (V_j^\dagger B^\dagger\otimes I_Z).
\tag{11.12}
$$

Applying the actual terminal binary test to each block gives its
joint $(a,j,y)$ law, and any actually retained history subrecord
can also be kept. This proves sufficiency for a joint task that
also retains the old record; its necessity follows by forgetting
that record and applying (11.2). Formula (11.12) is attained by
(11.11); it is not inferred for every decoder satisfying only
(11.2). Further
successive instruments agree on this upper because the original
embedded state was recovered before the late choice.

There are the original $n$ preparations, interactions, environment
measurements and label acquisitions. The continuation alternative
adds one of each, retains the new label, and performs one terminal
binary task measurement. The immediate alternative performs only
the binary task measurement after correction. Full-word acquisition
and inverse use at $\pi/6$ and zero angle are exactly the suppliers
specified in Definition 10.3. Their history record is needed through
the inverse, and can be released afterwards unless a later task
requires it; retaining it instead uses (11.12). None of these
attained costs is a minimum total hardware or control-cost theorem.

The Heisenberg correction interface and positivity implications
are those of [Bény–Kempf–Kribs, Definition 8 and Theorem 5][BKK].
Their Theorem 9 concerns algebras with compressed Kraus-product
commutators; it is not a license to replace the actual unsharp
full-$H$ effects by fair qutrit projections. The source-relative
increment in Theorem 11.2 is the combination of the supplied
effect fiber with the actual full-$H$ rank-one support (11.7)
and nonzero overlap (11.10). This `repo-derived` existence and
record-minimum deduction does not assert rectangular corrected-map
identity or transport Theorem 10.2 to full-$H$ storage.

## 12. Domains and independent realization requirements

**Definition 12.1 (Scope of the two continuation contracts).**
Sections 8–10 use qutrit output, the actual erased-label acquisition,
and the fixed finite-flag storage model. Section 11 uses unrestricted
full-$H$ output and retains the actual future label; its conclusion
is existence of decoders and the exact record refinement. The
two output domains, the two future record interfaces, and the
pre-correction and storage resource cuts are distinct. The preceding
theorems resolve these bounded contracts without changing the
erased-history minimax, signed P/Q, autonomous STOP or fixed-apparatus
settlements cited in §7. A classification of all successful leaked
corrected maps, a coherent-port minimum for that leaked-output
contract, and finite-precision or unknown-calibration versions are
not consequences of the results above.

The common actual source throughout is (1.1)–(1.4), with all qutrit
inputs, actual fresh-environment acquisitions, complete classical
records, the same inaccessible references, and the stated calibrated
control permissions. The finite-flag dimension counts do not infer
new native controls or reduce the dimension of the physical output
$H$. In particular the independent five-mode waiting and filter
experiments of [MRQB] retain their own inputs, detectors, finite
records and filter hypotheses; their all-filter classification is
not an identification with this measured-label source.

An independently meaningful spatial view would require its own
acquisition and a proved correspondence to these actual preparations,
actions and joint readouts. A physical-duration view would require
more than the integer number of acquisitions. An identification with
the native atomic $\alpha/\beta$ process would require a common
initialization, lawful selectors and installed retained-use operations,
with their resource and successor correspondence. None of these
additional structures is assumed or constructed in §§8–11. The
atomic global-port results, NCR/PVC/PR57/PG/Atlas results and the
original fixed-model open bridges keep their original domains.
Consequently the exact task-relative recovery statements above
do not supply a mutually recoverable space/time/boundary/memory
structure for the continuing programme.

[MRQB]: RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md
[CFP]: ../../../D5/S3/Quantum/Reduction/CoherentFlagPort.lean
[CFPB]: ../../../Blueprint/D5/S3/Quantum/Reduction/CoherentFlagPort.scribe.cs
[OCE]: ../../../D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.lean
[OCEB]: ../../../Blueprint/D5/S3/Quantum/Reduction/OrthogonalCoherentEmbedding.scribe.cs
[BRW]: https://arxiv.org/abs/1708.04898v4

## 追加锚（本行以下为增补区）
