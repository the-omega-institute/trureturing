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
