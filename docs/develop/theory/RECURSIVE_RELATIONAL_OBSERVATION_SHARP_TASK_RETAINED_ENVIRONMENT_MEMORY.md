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

## 13. Exact rectangular rigidity for the actual retained-label task

**Theorem 13.1 (All successful full-H corrected channels).**
Use exactly Definitions 1.1–1.2 and 11.1, with their actual embedding
$B:\mathbb C^3\to H=\mathbb C^5$, chronological words $Q_h$,
full-$H$ operators $A_j$ of (11.1), and common pre-choice decoders.
For every real $\theta$, integer $n\ge0$, finite or countable record
alphabet $\mathcal A$, input-independent kernel $r(a\mid h)$ satisfying
(1.6) for every length-$n$ history, and family of complex-linear CPTP
maps $\mathcal D_a:M_5(\mathbb C)\to M_5(\mathbb C)$, put

$$
\begin{aligned}
p_{h,a}&=2^{-n}r(a\mid h),\\
\Phi_{h,a}(X)&=\mathcal D_a(BQ_hXQ_h^\dagger B^\dagger),\\
\overline\Phi(X)&=\sum_{h,a}p_{h,a}\Phi_{h,a}(X).
\end{aligned}
\tag{13.1}
$$

The following statements are equivalent: all five averaged task
equations (11.2) hold for every complex qutrit density input, for both
late alternatives and every $j,y\in\{0,1\}$; the average satisfies

$$
\overline\Phi(X)=BXB^\dagger
\quad\text{for every }X\in M_3(\mathbb C);
\tag{13.2}
$$

and every positive original history/record branch satisfies

$$
\Phi_{h,a}(X)=BXB^\dagger
\quad\text{for every }X\in M_3(\mathbb C)
\quad\text{whenever }r(a\mid h)>0.
\tag{13.3}
$$

Equivalently, the restriction of every successful record-selected
physical decoder to its actual qutrit input is

$$
\mathcal D_a(BYB^\dagger)=BQ_h^\dagger YQ_hB^\dagger
\quad\text{for every }Y\in M_3(\mathbb C)
\quad\text{whenever }r(a\mid h)>0.
\tag{13.4}
$$

For every finite untouched inaccessible reference of dimension $d$ and
every joint density $\rho\in\mathsf D(\mathbb C^3\otimes\mathbb C^d)$,
these same conclusions give

$$
\begin{aligned}
(\overline\Phi\otimes\operatorname{id}_{M_d})(\rho)
 &=(B\otimes I_d)\rho(B^\dagger\otimes I_d),\\
(\Phi_{h,a}\otimes\operatorname{id}_{M_d})(\rho)
 &=(B\otimes I_d)\rho(B^\dagger\otimes I_d)
 \quad\text{if }r(a\mid h)>0.
\end{aligned}
\tag{13.5}
$$

No output-in-$R$ hypothesis or conditional future correctness is
assumed. Formula (13.4) specifies only the decoder's action on
$BM_3B^\dagger$, the matrices supported in $R$. Its action on inputs
outside that corner, including coherences between $R$ and $R^\perp$,
is not classified.

Proof. Each $Q_h$ is unitary, $B^\dagger B=I_3$, and every
$\Phi_{h,a}$ is CPTP. The actual original-history weights obey

$$
\sum_{h,a}p_{h,a}
 =\sum_{h\in\{0,1\}^n}2^{-n}\sum_a r(a\mid h)=1.
\tag{13.6}
$$

This includes $n=0$, when there is the sole empty history
$Q_\varnothing=I_3$. In the unnormalized Choi convention a CPTP map
$M_3\to M_5$ has a positive Choi matrix of trace three. Thus the
countable sum in (13.1) converges in Choi trace norm, has positive
Choi matrix and the trace-preserving partial trace, and defines a CPTP
map $T=\overline\Phi$. All following identities concern this original
average, with the chronological words and weights unchanged.

Use the actual §5 coordinates and §11 effects:

$$
\begin{gathered}
v_0=v_e=(\xi+e)/\sqrt2,\qquad p=Bv_0,\qquad
P=pp^\dagger=\widehat E,\\
t_j=A_j^\dagger p,\qquad
w_0=w_+,\quad w_1=w_-,\qquad F_j=w_jw_j^\dagger,\\
w_\pm=\frac{\xi-e/2\ \pm\ (\sqrt3/2)e^{2i\theta}f}{\sqrt2}.
\end{gathered}
\tag{13.7}
$$

Here $(\xi,e,f)$ and their physical embedding are exactly (1.1),
(1.5), and (5.5)–(5.7). The three unit vectors $v_0,w_0,w_1$
span $\mathbb C^3$ for every real angle: their difference supplies
$f$, their sum supplies $\xi-e/2$, and $v_0$ supplies $\xi+e$.
Their nonzero overlaps and the restricted action $A_jB=BV_j/\sqrt2$
give the precise identities

$$
\begin{aligned}
B^\dagger t_j&=e^{-i\theta}w_j/\sqrt2,&
\langle v_0,w_j\rangle&=1/4,\\
\langle p,t_j\rangle&=e^{-i\theta}/(4\sqrt2),&
A_jBw_j&=e^{i\theta}p/\sqrt2.
\end{aligned}
\tag{13.8}
$$

The inner product is conjugate-linear in its first argument. These
formulas use the actual full-$H$ operators on their embedded inputs;
they impose no fairness law on leaked outputs.

Assume (11.2). Density separation applied to those averaged equations,
using (11.4) for $y=1$ and the actual complementary effect for $y=0$,
gives

$$
\begin{aligned}
T^\dagger(P)&=v_0v_0^\dagger,\\
T^\dagger(t_jt_j^\dagger)&=\tfrac12 F_j,\\
T^\dagger\!\bigl(A_j^\dagger(I_5-P)A_j\bigr)
 &=\tfrac12(I_3-F_j)\qquad(j=0,1).
\end{aligned}
\tag{13.9}
$$

For the last identity the target compression is
$B^\dagger A_j^\dagger(I_5-P)A_jB=(I_3-F_j)/2$, by
$A_jB=BV_j/\sqrt2$. This compression is evaluated on the ideal
embedded input only. In particular (13.9) does not replace the
full-$H$ effect $A_j^\dagger A_j$ by $I_5/2$.
All complex density inputs are used: a Hermitian matrix with zero
expectation on every such density is zero, so the effect equalities
are identities, not merely equalities on the three probes.

Take a finite rectangular Kraus representation

$$
T(X)=\sum_\ell L_\ell XL_\ell^\dagger,\qquad
L_\ell:\mathbb C^3\to\mathbb C^5,\qquad
\sum_\ell L_\ell^\dagger L_\ell=I_3.
\tag{13.10}
$$

The immediate sharp identity in (13.9) forces, for each $\ell$,

$$
L_\ell v_0=c_\ell p,\qquad
L_\ell^\dagger p=\overline{c_\ell}v_0,\qquad
\sum_\ell|c_\ell|^2=1.
\tag{13.11}
$$

Indeed, for $x\perp v_0$ the identity gives
$\sum_\ell|\langle p,L_\ell x\rangle|^2=0$, so every
$L_\ell^\dagger p$ lies in $\mathbb Cv_0$. At $v_0$, trace
preservation and that same identity give
$\sum_\ell\|(I_5-P)L_\ell v_0\|^2=0$, so every
$L_\ell v_0$ lies in $\mathbb Cp$. Taking the indicated inner
products fixes the conjugation in (13.11), and Kraus normalization
at $v_0$ fixes the sum of squared coefficients.

The second identity of (13.9) is a positive rank-one sum:

$$
\sum_\ell(L_\ell^\dagger t_j)(L_\ell^\dagger t_j)^\dagger
 =\tfrac12w_jw_j^\dagger.
\tag{13.12}
$$

Testing on $w_j^\perp$ shows that every summand vector is
$L_\ell^\dagger t_j=d_{\ell j}w_j$. By (13.8) and (13.11),

$$
\frac{d_{\ell j}}4
 =\langle v_0,L_\ell^\dagger t_j\rangle
 =\langle L_\ell v_0,t_j\rangle
 =\frac{\overline{c_\ell}e^{-i\theta}}{4\sqrt2}.
\tag{13.13}
$$

Define $N_\ell=L_\ell-c_\ell B$ and
$S=\operatorname{span}\{p,t_0,t_1\}\subset H$. Equations
(13.8), (13.11) and (13.13) now imply

$$
N_\ell v_0=0,\qquad N_\ell^\dagger p=0,\qquad
N_\ell^\dagger t_0=N_\ell^\dagger t_1=0,\qquad
\operatorname{range}N_\ell\subset S^\perp.
\tag{13.14}
$$

The complementary equations in (13.9) supply the missing rectangular
constraint. Evaluate their quadratic forms at $w_j$. Their right
sides are zero, so

$$
\sum_\ell\|(I_5-P)A_jL_\ell w_j\|^2=0.
\tag{13.15}
$$

Every summand vanishes. Subtracting $c_\ell A_jBw_j$, which lies
in $\mathbb Cp$ by (13.8), gives
$(I_5-P)A_jN_\ell w_j=0$. Its remaining $p$ component also
vanishes because
$p^\dagger A_jN_\ell w_j=t_j^\dagger N_\ell w_j=0$ by
(13.14). Hence

$$
N_\ell w_j\in S^\perp\cap\ker A_j\qquad(j=0,1).
\tag{13.16}
$$

It remains to compute these actual kernels on all of $H$. Put

$$
\alpha=\frac{\sqrt2+1}{\sqrt{12}},\qquad
\beta=\frac{\sqrt2-2}{\sqrt{12}},\qquad
p=\alpha u+\alpha v+\beta z,\qquad
c=\cos\theta,\quad s=\sin\theta.
\tag{13.17}
$$

Here $u,v,z$ are precisely the physical vectors in (1.1).
In particular $\alpha\ne0$ and $\alpha-\beta=\sqrt3/2\ne0$.
For $k=\sum_{i=0}^4 k_i e_i$, direct substitution in (11.1) gives

$$
\begin{aligned}
A_0k&=(ck_0+is k_1)u
       +\frac{e^{i\theta}k_2}{\sqrt2}v
       +(is k_3+ck_4)z,\\
A_1k&=(is k_0+ck_1)u
       +\frac{e^{i\theta}k_2}{\sqrt2}v
       +(ck_3+is k_4)z.
\end{aligned}
\tag{13.18}
$$

The coefficient of $v$ vanishes only when $k_2=0$.
Since $c^2+s^2=1$, the row $(c,is)$ has kernel generated by
$(-is,c)$ and the row $(is,c)$ has kernel generated by $(c,-is)$.
For example the two rows $(c,is)$ and $(is,c)$ form an invertible
matrix of determinant $c^2+s^2=1$, proving these descriptions
without division by $c$ or $s$. Consequently the exact kernels are

$$
\begin{aligned}
\ker A_0
 &=\{x(-is e_0+c e_1)+y(c e_3-is e_4):x,y\in\mathbb C\},\\
\ker A_1
 &=\{x(c e_0-is e_1)+y(-is e_3+c e_4):x,y\in\mathbb C\}.
\end{aligned}
\tag{13.19}
$$

For $k$ in the first line, (13.18) gives $A_1k=xu+yz$ and

$$
\langle p,k\rangle
 =\frac{\alpha e^{-i\theta}}{\sqrt2}(x+y),\qquad
\langle t_1,k\rangle=\langle p,A_1k\rangle=\alpha x+\beta y.
\tag{13.20}
$$

If also $k\in S^\perp$, both quantities vanish. The first says
$x+y=0$, and the second then gives $(\alpha-\beta)x=0$.
Thus $x=y=0$. For $k$ in the second line of (13.19), one instead
has $A_0k=xu+yz$, the identical first formula in (13.20), and
$\langle t_0,k\rangle=\alpha x+\beta y$. The same two equations
again force $x=y=0$. Therefore

$$
S^\perp\cap\ker A_0=S^\perp\cap\ker A_1=\{0\}
\quad\text{for every real }\theta.
\tag{13.21}
$$

This includes $c=0$ and $s=0$. By (13.16), $N_\ell w_0=N_\ell w_1=0$.
Together with $N_\ell v_0=0$ and the all-angle spanning in (13.7),
this proves $N_\ell=0$. Thus $L_\ell=c_\ell B$, and (13.11)
gives $T(X)=BXB^\dagger$ for every complex matrix $X$, proving
(13.2) from the averaged task equations.

To recover the individual branches, use the original mixture (13.1),
not a relabelled or conditionally reweighted history law. With
$|B\rangle\!\rangle=\sum_{i=0}^2|i\rangle\otimes B|i\rangle$,
linearity and trace-norm convergence of the Choi sum give

$$
J(T)=\sum_{h,a}p_{h,a}J(\Phi_{h,a})
 =|B\rangle\!\rangle\langle\!\langle B|.
\tag{13.22}
$$

The right side is positive of rank one. For each $p_{h,a}>0$,
positivity of every other summand, also for a countable alphabet,
gives $0\le p_{h,a}J(\Phi_{h,a})\le J(T)$. Its support is
therefore contained in the line $\mathbb C|B\rangle\!\rangle$.
Write $J(\Phi_{h,a})=\lambda_{h,a}J(T)$ with
$\lambda_{h,a}\ge0$. Both unweighted Choi matrices have trace
three, since both maps are trace preserving. Hence
$\lambda_{h,a}=1$, proving (13.3). Because $2^{-n}>0$, the positive
branches are exactly those with $r(a\mid h)>0$, including $n=0$.
This is the rank-one Choi mixture argument used in Theorem 5.2,
now applied after establishing the rectangular identity.

Conversely (13.3) and (13.6) imply (13.2). Substituting (13.2)
into the actual immediate and joint $(j,y)$ tests gives precisely
(11.2), including both complementary outcomes. Changing variables
$Y=Q_hXQ_h^\dagger$ proves the equivalence of (13.3) and (13.4).
For every positive record $a$ there is a compatible history, and
its terminal qutrit input ranges over all qutrit densities as the
original input varies. Thus (13.4) really restricts that decoder on
its entire actual input corner; it is not a restriction to three
probe states. Different compatible histories must give the same
restriction. Their full word-class refinement is the existing
Theorem 11.2, rather than an additional resource assertion here.

Finally (13.2)–(13.3) are equalities of complex-linear maps on all
$M_3$, so tensoring with $\operatorname{id}_{M_d}$ proves (13.5)
for arbitrary joint inputs. This accesses no reference. In the
original history/record mixture each positive block therefore has
the same corrected embedded joint state, with its original weight
$p_{h,a}$. Composing such an equality with the actual next instrument
recovers its joint tests; no branchwise future equality was presumed
in obtaining (13.9). $\square$

The current exact classification under Definition 11.1 is therefore
(13.2)–(13.4): every successful corrected $M_3\to M_5$ map is the
original embedding, and every reached record selects the appropriate
inverse on its actual qutrit input. This supplies the rectangular
classification beyond the existence assertion of Theorem 11.2 and
the corresponding unclassified case described in Definition 12.1.
It leaves the physical $M_5\to M_5$ decoder's off-$R$ action
unclassified.

The existing square-system nondisturbance supplier is Mayer–Knill,
[arXiv:1805.04491v1](https://arxiv.org/abs/1805.04491v1), Theorem 1,
and the existing repository [ProbeComponentRigidity][PCR], including
its `dual_fixed`, `kraus_commutes_projection` and `overlap_scalar`
steps. Their square-output conclusion is not applied to the
rectangular $T$ in (13.10). The observable-correction interface is
[Bény–Kempf–Kribs, arXiv:0705.1574v1][BKK], Definition 8 and
Theorem 9; its algebraic compressed-Kraus-product criterion does
not turn an actual unsharp full-$H$ effect into a projection.
Finite CP/Kraus representation, density separation, and positive
Choi support are existing suppliers. The source-relative increment
is the actual rectangular residual calculation (13.14)–(13.21)
and its resulting classification for these specified source task
equations. This increment is `repo-derived`; no global literature
novelty assertion is made.

This is an ordinary analytical theorem, not a Lean certification.
Broader finite-precision bounds, storage minima for the leaked-output
contract, minimum total controls, atomic or spatial realization, and
the original critical causal-memory estimate are outside its scope.
The qutrit-output storage conclusions of §10 and the independent
realization requirements of §12 retain their stated hypotheses.

## 追加锚（本行以下为增补区）

## 14. Full-H labelled continuation through a finite coherent port

**Definition 14.1 (the storage extension of the actual late task).**
Keep Definitions 1.1–1.2 and 11.1 exactly: every real calibration
$\theta$, known integer horizon $n\ge0$, every qutrit density input
$\rho$ embedded by the specified $B$, the actual fair histories,
and a complete input-independent finite or countable kernel $r(a\mid h)$.
There is no intermediate quantum feedback. The physical terminal
specimen, inaccessible untouched reference and history information
are those of that acquisition, without a copy or alternative dilation.

For an integer $q\ge1$ and each record $a$, allow an encoder and
decoder

$$
\begin{aligned}
 \operatorname{Enc}_a &:M_5\longrightarrow
                      \bigoplus_{\ell\in\mathsf L_a}M_q,\\
 \operatorname{Dec}_a((Y_\ell)_\ell)
       &=\sum_{\ell\in\mathsf L_a}\operatorname{Dec}_{a\ell}(Y_\ell),
 \qquad \operatorname{Dec}_{a\ell}:M_q\longrightarrow M_5,\\
 \mathcal D_a&=\operatorname{Dec}_a\circ\operatorname{Enc}_a.
\end{aligned}
\tag{14.1}
$$

The flag alphabet $\mathsf L_a$ is finite, with no prescribed bound
on its finite size. The encoder is CPTP into the direct sum and each
decoder is CPTP on its **entire** block. The flags may depend on the
unknown specimen. They are classical, with no coherent cross-flag
carrier, and are consumed or discarded by decoding before the task.
During the storage interval all input-dependent quantum information
available for use passes through the $q$-dimensional block. The
original specimen, an environment, a reference or preshared entanglement
cannot bypass it. The history record is distinct from these new
specimen-dependent flags; every accessible history-dependent classical
carrier is already included in $a$.

All maps are fixed, calibrated and installed before the unknown input
and before the late task choice. They may depend on $a,n,\theta$,
but not on that choice. Their full-$H$ output may leak outside $R$.
Correctness is exactly the two alternatives of (11.2): immediate
$(\widehat E,I_5-\widehat E)$, or one further actual **full-$H$**
acquisition (11.1), retaining both $j$ and the terminal result $y$.
There is no further correction after that acquisition. Thus this is a
port-factorization restriction on the full-$H$ decoder contract, not
an application of the qutrit-output theorem to leaked states.

**Corollary 14.2 (exact coherent dimension with arbitrary full-H output).**
For every $\theta\in\mathbb R$, $n\ge0$, complete kernel $r$ as
above and integer $q\ge1$, maps (14.1) satisfying the whole task
(11.2) exist if and only if

$$
 \left[r(a\mid h)r(a\mid g)>0\ \Longrightarrow\
                [Q_h]=[Q_g]\right]\quad\text{for every }a,h,g,
 \qquad q\ge3.
 \tag{14.2}
$$

For every admissible supplied record, the exact minimum coherent port
dimension is therefore three, with unrestricted full-$H$ output and
arbitrarily many finite consumed classical flags. The record criterion
and its alphabet minimum $m_n(\theta)$ are supplied by Theorem 11.2.
Theorem 13.1 supplies the complete corrected-channel classification on
the actual qutrit input corner, including every positive history/record
branch. This corollary applies that classification to the finite-port
factorization; it asserts no additional rigidity theorem.

Proof. Each $\mathcal D_a$ in (14.1) is CPTP on all of $H$ and is
applied before the same late choice. Theorem 11.2 gives the record
necessity. All of Theorem 13.1's hypotheses also hold: the original
weights are still $p_{h,a}=2^{-n}r(a\mid h)$, every qutrit density
is allowed, and all immediate and future joint $(j,y)$ equations,
including $y=0$, are required. Its conclusion (13.3) therefore gives
$\Phi_{h,a}(X)=BXB^\dagger$ for every positive original branch.
No output-in-$R$ condition is assumed in this application; it is a
consequence of that supplied classification on the actual inputs.

Fix any positive $(h,a)$. Finite rectangular Kraus representations for
the encoder and the whole-block decoders give matrices
$E_{a\ell u}:H\to\mathbb C^q$ and
$D_{a\ell v}:\mathbb C^q\to H$, normalized by
$\sum_{\ell,u}E_{a\ell u}^\dagger E_{a\ell u}=I_5$ and
$\sum_vD_{a\ell v}^\dagger D_{a\ell v}=I_q$ for each flag.
Thus the actual corrected branch has the finite Kraus family

$$
 K_{\ell vu}=D_{a\ell v}E_{a\ell u}BQ_h,
 \qquad \operatorname{rank}K_{\ell vu}\le q,
 \qquad \sum_{\ell,v,u}K_{\ell vu}^\dagger K_{\ell vu}=I_3.
 \tag{14.3}
$$

This is the same-flag factorization supplied by [CoherentFlagPort][CFP]
and [FiniteKrausRepresentation][KRAUS], now with input dimension three
and output dimension five. The Choi matrix of this branch is the
rank-one $|B\rangle\!\rangle\langle\!\langle B|$ by (13.3).
The positive Choi support argument used in Theorem 13.1 consequently
makes every $K_{\ell vu}$ a scalar multiple of $B$. Kraus
normalization guarantees a nonzero member. That member has rank three,
so (14.3) forces $q\ge3$. Choosing one positive branch suffices also
when the history record is countable; no finite global record alphabet
or new conditional-correctness assumption has been inserted. Such a
branch exists by (13.6), including at $n=0$.

For attainment suppose the record condition holds. For every positive
$a$ choose a word-class representative $Q_a$, and fix any qutrit
density $\tau$. For $q=3$ take a single constant storage flag and
the whole-space maps

$$
 \operatorname{Enc}_a(X)
   =Q_a^\dagger B^\dagger XBQ_a+
                    \operatorname{Tr}((I_5-P_R)X)\tau,
 \qquad \operatorname{Dec}(Y)=BYB^\dagger.
 \tag{14.4}
$$

The first encoder term is CP with Kraus matrix $Q_a^\dagger B^\dagger$;
the second is CP measure-and-prepare on the positive complement effect.
Their traces sum to $\operatorname{Tr}X$. The decoder is CPTP since
$B^\dagger B=I_3$. Thus the encoder acts on all of $H$, not only on
promised inputs. On every actual compatible history,
$Q_a^\dagger Q_h$ is scalar, so their composition restores
$B\rho B^\dagger$ branchwise, and with any untouched finite reference.
The immediate task and every actual future $j,y$ event then have their
specified laws, including $y=0$.

For $q>3$, choose an isometry $J:\mathbb C^3\to\mathbb C^q$,
encode the right side of (14.4) by $Y\mapsto JYJ^\dagger$, and
decode a whole block $Z$ by

$$
 BJ^\dagger ZJB^\dagger+
         \operatorname{Tr}((I_q-JJ^\dagger)Z)\sigma,
 \tag{14.5}
$$

where $\sigma$ is any density on $H$. This is a complete CPTP
padding on unused directions and agrees on the encoded block. Zero
probability records may have arbitrary fixed CPTP codecs. The construction
also covers $n=0$, with the unique empty-word representative. It proves
sufficiency and exact attainment of (14.2). $\square$

## 15. Attained joint retention and continued use

**Proposition 15.1 (the upper's complete interface).** For (14.4),
retain the acquired history record through its representative inverse
and keep its actual subrecords if the future task requests them.
For every finite reference $Z$ and input density on $\mathbb C^3\otimes Z$,
the history-resolved post-decoding joint law is

$$
 \sum_{h,a}p_{h,a}|h,a\rangle\langle h,a|\otimes
                (B\otimes I_Z)\rho(B^\dagger\otimes I_Z).
 \tag{15.1}
$$

Here $h$ indexes the actual acquisition events, not an additional
accessible history register. Sum over its unretained components to
obtain the retained-record interface. Any history subrecord kept for
later use must actually have been acquired, included in the complete
record $a$, and retained with its own backing and cost.

After the one actual full-$H$ acquisition their joint successor is
exactly

$$
 \sum_{h,a,j}p_{h,a}|h,a,j\rangle\langle h,a,j|\otimes
        \tfrac12(BV_j\otimes I_Z)\rho
                         (V_j^\dagger B^\dagger\otimes I_Z).
 \tag{15.2}
$$

The storage flag is constant in this construction. Keeping it adds
only that constant classical field. These formulas attain the stronger
joint task that retains the old record as well as $j,y$. The existence
criterion and coherent minimum stay (14.2) for that stronger task.

Proof. Branchwise restoration in (14.4) gives each block of (15.1).
Apply the very same $A_j$, using $A_jB=BV_j/\sqrt2$, to obtain
(15.2). Composing the terminal binary test on each block gives the
full joint $(a,j,y)$ law and any actually retained subrecord of $h$.
Any specified common finite continuation instrument, including one
controlled by that retained subrecord, composes with equal subnormalized
blocks and therefore has equal joint outputs and successors. These
identities describe the attained construction. The underlying branchwise
recovery is also supplied for every successful unflagged scheme by
Theorem 13.1; no new classification is inferred here. Necessity for the
stronger task follows by forgetting the old record and applying
Corollary 14.2; the upper just given proves sufficiency. $\square$

For an arbitrary encoder with specimen-dependent flags, retaining a
flag past decoding requires its actual CP instrument blocks
$\mathcal K_{a\ell}=\operatorname{Dec}_{a\ell}\operatorname{Enc}_{a\ell}$,
not an independent flag appended to the average (13.1). Its successor blocks are
$p_{h,a}\mathcal A_j\mathcal K_{a\ell}
(BQ_h\rho Q_h^\dagger B^\dagger)$, with the reference map when
present. The unflagged task does not prescribe the probabilities of
these added flag values. Its corrected-channel classification is Theorem 13.1; a
flag-resolved comparison must still specify the actual instrument blocks
and the intended flag law. The constant-flag upper fixes that law
explicitly.

At $\theta=\pi/6$, use the existing actual acquisition of all $n$
labels and the $n$ inverse-letter invocations of ERM16.1 before the
fixed $R$-to-qutrit storage encoding and $B$ decoder. At $\theta=0$,
use its acquired full-word permutation accumulator and selected inverse:
the reachable full-word counts are $1,2,4,6$ at $n=0,1,2,\ge3$,
with the supplied known-horizon small-case encodings. These are
full-word controls, not the smaller single-task suffix or three-position
record of §3. One may factor (14.4) as this full-$H$ inverse followed
by the fixed encoder, since the inverse is identity on $R^\perp$.
This realizes the same channel, and makes explicit when the old
record can be released. No inverse is needed for $n=0$.

The same run pays $n$ fresh environment preparations, interactions,
measurements and actual label acquisitions, all record writes and
retained reads, inverse controls, one encoder, the three-dimensional
coherent port for its holding interval, one decoder, calibration,
schedule/address workspace, service permissions and any classical
carrier. The old record must remain readable through inverse selection
and invocation; keeping it longer costs its actual lifetime. The late
continuation adds one actual preparation, interaction, measurement and
new label acquisition, then one terminal binary test; the immediate
choice adds that test alone. All those prices coexist. The port minimum
does not minimize total memory, control count, energy, latency, or
physical carrier dimension five. The inaccessible reference is preserved
by the upper and supplies no usable storage bypass.

For an arbitrary fixed real $\theta$, (14.2) is a finite-dimensional
channel-existence theorem for a supplied kernel. It does not uniformly
decide exact-real word equalities, acquire an unknown calibration,
compile arbitrary representative tables or install exact codecs.
The explicit acquired/effective upper accounts above are restricted
to the supplied exact calibrations and installed controls. The
existential theorem does not replace those operational prerequisites.

## 16. Supplier correspondence and the remaining recovery scope

The full-$H$ corrected-channel classification is Theorem 13.1,
(13.2)–(13.5), on the exact original domain of Definition 11.1.
Its evaluated residual calculation (13.14)–(13.21), including the
actual complementary future outcomes, is the supplier that removes
possible leakage on the actual corrected inputs. It is not an open
classification problem here. The physical decoder's off-$R$ input
behavior remains outside that classification.

Corollary 14.2 expresses the finite consumed-flag storage consequence
of that supplied theorem and the existing rank-through-port principle.
The full-word record iff and $m_n$ are reused from Theorem 11.2;
branchwise recovery, including an untouched finite reference, is reused
from Theorem 13.1. In particular the existence, corrected-channel and
reference conclusions already have their suppliers. The remaining
storage application specifies the whole-$H$ encoder, whole-block
padding, attained joint interface and the acquired-use resource cuts
in §§14–15. It is an explicit application and attainment, not a new
classification, rank inequality or independently new rigidity argument.
It resolves the finite-flag coherent-port question left outside §13
only on Definition 14.1's exact storage domain.

[CoherentFlagPort][CFP] and its [owning Scribe][CFPB] supply the
same-flag Kraus composition and complete complement-filled decoder
construction; [FiniteKrausRepresentation][KRAUS] and its
[owning Scribe][KRAUSB] supply finite rectangular CP representations.
The square connected-probe statement
`port_component_lower_bound` is not directly a theorem about an
$M_3\to M_5$ channel. In (14.3) only the rectangular product and its
rank bound are used; Theorem 13.1 supplies the actual channel to which
that factorization is applied. The ordinary rank inequality for a
product through $\mathbb C^q$ is the `rank_mul_le`/`rank_le_card_width`
supplier in pinned mathlib's `Mathlib/LinearAlgebra/Matrix/Rank.lean`.

Bluhm–Rauber–Wolf, [arXiv:1708.04898v4][BRW], Definition 4.1 and
the proof of Lemma 5.2, supply the finite classical-quantum compression
model and the rank-at-most-$q$ composite Kraus argument. The present
input corner is the actual $R$ of the five-level source, rather than
all five-level densities; (14.4) extends the attained encoder to the
entire physical input algebra. The source-specific classification is
credited to §13, not to a generic observable-compression theorem.
These are ordinary analytical applications with no worldwide-priority
or new Lean-certification claim.

The independent full-$H$ real-filter classification in [MRQB], §§19–26,
concerns contractive invertible filters, real/skew source coordinates,
all-success-prefix detector laws and least filter depth. Its preparations,
records, controls and output task differ from (11.2). It does not
identify those filters with the codecs (14.1).

[ERM II][ERMII], §§31–35, already supplies, for its fixed actual
channel, the exact erased-history spectator–$e$ task value for every
population $0<p<1$ and finite $n\ge2$, with a same-qutrit decoder
and matching full-complex certificates. That quantitative boundary
with zero $f$ population, including the reused balanced case, is
supplied rather than a missing minimax result. It permits neither a
retained history record nor the late joint task (11.2), and does not
supply (14.2). Its interior with all three populations positive and
uniform unbounded-horizon questions keep their own stated scope.
The signed P/Q, autonomous STOP, fixed-apparatus, original-Q,
parked-consumer and unchanged-initialization problems likewise retain
their original conditions and remaining obligations.

Chronology here is the actual label word with its acquisition count;
the terminal task boundary is the stated immediate/future effect
interface; memory is an acquired word-class record plus the coherent
specimen with installed callable controls. Their common-source relation
is (13.1) and the attained joint law (15.2). The count alone does not
select a nontrivial word class. No independent acquired spatial
incidence or metric view, physical-duration inverse, atomic/quantum
common initialization, or alpha/beta universality is supplied. Unknown
calibration acquisition, finite-precision stability and total-resource
parsimony remain separate. Thus this full-$H$ port application is a
bounded recovery/continued-use contribution toward the continuing
programme, not unrestricted four-expression recovery.

## 追加锚（本行以下为增补区）
## 13.3. Uniform finite-precision stability for the actual full-H tests

**Theorem 13.3 (Uniform stability of the average corrected channel).**
Fix precisely the model of Definitions 1.1–1.2 and 11.1 and the
actual coordinates used in Theorem 13.1. Thus
$B:\mathbb C^3\to H=\mathbb C^5$ is the specified isometric
embedding, $v=v_e$, $E=vv^\dagger$, $p=Bv$, $P=pp^\dagger$,
$P_1=P$, and $P_0=I_5-P$. For each real calibration angle
$\theta$, the instrument is fixed and known: its two operators
$A_j=A_j(\theta)$, $j\in\{0,1\}$, are exactly the actual
full-$H$ operators (11.1), acting on all five output dimensions.
For every complex-linear CPTP map
$T:M_3(\mathbb C)\to M_5(\mathbb C)$, let $T^\dagger$ denote
its trace adjoint and define the actual test defect by

$$
\begin{aligned}
\delta_\theta(T)=\max\Bigl\{&\|T^\dagger(P)-E\|_{\mathrm{op}},\\
&\max_{j,y\in\{0,1\}}
\bigl\|T^\dagger(A_j^\dagger P_yA_j)
       -B^\dagger A_j^\dagger P_yA_jB\bigr\|_{\mathrm{op}}
\Bigr\}.
\end{aligned}
\tag{13.23}
$$

Both outcomes of each labelled continuation are included; these are
joint effects for the actual label $j$, without conditioning or
renormalizing its probability. Uniformly for every real $\theta$,
every such $T$, and every real $0<\varepsilon\le\varepsilon_0=1/2$,

$$
\delta_\theta(T)\le\varepsilon
\quad\Longrightarrow\quad
\|T-\operatorname{Ad}_B\|_\diamond
 \le C\sqrt\varepsilon,\qquad
C=800,\qquad \operatorname{Ad}_B(X)=BXB^\dagger.
\tag{13.24}
$$

Here the diamond norm is unhalved and ranges over arbitrary finite
untouched inaccessible references:

$$
\|\Lambda\|_\diamond
 =\sup_{d\ge1}\ \sup_{0\ne X\in M_3(\mathbb C)\otimes M_d(\mathbb C)}
 \frac{\|(\Lambda\otimes\operatorname{id}_{M_d})(X)\|_1}{\|X\|_1}.
\tag{13.25}
$$

In particular the bound holds on every joint input density with such
a reference. There is no restriction that $T$ have output in
$R=B\mathbb C^3$, no assumed conditional branch correctness, no
full-$H$ fairness law, and no assumption that the input state is
known. The defect is a uniform input test: for each Hermitian effect
difference its operator norm equals the supremum of the absolute
expectation over all complex qutrit density inputs. The statement
therefore retains all input coherences. When $T$ is the average
corrected channel (13.1), (13.24) certifies that average; it does not
assert a uniform approximate guarantee on every history/record
branch of arbitrarily small weight.

Proof. Fix an arbitrary real $\theta$ and a channel satisfying the
hypotheses. Vector norms are Euclidean, and $\|\cdot\|_{\mathrm{HS}}$
is the Hilbert–Schmidt norm. Put $Q=I_5-P$,
$t_j=A_j^\dagger p$, and $F_j=w_jw_j^\dagger$, with the actual
vectors from (13.7). In the orthonormal input frame $(\xi,e,f)$,
these vectors and their frame operator are

$$
\begin{gathered}
v=\frac{\xi+e}{\sqrt2},\qquad
w_0=\frac{\xi-e/2+(\sqrt3/2)e^{2i\theta}f}{\sqrt2},\qquad
w_1=\frac{\xi-e/2-(\sqrt3/2)e^{2i\theta}f}{\sqrt2},\\
vv^\dagger+F_0+F_1
 =\operatorname{diag}_{(\xi,e,f)}(3/2,3/4,3/4)
 \succeq\tfrac34 I_3.
\end{gathered}
\tag{13.26}
$$

Indeed, $F_0+F_1$ is the outer product of $\xi-e/2$ with
itself plus $(3/4)ff^\dagger$, whereas
$vv^\dagger=(\xi+e)(\xi+e)^\dagger/2$; their mixed
$\xi,e$ entries cancel. This is a uniformly conditioned
nonorthogonal frame, not an orthogonal-probe assumption. The exact
identities (13.8) and the ideal compression used in (13.9) give

$$
\begin{aligned}
B^\dagger t_j&=e^{-i\theta}w_j/\sqrt2,&
w_j^\dagger v&=1/4,&
A_jBw_j&=e^{i\theta}p/\sqrt2,\\
B^\dagger A_j^\dagger PA_jB&=F_j/2,&
B^\dagger A_j^\dagger QA_jB&=(I_3-F_j)/2.
\end{aligned}
\tag{13.27}
$$

The last identity uses $A_jB=BV_j/\sqrt2$ only on the ideal
embedded corner. It does not replace $A_j^\dagger A_j$ on $H$
by $I_5/2$.

We first quantify the full-$H$ kernel calculation of Theorem 13.1.
To distinguish the physical vector from the input $v$, write
$v_H=(e_1+e_4)/\sqrt2$, with $u=(e_0+e_3)/\sqrt2$ and
$z=e_2$ as in (1.1). Put $c_\theta=\cos\theta$ and
$s_\theta=\sin\theta$. The actual formulas (13.18) read

$$
\begin{aligned}
A_0k&=(c_\theta k_0+i s_\theta k_1)u
       +e^{i\theta}k_2v_H/\sqrt2
       +(i s_\theta k_3+c_\theta k_4)z,\\
A_1k&=(i s_\theta k_0+c_\theta k_1)u
       +e^{i\theta}k_2v_H/\sqrt2
       +(c_\theta k_3+i s_\theta k_4)z.
\end{aligned}
\tag{13.28}
$$

Their three rows in the orthonormal output frame $(u,v_H,z)$
have disjoint coordinate supports and squared norms $1,1/2,1$.
Consequently the nonzero singular values of each $A_j$ are
$1,1,1/\sqrt2$, so $\|A_j\|_{\mathrm{op}}=1$ and
$\|t_j\|\le1$. Orthonormal bases for their kernels are,
respectively,

$$
\begin{aligned}
\ker A_0&=\operatorname{span}\{
 -i s_\theta e_0+c_\theta e_1,
 c_\theta e_3-i s_\theta e_4\},\\
\ker A_1&=\operatorname{span}\{
 c_\theta e_0-i s_\theta e_1,
 -i s_\theta e_3+c_\theta e_4\}.
\end{aligned}
\tag{13.29}
$$

Write $h=x$ times the first displayed kernel vector plus $y$ times
the second for either $j$. As in (13.17)–(13.20), set

$$
\begin{gathered}
\alpha=\frac{\sqrt2+1}{\sqrt{12}},\qquad
\beta=\frac{\sqrt2-2}{\sqrt{12}},\qquad
p=\alpha u+\alpha v_H+\beta z,\qquad
\gamma=\alpha-\beta=\alpha+|\beta|=\frac{\sqrt3}{2},\\
p^\dagger h=\frac{\alpha e^{-i\theta}}{\sqrt2}(x+y),
\qquad t_{1-j}^\dagger h=\alpha x+\beta y.
\end{gathered}
\tag{13.30}
$$

For completeness, the second identity follows from
$A_{1-j}h=xu+yz$ in both kernel bases; the first follows by
substituting $u,v_H,z$ into $p$. If $m=x+y$ and
$n=\alpha x+\beta y$, then
$x=(n-\beta m)/\gamma$ and $y=(\alpha m-n)/\gamma$.
Since $\sqrt2/\alpha<3$ and $2/\gamma<3$, it follows that

$$
\|h\|\le |x|+|y|
 \le |m|+\frac{2}{\gamma}|n|
 \le3\bigl(|p^\dagger h|+|t_{1-j}^\dagger h|\bigr).
\tag{13.31}
$$

For arbitrary $k\in H$, decompose $k=h+r$ orthogonally with
$h\in\ker A_j$. The singular values give
$\|r\|\le\sqrt2\|A_jk\|$. Using (13.31),
$\|p\|=1$, and $\|t_{1-j}\|\le1$, we obtain the uniform
full-$H$ coercivity estimate

$$
\begin{aligned}
\|k\|&\le
 3\bigl(|p^\dagger k|+|t_{1-j}^\dagger k|\bigr)+7\|r\|\\
&\le 10\|A_jk\|+3|p^\dagger k|+3|t_{1-j}^\dagger k|,
\qquad j=0,1.
\end{aligned}
\tag{13.32}
$$

Here $7\sqrt2<10$. No step divides by $\sin\theta$ or
$\cos\theta$, so the constants include their zero cases.

By the standard finite-dimensional CP/Kraus representation, choose
$T(X)=\sum_\ell L_\ell XL_\ell^\dagger$ with
$L_\ell:\mathbb C^3\to H$ and
$\sum_\ell L_\ell^\dagger L_\ell=I_3$. One can obtain this
finite family by diagonalizing the positive $15\times15$ Choi
matrix. For each Kraus operator define nonnegative quadratic defects

$$
\begin{aligned}
a_\ell&=\|QL_\ell v\|^2,&
b_\ell&=\|p^\dagger L_\ell(I_3-E)\|_{\mathrm{HS}}^2,\\
g_{\ell j}&=\|t_j^\dagger L_\ell(I_3-F_j)\|_{\mathrm{HS}}^2,&
h_{\ell j}&=\|QA_jL_\ell w_j\|^2,\\
q_\ell&=a_\ell+b_\ell+g_{\ell0}+g_{\ell1}
                      +h_{\ell0}+h_{\ell1}.
\end{aligned}
\tag{13.33}
$$

Let $(x_1,x_2)$ and $(z_{j1},z_{j2})$ be orthonormal bases of
$v^\perp$ and $w_j^\perp$, respectively. Trace preservation,
(13.23), and (13.27) imply

$$
\begin{aligned}
\sum_\ell a_\ell
 &=1-\langle v,T^\dagger(P)v\rangle\le\varepsilon,\\
\sum_\ell b_\ell
 &=\sum_{a=1}^2\langle x_a,T^\dagger(P)x_a\rangle
 \le2\varepsilon,\\
\sum_\ell g_{\ell j}
 &=\sum_{a=1}^2\langle z_{ja},T^\dagger(t_jt_j^\dagger)z_{ja}\rangle
 \le2\varepsilon,\\
\sum_\ell h_{\ell j}
 &=\langle w_j,T^\dagger(A_j^\dagger QA_j)w_j\rangle
 \le\varepsilon,\\
\sum_\ell q_\ell&\le9\varepsilon.
\end{aligned}
\tag{13.34}
$$

Each quantity on the left is nonnegative. In the second and third
lines the ideal expectation is zero on the indicated orthogonal
complement, giving positive false-positive defects rather than
cancellation estimates. In the fourth line the ideal expectation
vanishes at $w_j$ because its compression is $(I_3-F_j)/2$.
This line uses the actual $y=0$ effect and is essential for leaked
outputs. The $y=1$ effect is $t_jt_j^\dagger$ and supplies the
third line. Thus both continuation outcomes enter the estimate.

For a single index $\ell$, suppress that index temporarily and put
$c=p^\dagger Lv$ and $N=L-cB$. The definitions give

$$
Nv=QLv,\qquad \|Nv\|=\sqrt a,\qquad
p^\dagger N=p^\dagger L(I_3-E),\qquad
\|p^\dagger N\|=\sqrt b.
\tag{13.35}
$$

Decompose $t_j^\dagger L=\lambda_jw_j^\dagger+\rho_j$ with
$\rho_j=t_j^\dagger L(I_3-F_j)$ and
$\|\rho_j\|=\sqrt{g_j}$. By (13.27),
$t_j^\dagger B=e^{i\theta}w_j^\dagger/\sqrt2$.
Hence $t_j^\dagger N=d_jw_j^\dagger+\rho_j$ for
$d_j=\lambda_j-ce^{i\theta}/\sqrt2$. Evaluating this row at
$v$ gives $d_j/4=t_j^\dagger Nv-\rho_jv$, and consequently

$$
|d_j|\le4(\sqrt a+\sqrt{g_j}),\qquad
\|t_j^\dagger N\|\le4\sqrt a+5\sqrt{g_j}.
\tag{13.36}
$$

Since $QA_jBw_j=0$, one has
$\|QA_jNw_j\|=\sqrt{h_j}$. The remaining component of
$A_jNw_j$ is $p^\dagger A_jNw_j=t_j^\dagger Nw_j$.
Applying (13.36) and then (13.32) to $k=Nw_j$ proves the
per-Kraus residual bounds

$$
\begin{aligned}
\|A_jNw_j\|&\le\sqrt{h_j}+4\sqrt a+5\sqrt{g_j},\\
\|Nw_j\|&\le
 52\sqrt a+3\sqrt b+50\sqrt{g_j}
          +15\sqrt{g_{1-j}}+10\sqrt{h_j},\\
\|Nw_j\|^2&\le5538q,
\qquad 52^2+3^2+50^2+15^2+10^2=5538.
\end{aligned}
\tag{13.37}
$$

The last line is Cauchy–Schwarz applied to the five indicated
nonnegative defects, whose sum is at most $q$. The coefficient
$52$ in the second line is $10\cdot4+3\cdot4$; the other terms
come directly from the three terms in (13.32). This also makes
explicit where the complementary label $1-j$ supplies coercivity.

The frame lower bound (13.26) now controls the whole rectangular
operator, including its components outside $R$:

$$
\begin{aligned}
\|N\|_{\mathrm{HS}}^2
 &\le\tfrac43\bigl(\|Nv\|^2+\|Nw_0\|^2+\|Nw_1\|^2\bigr)\\
 &\le\tfrac43(1+2\cdot5538)q
   =\tfrac{44308}{3}q\le15000q,\\
\sum_\ell\|L_\ell-c_\ell B\|_{\mathrm{HS}}^2
 &\le135000\varepsilon,
 \qquad c_\ell=p^\dagger L_\ell v.
\end{aligned}
\tag{13.38}
$$

For the first inequality, take the trace of $N^\dagger N$ times
the positive operator inequality (13.26). The last line uses
(13.34); neither the number of Kraus operators nor $\theta$
appears in its constant.

Let $\mathcal K$ have orthonormal basis $|\ell\rangle$ indexed
by this finite Kraus family. Define
$Wx=\sum_\ell L_\ell x\otimes|\ell\rangle$ and
$\mathbf c=\sum_\ell c_\ell|\ell\rangle$. Trace preservation
makes $W$ an isometry. Positivity and the immediate defect give

$$
 r^2:=\|\mathbf c\|^2
 =\langle v,T^\dagger(P)v\rangle\in[1-\varepsilon,1].
\tag{13.39}
$$

Thus $r>0$ for the stated range of $\varepsilon$. Put
$\eta=\mathbf c/r$ and $Ux=Bx\otimes\eta$; $U$ is an
isometry inducing $\operatorname{Ad}_B$. If
$W_cx=Bx\otimes\mathbf c$, then (13.38) bounds
$\|W-W_c\|_{\mathrm{op}}$ by its Hilbert–Schmidt norm, and
$\|W_c-U\|_{\mathrm{op}}=1-r$. Since
$1-r=(1-r^2)/(1+r)\le\varepsilon\le\sqrt\varepsilon$, we get

$$
\|W-U\|_{\mathrm{op}}
 \le\sqrt{135000\varepsilon}+1-r
 \le(\sqrt{135000}+1)\sqrt\varepsilon.
\tag{13.40}
$$

Finally let $Z=\mathbb C^d$ be any finite untouched reference and
let $X$ be any complex matrix on $\mathbb C^3\otimes Z$, without
assuming positivity or Hermiticity. Up to the canonical reordering
of tensor factors, write $W_Z=W\otimes I_Z$ and
$U_Z=U\otimes I_Z$. The difference before discarding
$\mathcal K$ is

$$
W_ZXW_Z^\dagger-U_ZXU_Z^\dagger
 =(W_Z-U_Z)XW_Z^\dagger
      +U_ZX(W_Z^\dagger-U_Z^\dagger).
\tag{13.41}
$$

The standard ideal-property estimate
$\|AXB\|_1\le\|A\|_{\mathrm{op}}\|X\|_1\|B\|_{\mathrm{op}}$
and the isometry norms bound this by
$2\|W-U\|_{\mathrm{op}}\|X\|_1$. Partial trace over
$\mathcal K$ is trace-norm contractive even for these arbitrary
matrices: its trace-dual map sends $Y$ to $Y\otimes I_{\mathcal K}$,
which has the same operator norm as $Y$, so trace/operator-norm
duality proves the contraction. Therefore, simultaneously for all
finite $d$ and all $X$,

$$
\begin{aligned}
\|((T-\operatorname{Ad}_B)\otimes\operatorname{id}_{M_d})(X)\|_1
 &\le2\|W-U\|_{\mathrm{op}}\|X\|_1,\\
\|T-\operatorname{Ad}_B\|_\diamond
 &\le2(\sqrt{135000}+1)\sqrt\varepsilon
 <800\sqrt\varepsilon.
\end{aligned}
\tag{13.42}
$$

For the final numerical comparison, $135000<399^2$, so
$2(\sqrt{135000}+1)<800$. This proves (13.24) with the full
unhalved reference norm. $\square$

The concrete use is finite-precision average-channel certification
in this specified model: uniform error at most $\varepsilon$ in
the immediate effect and the four actual labelled continuation
effects certifies diamond error at most $800\sqrt\varepsilon$
for the corrected average, including correlations with every finite
inaccessible reference. Theorem 13.1 supplies exact rigidity and
the source identities; (13.32)–(13.42) supply its quantitative
continuation, rather than inferring a modulus from exact rigidity
alone. Finite CP/Kraus representation, frame estimates, isometric
dilations, the trace-norm ideal property and trace/operator-norm
duality are standard finite-dimensional suppliers; see, for example,
John Watrous, [The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/),
Chapters 2–3. The actual full-$H$ identities are (11.1),
(13.7)–(13.8), and (13.17)–(13.20) of this volume, with fixed
source version `e0e3018402506726c33d4521451e9d3153abd0bc`.
The quantitative increment here is source-relative; no global
literature novelty, optimal constant, or optimal exponent is claimed.

The estimate supplies no calibration-error model,
physical realization, resource minimum, or additional exact
record/resource classification. The known instrument is held fixed
when the defect is evaluated. The estimate does not transfer to
every rare history/record branch: approximate closeness of an
average does not give Theorem 13.1's exact rank-one-mixture conclusion
uniformly on branches with arbitrarily small weights. The original
critical causal-memory and realization questions retain their own
hypotheses and unresolved boundaries.

The optimal local modulus remains undetermined: for these same
actual tests, determine whether a uniform local linear modulus is
available or whether lawful CPTP perturbations require square-root
behavior. Neither alternative is resolved here.

## 追加锚（本行以下为增补区）
## 17. The optimal uniform local Hölder exponent for the actual full-H tests

**Theorem 17.1 (A first-order invisible family and the sharp exponent;
repo-derived).** Keep exactly Definitions 1.1–1.2 and 11.1. All spaces
and matrix algebras are over $\mathbb C$. In the fixed physical
orthonormal basis $(e_0,\ldots,e_4)$ of $H=\mathbb C^5$, put

$$
\begin{gathered}
r=\sqrt2,\qquad
u=(e_0+e_3)/r,\qquad v_H=(e_1+e_4)/r,\qquad z=e_2,
\qquad B=(u,v_H,z),\\
c_0=(e_0-e_3)/r,\qquad c_1=(e_1-e_4)/r,
\qquad C_\perp=(c_0,c_1),\qquad J=I_5-BB^\dagger,\\
a=\frac{r+1}{\sqrt{12}},\qquad b=\frac{r-2}{\sqrt{12}},
\qquad q=v_e=(a,a,b)^{\mathsf T},\qquad E=qq^\dagger,\\
p=Bq=a u+a v_H+bz,\qquad P=pp^\dagger,
\qquad P_1=P,\qquad P_0=I_5-P.
\end{gathered}
\tag{17.1}
$$

Here $u,v_H,z$ are precisely the vectors of (1.1), and $q$ is the
vector of (1.5). For each real, fixed, known calibration angle
$\theta$, use the actual operators $A_j(\theta)$ of (11.1) on all
of $H$. For every complex-linear CPTP map
$T:M_3(\mathbb C)\to M_5(\mathbb C)$ define

$$
\begin{aligned}
\delta_\theta(T)=\max\Bigl\{&\|T^\dagger(P)-E\|_{\mathrm{op}},\\
&\max_{j,y\in\{0,1\}}
\|T^\dagger(A_j(\theta)^\dagger P_yA_j(\theta))
-B^\dagger A_j(\theta)^\dagger P_yA_j(\theta)B\|_{\mathrm{op}}
\Bigr\}.
\end{aligned}
\tag{17.2}
$$

Thus this is exactly (13.23), including both outcomes $y$ for each
actual label $j$. The channel error uses the full unhalved diamond
norm, with arbitrary finite untouched inaccessible references:

$$
\|\Lambda\|_\diamond
=\sup_{d\ge1}\ \sup_{0\ne X\in M_3(\mathbb C)\otimes M_d(\mathbb C)}
\frac{\|(\Lambda\otimes\operatorname{id}_{M_d})(X)\|_1}{\|X\|_1},
\qquad \operatorname{Ad}_B(X)=BXB^\dagger.
\tag{17.3}
$$

Define explicitly

$$
\begin{gathered}
S=\begin{pmatrix}
-(1+2r)/3&-(5+2r)/9&(1+r)/9\\
-(5+2r)/9&-(1+2r)/3&(1+r)/9\\
(1+r)/9&(1+r)/9&0
\end{pmatrix},\qquad
Z=\begin{pmatrix}1&0&0\\0&1&0\end{pmatrix},\\
G=BSB^\dagger+C_\perp ZB^\dagger+BZ^\dagger C_\perp^\dagger,
\qquad K=GB=BS+C_\perp Z,\\
U_t=\exp(itG),\qquad W_t=U_tB,\qquad
T_t(X)=W_tXW_t^\dagger\quad(t\in\mathbb R).
\end{gathered}
\tag{17.4}
$$

Each $T_t$ is a complex-linear CPTP map on the full stipulated
rectangular domain. At the permitted fixed calibration $\theta=0$,
for every $0<t\le1/25$ it satisfies

$$
\begin{gathered}
0< t^2\left(\sqrt2 a-\frac12\right)^2
\le\delta_0(T_t)\le50t^2,\\
\|T_t-\operatorname{Ad}_B\|_\diamond\ge t.
\end{gathered}
\tag{17.5}
$$

In particular, with $t_n=1/(25n)$ and $T_n=T_{t_n}$, for every
integer $n\ge1$,

$$
0<\delta_0(T_n)\le\frac{2}{25n^2},\qquad
\|T_n-\operatorname{Ad}_B\|_\diamond\ge\frac1{25n},\qquad
\frac{\|T_n-\operatorname{Ad}_B\|_\diamond}{\delta_0(T_n)}
\ge\frac n2.
\tag{17.6}
$$

Consequently there are no finite constants $C>0$ and $\eta>0$
such that, simultaneously for all real $\theta$ and all these
complex CPTP maps,

$$
\delta_\theta(T)\le\eta
\quad\Longrightarrow\quad
\|T-\operatorname{Ad}_B\|_\diamond\le C\delta_\theta(T).
\tag{17.7}
$$

More generally no exponent $\alpha>1/2$ admits a local bound with
a finite constant, even at $\theta=0$. Together with Theorem 13.3,
this makes $1/2$ the optimal worst-case uniform local Hölder exponent
on exactly this domain. This does not determine a best constant,
an exact optimal modulus function, or the optimal exponent
separately at each nonzero angle.

No output restriction to $R=B\mathbb C^3$, conditional branch
correctness, full-$H$ fairness, or known input state is assumed.
The effects in (17.2) retain the actual joint label probabilities;
they are not conditioned or renormalized. When $T$ is an average
corrected channel, the channel error here is the error of that
average, without a uniform approximation assertion on every
history/record branch of arbitrarily small weight. Calibration is
held fixed and known when each defect is evaluated.

Proof. The coordinates (17.1) give

$$
\begin{gathered}
B^\dagger B=I_3,\qquad
C_\perp^\dagger C_\perp=I_2,\qquad
B^\dagger C_\perp=0,\\
BB^\dagger+C_\perp C_\perp^\dagger=I_5,
\qquad \|q\|=\|p\|=1.
\end{gathered}
\tag{17.8}
$$

At $\theta=0$, (11.1) gives $A_0=K_0$ and $A_1=K_1$.
Their full five-dimensional effects and the tested rank-one vectors
are exactly

$$
\begin{aligned}
D_0:=A_0^\dagger A_0&=\operatorname{diag}(1,0,1/2,0,1),
& D_1:=A_1^\dagger A_1&=I_5-D_0,\\
t_0:=A_0^\dagger p&=a e_0+(a/r)e_2+b e_4,
& t_1:=A_1^\dagger p&=a e_1+(a/r)e_2+b e_3.
\end{aligned}
\tag{17.9}
$$

It follows that the entire collection of five effects tested in
(17.2), at this angle, is

$$
\mathcal M={P,\ t_0t_0^\dagger,\ t_1t_1^\dagger,
\ D_0-t_0t_0^\dagger,\ D_1-t_1t_1^\dagger\}.
\tag{17.10}
$$

Indeed $A_j^\dagger P_1A_j=t_jt_j^\dagger$ and
$A_j^\dagger P_0A_j=D_j-t_jt_j^\dagger$. Each $M\in\mathcal M$
is a positive contraction: $0\le P\le I_5$ and
$0\le A_j^\dagger P_yA_j\le D_j\le I_5$. These are actual
full-$H$ effects, and $D_j$ has not been replaced by $I_5/2$.

The matrix $S$ is real symmetric, so (17.4) gives $G=G^\dagger$.
Hence $U_t$ is unitary and $W_t^\dagger W_t=I_3$ for real $t$.
For every finite reference, conjugation by $W_t\otimes I$ preserves
positivity, and the last identity gives trace preservation.
Thus the single rectangular Kraus operator $W_t$ defines a
complex-linear CPTP map, including all complex input coherences.
This is the usual finite-dimensional Kraus criterion; see John
Watrous, [The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/),
Chapter 2. No postselection is involved. A useful explicit bound is

$$
\begin{gathered}
\|Z\|_{\mathrm{op}}=1,\qquad
\|S\|_{\mathrm{HS}}^2=\frac{80+40r}{27}<6,\\
h:=\|G\|_{\mathrm{op}}
\le\|S\|_{\mathrm{op}}+2\|Z\|_{\mathrm{op}}
\le\|S\|_{\mathrm{HS}}+2<\sqrt6+2<5.
\end{gathered}
\tag{17.11}
$$

The displayed Hilbert–Schmidt identity is obtained by squaring the
nine entries of $S$ and using $r^2=2$; its strict inequality follows
from $r<3/2$.

The exact cancellation certificate consists of the following finite
matrix identities, all in the coordinates (17.1) and (17.4):

$$
\begin{gathered}
\lambda=-\frac{10+7r}{9},\qquad
\mu=\frac{2r-1}{9},\\
p^\dagger K=\lambda p^\dagger B,\qquad
t_j^\dagger K=\mu t_j^\dagger B\quad(j=0,1),
\qquad B^\dagger K=S,\\
B^\dagger D_0K=
\begin{pmatrix}
(1-r)/3&-(5+2r)/18&(1+r)/18\\
-(5+2r)/18&-(2+r)/3&(1+r)/18\\
(1+r)/18&(1+r)/18&0
\end{pmatrix}.
\end{gathered}
\tag{17.12}
$$

These equalities follow by substituting (17.1), (17.4) and (17.9)
and multiplying, with $r^2=2$. They give, in particular,

$$
\begin{aligned}
B^\dagger PK&=\lambda B^\dagger PB,\\
B^\dagger(t_jt_j^\dagger)K&=
\mu B^\dagger(t_jt_j^\dagger)B\quad(j=0,1),\\
B^\dagger D_1K&=S-B^\dagger D_0K.
\end{aligned}
\tag{17.13}
$$

The first two lines are Hermitian because $\lambda,\mu$ are real.
The displayed matrix $B^\dagger D_0K$ is real symmetric, as are
$S$ and therefore $B^\dagger D_1K$. Subtracting the corresponding
rank-one terms proves that $B^\dagger MK$ is Hermitian for every
one of the five effects in (17.10), including both $y=0$ effects.
For each such $M$ define $F_M(t)=B^\dagger U_t^\dagger MU_tB$.
Differentiation now gives the whole matrix identity

$$
F_M'(0)=i(B^\dagger MK-K^\dagger MB)=0
\qquad(M\in\mathcal M).
\tag{17.14}
$$

Thus the certificate cancels all entries of the complex $3\times3$
effect matrices, not just expectations on particular real inputs.

For every real $s$, differentiating once more yields

$$
\begin{aligned}
F_M''(s)&=-B^\dagger U_s^\dagger[G,[G,M]]U_sB,\\
\|F_M''(s)\|_{\mathrm{op}}
&\le4h^2\|M\|_{\mathrm{op}}\le100,\\
\|F_M(t)-F_M(0)\|_{\mathrm{op}}&\le50t^2
\quad(t\in\mathbb R).
\end{aligned}
\tag{17.15}
$$

The last line follows by integrating twice and using (17.14).
Since $T_t^\dagger(M)=F_M(t)$ and $F_M(0)=B^\dagger MB$,
these are exactly the five differences in (17.2). Consequently
$\delta_0(T_t)\le50t^2$, without a fairness assumption or an
output restriction.

For the lower bound on channel error, use the legitimate pure
qutrit input $x=(1,0,0)^{\mathsf T}$, with ideal output $u=Bx$.
By (17.4) and (17.8), $JGu=C_\perp Zx=c_0$ and $\|c_0\|=1$.
The integral remainder for the finite matrix exponential gives

$$
\|U_t-I_5-itG\|_{\mathrm{op}}
\le\frac{h^2t^2}{2}\le\frac{25t^2}{2},\qquad
\|JU_tu\|\ge t-\frac{25t^2}{2}\ge\frac t2
\quad(0<t\le1/25).
\tag{17.16}
$$

Indeed the second derivative of $U_s$ is $-G^2U_s$, whose norm
is at most $h^2$, and $Ju=0$.
For two unit vectors $u,w$, the unhalved trace distance of their
rank-one projections is

$$
\|ww^\dagger-uu^\dagger\|_1
=2\sqrt{1-|\langle u,w\rangle|^2}.
\tag{17.17}
$$

This standard pure-state trace-distance identity is also immediate
on their at most two-dimensional span: the difference has trace
zero and eigenvalues
$\pm\sqrt{1-|\langle u,w\rangle|^2}$, with zeros on the
orthogonal complement. See also Watrous, Chapters 2–3, for
trace-distance and channel-distinguishability conventions.
The range of $J$ is orthogonal to $u$, so taking $w=U_tu$ gives

$$
\begin{aligned}
\|(T_t-\operatorname{Ad}_B)(xx^\dagger)\|_1
&=2\sqrt{1-|\langle u,U_tu\rangle|^2}\\
&\ge2\|JU_tu\|\ge t,\\
\|T_t-\operatorname{Ad}_B\|_\diamond&\ge t
\qquad(0<t\le1/25).
\end{aligned}
\tag{17.18}
$$

The last line uses $d=1$ and $X=xx^\dagger$ in (17.3), where
$\|X\|_1=1$. Allowing any further finite untouched reference can
only increase the supremum. In particular no factor of two is
removed from this lower bound.

The defect on this interval is strictly positive as well.
Since $JGp=C_\perp Zq=a(c_0+c_1)$, (17.16)'s remainder estimate
applied to $p$ yields

$$
\begin{aligned}
\|JU_tp\|&\ge t\sqrt2 a-\frac{25t^2}{2}
\ge t\left(\sqrt2 a-\frac12\right)>0,\\
\sqrt2 a&=\frac{1+\sqrt2}{\sqrt6}>\frac12
\qquad(0<t\le1/25).
\end{aligned}
\tag{17.19}
$$

On input $q$, the immediate ideal effect has expectation one,
whereas the actual expectation is $|\langle p,U_tp\rangle|^2$.
As $\operatorname{ran}J\subseteq p^\perp$, this gives

$$
\begin{aligned}
\delta_0(T_t)
&\ge|\langle q,(T_t^\dagger(P)-E)q\rangle|\\
&=1-|\langle p,U_tp\rangle|^2
\ge\|JU_tp\|^2
\ge t^2\left(\sqrt2 a-\frac12\right)^2>0.
\end{aligned}
\tag{17.20}
$$

Equations (17.15), (17.18) and (17.20) prove (17.5).
Substitution of $t_n=1/(25n)$ gives
$50t_n^2=2/(25n^2)$ and hence all of (17.6). In particular the
defects tend to zero while the displayed error-to-defect ratios
diverge. Given any proposed finite $C>0$ and $\eta>0$ in (17.7),
choose an integer $n$ large enough that

$$
n>2C,\qquad \frac{2}{25n^2}\le\eta.
\tag{17.21}
$$

Then $\delta_0(T_n)\le\eta$ but the ratio in (17.6) exceeds
$C$, a contradiction. The permitted single calibration
$\theta=0$ suffices to refute constants quantified over all real
calibration angles.

For any fixed $\alpha>1/2$, (17.5) also gives

$$
\frac{\|T_t-\operatorname{Ad}_B\|_\diamond}
{\delta_0(T_t)^\alpha}
\ge 50^{-\alpha}t^{1-2\alpha}\longrightarrow+\infty
\qquad(t\downarrow0).
\tag{17.22}
$$

Thus no finite coefficient and positive local defect threshold
can give that exponent, even at zero angle. For the complementary
upper bound, directly reuse Theorem 13.3: on precisely this full
complex CPTP domain, uniformly over all real $\theta$,

$$
\delta_\theta(T)\le\varepsilon\le\frac12,\quad\varepsilon>0
\quad\Longrightarrow\quad
\|T-\operatorname{Ad}_B\|_\diamond\le800\sqrt\varepsilon.
\tag{17.23}
$$

For positive defect take $\varepsilon=\delta_\theta(T)$; at zero
defect let $\varepsilon\downarrow0$ in the same inequality.
This supplies the exponent $1/2$, while (17.22) excludes every
larger exponent. The upper estimate is the existing Theorem 13.3,
and the present construction adds its matching exponent obstruction.
It does not yield an optimal coefficient, an exact modulus, a
classification at every nonzero angle, or a calibration-error model.
It makes no physical-realization or resource-minimum assertion.
$\square$

## 追加锚（本行以下为增补区）

## 18. Global linear stability with exact qutrit output support

**Theorem 18.1 (All-angle effect-to-diamond linear bound on the supported output; repo-derived).**
Use the actual embedding and tests of Definitions 1.1–1.2 and 11.1.
Explicitly, in the physical orthonormal basis $(e_0,\ldots,e_4)$ of
$H=\mathbb C^5$, and in the input qutrit, respectively, put

$$
\begin{gathered}
u=(e_0+e_3)/\sqrt2,\qquad v_H=(e_1+e_4)/\sqrt2,\qquad z=e_2,
\qquad B=(u,v_H,z),\qquad R=\operatorname{ran}B,\qquad Q=BB^\dagger,\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
 e=(1,1,-2)^{\mathsf T}/\sqrt6,\qquad
 f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
u_0=(\xi+e)/\sqrt2,\qquad E=u_0u_0^\dagger,\qquad
 p=Bu_0,\qquad P=pp^\dagger,\qquad P_1=P,\qquad P_0=I_5-P.
\end{gathered}
\tag{18.1}
$$

Thus $B^\dagger B=I_3$ and $Q$ is precisely the output-support
projection, whereas $P$ is the immediate task effect. For every real,
fixed, known angle $\theta$, the actual acquisition on all of $H$ is

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+2^{-1/2}|v_H\rangle\langle e_2|
                         +|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+2^{-1/2}|v_H\rangle\langle e_2|
                         +|z\rangle\langle e_3|,\\
A_0(\theta)&=\cos\theta K_0+i\sin\theta K_1,\qquad
A_1(\theta)=i\sin\theta K_0+\cos\theta K_1.
\end{aligned}
\tag{18.2}
$$

Let $T:M_3(\mathbb C)\to M_5(\mathbb C)$ be any complex-linear
CPTP map with the exact output-support property

$$
T(X)=QT(X)Q\qquad\text{for every }X\in M_3(\mathbb C).
\tag{18.3}
$$

With $T^\dagger$ its trace adjoint, define the same actual defect as
in (13.23) and (17.2):

$$
\begin{aligned}
\delta_\theta(T)=\max\Bigl\{&\|T^\dagger(P)-E\|_{\mathrm{op}},\\
&\max_{j,y\in\{0,1\}}
\bigl\|T^\dagger(A_j^\dagger P_yA_j)
       -B^\dagger A_j^\dagger P_yA_jB\bigr\|_{\mathrm{op}}\Bigr\}.
\end{aligned}
\tag{18.4}
$$

Here $A_j=A_j(\theta)$. The continuation effects retain their actual
labels and their joint probabilities; neither outcome is conditioned
or renormalized. Then, uniformly in every such $\theta$ and $T$,

$$
\|T-\operatorname{Ad}_B\|_\diamond
\le216578\,\delta_\theta(T),\qquad
\operatorname{Ad}_B(X)=BXB^\dagger.
\tag{18.5}
$$

This is a global bound, with no restriction on the size of the defect.
In particular it gives the local implication with $C=216578$ and
$\eta=1/2$. The norm is the full unhalved diamond norm

$$
\|\Lambda\|_\diamond
=\sup_{d\ge1}\ \sup_{0\ne X\in M_3(\mathbb C)\otimes M_d(\mathbb C)}
\frac{\|(\Lambda\otimes\operatorname{id}_{M_d})(X)\|_1}{\|X\|_1}.
\tag{18.6}
$$

Thus the estimate includes every finite untouched inaccessible
reference and every complex amplified input matrix, and in particular
every joint density matrix. The constant is an explicit upper bound.
Theorem 17.1 retains its stated domain and conclusion: its obstructing
family has output outside $R$, as identified below, so (18.3) excludes
that family. The supported-output contract here is precisely the one
in Theorem 5.2; the continuation still uses the full actual operators
(11.1), restated in (18.2).

Proof. Write $\delta=\delta_\theta(T)$, use Euclidean vector norms,
and let $\|M\|_{\mathrm{HS}}^2=\operatorname{Tr}(M^\dagger M)$.
Compression gives

$$
\Phi(X)=B^\dagger T(X)B,\qquad
T=\operatorname{Ad}_B\circ\Phi,\qquad
\Psi=\Phi^\dagger,\qquad \Psi(I_3)=I_3.
\tag{18.7}
$$

Indeed compression is completely positive, and exact support gives
$\operatorname{Tr}\Phi(X)=\operatorname{Tr}(QT(X))
=\operatorname{Tr}T(X)=\operatorname{Tr}X$. Consequently $\Phi$ is
CPTP and, for every physical matrix $M\in M_5(\mathbb C)$,
$T^\dagger(M)=\Psi(B^\dagger MB)$.

Use exactly the three probes of (5.6)–(5.7) and the frame (13.26):

$$
\begin{gathered}
u_1=\frac{\xi-e/2+(\sqrt3/2)e^{2i\theta}f}{\sqrt2},\qquad
u_2=\frac{\xi-e/2-(\sqrt3/2)e^{2i\theta}f}{\sqrt2},\qquad
\Pi_i=u_iu_i^\dagger\quad(0\le i\le2),\\
\|u_i\|=1,\qquad \langle u_i,u_k\rangle=\tfrac14\quad(i\ne k),\\
S=\sum_{i=0}^2\Pi_i
 =\operatorname{diag}_{(\xi,e,f)}(3/2,3/4,3/4)
 \succeq\tfrac34I_3.
\end{gathered}
\tag{18.8}
$$

The inner product is conjugate-linear in its first argument.
For the exact correspondence with (1.4), let
$U_0(x_0,x_1,x_2)=(x_0,x_2,x_1)$,
$W(x_0,x_1,x_2)=(x_1,x_0,x_2)$,
$V_0=U_0e^{i\theta W}$ and $V_1=V_0W$.
The actual identity $A_jB=BV_j/\sqrt2$ and the probe identities
already evaluated in §5 give

$$
\begin{aligned}
B^\dagger PB&=\Pi_0,&
B^\dagger A_j^\dagger P_1A_jB&=\tfrac12\Pi_{j+1},\\
B^\dagger A_j^\dagger P_0A_jB&=\tfrac12(I_3-\Pi_{j+1})
&& (j=0,1).
\end{aligned}
\tag{18.9}
$$

These are compressions of the actual full-$H$ effects, justified for
$T$ by (18.3). In particular the weights are $1/2$, with no
full-$H$ fairness identity assumed. Set
$\epsilon_i=\|\Psi(\Pi_i)-\Pi_i\|_{\mathrm{op}}$.
Since $\Psi$ is unital, the complementary effect differences are
negatives of their corresponding $y=1$ differences. Thus

$$
\delta=\max\{\epsilon_0,\epsilon_1/2,\epsilon_2/2\},\qquad
\sum_{i=0}^2\epsilon_i\le5\delta,\qquad
\epsilon_i\le2\delta.
\tag{18.10}
$$

We first establish the elementary scalar estimate needed for the
quantitative argument, inside this proof. For an arbitrary complex
$3\times3$ matrix $M$, put

$$
\begin{gathered}
d_i=\|[\Pi_i,M]\|_{\mathrm{HS}},\qquad
\lambda_i=\langle u_i,Mu_i\rangle,\qquad c=\lambda_0,\\
e_i=(I_3-\Pi_i)Mu_i,\qquad
f_0=u_0^\dagger M(I_3-\Pi_0).
\end{gathered}
\tag{18.11}
$$

Here $f_0$ is a row vector. Since
$e_i=-[\Pi_i,M]u_i$ and
$f_0=u_0^\dagger[\Pi_0,M]$, we have
$\|e_i\|\le d_i$ and $\|f_0\|\le d_0$.
Evaluate $u_0^\dagger Mu_i$ using first the row decomposition at
$u_0$, then the column decomposition at $u_i$. For $i=1,2$ the
nonzero overlap in (18.8) gives

$$
\frac{\lambda_i-\lambda_0}{4}
=f_0u_i-u_0^\dagger e_i,\qquad
|\lambda_i-c|\le4(d_0+d_i).
\tag{18.12}
$$

It follows that
$\|(M-cI_3)u_0\|\le d_0$ and
$\|(M-cI_3)u_i\|\le4d_0+5d_i$ for $i=1,2$.
For $A=M-cI_3$, the frame bound gives
$\sum_i\|Au_i\|^2=\operatorname{Tr}(A^\dagger AS)
\ge(3/4)\|A\|_{\mathrm{HS}}^2$.
Cauchy–Schwarz, in the form
$(4a+5b)^2\le41(a^2+b^2)$, therefore yields

$$
\begin{aligned}
\|M-cI_3\|_{\mathrm{HS}}^2
&\le\tfrac43\bigl[d_0^2+(4d_0+5d_1)^2+(4d_0+5d_2)^2\bigr]\\
&\le\tfrac43(83d_0^2+41d_1^2+41d_2^2)
\le111\sum_{i=0}^2\|[\Pi_i,M]\|_{\mathrm{HS}}^2.
\end{aligned}
\tag{18.13}
$$

No reality or self-adjointness assumption on $M$ was used.

Take a finite Kraus representation
$\Phi(X)=\sum_\ell L_\ell XL_\ell^\dagger$ with
$\sum_\ell L_\ell^\dagger L_\ell=I_3$.
Such a representation follows by spectral decomposition of the
positive $9\times9$ Choi matrix
$\sum_{a,b=1}^3|a\rangle\langle b|\otimes
\Phi(|a\rangle\langle b|)$: writing its eigenvectors as vectorized
matrices yields the $L_\ell$, and its trace-preserving partial trace
gives the displayed Kraus normalization.
For any projection $\Pi$ let $\Delta=\Psi(\Pi)-\Pi$.
Expanding the commutators and using that normalization gives

$$
\begin{aligned}
\sum_\ell[\Pi,L_\ell]^\dagger[\Pi,L_\ell]
&=\Psi(\Pi)-\Psi(\Pi)\Pi-\Pi\Psi(\Pi)+\Pi\\
&=\Delta-\Delta\Pi-\Pi\Delta.
\end{aligned}
\tag{18.14}
$$

For each rank-one $\Pi_i$, taking the trace and using trace norm
and operator norm duality gives

$$
\begin{aligned}
\sum_\ell\|[\Pi_i,L_\ell]\|_{\mathrm{HS}}^2
&=\operatorname{Tr}\bigl((I_3-2\Pi_i)
                    (\Psi(\Pi_i)-\Pi_i)\bigr)\\
&\le\|I_3-2\Pi_i\|_1\,\epsilon_i=3\epsilon_i.
\end{aligned}
\tag{18.15}
$$

The left side is nonnegative. Put
$c_\ell=\langle u_0,L_\ell u_0\rangle$ and
$N_\ell=L_\ell-c_\ell I_3$.
Apply (18.13) to each $L_\ell$, then (18.15) and (18.10), to obtain
the Kraus residual estimate

$$
R_N:=\sum_\ell\|N_\ell\|_{\mathrm{HS}}^2
\le111\cdot3\sum_{i=0}^2\epsilon_i
\le1665\delta.
\tag{18.16}
$$

The symbol $R_N$ is a nonnegative scalar, distinct from the output
space $R$.

To retain the coherent contribution rather than lose a square root,
use trace preservation exactly. Define

$$
\begin{gathered}
s=\sum_\ell|c_\ell|^2,\qquad
M_0=\sum_\ell\overline{c_\ell}N_\ell,\qquad
D=\sum_\ell N_\ell^\dagger N_\ell,\\
sI_3+M_0+M_0^\dagger+D=I_3,\qquad
H_c=\frac{M_0-M_0^\dagger}{2i}=H_c^\dagger.
\end{gathered}
\tag{18.17}
$$

Expanding $\Phi(X)$ and substituting the Hermitian part of $M_0$
from this identity gives the exact decomposition on every complex
matrix $X$:

$$
\begin{aligned}
\Phi(X)-X&=i[H_c,X]+\mathcal V(X),\\
\mathcal V(X)&=\sum_\ell N_\ell XN_\ell^\dagger
                        -\tfrac12(DX+XD).
\end{aligned}
\tag{18.18}
$$

Since $D\succeq0$, we have
$\|D\|_{\mathrm{op}}\le\operatorname{Tr}D=R_N$ and
$\sum_\ell\|N_\ell\|_{\mathrm{op}}^2\le R_N$.
The trace-norm ideal inequality
$\|AXB\|_1\le\|A\|_{\mathrm{op}}\|X\|_1\|B\|_{\mathrm{op}}$
therefore implies, for every finite $d$ and every complex
$X\in M_3(\mathbb C)\otimes M_d(\mathbb C)$,

$$
\begin{aligned}
\|(\mathcal V\otimes\operatorname{id}_{M_d})(X)\|_1
&\le\left(\sum_\ell\|N_\ell\|_{\mathrm{op}}^2
                           +\|D\|_{\mathrm{op}}\right)\|X\|_1\\
&\le2R_N\|X\|_1.
\end{aligned}
\tag{18.19}
$$

Likewise the explicit adjoint
$\mathcal V^\dagger(Y)=\sum_\ell N_\ell^\dagger YN_\ell
-(DY+YD)/2$ satisfies
$\|\mathcal V^\dagger(\Pi_i)\|_{\mathrm{op}}\le2R_N$.
Taking the trace adjoint in (18.18) gives
$\Psi(\Pi_i)-\Pi_i=-i[H_c,\Pi_i]
+\mathcal V^\dagger(\Pi_i)$, hence

$$
\|[H_c,\Pi_i]\|_{\mathrm{op}}
\le\epsilon_i+2R_N\le2\delta+2R_N.
\tag{18.20}
$$

Apply the scalar estimate (18.13) again, now to $M=H_c$.
Its scalar $h=\langle u_0,H_cu_0\rangle$ is real.
For $3\times3$ matrices,
$\|A\|_{\mathrm{HS}}\le\sqrt3\|A\|_{\mathrm{op}}$.
Thus (18.20), with three commutators, yields

$$
\begin{aligned}
\|H_c-hI_3\|_{\mathrm{op}}
&\le\|H_c-hI_3\|_{\mathrm{HS}}\\
&\le\sqrt{111\cdot3\cdot3}\,(2\delta+2R_N)\\
&=\sqrt{999}\,(2\delta+2R_N)
\le64(\delta+R_N),
\end{aligned}
\tag{18.21}
$$

where $999<32^2$. Since scalar matrices do not contribute to a
commutator, the same trace-norm ideal inequality, together with
(18.19), proves for every such $d$ and complex $X$ that

$$
\begin{aligned}
\|((\Phi-\operatorname{id}_{M_3})\otimes\operatorname{id}_{M_d})(X)\|_1
&\le\bigl(2\|H_c-hI_3\|_{\mathrm{op}}+2R_N\bigr)\|X\|_1\\
&\le(128\delta+130R_N)\|X\|_1\\
&\le(128+130\cdot1665)\delta\|X\|_1\\
&=216578\delta\|X\|_1.
\end{aligned}
\tag{18.22}
$$

Finally (18.7) gives the exact amplified correspondence

$$
\begin{aligned}
&((T-\operatorname{Ad}_B)\otimes\operatorname{id}_{M_d})(X)\\
&\quad=(B\otimes I_d)
  [((\Phi-\operatorname{id}_{M_3})\otimes\operatorname{id}_{M_d})(X)]
  (B^\dagger\otimes I_d).
\end{aligned}
\tag{18.23}
$$

Isometric embedding preserves the nonzero singular values and hence
the trace norm of every complex matrix. Taking both suprema in
(18.6) proves
$\|T-\operatorname{Ad}_B\|_\diamond
=\|\Phi-\operatorname{id}_{M_3}\|_\diamond\le216578\delta$.
Nothing in the argument uses smallness of $\delta$; it also includes
$\delta=0$ directly. Choosing $\eta=1/2$ gives the stated local form.
The exact rigidity at zero defect is the existing supported-output
conclusion of Theorem 5.2; no new general exact-rigidity theorem is
needed here.

For the distinction from Theorem 17.1, retain its notation
$U_t=\exp(itG)$ and $T_t=\operatorname{Ad}_{U_tB}$ at $\theta=0$.
For $x=(1,0,0)^{\mathsf T}$ its exhibited family satisfies

$$
\|(I_5-Q)U_tBx\|\ge t/2>0\qquad(0<t\le1/25).
\tag{18.24}
$$

Consequently $T_t(xx^\dagger)$ is not supported in $R$, so it fails
(18.3). Its obstruction on the unrestricted output domain and the
linear estimate on the exactly supported domain are compatible.
$\square$

## 追加锚（本行以下为增补区）

## 19. Global linear stability from two actual labelled acquisitions

**Theorem 19.1 (All-angle linear effect-to-diamond bound with unrestricted output; repo-derived).**
Keep precisely Definitions 1.1–1.2 and 11.1. All spaces and matrices
are over $\mathbb C$, and every angle $\theta\in\mathbb R$ is fixed
and known. In the physical orthonormal basis $(e_0,\ldots,e_4)$ put

$$
\begin{gathered}
u=(e_0+e_3)/\sqrt2,\qquad v_H=(e_1+e_4)/\sqrt2,\qquad z=e_2,
\qquad B=(u,v_H,z):\mathbb C^3\longrightarrow\mathbb C^5,\\
\xi=(1,1,1)^{\mathsf T}/\sqrt3,\qquad
 e=(1,1,-2)^{\mathsf T}/\sqrt6,\qquad
 f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
q_0=(\xi+e)/\sqrt2,\qquad E=q_0q_0^\dagger,\qquad
p=Bq_0,\qquad P=pp^\dagger,\qquad P_1=P,\quad P_0=I_5-P.
\end{gathered}
\tag{19.1}
$$

Use the actual full-$H$ acquisition, including its action outside
$\operatorname{ran}B$:

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+2^{-1/2}|v_H\rangle\langle e_2|
                         +|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+2^{-1/2}|v_H\rangle\langle e_2|
                         +|z\rangle\langle e_3|,\\
A_0&=\cos\theta K_0+i\sin\theta K_1,\qquad
A_1=i\sin\theta K_0+\cos\theta K_1.
\end{aligned}
\tag{19.2}
$$

For every complex-linear CPTP map
$T:M_3(\mathbb C)\to M_5(\mathbb C)$, with unrestricted output,
let $T^\dagger$ be its trace adjoint and define exactly

$$
\begin{aligned}
\delta_{2,\theta}(T)=\max\Bigl\{&\|T^\dagger(P)-E\|_{\mathrm{op}},\\
&\max_{j,y\in\{0,1\}}
 \|T^\dagger(A_j^\dagger P_yA_j)
       -B^\dagger A_j^\dagger P_yA_jB\|_{\mathrm{op}},\\
&\max_{j,k,y\in\{0,1\}}
 \|T^\dagger((A_kA_j)^\dagger P_y(A_kA_j))
       -B^\dagger(A_kA_j)^\dagger P_y(A_kA_j)B\|_{\mathrm{op}}
\Bigr\}.
\end{aligned}
\tag{19.3}
$$

Thus the immediate test, all four original one-step joint effects,
and all eight actual depth-two joint effects are retained. The first
acquisition has label $j$, the next has label $k$, so the product is
$A_kA_j$. With $U_0,W,V_0,V_1$ exactly as in (1.4), and
$E_1=E$, $E_0=I_3-E$, the ideal compressions are

$$
\begin{aligned}
B^\dagger A_j^\dagger P_yA_jB
 &=\tfrac12 V_j^\dagger E_yV_j,\\
B^\dagger(A_kA_j)^\dagger P_y(A_kA_j)B
 &=\tfrac14 V_j^\dagger V_k^\dagger E_yV_kV_j.
\end{aligned}
\tag{19.4}
$$

The factors $1/2$ and $1/4$ are the actual ideal joint weights;
they are not removed by conditional normalization. Then the global
estimate, uniformly in every real $\theta$ and every such $T$, is

$$
\|T-\operatorname{Ad}_B\|_\diamond
 \le C\,\delta_{2,\theta}(T),\qquad
 C=418231548,\qquad \operatorname{Ad}_B(X)=BXB^\dagger.
\tag{19.5}
$$

In particular, the uniform local consequence has the explicit
constants $C=418231548$ and $\eta=1/2$:

$$
\delta_{2,\theta}(T)\le\eta=\tfrac12
\quad\Longrightarrow\quad
\|T-\operatorname{Ad}_B\|_\diamond\le418231548\,\delta_{2,\theta}(T).
\tag{19.6}
$$

Here the norm is the full unhalved diamond norm

$$
\|\Lambda\|_\diamond
 =\sup_{d\ge1}\ \sup_{0\ne X\in M_3(\mathbb C)\otimes M_d(\mathbb C)}
 \frac{\|(\Lambda\otimes\operatorname{id}_{M_d})(X)\|_1}{\|X\|_1}.
\tag{19.7}
$$

It includes arbitrary finite untouched inaccessible references and
every complex amplified input matrix. The tests in (19.3) are uniform
over all complex qutrit density inputs: each operator norm equals
the supremum of the absolute expectation of its Hermitian difference
over those inputs. No known-input, output-support, conditional-branch,
full-$H$ fairness, or extra correction hypothesis is imposed. When
$T$ is a corrected average channel, the conclusion is for that average;
it asserts no uniform guarantee on arbitrarily rare branches.

There is also a global persistence consequence within this statement.
For every integer $m\ge2$, let $A_h=A_{h_r}\cdots A_{h_1}$ for
$h\in\{0,1\}^r$, in chronological order, and set

$$
\begin{aligned}
\delta_{m,\theta}(T)=\max\Bigl\{&
 \|T^\dagger(P)-E\|_{\mathrm{op}},\\
 &\max_{\substack{1\le r\le m,\ h\in\{0,1\}^r\\y\in\{0,1\}}}
 \|T^\dagger(A_h^\dagger P_yA_h)-B^\dagger A_h^\dagger P_yA_hB\|_{\mathrm{op}}
 \Bigr\}.
\end{aligned}
\tag{19.8}
$$

These are again actual joint effects, whose ideal compressions have
weights $2^{-r}$. Then
$\|T-\operatorname{Ad}_B\|_\diamond\le418231548\,\delta_{m,\theta}(T)$
for all the same $\theta,T$, without a small-defect restriction.
Theorem 17.1 concerns the older five-effect defect only; its
obstruction is not asserted for (19.3). The support promise (18.3)
of Theorem 18.1 is not assumed here. The coefficient in (19.5) is
an upper bound, with no assertion of optimality, minimum continuation
depth at individual angles, uncertain-calibration stability, or
physical realization.

The quantitative bridge from these augmented actual effects to
unrestricted-output linear control is `repo-derived`, relative to
the source geometry of this volume; no global novelty is claimed.
Its residual ingredient is (13.38), and its scalar frame ingredient
is (18.13), both recalled in the proof on their required domains.
Finite rectangular Kraus representation is the standard supplier
[FiniteKrausRepresentation][KRAUS]; finite-dimensional norm duality
and the trace-norm ideal property are as in John Watrous,
[The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/),
Chapters 2–3. The exact observable-correction framework of
[Bény–Kempf–Kribs, Definition 8, equation (7), and Theorem 9][BKK]
is a source for that framework, not for the quantitative coefficient
or the augmented-effect estimate (19.5).

Proof. Fix $\theta,T$ as stated and write $\delta=\delta_{2,\theta}(T)$.
Use Euclidean vector norms, operator matrix norms unless otherwise
indicated, and $\|M\|_{\mathrm{HS}}^2=\operatorname{Tr}(M^\dagger M)$.
No smallness assumption on $\delta$ will be used. Complete $B$ by

$$
c_0=(e_0-e_3)/\sqrt2,\qquad c_1=(e_1-e_4)/\sqrt2,\qquad
C_\perp=(c_0,c_1).
\tag{19.9}
$$

Then $B^\dagger B=I_3$, $C_\perp^\dagger C_\perp=I_2$,
$B^\dagger C_\perp=0$, and
$BB^\dagger+C_\perp C_\perp^\dagger=I_5$.
The actual three probes of (5.6)–(5.7) are

$$
\begin{gathered}
q_1=(\xi-e/2+(\sqrt3/2)e^{2i\theta}f)/\sqrt2,\qquad
q_2=(\xi-e/2-(\sqrt3/2)e^{2i\theta}f)/\sqrt2,\qquad
\Pi_i=q_iq_i^\dagger,\\
\|q_i\|=1,\qquad q_i^\dagger q_k=\tfrac14\quad(i\ne k),\qquad
S=\sum_{i=0}^2\Pi_i
 =\tfrac32\xi\xi^\dagger+\tfrac34ee^\dagger+\tfrac34ff^\dagger
 \succeq\tfrac34I_3.
\end{gathered}
\tag{19.10}
$$

The last identities follow by expanding the displayed vectors in
the orthonormal basis $(\xi,e,f)$. In particular their constants
are independent of $\theta$. The source acquisition gives

$$
A_jB=BV_j/\sqrt2,\qquad
V_k^\dagger EV_k=\Pi_{k+1},\qquad
\operatorname{ran}A_j\subseteq\operatorname{ran}B.
\tag{19.11}
$$

Each $A_j$ has norm one, so all actual effects in (19.3) are positive
contractions. Define, for $j=0,1$ and $i=0,1,2$,

$$
N_{ji}=A_j^\dagger B\Pi_iB^\dagger A_j.
\tag{19.12}
$$

Since $P=B\Pi_0B^\dagger$, (19.11) gives the exact physical identities

$$
\begin{aligned}
N_{j0}&=A_j^\dagger PA_j,\\
N_{j,k+1}&=2(A_kA_j)^\dagger P(A_kA_j)\quad(k=0,1),\\
A_j^\dagger A_j&=A_j^\dagger P_0A_j+A_j^\dagger P_1A_j.
\end{aligned}
\tag{19.13}
$$

For the second line insert $BB^\dagger$ on both sides of
$A_k^\dagger PA_k$ between $A_j^\dagger$ and $A_j$ and use
$B^\dagger A_k^\dagger PA_kB=\Pi_{k+1}/2$. This uses the actual
range of $A_j$, not a restriction on $T$.

First recall (13.38), including a derivation valid at $\delta=0$.
Take a finite rectangular Kraus family

$$
T(X)=\sum_\ell L_\ell XL_\ell^\dagger,\qquad
\sum_\ell L_\ell^\dagger L_\ell=I_3,\qquad
c_\ell=p^\dagger L_\ell q_0,\quad N_\ell=L_\ell-c_\ell B,\quad
\mathcal R=\sum_\ell\|N_\ell\|_{\mathrm{HS}}^2.
\tag{19.14}
$$

Put $Q_p=I_5-P$, $t_j=A_j^\dagger p$, $w_j=q_{j+1}$, and
$F_j=w_jw_j^\dagger$. Directly from the actual probes and (19.2),

$$
B^\dagger t_j=e^{-i\theta}w_j/\sqrt2,\qquad
w_j^\dagger q_0=\tfrac14,\qquad
A_jBw_j=e^{i\theta}p/\sqrt2.
\tag{19.15}
$$

For each $\ell$ define the nonnegative defects

$$
\begin{aligned}
a_\ell&=\|Q_pL_\ell q_0\|^2,&
b_\ell&=\|p^\dagger L_\ell(I_3-E)\|_{\mathrm{HS}}^2,\\
g_{\ell j}&=\|t_j^\dagger L_\ell(I_3-F_j)\|_{\mathrm{HS}}^2,&
h_{\ell j}&=\|Q_pA_jL_\ell w_j\|^2,\\
q_\ell&=a_\ell+b_\ell+g_{\ell0}+g_{\ell1}+h_{\ell0}+h_{\ell1}.
\end{aligned}
\tag{19.16}
$$

For orthonormal bases $(x_1,x_2)$ of $q_0^\perp$ and
$(z_{j1},z_{j2})$ of $w_j^\perp$, positivity, trace preservation,
and the original five effects contained in (19.3) give

$$
\begin{aligned}
\sum_\ell a_\ell
 &=1-\langle q_0,T^\dagger(P)q_0\rangle\le\delta,\\
\sum_\ell b_\ell
 &=\sum_{a=1}^2\langle x_a,T^\dagger(P)x_a\rangle\le2\delta,\\
\sum_\ell g_{\ell j}
 &=\sum_{a=1}^2\langle z_{ja},T^\dagger(t_jt_j^\dagger)z_{ja}\rangle
 \le2\delta,\\
\sum_\ell h_{\ell j}
 &=\langle w_j,T^\dagger(A_j^\dagger Q_pA_j)w_j\rangle\le\delta,\\
\sum_\ell q_\ell&\le9\delta.
\end{aligned}
\tag{19.17}
$$

Indeed the ideal expectations in the second and third lines vanish
on the indicated orthogonal complements. For the fourth line,
$B^\dagger A_j^\dagger Q_pA_jB=(I_3-F_j)/2$, whose expectation
at $w_j$ is zero. Thus both original $y=0$ effects, as well as both
$y=1$ effects, are used; no cancellation or conditional test is substituted.

The rectangular coercivity behind this residual estimate is

$$
\|k\|\le10\|A_jk\|+3|p^\dagger k|+3|t_{1-j}^\dagger k|
\qquad(k\in\mathbb C^5,\ j=0,1).
\tag{19.18}
$$

To see its uniformity explicitly, the three nonzero singular values
of $A_j$ are $1,1,1/\sqrt2$. Orthonormal bases of its kernel are

$$
\begin{aligned}
j=0:&\quad -i\sin\theta e_0+\cos\theta e_1,\quad
                 \cos\theta e_3-i\sin\theta e_4,\\
j=1:&\quad \cos\theta e_0-i\sin\theta e_1,\quad
                 -i\sin\theta e_3+\cos\theta e_4.
\end{aligned}
\tag{19.19}
$$

For $h=x$ times the first kernel vector plus $y$ times the second,
let $\alpha=(\sqrt2+1)/\sqrt{12}$ and
$\beta_0=(\sqrt2-2)/\sqrt{12}$. Substitution gives

$$
p^\dagger h=\alpha e^{-i\theta}(x+y)/\sqrt2,\qquad
 t_{1-j}^\dagger h=\alpha x+\beta_0y,\qquad
 \alpha-\beta_0=\alpha+|\beta_0|=\sqrt3/2.
\tag{19.20}
$$

Writing $m=x+y$, $n=\alpha x+\beta_0y$, solve
$x=(n-\beta_0m)/(\alpha-\beta_0)$ and
$y=(\alpha m-n)/(\alpha-\beta_0)$. Since
$\sqrt2/\alpha<3$ and $2/(\alpha-\beta_0)<3$, this gives
$\|h\|\le3(|p^\dagger h|+|t_{1-j}^\dagger h|)$.
For the orthogonal decomposition $k=h+r$, the singular values imply
$\|r\|\le\sqrt2\|A_jk\|$. Since $\|p\|=1$ and $\|t_{1-j}\|\le1$,
the triangle inequality gives (19.18), using $7\sqrt2<10$.

Suppress $\ell$ temporarily in (19.14)–(19.16). Then
$\|Nq_0\|=\sqrt a$ and $\|p^\dagger N\|=\sqrt b$.
Decompose
$t_j^\dagger L=\lambda_jw_j^\dagger+\rho_j$, where
$\rho_j=t_j^\dagger L(I_3-F_j)$ and $\|\rho_j\|=\sqrt{g_j}$.
Consequently $t_j^\dagger N=d_jw_j^\dagger+\rho_j$, where
$d_j=\lambda_j-ce^{i\theta}/\sqrt2$. Evaluating at $q_0$ yields

$$
|d_j|\le4(\sqrt a+\sqrt{g_j}),\qquad
\|t_j^\dagger N\|\le4\sqrt a+5\sqrt{g_j}.
\tag{19.21}
$$

Because $Q_pA_jBw_j=0$,
$\|Q_pA_jNw_j\|=\sqrt{h_j}$. Adding the $p$ component and then
applying (19.18) proves

$$
\begin{aligned}
\|A_jNw_j\|&\le\sqrt{h_j}+4\sqrt a+5\sqrt{g_j},\\
\|Nw_j\|&\le52\sqrt a+3\sqrt b+50\sqrt{g_j}
                  +15\sqrt{g_{1-j}}+10\sqrt{h_j},\\
\|Nw_j\|^2&\le5538q,\qquad
52^2+3^2+50^2+15^2+10^2=5538.
\end{aligned}
\tag{19.22}
$$

The last inequality is Cauchy–Schwarz. Taking the trace against the
frame bound in (19.10), and then summing (19.17), gives

$$
\begin{aligned}
\|N_\ell\|_{\mathrm{HS}}^2
 &\le\tfrac43\bigl(\|N_\ell q_0\|^2+
             \|N_\ell w_0\|^2+\|N_\ell w_1\|^2\bigr)\\
 &\le\tfrac43(1+2\cdot5538)q_\ell
   =\tfrac{44308}{3}q_\ell\le15000q_\ell,\\
\mathcal R&\le135000\delta.
\end{aligned}
\tag{19.23}
$$

This is the residual supplier (13.38), now with
$\delta_\theta(T)\le\delta_{2,\theta}(T)$. The non-strict endpoint
includes $q_\ell=0$ and $\delta=0$, with no division by a defect,
$\sin\theta$, or $\cos\theta$.

Next retain the coherent first-order term rather than bounding it
by $\sqrt{\mathcal R}$. Set

$$
\begin{gathered}
s=\sum_\ell|c_\ell|^2,\quad
M=\sum_\ell\overline{c_\ell}N_\ell,\quad
D=\sum_\ell N_\ell^\dagger N_\ell,\\
H_c=(B^\dagger M-M^\dagger B)/(2i),\qquad
Z=C_\perp^\dagger M,\qquad K=iBH_c+C_\perp Z.
\end{gathered}
\tag{19.24}
$$

Here $H_c=H_c^\dagger\in M_3(\mathbb C)$ and
$Z:\mathbb C^3\to\mathbb C^2$. Trace preservation gives

$$
sI_3+B^\dagger M+M^\dagger B+D=I_3,
\qquad B^\dagger K+K^\dagger B=0.
\tag{19.25}
$$

For completeness, the Hermitian part of $B^\dagger M$ is
$((1-s)I_3-D)/2$, so
$M=B((1-s)I_3-D)/2+K$. Expanding (19.14) therefore gives,
on every complex $X\in M_3(\mathbb C)$, the exact decomposition

$$
\begin{aligned}
T(X)-BXB^\dagger&=\mathcal L_K(X)+\mathcal V(X),\\
\mathcal L_K(X)&=KXB^\dagger+BXK^\dagger,\\
\mathcal V(X)&=\sum_\ell N_\ell XN_\ell^\dagger
                   -\tfrac12B(DX+XD)B^\dagger.
\end{aligned}
\tag{19.26}
$$

Since $\|D\|\le\operatorname{Tr}D=\mathcal R$ and
$\sum_\ell\|N_\ell\|^2\le\mathcal R$, the trace-norm ideal
inequality at every finite amplification gives

$$
\|(\mathcal V\otimes\operatorname{id}_{M_d})(X)\|_1
 \le2\mathcal R\|X\|_1
\quad(d\ge1,\ X\in M_3(\mathbb C)\otimes M_d(\mathbb C)).
\tag{19.27}
$$

In detail the Kraus sum contributes at most $\mathcal R\|X\|_1$,
and the two terms involving $D/2$ together contribute at most
$\mathcal R\|X\|_1$. The explicit adjoint is

$$
\mathcal V^\dagger(J)=\sum_\ell N_\ell^\dagger JN_\ell
 -\tfrac12\bigl(DB^\dagger JB+B^\dagger JBD\bigr),\qquad
\|\mathcal V^\dagger(J)\|\le2\mathcal R\|J\|.
\tag{19.28}
$$

Let $b=\delta+2\mathcal R$. For every actual tested positive
contraction $J$ in (19.3), (19.26)–(19.28) imply
$\|\mathcal L_K^\dagger(J)\|\le b$.

The additional tests now control $K$ using the full-$H$ geometry.
Define the isometry $D_0:\mathbb C^2\to\mathbb C^3$ and $F$ by

$$
D_0(y_0,y_1)=(y_0,-y_1,0),\qquad
F=e^{-2i\theta W}D_0,\qquad F^\dagger F=I_2.
\tag{19.29}
$$

Direct substitution in the full operators (19.2) gives

$$
K_0C_\perp=BU_0D_0/\sqrt2,\qquad
K_1C_\perp=-BU_0WD_0/\sqrt2.
\tag{19.30}
$$

Thus $A_0C_\perp=BU_0e^{-i\theta W}D_0/\sqrt2
=BV_0F/\sqrt2$, while
$A_1C_\perp=-BU_0e^{-i\theta W}WD_0/\sqrt2
=-BV_1F/\sqrt2$. Together with (19.11) and the orthogonal
resolution in (19.9), these are the all-five-dimensional identities

$$
A_j=\tfrac1{\sqrt2}BV_j(B^\dagger+\sigma_jFC_\perp^\dagger),
\qquad \sigma_0=1,\quad\sigma_1=-1.
\tag{19.31}
$$

In particular set

$$
Q_j=iH_c+\sigma_jFZ,\qquad
A_jK=BV_jQ_j/\sqrt2,\qquad
\Gamma_{ji}=V_j^\dagger\Pi_iV_j.
\tag{19.32}
$$

Using (19.12) and
$\mathcal L_K^\dagger(J)=B^\dagger JK+K^\dagger JB$, we obtain

$$
\mathcal L_K^\dagger(N_{ji})
 =\tfrac12(\Gamma_{ji}Q_j+Q_j^\dagger\Gamma_{ji}).
\tag{19.33}
$$

The first line of (19.13) is an original $y=1$ effect, whereas its
second line is twice an actual depth-two $y=1$ effect. Therefore

$$
\begin{aligned}
\|\Gamma_{j0}Q_j+Q_j^\dagger\Gamma_{j0}\|&\le2b,\\
\|\Gamma_{ji}Q_j+Q_j^\dagger\Gamma_{ji}\|&\le4b\quad(i=1,2).
\end{aligned}
\tag{19.34}
$$

Both original outcomes also give
$\|\mathcal L_K^\dagger(A_j^\dagger A_j)\|\le2b$.
Since this derivative is $(Q_j+Q_j^\dagger)/2$, it follows that

$$
\|Q_j+Q_j^\dagger\|\le4b.
\tag{19.35}
$$

We use the scalar frame estimate (18.13), with its numerical constant
made explicit. For unit vectors $a_0,a_1,a_2$ satisfying
$a_i^\dagger a_k=1/4$ for $i\ne k$ and
$\sum_i a_ia_i^\dagger\succeq3I_3/4$, put
$\Pi'_i=a_ia_i^\dagger$, and for any complex matrix $J$ define

$$
\begin{gathered}
d_i=\|[\Pi'_i,J]\|_{\mathrm{HS}},\quad
\lambda_i=a_i^\dagger Ja_i,\quad c=\lambda_0,\\
e_i=(I_3-\Pi'_i)Ja_i,\qquad f_0=a_0^\dagger J(I_3-\Pi'_0).
\end{gathered}
\tag{19.36}
$$

The commutators give $\|e_i\|\le d_i$ and $\|f_0\|\le d_0$.
The row and column decompositions of $a_0^\dagger Ja_i$ give
$(\lambda_i-c)/4=f_0a_i-a_0^\dagger e_i$ for $i=1,2$.
Hence $\|(J-cI_3)a_0\|\le d_0$ and
$\|(J-cI_3)a_i\|\le4d_0+5d_i$ for $i=1,2$.
The frame inequality and $(4a+5b)^2\le41(a^2+b^2)$ yield

$$
\begin{aligned}
\|J-cI_3\|_{\mathrm{HS}}^2
 &\le\tfrac43\bigl[d_0^2+(4d_0+5d_1)^2+(4d_0+5d_2)^2\bigr]\\
 &\le\tfrac43(83d_0^2+41d_1^2+41d_2^2)
 \le111\sum_{i=0}^2d_i^2.
\end{aligned}
\tag{19.37}
$$

This holds for every $J$, and after any common unitary conjugation
of the three frame vectors.

Write $Q_j=X_j+iY_j$, where $X_j=X_j^\dagger$ and
$Y_j=Y_j^\dagger$. Equation (19.35) gives $\|X_j\|\le2b$.
In (19.34), subtract $\Gamma_{ji}X_j+X_j\Gamma_{ji}$, whose norm
is at most $4b$. The remaining term is $i[\Gamma_{ji},Y_j]$, so

$$
\|[\Gamma_{ji},Y_j]\|\le8b\qquad(i=0,1,2).
\tag{19.38}
$$

Apply (19.37) to $Y_j$ and $a_i=V_j^\dagger q_i$.
Since $\|J\|_{\mathrm{HS}}\le\sqrt3\|J\|$ for $3\times3$
matrices, the real scalar $h_j=a_0^\dagger Y_ja_0$ satisfies

$$
\begin{aligned}
\|Y_j-h_jI_3\|
 &\le\|Y_j-h_jI_3\|_{\mathrm{HS}}
 \le8\sqrt{999}\,b\le256b,\\
\|Q_j-ih_jI_3\|&\le258b.
\end{aligned}
\tag{19.39}
$$

Now put $h=(h_0+h_1)/2$ and $a=(h_0-h_1)/2$, both real.
Adding and subtracting the two estimates in (19.39), and using
$Q_0=iH_c+FZ$, $Q_1=iH_c-FZ$, gives

$$
\|H_c-hI_3\|\le258b,\qquad
\|FZ-iaI_3\|\le258b.
\tag{19.40}
$$

The map $Z:\mathbb C^3\to\mathbb C^2$ has rank at most two,
so it has a unit kernel vector $x$. Applying the second inequality
to that vector gives $|a|\le258b$. Since $F$ is an isometry,

$$
\|Z\|=\|FZ\|\le516b,\qquad
\|K-ihB\|\le\|H_c-hI_3\|+\|Z\|\le774b.
\tag{19.41}
$$

The scalar term $ihB$ contributes zero to $\mathcal L_K$, because
$h$ is real. At every finite amplification and on every complex
input matrix, the trace-norm ideal inequality therefore gives

$$
\|(\mathcal L_K\otimes\operatorname{id}_{M_d})(X)\|_1
 \le2\|K-ihB\|\|X\|_1\le1548b\|X\|_1.
\tag{19.42}
$$

Combining (19.23), (19.26), (19.27), and (19.42) proves

$$
\begin{aligned}
\|((T-\operatorname{Ad}_B)\otimes\operatorname{id}_{M_d})(X)\|_1
 &\le\bigl(1548(\delta+2\mathcal R)+2\mathcal R\bigr)\|X\|_1\\
 &=\bigl(1548\delta+3098\mathcal R\bigr)\|X\|_1\\
 &\le(1548+3098\cdot135000)\delta\|X\|_1\\
 &=418231548\,\delta\|X\|_1.
\end{aligned}
\tag{19.43}
$$

Taking both suprema in (19.7) proves (19.5). All inequalities hold
at $\delta=0$ and require no smallness, so (19.6) follows with
$\eta=1/2$. Finally (19.8) retains every effect in (19.3), whence
$\delta_{m,\theta}(T)\ge\delta_{2,\theta}(T)$ for $m\ge2$;
substitution in the already global bound proves the stated
all-depth persistence consequence. $\square$

## 追加锚（本行以下为增补区）

## 24. Global linear stability after erasing only the first acquisition label

**Theorem 24.1 (All-angle linear stability from the actual first-label-erased depth-two effects; repo-derived).**
Keep exactly Definitions 1.1, 1.2 and 11.1 and the model of
Theorem 19.1, as in revision
`18a1747aed2fed3feeec42c090ed9bd2f299bbde`, inherited from
`34fd39ed3a39104806b0ec0f202750f3f552689f`.
In particular $B:\mathbb C^3\to\mathbb C^5$ is the specified isometry,
$E=q_0q_0^\dagger$, $P=BEB^\dagger$, $P_1=P$ and $P_0=I_5-P$
are exactly (19.1). For every fixed known real $\theta$, use exactly
the actual full-$H$ acquisition operators $A_j(\theta)$ in (19.2),
including their action outside $\operatorname{ran}B$.
For every complex-linear CPTP map
$T:M_3(\mathbb C)\to M_5(\mathbb C)$ with unrestricted output, retain
the original five-effect defect

$$
\delta_{1,\theta}(T)=\max\Bigl\{
\|T^\dagger(P)-E\|_{\mathrm{op}},
\max_{j,y\in\{0,1\}}
\|T^\dagger(A_j^\dagger P_yA_j)-B^\dagger A_j^\dagger P_yA_jB\|_{\mathrm{op}}
\Bigr\}.
\tag{24.1}
$$

Erase only the first acquisition label $j$, retaining the second
label $k$ and the final outcome $y$, by defining

$$
\begin{aligned}
D_{k,y}&=\sum_{j=0}^1(A_kA_j)^\dagger P_y(A_kA_j),\\
\delta_{\mathrm{erased},\theta}(T)
&=\max\Bigl\{\delta_{1,\theta}(T),
\max_{k,y\in\{0,1\}}
\|T^\dagger(D_{k,y})-B^\dagger D_{k,y}B\|_{\mathrm{op}}\Bigr\}.
\end{aligned}
\tag{24.2}
$$

Then, uniformly over all stipulated $\theta$ and $T$,

$$
\|T-\operatorname{Ad}_B\|_\diamond
 \le6000000000000\,\delta_{\mathrm{erased},\theta}(T),
\qquad \operatorname{Ad}_B(X)=BXB^\dagger.
\tag{24.3}
$$

In particular the local implication holds with constants
$C=6000000000000$ and $\eta=1/2$, independent of $\theta,T$.
The diamond norm is full and unhalved: it takes the supremum over
all finite untouched, inaccessible reference spaces and every nonzero
complex amplified input matrix, as in (19.7). The effect errors are
uniform over all qutrit input density matrices and concern the actual
raw joint weights. No output-support, normalized conditional-branch,
new-detector, quantum-feedback or unknown-calibration hypothesis is
introduced; no resource-minimum or physical-realization conclusion is
part of the statement.

Proof. Write $\delta=\delta_{\mathrm{erased},\theta}(T)$ and $q=q_0$.
All spaces are complex; vector norms are Euclidean and unlabelled
matrix norms are operator norms. Use $C_\perp$ from (19.9),
$w_0=q_1,w_1=q_2$ from (19.10), and the finite rectangular Kraus
family and residuals $c_\ell,N_\ell,\mathcal R$ of (19.14).
The five-effect residual argument (19.14)–(19.23) uses only the
original immediate and one-step effects. It therefore applies directly
with $\delta_{1,\theta}(T)$, without any separately labelled depth-two
hypothesis, and gives

$$
\mathcal R=\sum_\ell\|N_\ell\|_{\mathrm{HS}}^2
 \le135000\,\delta_{1,\theta}(T)\le135000\delta.
\tag{24.4}
$$

Use $M,D,Z,K$ from (19.24) and write $H=H_c$, so that
$K=iBH+C_\perp Z$. Trace preservation gives exactly the decomposition
(19.26), on every complex input matrix, with the amplified and adjoint
bounds (19.27)–(19.28). Thus, setting $b=\delta+2\mathcal R$, for
each of the nine actual tested effects $J_{\mathrm{test}}$,

$$
\|\mathcal L_K^\dagger(J_{\mathrm{test}})\|\le b,
\qquad
\|(\mathcal V\otimes\operatorname{id}_{M_d})(Y)\|_1
 \le2\mathcal R\|Y\|_1.
\tag{24.5}
$$

Each tested effect is a positive contraction because the actual
acquisition is trace preserving; this includes each $D_{k,y}$.
The second inequality holds for every finite $d$ and every complex
$Y\in M_3(\mathbb C)\otimes M_d(\mathbb C)$.
The finite Kraus representation is the standard finite-dimensional
CP-map representation; the quantitative residual supplier is precisely
(19.14)–(19.28), rather than the separately labelled conclusion (19.5).

Let $U=U_0$ and $W$ be the permutation matrices of (1.4): $U$ swaps
qutrit coordinates $1,2$ and $W$ swaps coordinates $0,1$.
Put $V_0=Ue^{i\theta W}$, $V_1=V_0W$,
$D_0(y_0,y_1)=(y_0,-y_1,0)$ and $F=e^{-2i\theta W}D_0$.
Direct multiplication of the full physical matrices gives

$$
A_j=2^{-1/2}BV_j(B^\dagger+\sigma_jFC_\perp^\dagger),
\qquad \sigma_0=1,\quad\sigma_1=-1,\qquad F^\dagger F=I_2.
\tag{24.6}
$$

In particular $X=FZ$ has image in
$L=\operatorname{span}\{(1,0,0),(0,1,0)\}$.
Put $Q_j=iH+\sigma_jX$. The two original outcomes for each $j$
and the immediate effect imply

$$
\|X+X^\dagger\|\le4b,\qquad \|[E,H]\|\le b.
\tag{24.7}
$$

Indeed the derivative of $A_j^\dagger A_j$ is
$(Q_j+Q_j^\dagger)/2$, and the immediate effect is $P$.
Let $L$ also denote the orthogonal projection onto that subspace and set

$$
J=\frac{L(X-X^\dagger)L}{2i},\qquad
H'=EHE+(I_3-E)H(I_3-E),\qquad
h=q^\dagger Hq,\qquad H_0=H'-hI_3.
\tag{24.8}
$$

Then $J$ is Hermitian, supported on $L$, and

$$
\|X-iJ\|\le6b,\qquad \|H-H'\|\le b,\qquad
\|Q_j-i(H'+\sigma_jJ)\|\le7b.
\tag{24.9}
$$

For the first bound the Hermitian part of $LXL$ has norm at most
$2b$, and $XL^\perp=L(X+X^\dagger)L^\perp$ has norm at most $4b$.
For the second the norm of the off-diagonal $E$ block of Hermitian
$H$ equals the norm of $[E,H]$.

Write $\Pi_0=E$, $\Pi_{j+1}=w_jw_j^\dagger$, and define
$\Gamma_{ji}=V_j^\dagger\Pi_iV_j$ and
$N_{ji}=A_j^\dagger B\Pi_iB^\dagger A_j$.
Identity (24.6) gives

$$
\mathcal L_K^\dagger(N_{ji})
 =\tfrac12(\Gamma_{ji}Q_j+Q_j^\dagger\Gamma_{ji}),\qquad
D_{k,1}=\tfrac12\sum_jN_{j,k+1}.
\tag{24.10}
$$

The original success effects and (24.9) give

$$
\|[\Pi_{j+1},H_0+\sigma_jJ]\|\le16b.
\tag{24.11}
$$

To use only available erased effects, set $S_2=D_{0,1}+D_{1,1}$.
Its derivative has norm at most $2b$. In (24.10), replacing $Q_j$
by $i(H'+\sigma_jJ)$ changes this derivative by at most $14b$:
there are four terms, each with coefficient $1/4$ and error at most
$2\cdot7b$. The scalar $h$ cancels in all commutators.

Put $r=(\xi-e)/\sqrt2$, $\phi=2\theta$, and use the orthonormal
moving qutrit basis $(q,r,e^{i\phi}f)$. In this basis

$$
\Pi_{1,2}=a_\pm a_\pm^\dagger,\qquad
 a_\pm=(1,3,\pm\sqrt6)^{\mathsf T}/4,\qquad
W=\operatorname{diag}(1,1,-1).
\tag{24.12}
$$

Define the explicit matrices

$$
\bar U=\frac14\begin{pmatrix}
1&3&\sqrt6\\3&1&-\sqrt6\\\sqrt6&-\sqrt6&2
\end{pmatrix},\qquad
G=\frac1{32}\begin{pmatrix}
17&3&-\sqrt6\\3&9&-3\sqrt6\\-\sqrt6&-3\sqrt6&6
\end{pmatrix}.
\tag{24.13}
$$

The matrix of $V_0$ is
$e^{i\theta}\operatorname{diag}(1,1,e^{-i\phi})\bar U$.
Since $\Pi_1+\Pi_2$ has no coupling between $f$ and its orthogonal
complement, these matrices give

$$
\Gamma_{01}+\Gamma_{02}=2G,\qquad
\Gamma_{11}+\Gamma_{12}=2WGW.
\tag{24.14}
$$

Formula (24.10) for $S_2$ and the preceding error bound yield

$$
\|[G,H_0+J]+[WGW,H_0-J]\|\le32b.
\tag{24.15}
$$

No separately retained first label is reconstructed from a sum.

Here is a complete real-coordinate certificate for (24.11) and (24.15).
Put $d=(\sqrt2+1)/\sqrt6$ and $e_*=(\sqrt2-1)/\sqrt6$.
Since $(1,1,0)^{\mathsf T}/\sqrt2=dq+e_*r$, the general matrices
$H_0$ and $J$ in the moving basis have the forms

$$
H_0=\begin{pmatrix}0&0&0\\0&x&z+iw\\0&z-iw&y\end{pmatrix},\qquad
J=\begin{pmatrix}
d^2A&de_*A&d(R+iI)\\
de_*A&e_*^2A&e_*(R+iI)\\
d(R-iI)&e_*(R-iI)&D
\end{pmatrix},\qquad
v=(x,y,z,w,A,D,R,I)\in\mathbb R^8.
\tag{24.16}
$$

Here $D$ in the coordinate matrix denotes a real coordinate, distinct
from the residual matrix $D$ of (19.24).
Define the real linear map $\mathsf M$ by listing the real and imaginary
parts of all entries of the three matrices

$$
[a_+a_+^\dagger,H_0+J],\qquad
[a_-a_-^\dagger,H_0-J],\qquad
[G,H_0+J]+[WGW,H_0-J].
\tag{24.17}
$$

The Euclidean norm of $\mathsf Mv$ is exactly the square root of the
sum of their three squared Hilbert–Schmidt norms. Expansion gives

$$
\begin{aligned}
\operatorname{Tr}(\mathsf M^{\mathsf T}\mathsf M)
 &=\frac{16187}{1152}-\frac{7\sqrt2}{8}<16,\\
\det(\mathsf M^{\mathsf T}\mathsf M)
 &=\frac{91264725\sqrt2}{268435456}
   +\frac{262163385}{536870912}>\frac12.
\end{aligned}
\tag{24.18}
$$

These are polynomial matrix identities over the real algebraic numbers.
The Gram matrix splits into coordinate blocks $(x,y,R)$, $(z,A,D)$,
$(w)$ and $(I)$, with respective determinants

$$
\frac{27\sqrt2}{256}+\frac{81}{512},\qquad
\frac{45\sqrt2}{512}+\frac{165}{1024},\qquad
\frac{249}{64},\qquad
\frac{69}{16}-\frac{25\sqrt2}{24}.
\tag{24.19}
$$

Their product is the determinant in (24.18).
The Gram matrix is positive semidefinite, and its positive determinant
makes it positive definite. Each eigenvalue is below $16$, so its
least eigenvalue exceeds $(1/2)16^{-7}=2^{-29}$. Consequently

$$
\|v\|_2\le32768\|\mathsf Mv\|_2
 \le32768\cdot96b=3145728b.
\tag{24.20}
$$

The bound $\|\mathsf Mv\|_2\le96b$ follows from (24.11), (24.15)
and $\|Q\|_{\mathrm{HS}}\le\sqrt3\|Q\|$ for $3\times3$ matrices.
Formula (24.16) also gives

$$
\begin{aligned}
\|H_0\|_{\mathrm{HS}}^2&=x^2+y^2+2z^2+2w^2,\\
\|J\|_{\mathrm{HS}}^2&=A^2+D^2+2R^2+2I^2,\\
\|H_0\|+\|J\|&\le2\sqrt2\|v\|_2\le9437184b.
\end{aligned}
\tag{24.21}
$$

Since $F$ is an isometry, $\|Z\|=\|X\|$. Combining with (24.9),

$$
\|K-ihB\|\le\|H-hI_3\|+\|Z\|
 \le(9437184+7)b\le10000000b.
\tag{24.22}
$$

The scalar term $ihB$ contributes zero to $\mathcal L_K$.
For every finite reference dimension $d$ and every complex amplified
matrix $Y$, the trace-norm ideal inequality, (19.26)–(19.28) and
(24.22) therefore give

$$
\|((T-\operatorname{Ad}_B)\otimes\operatorname{id}_{M_d})(Y)\|_1
 \le(20000000b+2\mathcal R)\|Y\|_1.
\tag{24.23}
$$

By (24.4), $b\le270001\delta$, and the coefficient is at most

$$
(20000000\cdot270001+270000)\delta
 =5400020270000\delta\le6000000000000\delta.
\tag{24.24}
$$

Taking both defining diamond suprema proves (24.3), including at zero
defect. There is no division by an angle, a branch probability or a
defect. Every effect used is either an original effect or an actual
sum of the stipulated raw erased depth-two success effects. The
argument uses no output-support restriction and no identification of
a density-state supremum with the full complex-matrix diamond norm.
$\square$

## 追加锚（本行以下为增补区）

## 25. Full-H leakage invisible to completely erased acquisitions

**Theorem 25.1 (Zero erased defect outside the embedded dephasing family; repo-derived).**
Keep exactly $B,E,P,P_0,P_1$ of (19.1), Definitions 1.1–1.2
and 11.1, and the actual full-$H$ operators $A_j(\theta)$ of
(19.2). Write $z_H=e_2$ for the physical vector denoted by $z$ there,
to distinguish it from the complex parameter in $\mathcal D_z$ of
(8.3). For every fixed known real $\theta$, erase all acquisition
labels at depths one and two and retain only the raw final-success
effects

$$
\begin{aligned}
J_0&=P,\\
J_1&=\sum_{j=0}^1 A_j^\dagger P A_j,\\
J_2&=\sum_{j,k=0}^1(A_kA_j)^\dagger P(A_kA_j),\\
\delta_{\mathrm{unlabelled},\theta}(T)
 &=\max_{r=0,1,2}
 \|T^\dagger(J_r)-B^\dagger J_rB\|_{\mathrm{op}}.
\end{aligned}
\tag{25.1}
$$

There is a single complex-linear CPTP map
$T:M_3(\mathbb C)\to M_5(\mathbb C)$, independent of $\theta$,
with unrestricted output, such that for every real $\theta$

$$
\delta_{\mathrm{unlabelled},\theta}(T)=0,\qquad
\inf_{z\in\mathbb C,\ |z|\le1}
 \|T-\operatorname{Ad}_B\circ\mathcal D_z\|_\diamond\ge2.
\tag{25.2}
$$

Here the diamond norm is unhalved and takes both suprema over all
finite untouched reference spaces and all nonzero complex amplified
input matrices. Thus no finite constants $C,\eta>0$, independent of
$\theta,T$, can make
$\delta_{\mathrm{unlabelled},\theta}(T)\le\eta$ imply a diamond
distance at most $C\sqrt{\delta_{\mathrm{unlabelled},\theta}(T)}$
to this family. The defect uses raw probabilities uniformly over all
qutrit density inputs, without conditional normalization.

Proof. With $f$ of (1.5), set

$$
\begin{gathered}
c=(e_0+e_1-e_3-e_4)/2,\qquad b=Bf,\\
c^\dagger c=1,\qquad B^\dagger c=0,\qquad P_-=ff^\dagger,\\
L_0=BP_+,\qquad L_1=cf^\dagger,\qquad
T(X)=L_0XL_0^\dagger+L_1XL_1^\dagger.
\end{gathered}
\tag{25.3}
$$

The two rectangular Kraus matrices satisfy
$L_0^\dagger L_0+L_1^\dagger L_1=P_++ff^\dagger=I_3$.
The standard Kraus criterion therefore makes $T$ a complex-linear
CPTP map on the full stated domain. In particular its minus-sector
output is allowed to lie outside $\operatorname{ran}B$.

Define the actual erased acquisition on $M_5(\mathbb C)$ by

$$
\mathcal G(Y)=K_0YK_0^\dagger+K_1YK_1^\dagger
 =\sum_{j=0}^1A_j(\theta)YA_j(\theta)^\dagger,\qquad
J_r=(\mathcal G^\dagger)^r(P)\quad(r=0,1,2).
\tag{25.4}
$$

The equality follows because the coefficient matrix
$\left(\begin{smallmatrix}\cos\theta&i\sin\theta\\
i\sin\theta&\cos\theta\end{smallmatrix}\right)$ taking
$(K_0,K_1)$ to $(A_0,A_1)$ is unitary for every real $\theta$.
Thus (25.4) is angle independent on every full-$H$ matrix, including
leaked states. Directly from the original operators (11.1), (19.2),

$$
\begin{aligned}
K_0B&=BU_0/\sqrt2,& K_1B&=BU_0W/\sqrt2,\\
K_0c&=(u-z_H)/2,& K_1c&=(u-z_H)/2,\\
K_0b&=(u-z_H)/2,& K_1b&=-(u-z_H)/2.
\end{aligned}
\tag{25.5}
$$

Consequently the erased identity (8.1) and these full-$H$ actions give

$$
\begin{aligned}
\mathcal G\circ\operatorname{Ad}_B
 &=\operatorname{Ad}_{BU_0}\circ\Delta_W,\\
\mathcal G(cc^\dagger)&=\mathcal G(bb^\dagger).
\end{aligned}
\tag{25.6}
$$

For every complex $X\in M_3(\mathbb C)$,
$P_-XP_-=(f^\dagger Xf)ff^\dagger$. Substitution into (25.3)
and (25.6), using $\Delta_W^2=\Delta_W$, proves the exact identity
of complex-linear maps

$$
\mathcal G\circ T
 =\mathcal G\circ\operatorname{Ad}_B\circ\Delta_W
 =\mathcal G\circ\operatorname{Ad}_B.
\tag{25.7}
$$

For the immediate effect, put $q=q_0$ of (19.1). Since $Wq=q$,
$E=P_+EP_+$; and $c\perp\operatorname{ran}B$ gives
$c^\dagger Pc=0$. Hence, directly from the Kraus formula,

$$
T^\dagger(J_0)=T^\dagger(P)=E=B^\dagger PB.
\tag{25.8}
$$

For $r=1,2$, compose (25.7) with $\mathcal G^{r-1}$ and take
trace adjoints at $P$. This yields the actual raw effect equalities

$$
T^\dagger(J_1)=B^\dagger J_1B,\qquad
T^\dagger(J_2)=B^\dagger J_2B.
\tag{25.9}
$$

No individually labelled effect has been substituted for a sum.
Equations (25.8)–(25.9) imply zero defect and equality of the three
raw success probabilities for every qutrit density input. Moreover
(25.7) tensor-extends to every finite untouched reference: any common
channel applied after that erased acquisition has the same output
on the two routes. This concerns the successor, rather than the
state before the acquisition.

For every complex $z$ with $|z|\le1$, (8.3) fixes $ff^\dagger$.
The same trace-one input therefore separates $T$ from every member
of the comparison family:

$$
\begin{aligned}
T(ff^\dagger)&=cc^\dagger,\\
(\operatorname{Ad}_B\circ\mathcal D_z)(ff^\dagger)&=bb^\dagger,\\
\|cc^\dagger-bb^\dagger\|_1&=2,\\
\inf_{|z|\le1}\|T-\operatorname{Ad}_B\circ\mathcal D_z\|_\diamond
 &\ge2.
\end{aligned}
\tag{25.10}
$$

Indeed $b,c$ are orthogonal unit vectors, so their projection
difference has eigenvalues $1,-1$ and zeros. The reference of
dimension one and input $ff^\dagger$ are included in the full
complex-matrix diamond supremum; allowing arbitrary finite references
preserves this lower bound. At this channel every proposed modulus
in the statement has right side zero, whereas (25.10) has left side
at least two, proving the asserted failure for every $C,\eta>0$.
No equality value of the diamond norm or optimal resource claim is
needed.

The source-relative construction is the replacement of the minus
output by $cc^\dagger$ in (25.3), together with (25.7) and (25.10).
It reuses the erased identity and dephasing family (8.1)–(8.3), and
the full-$H$ operators (11.1), (19.2). The Kraus criterion and
trace-norm principles are standard; see John Watrous,
[The Theory of Quantum Information](https://cs.uwaterloo.ca/~watrous/TQI/),
Chapters 2–3. Theorem 8.2 retains its supported qutrit-output domain;
Theorems 19.1 and 24.1 retain their richer labelled tests. None is
altered by (25.2), which neither classifies all full-$H$ solutions
nor asserts global priority, physical realization or native
availability of the stipulated observables. $\square$

## 追加锚（本行以下为增补区）

## 26. Three completely erased raw effects determine the full-H successor

**Theorem 26.1 (Unrestricted erased-successor rigidity; repo-derived).**
Keep exactly $B,E,P$ of Definitions 1.1–1.2 and (19.1), and the
actual full-$H$ operators $A_j(\theta)$ of Definition 11.1 and
(19.2), including their action outside $\operatorname{ran}B$.
For every fixed known $\theta\in\mathbb R$, set

$$
\begin{aligned}
\Phi_\theta(Y)&=\sum_{j=0}^1A_j(\theta)YA_j(\theta)^\dagger,\\
J_0&=P,\qquad J_1=\sum_{j=0}^1A_j^\dagger PA_j,\\
J_2&=\sum_{j,k=0}^1(A_kA_j)^\dagger P(A_kA_j).
\end{aligned}
\tag{26.1}
$$

These are precisely the three completely unlabelled raw success
effects of (25.1), with chronological products $A_kA_j$ and their
original joint weights. For every complex-linear CPTP map
$T:M_3(\mathbb C)\to M_5(\mathbb C)$ with unrestricted output,

$$
\left[T^\dagger(J_t)=B^\dagger J_tB\quad(t=0,1,2)\right]
\quad\Longrightarrow\quad
\Phi_\theta\circ T=\Phi_\theta\circ\operatorname{Ad}_B
\quad\text{on }M_3(\mathbb C).
\tag{26.2}
$$

The hypotheses mean equality of the three raw success probabilities
for every qutrit density input. The conclusion extends to every
complex amplified input and every finite untouched reference. No
output-support restriction on $T$, label access, control, conditional
normalization or additional observation is assumed.

Proof. Use qutrit coordinates throughout and abbreviate $U=U_0$.
Put $P_\pm=(I_3\pm W)/2$ and
$\Delta_W(X)=P_+XP_++P_-XP_-$. Define the orthonormal input basis
and the orthonormal output basis by

$$
\begin{gathered}
q=(\xi+e)/\sqrt2,\qquad r=(\xi-e)/\sqrt2,\qquad
f=(1,-1,0)^{\mathsf T}/\sqrt2,\\
a=Uq,\qquad h=Ur,\qquad g=Uf=(1,0,-1)^{\mathsf T}/\sqrt2,\\
k=(1,0,1)^{\mathsf T}/\sqrt2,\qquad
N=\operatorname{span}\{(1,0,0)^{\mathsf T},(0,0,1)^{\mathsf T}\},\\
F=\Delta_W(U^\dagger EU),\qquad Q=E+2F.
\end{gathered}
\tag{26.3}
$$

Here $q,r\in\operatorname{ran}P_+$ and
$f\in\operatorname{ran}P_-$. The coefficient matrix relating
$(A_0,A_1)$ to $(K_0,K_1)$ is
$\bigl(\begin{smallmatrix}\cos\theta&i\sin\theta\\
i\sin\theta&\cos\theta\end{smallmatrix}\bigr)$, which is unitary
for every real $\theta$. Thus, on every $Y\in M_5(\mathbb C)$,

$$
\Phi_\theta(Y)=\mathcal G(Y)
 :=K_0YK_0^\dagger+K_1YK_1^\dagger.
\tag{26.4}
$$

This cancellation precedes any input restriction. Introduce the
rectangular matrices
$D_+=B^\dagger(K_0+K_1)/\sqrt2$ and
$D_-=B^\dagger(K_0-K_1)/\sqrt2$. Their actual matrices in the
physical basis $(e_0,\ldots,e_4)$ are

$$
D_+=\frac1{\sqrt2}
\begin{pmatrix}1&1&0&0&0\\0&0&\sqrt2&0&0\\0&0&0&1&1\end{pmatrix},
\qquad
D_-=\frac1{\sqrt2}
\begin{pmatrix}1&-1&0&0&0\\0&0&0&0&0\\0&0&0&-1&1\end{pmatrix}.
\tag{26.5}
$$

Direct substitution gives

$$
\begin{gathered}
D_+^\dagger D_++D_-^\dagger D_-=I_5,\qquad
D_+B=UP_+,\qquad D_-B=UP_-,\qquad\operatorname{ran}D_-\subset N,\\
\mathcal G(Y)=B\bigl(D_+YD_+^\dagger+D_-YD_-^\dagger\bigr)B^\dagger.
\end{gathered}
\tag{26.6}
$$

In particular $Zx=(D_+x,D_-x)$ is an isometry into
$\mathbb C^3\oplus\mathbb C^3$ and $Z(Bq)=(a,0)$. Since
$B^\dagger PB=E$ and $\mathcal G$ has output in
$\operatorname{ran}B$, the chronological raw effects satisfy

$$
\begin{aligned}
J_1&=D_+^\dagger ED_++D_-^\dagger ED_-,\\
B^\dagger J_1B&=F,\\
J_2&=D_+^\dagger FD_++D_-^\dagger FD_-.
\end{aligned}
\tag{26.7}
$$

Indeed these are $\mathcal G^\dagger(P)$ and
$(\mathcal G^\dagger)^2(P)$, so no conditioning or branch label has
replaced the sums. In the output basis $(a,h,g)$, the matrices are

$$
E=\frac1{16}\begin{pmatrix}
1&3&\sqrt6\\3&9&3\sqrt6\\\sqrt6&3\sqrt6&6
\end{pmatrix},\qquad
F=\frac1{32}\begin{pmatrix}
17&3&-\sqrt6\\3&9&-3\sqrt6\\-\sqrt6&-3\sqrt6&6
\end{pmatrix}.
\tag{26.8}
$$

The two target compressions in the input basis $(q,r,f)$ are

$$
B^\dagger J_1B=\begin{pmatrix}
1/16&3/16&0\\3/16&9/16&0\\0&0&3/8
\end{pmatrix},\qquad
B^\dagger J_2B=\begin{pmatrix}
17/32&3/32&0\\3/32&9/32&0\\0&0&3/16
\end{pmatrix}.
\tag{26.9}
$$

Take any finite rectangular Kraus representation
$T(X)=\sum_\ell L_\ell XL_\ell^\dagger$, with
$\sum_\ell L_\ell^\dagger L_\ell=I_3$. Its existence for every
channel between these finite complex spaces is the standard Kraus
criterion; see John Watrous, [The Theory of Quantum Information,
Chapter 2, Corollary 2.27](https://cs.uwaterloo.ca/~watrous/TQI/TQI.2.pdf).
The immediate equality $T^\dagger(P)=qq^\dagger$ forces

$$
L_\ell q=\alpha_\ell Bq,\qquad
\sum_\ell|\alpha_\ell|^2=1,\qquad
(Bq)^\dagger L_\ell z=0\quad(z\perp q).
\tag{26.10}
$$

To see this, the $q$ expectation of $P$ is one, as is the total
squared norm supplied by trace preservation. Thus the sum of the
nonnegative squared norms $\|(I_5-P)L_\ell q\|^2$ is zero.
Every $L_\ell q$ lies in the line $Bq$. For $z\perp q$, the zero
$P$ expectation is $\sum_\ell\|PL_\ell z\|^2=0$, annihilating
that component for each $\ell$ separately.

Set $X_\ell=D_+L_\ell$, $Y_\ell=D_-L_\ell$ and
$M=\sum_\ell\overline{\alpha_\ell}X_\ell$. The isometry $Z$
transfers (26.10) and trace preservation to

$$
\begin{gathered}
X_\ell q=\alpha_\ell a,\qquad Y_\ell q=0,\qquad
a^\dagger X_\ell z=0\quad(z\perp q),\\
\sum_\ell(X_\ell^\dagger X_\ell+Y_\ell^\dagger Y_\ell)=I_3.
\end{gathered}
\tag{26.11}
$$

The $(q,r)$ entries of the two remaining effect equalities are
$a^\dagger EMr=3/16$ and $a^\dagger FMr=3/32$, while
$a^\dagger Mr=0$. Write $Mr=yh+tg$, with $y,t\in\mathbb C$.
Equation (26.8) gives the complex equations

$$
3y+\sqrt6\,t=3,\qquad 3y-\sqrt6\,t=3.
\tag{26.12}
$$

Their coefficient determinant is $-6\sqrt6\ne0$, so $Mr=h$.
The $(q,f)$ entries give the same equations with both right sides
zero, together with $a^\dagger Mf=0$; hence $Mf=0$. These
functionals separate complex vectors, without a reality restriction.
Trace preservation and $Mr=h$ now yield

$$
\sum_\ell\bigl(\|X_\ell r-\alpha_\ell h\|^2+
\|Y_\ell r\|^2\bigr)
=1-2\operatorname{Re}(h^\dagger Mr)+1=0.
\tag{26.13}
$$

Every summand is nonnegative. Therefore
$X_\ell r=\alpha_\ell h$ and $Y_\ell r=0$ for every $\ell$.
Together with (26.11), this fixes the entire plus input block after
erasure.

For the remaining input $f$, put $x_\ell=X_\ell f$ and
$y_\ell=Y_\ell f$. Then $x_\ell\perp a$ by (26.11), and
$y_\ell\in N$ by the actual range of $D_-$. The two relevant
compressions of $Q=E+2F$ are

$$
\begin{aligned}
Q\big|_{a^\perp=\operatorname{span}\{h,g\}}
 &=\begin{pmatrix}9/8&0\\0&3/4\end{pmatrix}_{(h,g)},\\
Q\big|_N&=\begin{pmatrix}1&1/4\\1/4&1\end{pmatrix}_{((1,0,0)^{\mathsf T},(0,0,1)^{\mathsf T})}.
\end{aligned}
\tag{26.14}
$$

The latter has orthonormal eigenvectors $k,g$ with eigenvalues
$5/4,3/4$. Both compressions have minimum $3/4$, attained only
on the line $g$. Explicitly,

$$
\begin{aligned}
&x_\ell^\dagger Qx_\ell+y_\ell^\dagger Qy_\ell
 -\tfrac34(\|x_\ell\|^2+\|y_\ell\|^2)\\
&\hspace{1cm}=\tfrac38|h^\dagger x_\ell|^2
 +\tfrac12|k^\dagger y_\ell|^2\ge0.
\end{aligned}
\tag{26.15}
$$

By (26.7) and the two effect equalities, the sum of the first two
terms on the left is the $f$ expectation of
$T^\dagger(J_1+2J_2)$, equal by (26.9) to
$3/8+2(3/16)=3/4$. Equation (26.11) makes the summed squared
norms one. The sum of the nonnegative right sides is consequently
zero, forcing

$$
x_\ell=\beta_\ell g,\qquad y_\ell=\gamma_\ell g,\qquad
\sum_\ell(|\beta_\ell|^2+|\gamma_\ell|^2)=1.
\tag{26.16}
$$

Define $\mathcal R(X)=\sum_\ell(X_\ell XX_\ell^\dagger+
Y_\ell XY_\ell^\dagger)=B^\dagger\mathcal G(T(X))B$.
Thus $\mathcal R(ff^\dagger)=gg^\dagger$.
Moreover $Mf=0$ says $\sum_\ell\overline{\alpha_\ell}\beta_\ell=0$.
It annihilates both cross units from the plus sector to $f$:

$$
\mathcal R(qf^\dagger)=ag^\dagger\sum_\ell\alpha_\ell\overline{\beta_\ell}=0,
\qquad
\mathcal R(rf^\dagger)=hg^\dagger\sum_\ell\alpha_\ell\overline{\beta_\ell}=0.
\tag{26.17}
$$

Their adjoints also vanish. The four plus-sector units
$qq^\dagger,qr^\dagger,rq^\dagger,rr^\dagger$ map respectively
to $aa^\dagger,ah^\dagger,ha^\dagger,hh^\dagger$ by
(26.10)–(26.13). Together with $ff^\dagger$ and the four cross
units, these are all nine complex matrix units. Hence, on every
$X\in M_3(\mathbb C)$,

$$
B^\dagger\mathcal G(T(X))B
 =U\Delta_W(X)U^\dagger
 =B^\dagger\mathcal G(BXB^\dagger)B.
\tag{26.18}
$$

Both full outputs are supported in $\operatorname{ran}B$ by
(26.6), as a consequence of the acquisition, not a promise about
$T$. Thus $\mathcal G\circ T=\mathcal G\circ\operatorname{Ad}_B$.
Equation (26.4) proves (26.2) for every real $\theta$.
For any finite reference dimension $d$, expand an arbitrary complex
input as $\sum_{i,j=1}^d|i\rangle\langle j|\otimes X_{ij}$.
Complex-linearity extends (26.2) term by term, establishing equality
of $\operatorname{id}_{M_d}\otimes(\Phi_\theta\circ T)$ and
$\operatorname{id}_{M_d}\otimes(\Phi_\theta\circ\operatorname{Ad}_B)$
without accessing the reference.

The source-relative deduction combines the two complex cross moments
with saturation of the original $Q=E+2F$ compression bounds for
arbitrary rectangular Kraus families. It reuses (8.1), (8.4),
(25.4)–(25.6) and the standard Kraus, trace and positivity facts.
Theorem 8.2 retains its supported qutrit-output scope; Theorems 19.1
and 24.1 retain their richer labelled data. Theorem 25.1 remains a
counterexample to identifying $T$ with the embedded dephasing family;
its successor identity (25.7) is consistent with (26.2).
This theorem identifies only the erased successor, without a complete
classification of the pre-acquisition channels, a quantitative
stability bound, an optimal constant or resource minimum, a physical
realization or a global priority claim. The symbols $D_\pm,Z,Q$
are mathematical intermediates, not extra detectors, observations,
controls or acquisition hypotheses. $\square$

## 追加锚（本行以下为增补区）
