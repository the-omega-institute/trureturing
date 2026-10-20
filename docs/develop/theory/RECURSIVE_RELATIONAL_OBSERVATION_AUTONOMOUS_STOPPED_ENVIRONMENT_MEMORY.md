# Recursive relational observation: autonomous STOP and environment memory

## 1. Actual source and credited inputs

**Convention 1.1 (Scope).** This volume concerns exact recovery of an unknown
embedded qutrit after an internally chosen first STOP of one fixed measured
instrument. The controller is deterministic, classical, finite and
autonomous in the precise sense of Definition 2.1. The quantum system is
retained throughout. The conclusions are ordinary mathematical deductions,
not Lean certification or physical implementation claims. They concern
acquired chronology, retained classical control and an executed recovery
boundary; no spatial reconstruction is asserted.

**Definition 1.2 (The specified measured instrument).** Write
$M_d=\mathcal B(\mathbb C^d)$ and
$\operatorname{Ad}_L(X)=LXL^\dagger$. A channel is complex-linear,
completely positive and trace-preserving (CPTP). In the ordered basis
$(e_0,e_1,e_2,e_3,e_4)$ of $H=\mathbb C^5$, set

$$
u=(e_0+e_3)/\sqrt2,\qquad v=(e_1+e_4)/\sqrt2,\qquad z=e_2,
\qquad B=[u\ v\ z],\qquad R=\operatorname{im}B.
$$

Thus $B^\dagger B=I_3$. Put $P_R=BB^\dagger$ and
$\iota(X)=BXB^\dagger$. The source is [ENV, Definitions 1.3 and 2.1][ENV],
with its angle fixed at $\theta=\pi/6$. Its environment is
$E=\mathbb C^2$, with orthonormal basis $(f_0,f_1)$ and ready state $f_0$.
The interaction is a fixed unitary completion of the isometry

$$
\begin{aligned}
\mathcal V e_0&=u\otimes f_0,&
\mathcal V e_1&=u\otimes f_1,&
\mathcal V e_2&=v\otimes(f_0+f_1)/\sqrt2,\\
\mathcal V e_3&=z\otimes f_1,&
\mathcal V e_4&=z\otimes f_0.
\end{aligned}
$$

The five displayed images are orthonormal, so such a completion exists;
its action outside $H\otimes f_0$ is fixed and immaterial to these fresh
preparations. The measured outgoing basis is

$$
g_0=(\sqrt3 f_0-if_1)/2,\qquad
g_1=(-if_0+\sqrt3 f_1)/2.
$$

One acquisition freshly prepares this environment, applies this interaction,
measures this basis, supplies the actual outcome $j\in\{0,1\}$ to the
controller, and discards the environment. It is not a choice of a Kraus
representation after an unread channel. In particular the actual operators
are

$$
\begin{aligned}
K_0&=|u\rangle\langle e_0|+2^{-1/2}|v\rangle\langle e_2|
                                  +|z\rangle\langle e_4|,\\
K_1&=|u\rangle\langle e_1|+2^{-1/2}|v\rangle\langle e_2|
                                  +|z\rangle\langle e_3|,\\
A_0&=(\sqrt3 K_0+iK_1)/2,\qquad
A_1=(iK_0+\sqrt3 K_1)/2.
\end{aligned}
$$

**Convention 1.3 (Restricted branch law and algebraic supplier).** Use the
actual matrices from [ENV, Theorem 2.2 and Definition 8.1][ENV]:

$$
\begin{gathered}
U_0=\begin{pmatrix}1&0&0\\0&0&1\\0&1&0\end{pmatrix},\qquad
U_1=\begin{pmatrix}0&1&0\\0&0&1\\1&0&0\end{pmatrix},\\
W=U_0^\dagger U_1=
\begin{pmatrix}0&1&0\\1&0&0\\0&0&1\end{pmatrix},\\
V_0=(\sqrt3 U_0+iU_1)/2=U_0e^{i\pi W/6},\qquad
V_1=(iU_0+\sqrt3 U_1)/2=V_0W.
\end{gathered}
$$

The supplier gives $A_jB=BV_j/\sqrt2$ with unitary $V_j$.
For a chronological binary word $h=h_1\cdots h_n$ put

$$
Q_h=V_{h_n}\cdots V_{h_1},\qquad Q_\epsilon=I_3,
\qquad Q_{hu}=Q_uQ_h.
\tag{1.1}
$$

Every legal acquired prefix has probability $2^{-n}$ and normalized
conditional quantum state

$$
(BQ_h\otimes I_Z)\rho(BQ_h\otimes I_Z)^\dagger
\tag{1.2}
$$

for every density operator $\rho$ on $\mathbb C^3\otimes Z$ and every
untouched finite-dimensional reference $Z$. Each next legal label has
conditional probability $1/2$. These statements follow by multiplying
the restricted branch operators; they apply because all outputs remain
in $R$. Fairness on arbitrary five-dimensional inputs is not assumed.

The essential algebraic input is exactly [ENV, Theorem 8.2][ENV]:

$$
Q_h=\lambda Q_k\text{ for some }|\lambda|=1
\quad\Longleftrightarrow\quad h=k
\qquad(h,k\in\{0,1\}^*).
\tag{1.3}
$$

Its quantification includes the empty word and different lengths. The
supplier's proof keeps the phase on the common qutrit line and the
integral restriction to its two-dimensional complement. Equation (1.3)
is not inferred from injectivity of two-dimensional projective products,
from fixed-length counts, or from the Shannon-rate comparison. The
matrices themselves originate in [FIVE, Definition 17.2, Theorem 17.3
and (18.4)][FIVE]. None of these supplied statements is a new result here.

## 2. Complete autonomous control and the first-STOP task

**Definition 2.1 (Controller, cuts and execution contract).** An installed
controller has a finite set $\mathsf Q$ of complete classical values at the
following comparison cuts: a live cut after initialization or label
processing and before another acquisition; and a stopped cut after the
actual STOP mark and before quantum correction. It has a fixed initial
value $q_0$, a terminal subset $F\subseteq\mathsf Q$, and a homogeneous
total macro-update

$$
\delta:(\mathsf Q\setminus F)\times\{0,1\}\longrightarrow\mathsf Q.
\tag{2.1}
$$

Every changing classical field available at these cuts is included in
the value: phase, clock or count, program selection, table selection,
pointer, buffer, archive and every decoder-visible side carrier. There
is no external varying clock, later index, retained output tape readable
by the controller, independent seed, source-dependent advice or hidden
history carrier. Installation data and static tables are fixed before
the unknown input and future labels; their descriptions are separate
resources. Any clock affecting (2.1) must be part of its state. No
unbounded classical workspace is hidden in the routines: the complete
classical state set $\Gamma$ over all their phases is finite and includes
these cut values. Its cardinality is accounted for separately below.

Initialization finishes in finite execution and sets $q_0$ independently
of the input and future labels. At a live cut the sole next source action
is one acquisition of Definition 1.2, which finishes and delivers its
label. Processing that label finishes in finite execution. If its update
value is outside $F$, it reaches the next live cut. If the value is in
$F$, it executes a marked STOP, removes acquisition permission, and
reaches the stopped cut. If $q_0\in F$, initialization includes this
actual immediate STOP. The episode has no subsequent acquisition port.
Pending STOP is a distinct execution phase, not a completed STOP cut.

For each $a\in F$ there is a fixed installed channel
$\mathcal D_a:M_5\to M_5$. From the stopped cut the controller invokes
that channel on the retained actual $H$ system and returns in finite
execution. The channel may be arbitrary CPTP, including nonunitary.
Decoder-local randomness can be part of that channel, but neither its
selection nor acquisition stopping uses classical randomness. Pending
STOP, acquisition, correction and return microstates belong to the
all-phase account $\Gamma$ when they are controller states; they are
not all comparison cuts. No identification of $|\mathsf Q|$ with the
entire apparatus's resources is made.

Between acquisitions only classical processing and ideal retention of
$H$ are permitted. There is no intermediate quantum read or correction,
adaptive instrument, retained environment, reference read, quantum
summary in another carrier, or input-dependent quantum side information.
The finite classical state set is not an enumeration of unknown quantum
states: every terminal decoder still receives $H$. Exact correction
controls and their finite-call interface are mathematical permissions;
gate synthesis and physical elapsed times are additional questions.

**Definition 2.2 (Actually acquired prefix tree).** The set $\mathcal P$
and sampled map $q:\mathcal P\to\mathsf Q$ are generated by the installed
controller, not by a requirement that different words have different
states. Start with $\epsilon\in\mathcal P$ and $q(\epsilon)=q_0$. If
$h\in\mathcal P$ and $q(h)\notin F$, both children $h0,h1$ belong to
$\mathcal P$, with

$$
q(hj)=\delta(q(h),j).
\tag{2.2}
$$

If $q(h)\in F$, it has no children. Write

$$
\mathcal L=\{h\in\mathcal P:q(h)\in F\},\qquad
\mathcal I=\mathcal P\setminus\mathcal L,\qquad
\mathsf Q_r=q(\mathcal P).
\tag{2.3}
$$

Thus $\mathcal L$ consists exactly of first-stopped words. No acquired
prefix crosses an earlier STOP. Each $h\in\mathcal P$ is possible on
the actual instrument and has acquisition probability $2^{-|h|}$;
both children of every live node have positive conditional probability.
This uses the actual branch law (1.2), not a facility for forcing labels.

Let $T$ be the number of acquisitions before the first actual STOP,
with $T=\infty$ on nonstopping paths, and let $W_{\rm stop}\in\mathcal L$
be the stopped word when it exists. The countably many leaf cylinders
are disjoint, and

$$
\Pr(W_{\rm stop}=w)=2^{-|w|},\qquad
\Pr(T<\infty)=\sum_{w\in\mathcal L}2^{-|w|}.
\tag{2.4}
$$

An assertion about every label stream means that every succession of
delivered labels, as long as acquisition remains legal, reaches STOP.
It does not posit measurement outcomes after STOP or supply an observer
with a counterfactual outcome table.

**Definition 2.3 (Exact ensemble recovery).** Success requires
$\Pr(T<\infty)=1$, the finite STOP/correction/return execution of
Definition 2.1, and the channel identity

$$
\mathcal E=
\sum_{w\in\mathcal L}2^{-|w|}
\mathcal D_{q(w)}\circ\iota\circ\operatorname{Ad}_{Q_w}
=\iota:M_3\longrightarrow M_5.
\tag{2.5}
$$

Equality means equality on the complex operator algebra and hence after
tensoring with every untouched finite reference. Equivalently it is
exact restoration of every density $\rho$ in (1.2), averaged over all
stopped outcomes, with no postselection. It is recovery of the unknown
input qutrit, not acquisition of its description. The actual acquisitions
are the measured disturbance labels. The classical controller cannot
read the input to decide its stopping time.

## 3. Acquired-prefix separation and an all-stream bound

**Theorem 3.1 (Exact recovery forbids every acquired-prefix merge).** For
the instrument of Definition 1.2, every successful controller of
Definitions 2.1–2.3 has an injective map
$q:\mathcal P\to\mathsf Q$. This includes live prefixes, first-stopped
prefixes, the root and comparisons between different lengths.
Consequently $\mathcal P$ is a finite full binary rooted tree. If
$\ell=|\mathcal L|$ and $I=|\mathcal I|$, then

$$
|\mathsf Q_r|=|\mathcal P|=2\ell-1,\qquad I=\ell-1,
\tag{3.1}
$$

and every label stream actually reaches STOP with

$$
T\le I=\frac{|\mathsf Q_r|-1}{2}
\le\left\lfloor\frac{|\mathsf Q|-1}{2}\right\rfloor.
\tag{3.2}
$$

These are acquisition and sampled-state statements. They neither count
all $\Gamma$ microstates nor bound physical elapsed time. Since
$\mathsf Q\subseteq\Gamma$, (3.2) also implies the generally weaker
bound $T\le\lfloor(|\Gamma|-1)/2\rfloor$; sharpness of the sampled
count is not sharpness of the all-phase account.

Proof. First establish terminal rigidity without assuming a finite leaf
set. By (2.4) and almost-sure stopping, the countable leaf weights
$p_w=2^{-|w|}$ sum to one. Each normalized branch

$$
\mathcal E_w=\mathcal D_{q(w)}\circ\iota\circ
\operatorname{Ad}_{Q_w}:M_3\longrightarrow M_5
$$

is CPTP. For such a map use the unnormalized output-first Choi matrix

$$
J(\Lambda)=\sum_{i,j=0}^2
\Lambda(|i\rangle\langle j|)\otimes|i\rangle\langle j|.
$$

It is positive and has trace and trace norm three. Therefore
$\sum_w p_wJ(\mathcal E_w)$ converges absolutely in trace norm.
By (2.5) it equals
$J(\iota)=|B\rangle\!\rangle\langle\!\langle B|$, a rank-one
matrix of trace three. For every $y$ perpendicular to
$|B\rangle\!\rangle$,

$$
0=\sum_{w\in\mathcal L}p_w
\langle y,J(\mathcal E_w)y\rangle.
\tag{3.3}
$$

All terms are nonnegative and all $p_w$ are positive. Each Choi
matrix annihilates the entire perpendicular complement: a positive
matrix with zero quadratic form on $y$ annihilates $y$, as follows
from its positive square root. Its support is thus the one line of
$J(\iota)$. Trace three fixes the scalar, proving

$$
\mathcal D_{q(w)}\circ\iota\circ\operatorname{Ad}_{Q_w}
=\iota\qquad(w\in\mathcal L).
\tag{3.4}
$$

This is the positive-Choi principle used by [ENV, Theorem 3.3][ENV],
with its countable convergence justified here for the initially
unbounded first-STOP task. No finite-index recovery theorem is being
applied to an unproved finite leaf set.

Suppose $w,v\in\mathcal L$ have $q(w)=q(v)=a$. Put
$\mathcal A=\mathcal D_a\circ\iota:M_3\to M_5$. Since $Q_w$ and
$Q_v$ are unitary, (3.4), precomposed with their inverse conjugations,
gives

$$
\mathcal A=\iota\circ\operatorname{Ad}_{Q_w^\dagger}
           =\iota\circ\operatorname{Ad}_{Q_v^\dagger}.
\tag{3.5}
$$

The embedding is injective, so the two conjugations on $M_3$ agree.
Their relative unitary commutes with every matrix, hence is a scalar
of modulus one; this follows directly by commuting with matrix units.
Equation (1.3) now yields $w=v$. Terminal states are therefore injective,
even for arbitrary full-$H$ CPTP decoders. The available quantum output
has not been replaced by a classical measure–prepare channel.

Now let $h,k\in\mathcal I$ have $q(h)=q(k)$. The event of acquiring
$h$ has probability $2^{-|h|}>0$. Conditional on that event, stopping
is still almost sure; otherwise global nontermination would have
positive probability. Hence some finite nonempty first-stopping suffix
$s$ exists from $h$. All its proper prefixes are live, and $hs$ is a
leaf. Homogeneity, state completeness and (2.2) imply, step by step,
that the very same suffix is legal from $k$, remains live for exactly
the same proper prefixes, and reaches a leaf $ks$ with

$$
q(hs)=q(ks).
$$

Both suffix occurrences have conditional probability $2^{-|s|}>0$
under the actual measured law. They are possible continuations in two
comparisons, not commands selecting measurement results and not a
requirement to execute both histories on one specimen. Terminal
injectivity gives $hs=ks$, and right cancellation of finite words
gives $h=k$. A live and a stopped prefix cannot share a state because
membership in $F$ differs. This proves injectivity on all of $\mathcal P$.

The state set is finite, so $\mathcal P$ is finite. Every live node has
exactly two children and every stopped node has none. Counting edges
in this finite rooted tree gives

$$
2I=|\mathcal P|-1=I+\ell-1.
$$

This proves (3.1). A path with $t$ acquisitions before its first leaf
visits $t$ different live nodes, so $t\le I$. An indefinitely live
stream would give infinitely many prefixes in the finite set
$\mathcal P$, which is impossible. Finally the execution contract
makes every acquisition, update, selected STOP, correction and return
finish: reaching a leaf is an actual executed STOP, not merely a
semantic plateau or a pending request. This proves (3.2). $\square$

## 4. Exact recovery condition and its acquired realization

**Theorem 4.1 (Finite-tree recovery correspondence).** Fix the actual
instrument and an installed finite autonomous transition controller
satisfying Definition 2.1's execution contract, with its terminal
channels left to be chosen. Exact almost-sure recovery is possible if
and only if $q$ is injective on the induced $\mathcal P$. Whenever it
is possible, stopping occurs on every label stream. If the terminal
channels are already fixed, success is equivalent to that injectivity
together with (3.4) at every reached leaf.

Every specified finite full binary rooted tree with edges labelled
$0,1$ has a realization attaining precisely $|\mathcal P|$ reachable
sampled state values. Thus $2\ell-1$ is the exact sampled-state
minimum for a prescribed stopping tree with $\ell$ leaves under this
task and these permissions.

Proof. Necessity is Theorem 3.1, including (3.4). Conversely, injectivity
into finite $\mathsf Q$ makes $\mathcal P$ a finite full binary tree.
The edge count and all-stream stopping argument in Theorem 3.1 use
only these facts, and therefore apply before any decoder is chosen.
Each reached terminal state $a$ corresponds to one unique leaf $w$.
Install the existing block inverse of [ENV, (3.3) and (16.2)][ENV]:

$$
C_w=BQ_w^\dagger B^\dagger+(I_5-P_R),\qquad
\mathcal D_{q(w)}=\operatorname{Ad}_{C_w}.
\tag{4.1}
$$

On the orthogonal summands $R$ and $R^\perp$, $C_w$ is respectively
the transported qutrit inverse and the identity. Hence
$C_w^\dagger C_w=C_wC_w^\dagger=I_5$ and

$$
C_wBQ_w=B.
\tag{4.2}
$$

Thus (3.4) holds, also after tensoring with every reference. All
streams stop, so the leaf probabilities sum to one and (2.5) follows.
Unreachable terminal channels can be arbitrary. For fixed channels,
(3.4) itself instead supplies this sufficiency; injectivity alone
cannot certify an arbitrary installed decoder.

For the prescribed-tree realization, retain the current node as the
sampled classical state, starting at its root. At a live node acquire
one actual label and follow its correspondingly labelled edge. At a
leaf execute STOP and invoke its (4.1) control. This is one homogeneous
node transition table, with no time-indexed table selection. Every
node is reached with probability $2^{-|h|}>0$ for its root-to-node
word $h$, so exactly $|\mathcal P|$ sampled values are used.
The node is accumulated from the labels actually delivered; neither
the word nor its terminal node is supplied as advice. No unknown seed
or full response oracle is installed. A finite phase controller can
sequence the permitted acquisition, STOP and correction calls; its
additional phase states are separate from this attained cut count.
Theorem 3.1 proves the matching lower bound for any successful
realization of this same prescribed stopping tree. $\square$

**Corollary 4.2 (Retained memory recovers acquired chronology and legal
updates).** On the actual domain $\mathcal P$ of a successful controller,
the acquired word and the sampled complete classical state mutually
determine one another. Their correspondence preserves the acquisition
count, acquisition permission, STOP status and the labelled next-step
updates. At a stopped cut it determines a valid correction choice
when the controls of Theorem 4.1 are installed.

Proof. The inverse $r:\mathsf Q_r\to\mathcal P$ exists by
Theorem 3.1, with $r(q(h))=h$. The forward map is obtained from $q_0$
by (2.2). For live $h$,

$$
r(\delta(q(h),j))=hj,
\qquad |hj|=|h|+1,
\qquad q(h)\in F\Longleftrightarrow h\in\mathcal L.
\tag{4.3}
$$

These identities prove both directions and their update compatibility
on the actual image; no inverse is asserted on unreachable states.
The finite table $r$ can be installed or its unique words enumerated
from the installed finite transition tree. For an arbitrary successful
controller this is informational determination, not an already
installed chronology-output port. An executable readout can use a
separately installed finite table to emit $r(a)$ on input $a$;
its description, scratch, lookup work and output buffer are additional
resources. Emitting a word of length $|h|$ costs that many output
symbols and does not acquire any new disturbance labels. The node
realization in Theorem 4.1 establishes actual acquisition without
needing this word enumeration during the run. At a leaf, (4.1)–(4.2) give actual
continued use of the retained value to select the restoring channel.
This is a proved separation requirement, not a definition that hands
every controller an unrestricted copy of its history. $\square$

## 5. Exposure, terminal information and resource accounts

**Corollary 5.1 (A required exposure and the separate clocked count).**
Suppose a successful controller must acquire at least $N\ge0$ labels
on every run. Then

$$
\ell\ge2^N,\qquad |\mathsf Q_r|\ge2^{N+1}-1.
\tag{5.1}
$$

Stopping exactly at depth $N$ attains both bounds in the sampled
account. Its maximum acquired depth also attains (3.2) when $N=0$
or $N=1$; a chain of $I$ live nodes with one leaf child at each
nonfinal live node and two leaf children at the final one attains
the depth bound $T\le I$ for every $I\ge1$.

Proof. Every node of depth less than $N$ is live. Fairness therefore
makes all $2^k$ words of each depth $0\le k\le N$ occur. Their
distinct states give $|\mathsf Q_r|\ge\sum_{k=0}^N2^k$.
Each depth-$N$ node has a leaf descendant in the finite tree, and
descendants of different such nodes are disjoint, giving
$\ell\ge2^N$. The complete depth-$N$ tree attains both by
Theorem 4.1. The stated chain has $I$ live nodes and a deepest
leaf at depth $I$, proving depth sharpness. $\square$

**Convention 5.1a (The separately clocked supplier).** The
fixed-known-horizon statistic in [ENV, Theorems 4.1, 9.2–9.3 and
16.1][ENV] still has its exact $2^N$ alphabet and $N$-bit optimum
at this angle, with a separately supplied deterministic clock and
time-dependent tables. Its register values may be reused at different
clock values. Equation (5.1) counts the joint complete sampled
autonomous values across all depths, including whatever internal
information selects a time table or executes STOP. It does not
increase that supplier's register minimum or count the Cartesian
product of all possible clock/register values: only jointly reachable
complete values are counted.

**Corollary 5.2 (Information at the stopped cut).** For a prescribed
finite full binary stopping tree, the minimum exact deterministic
terminal alphabet before correction is $\ell$, requiring
$\lceil\log_2\ell\rceil$ fixed binary bits. For any successful
controller in this model,

$$
H(q(W_{\rm stop}))=H(W_{\rm stop})
=\sum_{w\in\mathcal L}2^{-|w|}|w|=\mathbb E T,
\tag{5.2}
$$

where entropy is in bits. The sampled alphabet over live and stopped
cuts has $2\ell-1$ values and can be encoded in
$\lceil\log_2(2\ell-1)\rceil$ fixed bits at those cuts.

Proof. Terminal injectivity requires $\ell$ distinct values and the
node construction attains them. The elementary fixed-field cardinality
bound gives the displayed bit counts. Terminal injectivity also makes
$q(W_{\rm stop})$ a bijective relabelling of $W_{\rm stop}$.
Its probabilities are $2^{-|w|}$ by (2.4), giving (5.2) directly
from the definition of entropy. The state count is (3.1). These are
the usual prefix-tree and entropy identities applied after the new
separation result; they are not a new coding theorem or a statement
that entropy equals total storage or physical work. $\square$

**Convention 5.3 (Same-run costs and the scope of sharpness).** In the
node realization a leaf $w$ uses $|w|$ fresh environment preparations,
$|w|$ interactions and measurements, $|w|$ actual label deliveries
and $|w|$ completed transition macros. There is then one executed
STOP, one terminal correction invocation and a finite return, preceded
by finite initialization. Zero acquisitions is allowed at a terminal
root. The exact inverse invocation may contain many elementary
operations; one invocation is not one primitive gate.

A transition table for a tree with $I$ live nodes has $2I$ labelled
successor entries. A leaf table has $\ell$ inverse-control entries,
each specifiable by the finite product $Q_w$ and its block extension.
Descriptions, address widths, lookup work, scratch, phase control,
initialization and all $\Gamma$ states remain additional costs.
The actual retained $H$, environment apparatus, calibration, exact
control precision, inverse synthesis and invocation time are also
separate. Theorems 3.1 and 4.1 optimize only the declared sampled
alphabet for a prescribed tree, not these resources or their sum.
They give no uniform physical time bound without separate duration
bounds for the permitted operations.

The state or its leaf identifier must remain available through its
declared correction use. It can be erased after that use if no later
recall task is required. A requirement to remember the history after
return would be another task. With no positive exposure requirement,
immediate STOP and the identity correction solve this task with one
sampled value, so no nontrivial universal stopping-cost optimum is
claimed. A finite program description by itself would not establish
finite complete memory; finiteness here is an explicit controller
premise.

## 6. Source-specific failures of broader inferences

**Proposition 6.1 (Almost-sure first-1 stopping does not suffice here).**
For the fixed $\pi/6$ instrument, the controller with one live value
$a$, one terminal value $b$, initial $a$, and transitions
$\delta(a,0)=a$, $\delta(a,1)=b$ stops almost surely but admits no
single exact terminal decoder satisfying (2.5).

Proof. The stopped words are $0^k1$ for $k\ge0$ with probabilities
$2^{-(k+1)}$, summing to one. Words $1$ and $01$ reach the same
terminal value, contrary to the terminal rigidity proved in
Theorem 3.1. There is also a direct current-state obstruction within
the allowed input domain. In logical qutrit coordinates let

$$
\sigma=|0\rangle\langle0|,\qquad
|\psi\rangle=V_0^\dagger|0\rangle
=\frac{\sqrt3}{2}|0\rangle-\frac{i}{2}|1\rangle.
\tag{6.1}
$$

The empty-prefix run with original input $\sigma$, and the acquired
prefix $0$ run with original input $|\psi\rangle\langle\psi|$,
have identical current quantum state $\iota(\sigma)$ and the same
live classical value $a$. The next actual label $1$, of probability
$1/2$ in each comparison, gives identical terminal quantum and
classical inputs. Required restored originals differ. A single
channel cannot give these two different answers on that same input.
Equation (3.4) rules out compensation by other positive-probability
stopped words in the ensemble requirement. This is an allowed-input
mathematical witness, not an observed experimental run. $\square$

**Proposition 6.2 (The all-stream implication uses the actual angle).**
At the different measured instrument $\theta=0$ of [ENV, Definition
2.1][ENV], a deterministic controller with four sampled classical
values exactly corrects
almost surely at the first $1$, while never stopping on the all-zero
stream. Thus almost-sure exact correction by finite autonomous
control does not imply all-stream stopping for general instruments.

Proof. Now the restricted unitaries are $U_0,U_1$, still with fair
actual labels, and $U_0^2=I_3$. Use live states $a_0,a_1$ and
terminal states $b_0,b_1$, starting at $a_0$, with

$$
\delta(a_r,0)=a_{1-r},\qquad
\delta(a_r,1)=b_r\qquad(r\in\{0,1\}).
$$

The retained parity after $k$ zeros is $r=k\bmod2$. The stopped
product is $U_1U_0^k=U_1U_0^r$, so at $b_r$ install the block
inverse for that product. Each stopped branch recovers every
qutrit-reference input; its geometric weights sum to one.
All-zero paths remain live forever. This instrument lacks (1.3),
and no conclusion about it has been inferred by changing the
hypotheses of Theorem 3.1. $\square$

**Proposition 6.3 (Count, STOP flag and current quantum state are
insufficient substitutes for chronology).** In this task the acquired
count and STOP flag alone need not recover acquired chronology.
The current retained quantum state alone also need not recover it
over the allowed unknown-input domain.

Proof. In the depth-one stopping tree, the two leaves $0,1$ both
have acquisition count one and are stopped, but their complete
terminal states must differ by Theorem 3.1. For current quantum
state, the two actual input/prefix realizations in (6.1) have the
same state on $H$ and different acquired words. Those same prefixes
and inputs are legal also in the successful depth-one tree, where
their classical node values differ. These facts do not
prevent memory from determining count and status in (4.3). They
exclude reversing those projections without additional retained
information. $\square$

## 7. Supplier correspondence and remaining domains

**Convention 7.1 (Ownership of the inference).** All repository citations
below refer to immutable revision
`19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b`. The new inference is
`repo-derived`: countably many actual first-stopped branches obey
terminal rigidity; a hypothesized live-state merge supplies its own
legal first-stopping common suffix; the full-qutrit cross-length
supplier then forces injectivity on the acquired tree. Finiteness
turns that separation into an all-stream acquisition bound, with the
permitted block inverse giving the matching recovery condition.
This is the content of Theorems 3.1 and 4.1 and their scoped
consequences. It is not a literature-priority claim.

| Supplier | Correspondence and limit |
| --- | --- |
| [ENV, Definitions 1.3–2.1, Theorems 2.2, 3.3, 4.1, 8.2, 9.2–9.3 and 16.1][ENV] | Owns the actual source, qutrit/reference domain, fair measured acquisitions, exact-summary rigidity, cross-length injectivity and inverse permission. Its register optima and prefix tables have fixed known horizons and a separately priced deterministic clock. The present unbounded first-STOP necessity proves countable convergence before establishing finiteness. |
| [FIVE, Definition 17.2, Theorem 17.3 and (18.4)][FIVE] | Owns the five-dimensional operators and invariant-image permutations; no arbitrary random-unitary family has been substituted. |
| [Approximate online recovery memory, Definitions 2.3–2.4, Theorem 4.3, Theorem 9.1 and Convention 11.3][APPROX] | Allows stochastic time/horizon-dependent kernels and free independent seeds; its positive-error results concern a known horizon and a per-stage peak width. Its exact endpoint credits ENV. Neither its approximate formulas nor their limits assert branchwise exactness or autonomous cross-length state separation. |
| [Environment-record Shannon rate, Lemma 2.2, Theorem 8.1 and Conventions 8.2–9.1][SHANNON] | Owns the fixed-length class-law and complete-view entropy application. Its auxiliary mixture may merge ordinary two-dimensional products across lengths; that is not a full-qutrit projective equality. Its rate arguments do not supply actual STOP, and are not premises of Theorem 3.1. |
| [Common measurement compatibility, Theorems 9.2 and 10.2, Definition 10.3][COMPAT] | Its finite classical record retains an actual quantum decoder input. A measure–prepare bottleneck cannot be inferred. This volume preserves that permission and supplies no protocol-sensitive fidelity bridge. |
| [Process geometry, Definition 1.1, Theorems 3.2–3.4 and 19.7–19.8][PG] | Supplies the complete-response, legality, successor and selector-input discipline. A finite-stage response induction or a finite work carrier with an external history parameter does not by itself prove termination or finite complete classical control. |
| [DFAOStateLowerBound.lean][DFAO] and its [owning Scribe][DFAO-B] | Supplies deterministic common-suffix state separation when legal distinguishing continuations are given. Here a live collision and conditional almost-sure stopping produce the needed legal suffix; the quantum terminal rigidity and first-STOP domain are additional proof obligations discharged in Theorem 3.1. |
| [DistinguishingFamilyCardinalityBound.lean][RIGID] | Its private `continuation_constant` and output-alphabet bound require a unique-completion premise. General full stopping trees have many leaf completions, so that stronger premise is not imported. |
| [FiniteKrausReversibility.lean][KRAUS] and its [owning Scribe][KRAUS-B] | Supplies finite-index scalar-product recovery, including the private rotated-error helpers. Finite-index hypotheses do not settle an initially countable leaf sum. The only inverse needed here is ENV's supplied leaf block inverse. |
| [TypedFiniteViewKernel.lean][VIEW] and [FinitePrefixAntichainBudget.lean][PREFIX] | Complete response kernels and finite prefix-antichain accounting are existing suppliers. Semantic sufficiency is not actual label acquisition or an executed STOP; finite antichain accounting is not the countable normalization in (2.4). |
| [Pinned mathlib Myhill–Nerode][MN], `leftQuotient`, `leftQuotient_append`, `leftQuotient_accepts_apply` | `literature-attested`: deterministic suffix/state framework. It supplies neither the measured-source recovery condition nor the autonomous bound here. |
| Gregoratti–Werner, [Quantum Lost and Found][GW1], Proposition 2 and (7) | `literature-attested`: fine-outcome correction. Here $t_j=V_j/\sqrt2$ on the logical qutrit, with $t_j^\dagger t_j=I_3/2$; the embedding is rectangular. It is not an arbitrary-full-$H$ input inverse or a coarse-record stopping theorem. |
| Gregoratti–Werner, [On quantum error-correction by classical feedback in discrete time][GW2], Proposition 2, (10)–(12) | `literature-attested`: finite-step feedback correction. Earlier corrections can be identities and the final correction can undo the accumulated unitary. Its finite multi-step interface does not count complete autonomous first-STOP states. |
| Knill–Laflamme, [A Theory of Quantum Error-Correcting Codes][KL], Theorem 3.2, (19)–(20) | `literature-attested`: complex scalar cross-term criterion on the whole logical qutrit code. No new general correction criterion is claimed here. |

**Convention 7.2 (Distinct models and unresolved bridges).** The
ten-dimensional whole-input record dilation of [Minimal record
dilations, Definitions 1.1–1.4 and Theorem 2.2][DIL] has different
edges and input space. The original positive/double-wall controls,
full stopped instruments and future-menu coding of [Original-control
quantum carrier minimum, Convention 1.1 and Definition 1.2][ORIGINAL]
are different source permissions. Neither is silently identified
with the repeated $A_0,A_1$ acquisitions here.

The variable charged registers and NEXT requests of [Autonomous
predictive memory, Definitions 1.2–1.3][PREDICTIVE], the native tree
ports and callable tapes of [Native clocked recovery and order,
Convention 1.1 and Definitions 2.1–2.2][NATIVE], and the paid
Read/Stop residual-law task of [Effective acquisition horizon,
Scope 1.1 and Definitions 1.3–1.4][HORIZON] retain their own sources and objectives.
The present finite-state theorem changes none of their hypotheses,
initialization contracts or settlements. In particular all prior
fixed-$G_{gc}$, original-$Q$, parked-consumer and unchanged-initialization
obligations remain in their original scopes.

The precise gain toward relational observation is (4.3), derived
from one jointly realized measured process: exact recovery makes
retained complete memory distinguish actual acquired order, and
the resulting finite tree determines a legal executed recovery
boundary. Acquired time here means number and order of acquisitions;
it is not calibrated elapsed time. Boundary here means acquisition
permission and its STOP transition, independently of the memory
alphabet. Count and boundary flag do not invert memory, by
Proposition 6.3. No independently meaningful spatial view has been
constructed, and no four-view equivalence, universal alpha/beta
generation reduction or physical impossibility is concluded.

Randomized stopping, external seeds or clocks, unbounded memories,
other initialization families, intermediate quantum feedback,
alternative instruments and positive approximate error require
different analyses. In particular exact positive-Choi rigidity
does not turn an average approximate error into an exact guarantee
on rare stopped branches. No approximate autonomous bound or
protocol-sensitive fidelity theorem is asserted. All recovery here
is restricted to $R$ and untouched references; the full-$H$ Kraus
operators are not scaled full-$H$ unitaries. The sustained general
space/time/boundary/memory problem is not settled by this scoped
recovery correspondence.

[ENV]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_MEMORY.md
[FIVE]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/AURIC_FIB_FIVE_WINDOW_QUANTUM_MEMORY.md
[APPROX]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/AURIC_FIB_APPROXIMATE_ONLINE_RECOVERY_MEMORY.md
[SHANNON]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/AURIC_FIB_ENVIRONMENT_RECORD_SHANNON_RATE.md
[COMPAT]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/AURIC_FIB_COMMON_MEASUREMENT_COMPATIBILITY.md
[PG]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[DFAO]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/D5/S0/Automata/DFAOStateLowerBound.lean
[DFAO-B]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/Blueprint/D5/S0/Automata/DFAOStateLowerBound.scribe.cs
[RIGID]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/D5/S0/Automata/DistinguishingFamilyCardinalityBound.lean
[KRAUS]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/D5/S3/Quantum/Recovery/FiniteKrausReversibility.lean
[KRAUS-B]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/Blueprint/D5/S3/Quantum/Recovery/FiniteKrausReversibility.scribe.cs
[VIEW]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean
[PREFIX]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/D5/S0/History/FinitePrefixAntichainBudget.lean
[MN]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/MyhillNerode.lean
[GW1]: https://arxiv.org/html/quant-ph/0209025v1
[GW2]: https://arxiv.org/html/quant-ph/0403092v1
[KL]: https://arxiv.org/html/quant-ph/9604034v1
[DIL]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_MINIMAL_RECORD_DILATIONS.md
[ORIGINAL]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_QUANTUM_CARRIER_MINIMUM.md
[PREDICTIVE]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_AUTONOMOUS_PREDICTIVE_MEMORY.md
[NATIVE]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md
[HORIZON]: https://github.com/the-omega-institute/trureturing/blob/19009f6ca8152c87ab937dcd61f6f97d5fc1cf0b/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_ACQUISITION_HORIZON.md

## 追加锚（本行以下为增补区）
