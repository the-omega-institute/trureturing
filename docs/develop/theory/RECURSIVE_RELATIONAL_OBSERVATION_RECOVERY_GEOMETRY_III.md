# Recursive Relational Observation: Recovery Geometry III

> This reference-input volume uses the `generic-v1` Markdown convention.
> Locators depend on its own bytes. Published text is retained unchanged;
> corrections and further results belong after the final append anchor.
> The ordinary mathematical proofs here are not Lean kernel certification.
> Lean declarations and their verified dependencies remain the mathematical
> truth source of the repository.

## 112. An unknown field on the installed calibrated native source

**Definition 112.1 (terms, material and authentic context).** Write AA for
[Atomic Generation Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md),
AAII for its
[second volume](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION_II.md),
and RGII for
[Recovery Geometry II](RECURSIVE_RELATIONAL_OBSERVATION_RECOVERY_GEOMETRY_II.md).
Use AA Definitions 17.1 and 17.3 literally. A finite logical term is

$$
t::=\alpha\mid\beta\mid\langle t,t\rangle.
$$

Its logical addresses are words in $\{L,R\}^*$, with root $\varepsilon$.
The reachable domain $\mathcal D$ consists of terms having no logical
alpha leaf at an address ending in $L$. The material $C(t)$ has one
vertex for alpha, a root with one left terminal marker for beta, and a
root with two ordered child materials for a branch. Write $V_t$ for
its material addresses and $m(t)=|V_t|$. A beta marker is a real cell,
but not a logical child through which an addressed operation can descend.
Material arity parses this syntax; the unary case consumes its marker.

An authentic context $\mathfrak c$ consists of the same original root
binding, its original ordered address dispatcher, exclusive current native
rights, the installed law below, the fixed finite controller and framing
programs, and actual finite material and delivery backing. Equality of
states in this context retains those binding and authority relations and
the original orientation. It disregards unobservable fresh-name spellings.
It does not equate different roots or grants. No name, duration, quota,
meter, allocation index or hidden archive is an additional observation.
Any implementation exposing such information has a different interface.

**Definition 112.2 (persistent calibrated law).** Every actual material
cell at address $p$ has the two installed rational records of RGII
Definition 96.1:

$$
\begin{aligned}
(a_\varepsilon,\ell_\varepsilon)&=(0,1),\\
(a_{pL},\ell_{pL})&=(a_p+\ell_p/8,\ell_p/8),\\
(a_{pR},\ell_{pR})&=(a_p+3\ell_p/4,\ell_p/8).
\end{aligned}
\tag{112.1}
$$

For $u\in\mathcal D$, let $e_u=e_\varepsilon\in\mathbb Q^{V_u}$ and
let $T_u$ be the symmetric rational matrix

$$
(T_u)_{pp}=a_p+\ell_p/2,\qquad
(T_u)_{p,\operatorname{parent}(p)}
=(T_u)_{\operatorname{parent}(p),p}=\ell_p/100
\quad(p\ne\varepsilon),
\tag{112.2}
$$

with all other entries zero. This is an actual local installation, not
a coefficient table supplied to a receiver. Coefficients are determined
by the original material addresses, including marker addresses.

The native edit $P_p$ promotes alpha to beta, retaining $p$ and adding
$pL$. The edit $S_p$ splits beta into $\langle\beta,\alpha\rangle$,
retaining $p$ and its old marker $pL$, making that marker the left beta
root, and adding $pLL,pR$. Every old field, edge and calibration record
persists. Every fresh field is zero and its records are computed from
its actual parent by (112.1). In particular an old marker value is not
cleared when the marker becomes a logical root. The old matrix is the
principal submatrix on the retained material; a new neighbor does not
retroactively change an old diagonal or edge.

**Assumption 112.3 (arbitrary entrance and completed-run domain).** At a
settled attachment cut the actual source is an unknown $t\in\mathcal D$
with an arbitrary unknown field $x\in\mathbb Q^{V_t}$. Neither the term,
size, height, roster, coefficients, field, old controls, old replies nor
an allocation order is supplied to the receiver. The receiver has just
$\mathfrak c$ and source-independent finite code. This replaces RGII
Definition 96.1's zero-field, pure-growth entrance; it leaves its law and
complete menu unchanged. Section 114 will impose a separate actual
preparation promise only when a historical inverse is wanted.

Calls and edits are serialized. There is no autonomous Tick, concurrent
writer, reset, clone, deletion, rerooting, terminal field port or interior
field port. Hold permits finite local work without source evolution.
Every finite execution in a theorem has sufficient actually owned work,
fresh cells, grants, input/output buffers and completion backing for that
execution. Complete replies, local commits and returns are delivered.
Crashes, revocation, exhausted backing and wrong-phase calls are outside
this completed-run promise; none is decoded as a leaf refusal. This is
sourcewise finite backing, not one fixed finite reserve for all possible
growth or operand lengths. Providers, initialization, authority, retained
capacity and clearing remain paid on the same actual run.

**Definition 112.4 (complete current interface).** At a Ready cut $(u,w)$
the semantic table is the following. Tick returns the updated root value.

| Complete request | Actual successor | Complete semantic content |
| --- | --- | --- |
| Add$(q)$, $q\in\mathbb Q$ | $(u,w+qe_u)$ | fixed ACK |
| Read | $(u,w)$ | literal $e_u^{\mathsf T}w$ |
| Tick | $(u,T_uw)$ | literal $e_u^{\mathsf T}T_uw$ |
| Hold | $(u,w)$, held for local work | fixed ACK |
| enabled $P_p$ | promotion with zero lift | Growth$(P,p)$ |
| enabled $S_p$ | split with zero lift | Growth$(S,p)$ |
| absent logical target | identity | Refusal(absent) |
| branch logical target | identity | Refusal(branch) |
| wrong leaf type for $P/S$ | identity | Refusal(wrong type) |
| complete malformed or unused frame | identity | BadFrame |

At alpha only $P$ is enabled; at beta only $S$ is enabled. Navigation
descends only through branches. There is no attached Tick on growth and
no constructor Read, Tag, Next, FetchGrowth, HasPromotion, HasSplit,
terminal ordinal query or old-journal port.

Fix the framing of RGII Assumption 96.2, extending AAII Definition 53.3's
native channel. A request has a fixed kind, its self-delimiting payload
and input End. A response contains its entire semantic content and output
End. The receiver consumes it, commits the matching local state, supplies
the fixed LocalACK and completes Return and finite scratch cleanup before
the next Ready cut. LocalACK is distinct from semantic ACK. A proper
incomplete prefix retains its actual bytes and parser position and has
no completed reply or source step. Complete invalid encodings, including
noncanonical rational encodings, give BadFrame, not a native refusal.
Later request input is admitted only after the current cycle returns.

Receive, Navigate, Guard, reservation, editing, sealed reply construction,
printing, local commit and Return are real phases. Their pending bytes,
cursor, reserved references, busy latch, reply buffer and grants remain
material while live. Missing rights or backing disables a call; it does
not synthesize BadFrame or a leaf tag. The outer fixed tokens carry no
additional source data. All quantities and equivalences below concern
this full interface with this context, rather than arbitrary private busy
states or an unmentioned primitive trace.

**Proposition 112.5 (the exact linear suppliers used).** For every
$u\in\mathcal D$, with $n=|V_u|$, the matrices

$$
\mathcal K_u=[e_u,T_ue_u,\ldots,T_u^{n-1}e_u],\qquad
\mathcal O_u=
\begin{bmatrix}
e_u^{\mathsf T}\\ e_u^{\mathsf T}T_u\\ \vdots\\
e_u^{\mathsf T}T_u^{n-1}
\end{bmatrix}
=\mathcal K_u^{\mathsf T}
\tag{112.3}
$$

are invertible over $\mathbb Q$, and $T_u$ is invertible over
$\mathbb Q$. These assertions depend on the installed calibration,
not on the entrance field.

Proof. Apply RGII Lemma 97.1 and Theorem 97.2 to this exact material,
root, diagonals and edge weights. Their globally disjoint address windows
are
$[a_p+19\ell_p/40,a_p+21\ell_p/40]\subset(0,1)$.
They give simple spectrum, nonzero root overlap for every eigenvector,
and the invertible rational Krylov matrix in (112.3). Symmetry gives the
displayed transpose. All eigenvalues lie in $(0,1)$, so the rational
determinant of $T_u$ is nonzero as well. No new cyclicity, moment or
controllability theorem is asserted here. The exact hypotheses hold for
both an entry $t$ and any reachable enlarged term, independently of all
field values. $\square$

## 113. Joint acquisition on the same specimen

**Definition 113.1 (the existing split sweep with a field present).** Use
AAII Definition 69.1's actual preorder sweep. At a scheduled logical
address $p$ issue one $S_p$ frame and finish its whole response and
return. Refusal(wrong type) records alpha and finishes that visit.
Growth$(S,p)$ records beta and finishes that visit, without scheduling
either newborn child. Refusal(branch) records a branch and schedules its
old left subtree followed by its old right subtree. An absent refusal
is outside the promised executions, not an alternative leaf code.
The finite controller starts at the root and stops when the root visit
and every pending-right continuation have finished. It has no supplied
fuel, height or size bound.

Recall the exact existing syntax map and partial inverse from AAII
Definition 68.2 and Lemma 68.3:

$$
J(\alpha)=\alpha,\qquad J(\beta)=\langle\beta,\alpha\rangle,
\qquad J(\langle r,s\rangle)=\langle J(r),J(s)\rangle.
\tag{113.1}
$$

Write $\kappa$ for their partial decoder $K$, to distinguish it from
$\mathcal K$. It returns alpha at alpha, beta at the literal sentinel
$\langle\beta,\alpha\rangle$, and otherwise recursively decodes both
children of a pair. Bare beta fails. Its domain is the grammar
$\mathcal R::=\alpha\mid\langle\beta,\alpha\rangle
\mid\langle\mathcal R,\mathcal R\rangle$.
The sentinel rule precedes the recursive pair rule. The already proved
facts are $\kappa J=\mathrm{id}$, $J\kappa=\mathrm{id}$ on
$\mathcal R$, and $J[\mathcal D]=\mathcal R\cap\mathcal D$.
They are reused as syntax facts, not counted as additional results.

Let $u=J(t)$. Original addresses give a canonical actual inclusion
$\iota_t:\mathbb Q^{V_t}\to\mathbb Q^{V_u}$, retaining old coordinates
and setting all fresh coordinates to zero. Restriction to $V_t$ is a
left inverse of this inclusion.

**Lemma 113.2 (simultaneous acquisition and nonzero-field lift).** For
every entrance $(t,x)$ of Assumption 112.3, the actual sweep terminates,
earns the exact entry constructor word $t$, and ends at

$$
(u,z)=(J(t),\iota_t x)
\tag{113.2}
$$

on the same genuine root and current rights. It executes no field
command. Thus it preserves every old coordinate, even an old beta
marker value, rather than replacing the entry field by zero.

Proof. AAII Theorem 69.2 applies to the logical guards and persistent
native templates unchanged by the extra field. Its induction visits
exactly the entry logical positions: earlier edits lie in finished leaf
cones, disjoint from every pending old subtree, and newborn children
are never scheduled. Neither a guard nor a scheduling choice depends on
the field. It therefore earns the same $t$ and actual $J(t)$, with finite
termination and the same literal tagged replies.

For the additional field assertion, induct on those actual completed
transactions. A refusal changes no coordinate. A successful split
retains every existing coordinate and appends zero at exactly its two
fresh addresses. The coordinates in disjoint previously finished cones
persist too. No Tick or Add occurs in the sweep, so there is no other
field change. Composing these inclusions retains precisely $V_t$ and
puts zero at precisely $V_u\setminus V_t$. The calibration persists by
Definition 112.2. This proves (113.2) on the actual execution, not merely
on its recorded syntax. $\square$

**Definition 113.3 (earned root window).** After the sweep, compute
$u=J(t)$ and $N=|V_u|$ from the earned word and actual address inclusion.
Actually execute

$$
\mathrm{Hold};\ \mathrm{Read};\
\underbrace{\mathrm{Tick};\cdots;\mathrm{Tick}}_{N-1\text{ returning Ticks}};
\ \mathrm{Hold}.
\tag{113.3}
$$

Consume every scalar and every completion token. Let
$Y=(Y_0,\ldots,Y_{N-1})^{\mathsf T}$ be the literal scalar block.
While held, construct the rational coefficients of $T_u$ from the earned
addresses and the installed law. Solve $\mathcal O_u z=Y$ and restrict
the answer to $V_t$. The receiver has earned the stopping bound $N$;
it did not receive that bound at attachment.

**Theorem 113.4 (unknown geometry and arbitrary entry field).** For
every $t\in\mathcal D$, every $x\in\mathbb Q^{V_t}$ and every authentic
completed-run installation, Definitions 113.1 and 113.3 terminate and
recover exactly $t$ and $x$. With $H=N-1$, their literal block and actual
held return are

$$
Y=\mathcal O_u\iota_t x,\qquad
v=T_u^H\iota_t x,\qquad u=J(t).
\tag{113.4}
$$

They return an earned current predictor for $(u,v)$, the actual retained
callable root and current authority. They use neither Reset nor hidden
geometry or field advice. Recovery of the old field is numerical;
the actual returned field is $v$.

Proof. Lemma 113.2 supplies the actual geometry and the actual initial
field of the window. Read returns its root coordinate. After $r$
returning Ticks, induction using (112.2) gives field $T_u^r\iota_t x$
and literal scalar $e_u^{\mathsf T}T_u^r\iota_t x$. This proves the
first formula and the actual endpoint at $r=H$. Holds do not change it.
Proposition 112.5 makes the finite rational system uniquely solvable;
restriction gives $x$, since $\iota_t$ is an inclusion. The receiver
can compute $v$ by the same finite multiplications, so its retained
predictor agrees with the real current field at Return. All scheduled
transactions and finite local computations finish under the stated
backing and serialization assumptions. The singleton case $t=\alpha$
has one sweep refusal, $N=1$, one Read and no Tick; the same formulas
apply with $H=0$. No physical inverse evolution or entry restoration has
been executed. $\square$

**Proposition 113.5 (why the acquisition bridge is substantive).** The
geometric sweep works even when the entrance field is zero; root scalars
alone are then identically zero if no nonzero Add is used. After geometry
has been earned, the $N$-scalar window is sufficient for every rational
field on $u$, including the particular zero-lifted subspace in (113.2).
No claim that $N$ is the minimum number of scalars for that subspace is
needed or made.

Proof. Zero is preserved by the linear field commands without nonzero
input and by zero-lifting edits. The sweep distinguishes constructors by
the original guards, independently of those zero scalars. The window
assertion is the invertibility of $\mathcal O_u$ in Proposition 112.5.
Its full-domain rank statement does not make a minimum assertion about
a smaller subspace, adaptive growth strategies or total resources.
$\square$

## 114. A historical domain with actual root-pulse preparation

**Definition 114.1 (prepared entrances).** A prepared entrance is an
actual execution with the following phases, all on the source of §112.
Initialize a genuinely zero-field alpha root. Execute a finite legal
successful native word ending at $t\in\mathcal D$, with no Tick or field
input in this phase. Let $m=m(t)$. For actual rational choices
$q=(q_0,\ldots,q_{m-1})^{\mathsf T}$ execute exactly

$$
\mathrm{Add}(q_{m-1});\ \mathrm{Tick};\
\mathrm{Add}(q_{m-2});\ \cdots;\
\mathrm{Tick};\ \mathrm{Add}(q_0).
\tag{114.1}
$$

There are $m$ Adds and $m-1$ returning Ticks; zero operands are still
actual Adds. There are no edits during this pulse phase and no extra
Ticks. All intermediate Tick scalars, semantic ACKs, End tokens and
returns are really consumed. Preparation is followed by the handoff of
Assumption 112.3 and the actual acquisition of §113.

The producer's old code, input record, pulse list, old replies and
predictor are not receiver advice. They are erased or isolated from
receiver access before the acquisition. Their actual construction,
storage, clearing or inaccessible retained capacity remains in the same
run's resource account. The receiver retains the authentic root binding
and rights; clearing a record does not recreate these facilities. No
additional source step occurs between the stated phases. Any optional
maintenance call or transport copy is an additional actual cost.

**Proposition 114.2 (all rational fields, with a unique fixed schedule).**
The entry field of (114.1) is

$$
x=\sum_{j=0}^{m-1}q_jT_t^je_t=\mathcal K_tq.
\tag{114.2}
$$

For every $t\in\mathcal D$ and every prescribed
$x\in\mathbb Q^{V_t}$ there is a unique rational $q$ in this fixed
schedule producing that field. Such an entrance has an actual finite
preparation with the given installation. To prepare a specified $x$,
its input and the solve $q=\mathcal K_t^{-1}x$ are paid producer work.

Proof. Native preparation leaves all fields zero by persistence and the
absence of field commands. Expanding the first Add, then each successive
Tick and Add, shows that $q_j$ receives precisely $j$ subsequent powers
of $T_t$; this is (114.2). Proposition 112.5 makes $\mathcal K_t$ a
rational isomorphism. Thus the displayed inverse is rational and unique.
AA Theorem 17.2 supplies a finite legal native preparation of every $t$;
the resulting $m$ finite rational inputs and $m-1$ actual Ticks give the
required finite execution. The producer may instead receive arbitrary
$q$ and produce its corresponding $x$, without a target-field solve.
Neither variant hands $q$ to the receiver. $\square$

All preparation outputs have an explicit correspondence as well. Let
$f_0=q_{m-1}e_t$ be the field after the first Add. For
$0\le h<m-1$, the next actual Tick has field $T_tf_h$ and returns
$e_t^{\mathsf T}T_tf_h$; the following Add has ACK and leaves
$f_{h+1}=T_tf_h+q_{m-2-h}e_t$. Thus $(t,q)$ computes every pulse-phase
scalar and successor, including those replies consumed and not archived.
Computing an old output value does not recreate its past delivery event
or an erased record of that event.

For the parsimony of this declared preparation, fix $t$ and any fixed
schedule of root pulses and linear Ticks, starting from zero. If the
schedule has $k$ freely chosen scalar amplitudes, its attainable fields
lie in the span of the $k$ vectors obtained by propagating those root
inputs to the final cut. That span has dimension at most $k$ over
$\mathbb Q$. Consequently $k<m$ cannot produce every member of
$\mathbb Q^{V_t}$ in that fixed linear schedule, whereas (114.1) does
with $k=m$. This elementary rank comparison concerns freely varying
root amplitudes with fixed timing and geometry. It gives no minimum
over variable-time encodings, other generators, extra ports or total
same-run resources.

**Definition 114.3 (actual temporal content).** In AA's labelled native
causal order $E(t)$, a split event occurs at every final branch address;
a promotion event occurs at every position born alpha whose final
subtree is not alpha. Birth is beta at an $L$-ending address and alpha
at the root or an $R$-ending address. The edges are the required local
promotion before split and the creating parent split before the first
event at a child. Their transitive closure is the order. It records
actual generation dependencies, not a selected serial linear extension.

The temporal content used here consists of this labelled order together
with the actual chronological root amplitudes in (114.1), with the fixed
Tick interleaving. All native preparation events precede the pulse
phase. The fixed acquisition phases are a later, determined suffix.
There is no archive of waiting, failed producer requests, serial native
shuffles, transport microsteps or erased scalar replies in this temporal
content. Pulse amplitudes are actual controls at one root, not field
arrays relabelled as events. There are exactly $m$ independent rational
control coordinates in the declared schedule.

**Proposition 114.4 (the necessary historical restriction).** From an
arbitrary entrance of Assumption 112.3, the computation
$\mathcal K_t^{-1}x$ defines unique canonical pulse coordinates. It does
not imply that those controls actually occurred. Bare $E(t)$ cannot
recover the independent arbitrary field, even though it recovers $t$.
The historical inverse in §§115–117 is asserted only for actual
prepared entrances of Definition 114.1.

Proof. Invertibility defines the canonical coordinates for every $x$.
For the failure of the unqualified implication, initialize alpha and
compare an entrance with field zero to one with field one produced by
an actual Add$(1)$. Both have the same empty native causal order and the
same material. Their root Read replies differ. Thus no function of the
bare native causal order can return the arbitrary field or its boundary
window on this domain. Moreover Add$(c)$; Add$(-c)$, for a nonzero
rational $c$, can be inserted into an arbitrary old field journal without
changing its final field or any subsequent source service. That journal
differs from the one without the insertion. The final field therefore
does not determine an unrestricted old journal. Definition 114.1 excludes
these extra calls by an actual promise, not by a decoder's convention.
$\square$

## 115. Four independent views of the prepared and acquired process

**Definition 115.1 (sampled family and the meanings of the views).** Fix
the authentic context and the actual preparation, handoff and acquisition
rules above. Here fixing the context fixes the binding, orientation,
law, program and authority convention; each sample has its actual
sufficient finite backing as in Assumption 112.3. It does not fix one
finite arena serving the whole family. Backing sizes are unobserved,
remain paid and are not extra view coordinates. The sampled parameter
domain is

$$
\mathcal P=\coprod_{t\in\mathcal D}\mathbb Q^{m(t)}.
\tag{115.1}
$$

For $(t,q)\in\mathcal P$, a sample is the completed acquisition cut
of that actual prepared process. Different legal serial native
preparations with the same $E(t)$ are allowed. Put

$$
\begin{aligned}
m&=|V_t|,&u&=J(t),&N&=|V_u|,&H&=N-1,\\
x&=\mathcal K_tq,&z&=\iota_t x,&
Y&=\mathcal O_u z,&v&=T_u^H z.
\end{aligned}
\tag{115.2}
$$

The four views expose the following different objects of that process.

| View | Independently specified content at this sample |
| --- | --- |
| Space | The actual present ordered rooted material $C(u)$, its installed calibration and the present field $v$ on its material cells. |
| Time | The actual labelled native preparation order $E(t)$ and the chronological root amplitudes of (114.1), with its fixed pulse/Tick interleaving and the phase order of Definition 114.3. |
| Boundary | The literal complete preorder sweep replies, including every distinct refusal and Growth address, followed by the Hold, Read, returning-Tick and final Hold replies of (113.3), with their End, LocalACK and Return events. |
| Memory | An earned live constructor word for the physical current $u$, a mutable current-field predictor $v$, the finite update/parser program and the genuine retained callable context and rights. |

Space is a mathematical view of real incidence and fields, not a new
interior read port. Its internal acquisition is Theorem 113.4. Time
does not expose every producer or observer microstep. Boundary contains
only the actual acquisition boundary record, not a response oracle for
unasked calls. Its known controller determines each request from the
earlier replies. Memory can discard $t,x,q,Y$ and the guard archive after
any requested exports. It need not retain an immutable entry copy; it
is the live current predictor used by §116. Extra retained exports or
archives are extra charged records.

View equality keeps $\mathfrak c$ fixed and compares the declared content.
It disregards irrelevant workspace addresses, fresh-name spelling and
unexposed private provider history. The real context attached to a held
view is retained, not reconstructed from a rational word. A printed copy
of a view alone does not grant authority over the source. These conventions
also apply to every conversion below.

**Theorem 115.2 (explicit recovery in every direction).** On the sampled
family (115.1), each view uniquely determines $(t,q)$ and therefore all
four views. Every conversion uses finite rational and syntax operations
on actually held input records. It preserves the same actual return
$(u,v)$ and context, rather than recreating an old source or giving a
printed record new rights.

Proof from Time. AA Theorem 17.2 reconstructs $t$ from the actual labelled
order $E(t)$: branch positions are exactly its split addresses, and each
remaining leaf is beta exactly when born beta or promoted. The actual
pulse chain gives the chronological vector
$(q_{m-1},\ldots,q_0)$, hence $q$. Count $m$, form $\mathcal K_t$ and
compute $x$ by (114.2). Compute $u,z,Y,v$ by (115.2). The preorder
constructor at each entry node fixes its sweep reply and address; append
the exact fixed token cycles and the scalar block $Y$ to obtain Boundary.
The material and live predictor are Space and Memory. This reconstructs
only the declared order and pulse chain, not a chosen native shuffle.

Proof from Boundary. Parse the reply stream with the known sweep stack.
At each scheduled address, wrong type emits alpha, Growth$(S,p)$ emits
beta and ends that visit, and branch emits branch and schedules left
then right. Matching success addresses and all completion tokens are
checked. The promised actual stream has no absent or malformed case.
Lemma 113.2 makes its completed word exactly $t$. Obtain $u=J(t)$ and
$N$, parse precisely the $N$ scalar replies $Y$ and the two semantic
Hold ACKs in their fixed positions, and solve

$$
z=\mathcal O_u^{-1}Y,\qquad x=z|_{V_t},\qquad
q=\mathcal K_t^{-1}x.
\tag{115.3}
$$

Theorem 113.4 proves these are the actual old field and pulse coordinates.
Compute $v=T_u^H z$; the actual source is already at that value. This
gives Space and Memory, and Definition 114.3 gives Time. A recovered old
scalar or pulse is a mathematically recovered value, not a newly made
observation of the old cut.

Proof from Space. Parse $u$ from the actual ordered material arities,
including each unary marker, as in AA Definition 17.3. Apply the existing
partial decoder $\kappa$ to obtain $t$; the promised $u=J(t)$ is in its
domain. Then compute

$$
z=T_u^{-H}v,\qquad x=z|_{V_t},\qquad q=\mathcal K_t^{-1}x.
\tag{115.4}
$$

Both inverses exist by Proposition 112.5, and (115.2) proves each equality.
The same formulas give all other view content. This algebraic inverse
is local work on the Space representation; no reverse Tick is a source
command and no physical restoration follows.

Proof from Memory. Parse its earned live current word $u$ and use its
current predictor in place of the Space field in (115.4). The invariant
at the sample is the actual equality of that predictor with $v$.
Consequently the same $t,x,q$ are recovered. Computing the material
representation and the other two views is finite. None of these proofs
uses the producer's erased records or supplies a port not in §112.
$\square$

**Corollary 115.3 (both round trips and every route).** Denote the actual
content maps by $F_i:\mathcal P\to\mathcal V_i$, where
$i\in\{S,T,B,M\}$ and $\mathcal V_i=F_i[\mathcal P]$. Let $D_i$ be
the explicit decoder just proved, with values in $\mathcal P$. For all
$p\in\mathcal P$ and $w\in\mathcal V_i$,

$$
D_iF_i(p)=p,\qquad F_iD_i(w)=w.
\tag{115.5}
$$

Set $R_{ij}=F_jD_i$ for every $i,j$, including
$R_{ii}=\mathrm{id}_{\mathcal V_i}$. The twelve conversions with
$i\ne j$ satisfy, for all $i,j,k$ and every admissible input,

$$
R_{ji}R_{ij}=\mathrm{id},\qquad R_{jk}R_{ij}=R_{ik}.
\tag{115.6}
$$

Every finite route with a given starting and finishing view has the same
result.

Proof. Each part of Theorem 115.2 recovers the actual $t,q$, so it proves
the first identity of (115.5), rather than merely postulating a common
quotient. If $w=F_i(p)$, substituting that first identity proves the
second one. Substitute both identities into each composition in (115.6).
An induction on the number of route edges proves the final statement.
The algebra is the existing image-transport argument of RGII §99;
its required substantive inputs here are the nonzero-entry acquisition
and the actual pulse preparation. The maps were defined from independent
physical, temporal, boundary and live-record content before constructing
their inverses. $\square$

**Proposition 115.4 (exact numerical images).** The Space and Memory
numerical image consists exactly of pairs $(u,v)$ for which

$$
u\in J[\mathcal D],\quad t=\kappa(u),\quad H=|V_u|-1,
\quad (T_u^{-H}v)_p=0\quad(p\in V_u\setminus V_t).
\tag{115.7}
$$

The Boundary numerical image consists exactly of valid complete sweep
words decoding $t\in\mathcal D$, followed by the fixed window skeleton
with $N=|V_{J(t)}|$ rational scalars $Y$, such that

$$
(\mathcal O_{J(t)}^{-1}Y)_p=0
\quad(p\in V_{J(t)}\setminus V_t).
\tag{115.8}
$$

Time has precisely an order $E(t)$ and a length-$m(t)$ rational pulse
chain in the stated phases. All these conditions admit finite exact
tests on finite represented input. Passing a numerical image test does
not authenticate physical provenance, actual past controls, binding,
calibration or current rights.

Proof. Equations (115.2) give necessity. For (115.7), set
$z=T_u^{-H}v$, $x=z|_{V_t}$ and $q=\mathcal K_t^{-1}x$.
The zero condition says exactly $z=\iota_t x$. Proposition 114.2
prepares this $x$ and Theorem 113.4 yields this $(u,v)$, proving
sufficiency. For (115.8), put $z=\mathcal O_u^{-1}Y$ and use the same
construction. Invertibility returns exactly the proposed scalar block.
The sweep word is deterministic given $t$, so its literal content and
fixed completion skeleton agree too. The Time assertion follows from
AA Theorem 17.2 and Proposition 114.2: choose any legal native linear
extension and the given actual pulse chain.

Finite syntax parsing, the existing $\kappa$ test, reconstruction of
$E(t)$, rational inversion and equality tests implement these conditions.
These are existence and value tests. A counterfeit word can satisfy
them without being attached to any actual specimen. The context and
preparation hypotheses therefore remain separate. $\square$

## 116. Complete current service and actual lawful selection

**Theorem 116.1 (full service after the new acquisition).** Suppose a
Ready cut has an earned current logical term $u$, its original-address
calibration, and a retained predictor $\widehat w\in\mathbb Q^{V_u}$
equal to the actual field under the actual address correspondence.
Retain the genuine context, complete parser and finite backing of §112.
For every sufficiently backed finite continuation using the full menu,
the predictor computes exactly every complete semantic reply and
successor, and tracks the corresponding pending, busy and completion
phases. This includes finite adaptive continuations with arbitrary finite
addresses and rational operands, all refusals, and malformed or partial
input. The actual requests and their complete lifecycles are still
executed. Theorem 113.4 supplies precisely this invariant at its return.

Proof. This is RGII Theorem 100.1's current-service construction with
the actual initial field replaced by the proved $v$ of (113.4). The
replacement requires no change to its transition proof. For completeness,
the exact correspondence is checked row by row.

Add$(q)$ updates the retained root coordinate by $q$ and predicts its
fixed semantic ACK. Read predicts the current root coordinate and
changes nothing. Tick applies the earned $T_u$ and predicts the updated
root scalar; each row agrees with the actual neighbor sum because
incidence, calibration and all old field coordinates agree. Hold changes
neither field nor term and predicts its fixed ACK.

For a native frame, navigate the earned logical term using its actual
address, descending only through branches. Missing position, branch
target and wrong leaf type reproduce the three distinct identity
refusals. An enabled promotion retains all old coordinates and appends
zero at $pL$. An enabled split retains all old coordinates, including
the marker at $pL$, and appends zero at $pLL,pR$. Compute the new records
from their actual parent pairs. The real template and the predictor thus
have the same extended address correspondence, term, old coefficients,
fresh coefficients and field. Predict the full Growth kind and address.
The physical allocation and fresh grants are supplied by the real
installation, not by having computed their expected values.

The fixed parser stores a proper prefix and its parsing position without
a completed semantic reply or source step. Complete malformed, unused
or noncanonical frames yield BadFrame and the identity source successor.
During a complete request it retains the same request bytes, target
cursor and reserved material as required by the protocol. It then
tracks Guard, edit or refusal, sealed full reply, output End,
corresponding local commit, LocalACK, Return and cleanup. The next
Ready cut is exposed only after these actual events. No unsupported
extra ingress while busy is admitted. Disabled rights, wrong phase or
insufficient backing is a failure of the execution premise, not a
predicted native tag. No claim about a crash or revocation channel is
implicit in these rows.

Induction on completed transactions preserves the source-field and
protocol invariants. Proper-prefix steps preserve the pending-input
invariant within a transaction. A common adaptive policy receives the
same prior replies and retained inputs and therefore chooses the same
next input, stop decision and finite local calculation. For a randomized
policy fix a common source-independent random tape and apply the same
induction to each finite realized execution. This proves adaptive
service with its complete outputs and actual continued callable use.
Predicted replies never substitute for making the physical calls.
$\square$

**Theorem 116.2 (exact full-service kernel).** In the fixed authentic
context, two settled finite calibrated states are indistinguishable by
every finite common experiment in Definition 112.4 if and only if their
ordered terms and original-address fields agree. On the prepared sampled
family, this equivalence is also equality of $(t,q)$ and equality of any
one of the four views. It is not an equivalence theorem for arbitrary
old journals or private busy states.

Proof. Equal terms and fields give the same entire service by Theorem
116.1. For unequal terms choose the first differing logical constructor
in an ordered descent. Every strict ancestor is a common branch. Its
finite address therefore exists in both. A $P$ there gives Growth at
alpha, Refusal(wrong type) at beta, and Refusal(branch) at a branch.
These are distinct full replies. The separating address exists; this
argument does not give a receiver that has not acquired either term a
free selector.

For equal terms $u$ and unequal fields, invertibility of $\mathcal O_u$
makes at least one scalar in
$(e_u^{\mathsf T}w,\ldots,e_u^{\mathsf T}T_u^{N-1}w)$ differ.
Read followed by $N-1$ returning Ticks exposes this finite window on
the actual states. It advances their fields and uses the stated real
backing; no nondisturbing assay or Reset is assumed.

On the sampled family, equality of current terms gives equality of
$t$ by the existing injectivity of $J$. Equality of current fields,
followed by $T_u^{-H}$, restriction and $\mathcal K_t^{-1}$, gives
equality of $q$. Conversely (115.2) gives equal current states from
equal $(t,q)$. Theorem 115.2 then identifies equality of any view with
that same condition. Archives outside the task, different protocol
phases and differing bindings are not identified by this argument.
$\square$

**Corollary 116.3 (an acquired-input selector).** At the return of
Theorem 113.4 an actual lawful request can depend on recovered entry
information without a supplied address oracle. In particular, compare
the recovered $x_\varepsilon$ with zero. If it is nonnegative, choose
the current leftmost logical leaf of $u$; otherwise choose the current
rightmost logical leaf. Choose $P$ at alpha and $S$ at beta. Construct
its complete addressed frame and execute it through the retained genuine
dispatcher and authority. The request succeeds, its complete Growth
reply is consumed, and the current predictor extends by the real zero
lift and new calibration.

Proof. Theorem 113.4 has actually recovered $x$, so its root coordinate
and sign are real acquired inputs. The earned finite current word has
at least one logical leaf. Repeatedly choosing the left or right child
at a branch terminates at the indicated leaf and constructs its finite
address. The leaf's earned constructor selects its enabled native
operation. Exclusive rights and finite reserved fresh backing make the
real call lawful; Theorem 116.1 proves its reply and successor. The sign
comparison, selection computation, address, frame, input record, grants,
fresh cells, reply and whole lifecycle are actual costs. If $x$ is
discarded after this sample, an arbitrary later selector cannot treat
that old value as a retained input without recovering it from a valid
retained record or paying for its archive. $\square$

## 117. Dynamics, historical images and excluded inverses

**Definition 117.1 (the larger current-state carrier).** Let

$$
\mathcal C=\coprod_{u\in\mathcal D}\mathbb Q^{V_u}
\tag{117.1}
$$

with the fixed context and completed framing of §112. Native growth
uses its actual address inclusions in this carrier. Proper prefixes
and busy phases are tracked by adjoining the actual finite protocol
state; only a completed transaction returns to $\mathcal C$.
For a sampled view $w\in\mathcal V_i$, write $C_i(w)$ for the current
state $(u,v)$ recovered by Theorem 115.2. This forgets historical detail
only after its current meaning has been proved.

**Proposition 117.2 (the precise dynamics compatibility).** Every sampled
view initializes the same full current predictor. If a common finite
input continuation is actually executed from that sample, all four
initializations compute its same entire output and current-state path
in $\mathcal C$, including the same pending and completion phases.
The same holds for adaptive policies whose inputs correspond under
the proved view conversions. Thus converting the initial view and then
serving a continuation agrees with serving it from any other view.
The assertion does not require the raw successor to lie in a historical
image $\mathcal V_i$.

Proof. For any $i,j$ and $w\in\mathcal V_i$, Theorem 115.2 gives
$C_j(R_{ij}w)=C_i(w)$. Apply Theorem 116.1 to these equal initialized
current records and the same real finite requests. Row correspondence
gives equal complete outputs and successors at every transaction and
equal parser-prefix behavior within each cycle. Induction gives the
whole finite path. A policy conjugated by $R_{ij}$ has the same declared
input values; with equal earlier replies it makes the same choices.
All predictions still refer to the one actual source path. The conclusion
is a commuting current-service diagram, not a definition of new
historical coordinates for every successor. $\square$

**Proposition 117.3 (the historical image is not Tick invariant).** Even
one legal raw Tick can leave the sampled image of §115.

Proof. Take $t=\beta$, so $V_t=\{\varepsilon,L\}$, $m=2$ and
$u=J(t)=\langle\beta,\alpha\rangle$ has
$V_u=\{\varepsilon,L,LL,R\}$, $N=4$, $H=3$.
Proposition 114.2 supplies an actual pulse preparation of $x=e_t$.
After acquisition, $z=e_u$ and $v=T_u^3e_u$.
One real Tick gives $w=T_u^4e_u$. If $(u,w)$ belonged to (115.7),
the unique backward-computed vector would be
$T_u^{-3}w=T_ue_u$. Its fresh $R$ coordinate is
$\ell_R/100>0$, contradicting (115.7). No different entry term can
avoid this test because $\kappa(u)=\beta$ is unique. The full current
service still predicts this Tick and every later backed finite
continuation exactly. The failed implication is raw Tick successor
$\Rightarrow$ membership in the fixed prepared-and-acquired image.
$\square$

**Proposition 117.4 (value recovery and actual history are different).**
The inverse maps in §115 supply no general inverse for a chosen serial
native preparation or an arbitrary old journal. They do not recreate
an erased observation record, physically restore the entry or certify
an unknown installation. Output values of the promised deterministic
preparation and acquisition are recoverable; delivery records outside
the declared views are not thereby retained.

Proof. AA Theorem 17.2 allows different linear extensions of the same
labelled order whenever independent native events can be exchanged.
They give the same $t$ and, with the same pulse chain, the same four
declared views. Such a serial distinction is therefore absent from
their domain. The Add$(c)$; Add$(-c)$ pair of Proposition 114.4 gives
the stronger arbitrary-journal failure outside the fixed schedule.
All source evolution in §113 is an actual zero-lifting sweep followed
by $H$ forward Ticks. Equation (115.4) is a computation on a record and
is not an installed inverse source command. Finally an abstract word
satisfying (115.7) or (115.8) has no intrinsic physical binding or grant.
Consequently value consistency alone cannot prove those separate
operational or provenance premises. $\square$

## 118. Calls, literal traffic and actual preparation on one run

**Definition 118.1 (counting coordinates).** For the entry $t$, let $a,b$
be its alpha and beta leaf counts and put

$$
L=a+b,\quad r=2L-1,\quad m=r+b,\quad N=m+2b,\quad H=N-1.
\tag{118.1}
$$

Here $r$ counts logical nodes, $m$ counts entry material including markers,
and $N$ counts actual material after the sweep. Let

$$
D=\sum_{p\text{ logical in }t}|p|,\qquad
D_\beta=\sum_{p\text{ a beta leaf in }t}|p|.
\tag{118.2}
$$

Counts below describe one attained implementation and the one actual
execution of §§113–114. Calls, field arithmetic, structural assignments,
bits, navigation, authority and simultaneous storage are separate
coordinates. No scalar or call is a constant-price physical primitive.
Literal references and grants pay their actual widths, not the apparent
length of an opaque handle.

For exact payloads retain the three-bit native tags, the address code
$A(p)=1^{|p|}0p$, the Growth kind bit, and the five-bit distinct native
refusals of AAII Definition 53.3. Thus a native request at depth $d$
has $2d+4$ bits, its successful reply $2d+5$, and its refusal five.
Assign fixed three-bit field-operation and field-reply tags. Six of the
eight request tags are $P,S$, Add, Read, Tick and Hold; unused complete
tags give BadFrame. Fix one choice of these disjoint tags throughout.

Let $\lambda(k)$ be binary magnitude length for $k\ge0$, with
$\lambda(0)=0$. A signed integer $z$ is a sign bit, the word
$1^{\lambda(|z|)}0$, and its magnitude bits; negative zero is forbidden.
A reduced rational $A/B$, $B>0$, uses that signed numerator followed by
the positive denominator's length prefix and bits. Its exact length is

$$
\rho(A/B)=2\lambda(|A|)+2\lambda(B)+3.
\tag{118.3}
$$

The denominator must be positive, the fraction reduced and the magnitude
spelling canonical. Invalid complete spellings give BadFrame. This is
the codec already used in AAII Definition 90.2; it adds no field advice.
A scalar reply has length $3+\rho(y)$ and semantic ACK length three.
Read, Tick and Hold requests each have length three, and an Add request
has length $3+\rho(q)$. Input End, output End, LocalACK and Return are
additional fixed events, not included in these payload lengths.

**Theorem 118.2 (exact acquisition bill).** On the same execution as
Theorem 113.4, the sweep has exactly $r$ split attempts: $b$ successes
and $r-b$ refusals. It adds $2b$ cells and has request and reply payloads

$$
I_{\rm sweep}=2D+4r,\qquad O_{\rm sweep}=5r+2D_\beta.
\tag{118.4}
$$

With parent-chain return on each request, source navigation has $D$
descents and $D$ ascents. In AA's three-reference-field layout the sweep
has $8b$ source structural assignments, besides its calibration, zero
writes, allocation, grant, cursor and communication work.

The field window has one Read, $N-1$ returning Ticks and two Holds.
It has $N$ literal scalar replies and two semantic ACKs. Consequently
the whole acquisition has exactly

$$
r+N+2
\tag{118.5}
$$

completed transactions, no Add or Reset, and payloads

$$
\begin{aligned}
I_{\rm acq}&=2D+4r+3(N+2),\\
O_{\rm acq}&=5r+2D_\beta+3N+
\sum_{j=0}^{N-1}\rho(Y_j)+6.
\end{aligned}
\tag{118.6}
$$

There is one input End, output End, LocalACK and Return per completed
transaction: each of these four counts is $r+N+2$. These identities do
not count an incomplete prefix as a completed transaction.

Proof. AAII Theorem 73.2 supplies the unchanged sweep counts because
Lemma 113.2 uses exactly that actual sweep. Each success is at an entry
beta leaf; its additional reply length is $2|p|$. Summing all request
depths and successful reply depths gives (118.4). There are $2b$ actual
fresh cells, so $|V_u|=m+2b=N$. The literal schedule (113.3) has
$1+(N-1)+2=N+2$ field transactions. Their request tags total $3(N+2)$;
their scalar tags and rational words total
$3N+\sum_j\rho(Y_j)$, and the two ACKs add six. Add the sweep to get
(118.5)–(118.6). The completed framing adds exactly the four events
specified for each cycle. This proves the simultaneous identities for
this actual run, not separate favorable marginal counts. $\square$

**Proposition 118.3 (producer and selector bills).** For an actual
prepared entrance, the native preparation has $b$ promotions and $L-1$
splits. Set $e=b+L-1$ and let $D_{\rm prep}$ be the sum of their actual
address depths in the chosen legal word. It constructs $m-1$ cells
beyond the original root and has

$$
I_{\rm native}=2D_{\rm prep}+4e,\qquad
O_{\rm native}=2D_{\rm prep}+5e
\tag{118.7}
$$

payload bits and $e$ full cycles. The same reference-field layout has
$3+4b+8(L-1)$ structural assignments including root initialization.
Calibration, zero fields and actual buffers are additional writes.

The pulse preparation has exactly $2m-1$ full cycles. If $\eta_j$ are
its actual $m-1$ returning-Tick scalars, its payloads are

$$
\begin{aligned}
I_{\rm pulse}&=3(2m-1)+\sum_{j=0}^{m-1}\rho(q_j),\\
O_{\rm pulse}&=3(2m-1)+\sum_{j=1}^{m-1}\rho(\eta_j).
\end{aligned}
\tag{118.8}
$$

These are paid in addition to (118.6), the genuine handoff and every
input, retained record, erased record and provider operation. The optional
selector of Corollary 116.3 adds one actual full native cycle. At selected
depth $d_*$ it adds $2d_*+4$ request bits, $2d_*+5$ reply bits, one
fresh cell and four structural assignments if it chooses $P$, or two
fresh cells and eight assignments if it chooses $S$. It adds no Tick.

Proof. Promotion increases beta leaf count by one; splitting replaces a
beta by one beta and one alpha, leaving beta count unchanged and raising
leaf count by one. Starting from alpha, the chosen legal word thus has
exactly the stated event counts. The original templates allocate one
and two cells respectively. Summing the same addressed-frame lengths
proves (118.7) and the reference-field assignment count is AAII
Definition 73.1's original layout. In (114.1) each Add supplies one
actual rational and gets an ACK; each Tick gets its actual scalar.
Their three-bit tags give (118.8), including zero operands and unused
intermediate scalars. The selector is one enabled original request and
uses its corresponding template; all its address and selection work
is additional. $\square$

For the arbitrary entrance theorem, any earlier field preparation need
not have the fixed schedule. Its actual calls, provider construction,
input ingress, output delivery and retained or cleared material still
belong to the same-run bill. Equations (118.7)–(118.8) apply to the
declared preparation, not to an unspecified arbitrary old journal.
Obtaining a target $x$, computing its pulse inverse, selecting the
old native word, allocating the original root and installing its
binding, orientation and authority are not free initial advice. All
exports of a recovered view pay their construction, framing,
transmission and any coexistence with the input copy.

## 119. Exact work, numerical widths and simultaneous material

**Proposition 119.1 (attained rational work).** After the sweep, an
implementation can construct $T_u$ and $\mathcal O_u$, solve for $z$
and $x$, and form the physical-current predictor $v$ with $O(N^3)$
rational operations and $O(N^2)$ rational slots, besides actual syntax,
address, framing, source and authority work. The same cubic bound is
sufficient for the pulse solve at size $m$ and each Space or Time export
at the relevant sizes $m,N$. These are exact arithmetic operation counts,
not bit, duration or total-resource bounds.

One actual Tick on a current $M$-cell material tree can be implemented
with exactly $3M-2$ rational products and $2M-2$ rational additions,
besides old/new buffers, actual link traversal and control. In particular
the acquisition has $H=N-1$ such source Ticks at size $N$, while the
prepared pulse phase has $m-1$ at size $m$.

Proof. Parse the earned term, append its material markers and addresses,
and compute each calibration pair from its parent. The actual receiver
now knows the matrix; no source coefficient query is being assumed.
Sparse multiplication of $e_u$ by $T_u$ successively forms all $N$
columns of $\mathcal K_u$ in $O(N^2)$ rational work. Transposition
gives $\mathcal O_u$. Finite rational Gaussian elimination with pivot
search solves its nonsingular system in $O(N^3)$ operations. Use $H$
sparse multiplications to propagate $z$ to $v$ in $O(N^2)$ work and
store the matching current predictor. This produces only a constant
number of square and linear arrays. Constructing $\mathcal K_t$ and
solving (114.2) is the same computation at size $m$.

For (115.4), invert $T_u$ by finite elimination, or solve the nonzero
determinant system for all columns, then apply that inverse $H$ times.
The dense matrix-vector work is $O(HN^2)=O(N^3)$, with quadratic
workspace. All other view conversions use the displayed matrices,
finite tree/order construction and the same-size solves. There is no
enumeration over unknown geometries in this implementation.

For the source Tick, retain all old fields, traverse actual material
child links and compute a second buffer. There are $M$ diagonal terms
and two directed contributions per one of the $M-1$ edges, hence
$3M-2$ products. Summing the $1+\deg(p)$ terms of row $p$ needs
$\deg(p)$ additions, totaling $2M-2$. Commit buffers in a second
traversal. A backed stack detects completion on the actual finite tree
without a supplied size. This is RGII Proposition 96.3's source-side
implementation, not an observer interior port. Fixed reference
traversals and buffer writes are extra work. $\square$

**Proposition 119.2 (a passive-field width bound and its limit).** Let
$d$ be the maximum material depth of $u=J(t)$ and set
$\Delta=100\cdot8^d$. Every entry of $T_u$ has denominator dividing
$\Delta$. Suppose the reduced numerator magnitude and positive
denominator of each entry coordinate $x_p$ are at most $2^B$, with
$B\ge1$. During the acquisition's passive field epoch, after $k$ Ticks,
all source coordinates and literal root scalars have reduced numerator
and denominator widths at most

$$
O\bigl(mB+B+k(d+1)+1\bigr),\qquad 0\le k\le H.
\tag{119.1}
$$

This bound does not bound the pulse amplitudes, pulse transients,
elimination intermediates or arbitrary later Add operands.

Proof. At depth $h$ the exact local records have
$\ell_p=8^{-h}$ and $a_p=A_p/8^h$, with
$A_{pL}=8A_p+1$ and $A_{pR}=8A_p+6$. The diagonal denominator
divides $2\cdot8^h$ and the parent-edge denominator divides
$100\cdot8^h$, both divisors of $\Delta$.
The maximum off-diagonal row sum is at most $\ell_p/80$, with a
smaller bound at the root, and

$$
a_p+\ell_p/2+\ell_p/80<a_p+\ell_p\le1.
\tag{119.2}
$$

Thus the nonnegative matrix has $\|T_u\|_\infty<1$, so it does not
increase the sup norm of a signed vector either. The entry fields have
sup norm at most $2^B$. Let $Q$ be the product of their positive
denominators; $Q\le2^{mB}$. After zero lift, and after $k$ passive
Ticks, a common denominator is $Q\Delta^k$ because $\Delta T_u$
is integral. Reduced denominators divide it and reduced numerator
magnitudes are at most $2^B Q\Delta^k$. Taking binary lengths gives
(119.1), including $x=0$ and zero fresh coordinates. The inverse
Krylov solve can create large signed amplitudes even for small $x$;
the same passive bound therefore does not apply to (114.1) or to
local elimination. $\square$

**Definition 119.3 (actual arithmetic width).** For a chosen finite
implementation and run, let $W_{\rm run}\ge1$ be the maximum actual
bit width of its integer magnitudes, reduced rational numerators and
denominators, products, reduction and elimination intermediates, control
counters and numerical input/output words while live. It includes
producer target/pulse work and receiver work when those phases belong
to the run. An inaccessible provider's numerical arrays have their own
actual widths in the same material account. This is an actual finite-run
quantity, not a sensor-precision promise or receiver advice.

If $b_0$ bounds initial numerical and supplied operand widths and $A$
counts the rational operations of a finite segment, a sufficient loose
numerical bound is

$$
W_{\rm num}\le(b_0+2)2^{A+1}.
\tag{119.3}
$$

Indeed one addition, subtraction, multiplication or legal division of
reduced rationals of numerator/denominator width at most $B_0$ has
unreduced widths at most $2B_0+2$, and reduction cannot increase them.
Induction proves (119.3); every division follows a nonzero pivot test.
Counters, addresses and reference encodings are separately bounded by
their actual finite uses and included in $W_{\rm run}$ where numerical.
School integer arithmetic and Euclidean reduction give, conservatively,
$O(W_{\rm run}^3)$ bit work per rational operation, with finite scratch.
The cubic rational work of Proposition 119.1 must be multiplied by an
appropriate actual-width bound, and all bit ingress, output, traversal,
allocation, copying and control remain additional. Finite program size
does not make these words bounded over all possible finite runs.

**Definition 119.4 (a simultaneous layout).** A sufficient numeric core
uses $O(N^2)$ actual rational slots during acquisition and export, each
at its actual width. It includes the following whenever live: source
fields and source Tick buffer; observer predictor and its update buffer;
earned Krylov/observation matrices; elimination and inverse workspace;
literal $Y$; $x,z,v$ and pulse coefficients $q$ if retained; proposed,
returned and exported copies. Sequentially reusing the same actual array
counts it once; genuinely separate copies are simultaneous material.
Only a constant number of such square or linear arrays is required.

Add the earned logical/current words, material-address and old-inclusion
maps, which have an $O(N(d+1))$ address-content layout, with actual
indices and reference widths extra. The sweep can use one mutable
address, a pending-right flag per ancestor, and a tail-appended entry
word: its address and flags have $O(h+1)$ symbols for entry logical
height $h$, and its entry constructor payload is $2r$ bits. Retaining
both that word and a separate current $u$ word counts both. Computing
Time additionally constructs its labelled event/precedence representation;
the generator edges suffice and their endpoints have actual address
lengths. If a full transitive relation or extra export is constructed,
its actual records and work are additional.

The physical layout also counts every real source vertex and its three
reference fields, its $N-1$ material links, the $2N$ local calibration
records, edge/coupling machinery, field/buffer allocation and zero writes,
and every reserved fresh cell. Source fields already in the numeric core
are not counted twice. Count the original root and ordered dispatcher,
all old and fresh grant records, producer, receiver and provider programs,
current rights and their backing, allocation/retention machinery and
finite actual work arenas. An opaque callable reference is not the whole
cost of keeping its provider callable.

Finally count the literal guard archive if retained; the actual target
input, old producer controls and scalar archives while live; pulse input
backing; every sender/mailbox/receiver copy; request parser, pending input,
busy cursor and reserved targets; sealed response, End, LocalACK and
Return backing; counters, sign/selector inputs and chosen address; all
clearing work; and all inaccessible but retained provider capacity. These
quantities coexist on the one actual run at their respective cuts.

For a precise nonoverlapping account let $B_{\rm extra}(c)$ be the bits
at a cut $c$ in all actual installation, reference, authority, protocol,
provider and archive objects outside the specified numeric and
address/syntax arrays. A sufficient acquisition/export peak layout is

$$
\max_{c\text{ on this run}}
\left\{O\bigl(N^2W_{\rm run}+N(d+1)+N\log(N+1)\bigr)
+B_{\rm extra}(c)\right\}.
\tag{119.4}
$$

If an archive or provider representation is placed in the arrays instead,
remove it from $B_{\rm extra}$; if separate, add its full actual size.
Cell/link counts, transmitted bits and arithmetic work remain separate
coordinates. For the whole prepared run, apply the same layout to its
producer phase as well and take the maximum over all phases, including
the real handoff/clearing cut. Earlier peaks are not retroactively removed
by erasing an array. Actual provider capacity and old archives cannot be
bounded from the number of visible outputs.

For every later finite continuation add its actual address and operand
words, new field widths, successful fresh material, source/predictor
updates, full replies and completion cycles. Arbitrarily deep growth,
arbitrarily many Ticks and arbitrarily long rational operands preclude
a uniform lifetime bit or storage bound in this construction. None of
(118.4)–(119.4) combines minima from different realizations or establishes
a joint optimum, a physical energy/latency law, numerical stability or
cross-installation dominance.

## 120. Supplier correspondence and the remaining domains

**Mathematical attribution 120.1 (the additional composition).** The
source-specific addition is the joint actual acquisition of unknown
$(t,x)$ at the returned field $T_{J(t)}^{|V_{J(t)}|-1}\iota_t x$,
and its use with an actual fixed pulse preparation to obtain the
four-view sampled image. AAII already executes the destructive $J$
sweep and proves its inverse. RGII already proves calibrated root
cyclicity, finite root windows, pulse steering and complete current
service. Neither supplier alone establishes that the sweep preserves
an arbitrary unknown old field while earning the geometry needed to
observe that field on the same specimen. Lemma 113.2 establishes this
missing simultaneous correspondence; Theorem 113.4 actually obtains
the data and the advanced predictor. Proposition 114.2 then establishes
the exact historical preparation required for the Time inverse.

The following are the direct correspondences and the limits of reuse.
They do not create another abstract four-view or replay theorem.

| Original supplier | Exact use and hypothesis correspondence |
| --- | --- |
| AA Definitions 17.1, 17.3 and Theorem 17.2 | Same birth-typed $\mathcal D$, original ordered root, local $P/S$ edits, actual material and causal order. They reconstruct the native term and dependencies, not an arbitrary rational field or chosen serial extension. |
| AAII Definitions 68.2, 69.1, Lemma 68.3 and Theorem 69.2 | The very same $J$, its partial decoder and actual split sweep. Section 113 adds the field invariant without changing a sweep call or claiming a new syntax inverse. AAII's later represented $Q_J$ macros are not the raw menu of §112. |
| AAII §73 | Same addressed codec, three-reference-field templates, sweep/navigation counts and actual copy/authority discipline. The root field-window and pulse bills are added on the same run, not substituted for those charges. |
| RGII Definition 96.1, Proposition 96.3, Lemma 97.1 and Theorem 97.2 | Exactly (112.1)–(112.2), persistent local records and source-side sparse Tick. Their spectral-window/root-overlap proof supplies cyclicity for both $t$ and $J(t)$. Only the zero entrance of their acquisition is replaced here. |
| RGII §§99–102 | Image round-trip algebra, full native-service induction, fixed-term root window and paid exact arithmetic. Their genuine-zero spectral trial and any separately paid return-to-image procedure are not executed by §113. Historical image closure is not imported; Proposition 117.3 disproves it for the present raw Tick. |
| [Native Leaf Boundary Acquisition, §§10–12](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION.md) | Actual retained-marker templates, zero lifts and native-guard/predictor correspondence. Its supplied terminal roster and different field law and ports are not available to this receiver. |

For the root linear algebra, the relevant repository declarations are
[FiniteObservabilityEquivalence](../../../D5/S3/Observer/Linear/FiniteObservabilityEquivalence.lean),
`finite_observability_equivalence`, with its
[owning Scribe](../../../Blueprint/D5/S3/Observer/Linear/FiniteObservabilityEquivalence.scribe.cs),
and [FiniteTimeTomographySaturation](../../../D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation.lean),
`all_future_kernel_eq_finrank_kernel`, with its
[owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/Dynamics/FiniteTimeTomographySaturation.scribe.cs).
They supply fixed-dimensional linear kernel/rank and finite-horizon
facts. They do not supply an unknown native term, root binding, current
authority or the nonzero-field sweep. The current use of (112.3) is
ordinary exact linear algebra with those source-specific inputs proved.

[NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean),
including its private `traverse`, `production_reads` and `stationary`
helpers and its
[Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs),
actually acquires a source through its logical constructor Read while
remaining stationary. That Read is absent here. The private navigation
and field-readout helpers of
[NativeUniformTree](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.lean)
and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformTree.scribe.cs)
evaluate a supplied native code. The private coordinate, catalog,
root-recognition and inverse helpers of
[NativeMaterialRootRecognition](../../../D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.lean)
and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition.scribe.cs)
use a supplied full finite adjacency presentation, complete terminal
order and their minimum-leaf hypothesis. They do not acquire those
inputs from root scalars. Here the guards earn the ordered term before
the fixed-dimensional root solve; a supplied-code inverse cannot replace
that step.

**Mathematical attribution 120.2 (other published operational results).**
[Native Clocked Recovery](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md)
already supplies actual acquisition and fixed-controller use with its
literal native Read, real primitive receipts and closed-cut clocks.
[Native Paid View Conversion](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md),
Definitions 1.2–1.4, already supplies installed paid view conversion
after its acquired fixed-$H$ entrance, unused verifier lanes and
owner-authorized Ready installation. Those inputs are substantive
facilities; neither is a missing generic callable-wrapper result.

[PR57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#57-a-complete-paid-ideal-realization-of-the-original-ordered-tree-interface)
already realizes its actual Clifford-$E$ Read and whole-candidate
capacity-guarded tree interface on constructed tapes, with receipt,
copy and ownership costs. The present menu has addressed local guards,
root rational fields and persistent calibration instead. No PR57 meter
or exact source port is silently installed here.
[Process Geometry, Corollary 37.3](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md#37-有序-fib-源运输的中心化刚性与入口恢复)
already inverts the acquired exponent/current-tree pair on its certified
substitution image. It explicitly keeps acquisition, provenance, rights
and physical inverse execution separate. The current $J$ image inverse
is itself already supplied by AAII, while its actual arbitrary-field
attachment requires §113.
[Structural Storage Atlas, Definition 13.7](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md#13-restricted-set-to-value-refinement-by-three-slot-relocations)
keeps genuine-state realization, supplied code, atomic-patch conditions,
fine-clock access and prices distinct. These conditions are not removed
by replacing one representation with another.

The published [Native Leaf Boundary Acquisition II,
§§58–59](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LEAF_BOUNDARY_ACQUISITION_II.md#58-physically-returning-the-arbitrary-entry-field-without-reset)
already gives paid physical entry-field restoration under its own law,
terminal access and acquisition. Its §§60–62 separately give the original
symmetric-growth rank obstruction, adaptive scalar lower bound and
earned-map current-field attainment. The present calibrated construction
does not reprove those results or claim restoration: its physical return
is (113.4). RGII §§104–111 already gives the shared-input all-origin
criterion on its rational cyclic spectral class and its fixed path
service. That fixed-law digit-history theorem is distinct from unknown
branching geometry with arbitrary entrance field; it is not a new
supplier to be rederived here.

**Mathematical attribution 120.3 (primary and pinned ingredients).**
Classical moment/Krylov duality, single-input finite-dimensional
controllability, finite observability and matrix inversion are
`literature-attested`. In particular Teschl, *Jacobi Operators and
Completely Integrable Nonlinear Lattices*,
[§2.5](https://www.mat.univie.ac.at/~gerald/ftp/book-jac/jacop.pdf),
(2.94), (2.97), (2.114)–(2.118), treats cyclic vectors and moment
pairings; the finite-support discussion after Theorem 2.13 gives the
finite Jacobi representative. It supplies no native topology, acquired
address map or installed root authority.

The pinned mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` contains the classical
[Gershgorin inclusion](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/Gershgorin.lean),
[Vandermonde determinant criterion](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Vandermonde.lean),
and [nonsingular rational matrix inverse identities](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean).
RGII §97 supplies their exact calibrated-window and root-overlap
application. It is that existing proof, not the existence of a theorem
name, which discharges the hypotheses in Proposition 112.5.

Burgarth and Maruyama, *Indirect Hamiltonian Identification through a
small gateway*, [arXiv:0903.0612v1](https://arxiv.org/abs/0903.0612v1),
§§II–IV, works with a known coupling graph, Heisenberg interaction,
known anisotropy, its coupling-sign and infecting-gateway conditions,
and its preparation/tomography access. A branching root is not
automatically such a gateway. Those results do not install this
unknown-tree calibrated rational source. They also do not turn exact
rational root reports into cost-free physical measurements.

The additional same-specimen composition and the prepared-image
correspondence in §§113–117 are `repo-derived`, with the ordinary proofs
given here. The call and width statements concern the stated attained
implementation. No `suspected-novel` or world-priority claim is made;
a changed notation, a module search or a failure to find a paper would
not establish one.

**Scope 120.4 (source-relative residual obligations).** The calibration,
authentic root, orientation, rights and actual pulse preparation are
explicit premises. An arbitrary unknown weighted tree or uncalibrated
uniform law is outside them. In particular RGII Proposition 103.1's
ordered uniform-root counterpair remains a counterpair in its exact
domain. The dense Rainbow/literal native degree-at-most-three mismatch
is untouched; no route through that mismatch is used here.

Theorem 113.4 covers all rational entrance fields under this calibrated
law, but the historical inverse covers only Definition 114.1's actual
fixed-length preparation and the acquired sampled cut. It does not
recover an arbitrary earlier journal, unknown provenance, chosen native
serial shuffle, raw busy-state history, revoked rights or inaccessible
archives. Section 116 covers the broader current service without making
that historical image invariant. Zero input and zero pulses are allowed;
they do not remove geometry's guard acquisition or genuine preparation
costs. Exact inversions and zero tests have no proved bounded-noise
replacement, uniform conditioning or fixed-precision implementation.

Raw-clock growing histories, a post-growth digital clock with disturbed
Read, and the calibrated-root process here are distinct installations.
No common actual apparatus or transferred precision/cost theorem is
asserted. No physical evolution law, universal alpha/beta minimum,
entry-state restoration or total resource optimum follows. All earlier
fixed-$G_{\rm gc}$, original-$Q$, parked-consumer, unchanged-initialization,
final-no-Ready and erased-history obligations retain their original
statements. They require their own source and task bridges. The bounded
joint-acquisition result therefore leaves the continuing four-expression
objective open outside these explicitly proved domains.

## 追加锚（本行以下为增补区）
