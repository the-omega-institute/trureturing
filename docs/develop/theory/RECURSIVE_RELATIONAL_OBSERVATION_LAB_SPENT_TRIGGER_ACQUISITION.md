# LAB spent-trigger acquisition at an unknown attained cut

> Continuation volume for the LAB source and service of [Atomic Generation
> Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md).
> The statements below are ordinary mathematics about the declared actual
> process. They are not Lean certification. The known-seed, no-reset,
> complete-frame, current-rights and finite-completion conditions of AA §§17,
> 20 and 32 remain in force.

This is an append-only `generic-v1` reference input. Incorporated text is
fixed; additions belong after the final empty append anchor. The new fibre
and tariff statements are `repo-derived`; the continued-service and view
conversions below are applications of their named suppliers.

## 1. The actual late-entry family

Write $A=S_L$ and $B=P_R$, where the addresses are measured from the root of
the LAB of AA §17. A successful $A$ makes the left child a branch and a
successful $B$ changes the right child from its born-$\alpha$ leaf to a
$\beta$ leaf. For a finite source $t$, let $E(t)$ be the labelled event set
of AA (AA.67), and let $\mathcal H(t)$ be its actual successful-event words.
The latter is the complete set of legal old interleavings, by Theorem 17.2;
it is not a pair of selected witnesses.
Interposed completed queries, refusals and bad frames do not enter the
successful-event projection or affect selection. Their old interleavings
are therefore included without an extra historical-control assumption.

**Definition 1.1 (the spent-trigger image).** Fix $n\ge2$. Let
$\mathscr I_n$ be the set of pairs $(t,\nu)$ for which

1. $t=\langle u,v\rangle$, $u$ is a branch and $v\ne\alpha$;
2. there is a word $w\in\mathcal H(t)$ with selected word $\nu$ for the
   selector in Definition 1.2 below.

For $(t,\nu)\in\mathscr I_n$, define the whole-history control fibre

$$
\Phi_n(t,\nu)=\{q_{F_n}(w):w\in\mathcal H(t),\ \nu_{F_n}(w)=\nu\}.
\tag{AA.135}
$$

The quantifier is over the actual image of the one allocated $\alpha$ root.
It does not quantify over arbitrary unknown seeds, arbitrary initial trees,
or an externally supplied history. The late entrant is given neither the old
word nor the hidden control; it may acquire only the complete replies of the
original service.

Let $\nu_L$ be the subword of $\nu$ whose event addresses begin with $L$ and
put

$$
H_R^n(t)=\{e\in E(t):\operatorname{addr}(e)\text{ begins with }R,\quad
                         |\operatorname{addr}(e)|\ge n\}.
\tag{AA.136}
$$

The notation $\operatorname{set}(\nu)$ forgets the order only for the
comparison in (AA.138); the selected word itself remains literal and ordered.

**Definition 1.2 (the known two-state selector).** Let $F_n$ have states
$0,1$, initial state $0$, and receive each actual successful event exactly
once. On $B$ it changes to $1$ and emits $0$; on $A$ it changes to $0$ and
emits $0$. On every other event it preserves its state and emits

$$
\lambda(q,e)=q\,\mathbf 1_{\{|\operatorname{addr}(e)|\ge n\}}.
\tag{AA.137}
$$

Requests, refused growths, ordinary queries, bad frames and waiting do not
feed the selector. This is the event-only selector of AA §30 with the two
spent trigger classes specialized to $A$ and $B$.

**Theorem 1.3 (exact whole-family control classification).** For every
$(t,\nu)\in\mathscr I_n$,

$$
\Phi_n(t,\nu)=
\begin{cases}
\{1\},&\nu_L\ne\varepsilon,\\[2mm]
\{0\},&\nu_L=\varepsilon\text{ and }\operatorname{set}(\nu)\ne H_R^n(t),\\[2mm]
\{0,1\},&\nu_L=\varepsilon\text{ and }\operatorname{set}(\nu)=H_R^n(t).
\end{cases}
\tag{AA.138}
$$

Every clause is restricted to the actual image. In particular, the formula
does not assert that an arbitrary proposed pair is realizable.

**Proof.** Every event strictly below $R$ requires $B$ first. Every event
strictly below $L$ requires $A$ first. Both triggers have depth one and hence
emit zero when $n\ge2$.

Consider any $w\in\mathcal H(t)$. If $A$ precedes $B$, the state is zero until
$B$, and thereafter it is one until the end of the word: $A$ and $B$ cannot
recur because $A$ is a split and $B$ is a promotion already consumed at the
fixed endpoint. Every high right event must follow $B$ and is selected.
High left events can precede or follow $B$; precisely those after $B$ are
selected. Thus $\operatorname{set}(\nu)$ contains $H_R^n(t)$ and may also
contain left events.

If $B$ precedes $A$, state one can occur only in the interval after $B$ and
before $A$. A selected event is therefore in the right cone, and it belongs
to $H_R^n(t)$. If a high right event occurs after $A$, it is not selected;
conversely every high right event before $A$ is selected. Hence final
control zero forces $\nu_L=\varepsilon$ and
$\operatorname{set}(\nu)\subseteq H_R^n(t)$, whereas final control one
forces $H_R^n(t)\subseteq\operatorname{set}(\nu)$. At an actual image with
no selected left event, the latter inclusion is equality. These facts give
the two singleton exclusions in (AA.138).

These observations prove the singleton alternatives in (AA.138). For the
remaining alternative, take any actual witness $w$ for $(t,\nu)$. Its
right-cone projection has the form $B\rho$ and contains every right event
of $E(t)$; it is a legal construction of the right subtree by Theorem 17.2.
Because $\operatorname{set}(\nu)=H_R^n(t)$, its high-event projection
is exactly the literal $\nu$: this is immediate for a final-one witness;
for a final-zero witness every high right event was selected before $A$.
Choose any legal left-cone construction $A\ell$. The cones are independent
after the common root prefix $r=P_\varepsilon S_\varepsilon$. The words
$rB\rho A\ell$ and $rA\ell B\rho$ are therefore legal complete constructions
of $t$. The first finishes in zero and the second in one. Every left event
occurs with state zero; every high right event occurs with state one.
Both selected words are the same literal $\nu$.

The construction uses the actual event prerequisites, not a free source
projection: every prefix is a legal extension supplied by Theorem 17.2.
AA Theorem 32.3 realizes each word by complete addressed growth requests
from the same initialized service, constructing its own marks and selected
tapes. The witnesses are alternative runs with the same bound-source and
authority roles, not independently assigned record tuples or a source copy.
Conversely, the preceding order argument applies to every member of
$\mathcal H(t)$, so no other final control occurs. This proves the exact
whole-family equality. $\square$

**Corollary 1.4 (nonempty selected-word ambiguity).** For $n=2$, after
the common root prefix, the two legal words

$$
B\,S_R\,S_{RL}\,A,
\qquad
A\,B\,S_R\,S_{RL}
\tag{AA.139}
$$

have the same endpoint
$\langle\langle\beta,\alpha\rangle,\langle\langle\beta,\alpha\rangle,\alpha\rangle\rangle$
and the same nonempty selected word $[S_{RL}]$, while their final controls
are $0$ and $1$. The low-depth event $S_R$ is not selected because its
address has depth one. Thus the ambiguity is not an empty-word artefact.

**Proof.** Apply the construction in the proof of Theorem 1.3. The
displayed words differ only in the relative placement of the two spent
triggers; the right subtree and its selected event are identical. $\square$

**Proposition 1.5 (persistent future distinguishability).** The two
controls in the last line of (AA.138) remain distinct under every finite
lawful future request sequence, and their complete seven-request tasks are
inequivalent at every reached MarkedReady cut.

**Proof.** At the endpoint in Definition 1.1 both $A$ and $B$ are spent.
All later events preserve the two controls. If future selected words differ,
FetchSelected already distinguishes them; if source terms differ, Tag does.
Otherwise their current $(t,\nu)$ is common. A reachable non-$\alpha$ LAB
source has a deepest $\beta$ leaf at the maximum logical leaf depth $D$:
a deepest $\alpha$ leaf is a right child. Its left sibling cannot be a branch,
which would have a deeper leaf, and cannot be $\alpha$ by birth typing.
It is therefore $\beta$ at the same depth. A deepest leaf already labelled
$\beta$ needs no sibling argument. Split
that $\beta$ leaf repeatedly along its left child until an event has depth
at least $n$. This is legal at every step and emits one on state one and zero
on state zero. FetchSelected at the common old length plus one returns a literal
identity in one run and OutOfRange in the other. If the selected event is
consumed by NextSelected instead, the old identity in its complete reply and
the selected successor still separate the runs. Thus the difference is a
future legal reply and successor, not a forgotten event that can never be
queried. $\square$

## 2. The four-state latch is a different observation

**Definition 2.1 (the absorbing latch).** For each $n\ge1$, let $L_n$ have states
$u,a,z_0,z_1$ and initial state $u$. Its state transitions are

$$
\begin{aligned}
\delta(u,A)&=a,&\delta(u,B)&=z_0,&\delta(u,e)&=u\quad(e\notin\{A,B\}),\\
\delta(a,B)&=z_1,&\delta(a,e)&=a\quad(e\ne B),\\
\delta(z_i,e)&=z_i&& (i\in\{0,1\}).
\end{aligned}
\tag{AA.140}
$$

All outputs are zero in states $u$ and $a$ and in state $z_0$. In state
$z_1$, the output on $e$ is
$\mathbf 1_{\{|\operatorname{addr}(e)|\ge n\}}$. Thus $u$ sends $A$ to
$a$ and $B$ to $z_0$; $a$ sends $B$ to $z_1$; and $z_0,z_1$ absorb.

For an endpoint $t$ satisfying clause 1 of Definition 1.1, define

$$
H_R^{4}(t)=\{e\in E(t):\operatorname{addr}(e)\text{ begins with }R, e\ne B,
                                      |\operatorname{addr}(e)|\ge n\}.
\tag{AA.141}
$$

For a pair $(t,\nu)$ in the actual image of $L_n$, let $\Phi_n^4(t,\nu)$ be
the set of final latch states over all actual histories with that endpoint
and selected word.

**Theorem 2.2 (four-state fibre and observation boundary).** On the
actual image of $L_n$ with an endpoint satisfying clause 1 of Definition
1.1,

$$
\Phi_n^4(t,\nu)=
\begin{cases}
\{z_1\},&\nu\ne\varepsilon,\\
\{z_0\},&\nu=\varepsilon\text{ and }H_R^4(t)\ne\varnothing,\\
\{z_0,z_1\},&\nu=\varepsilon\text{ and }H_R^4(t)=\varnothing.
\end{cases}
\tag{AA.142}
$$

The first line permits selected left events after the latch has entered
$z_1$. It does not identify the selected word with its right-cone subword.

**Proof.** If $B$ occurs first, the latch enters $z_0$ and selects nothing.
If $A$ occurs first, it enters $a$; after $B$ it enters $z_1$, and every
right event other than $B$ is then selected exactly when its depth is at least
$n$. The two triggers are spent, so these states cannot change later. This
proves the first two cases. If $H_R^4(t)$ is empty, finish all left work
between $A$ and $B$, then do all right work. The resulting $A$-first word
reaches $z_1$ with no selected events. A $B$-first construction reaches
$z_0$ with no selected events at the same source. These actual witnesses
prove exactly the empty ambiguous case. Every $z_0,z_1$ pair so obtained is
future-task inequivalent after every finite continuation: both controls are
absorbing, and the deepest-beta construction of Proposition 1.5 produces
a new threshold event and a differing selected reply. Unequal sources or
selected words are already separated by Tag or FetchSelected. $\square$

**Proposition 2.3 (selected observations are not conflated).** For the
$n=2$ endpoint and words of (AA.139), $F_2$ selects $[S_{RL}]$ in both
histories. The latch selects $[S_{RL}]$ on the $A$-first history and selects
nothing on the $B$-first history. Consequently these selectors have
different selected-word observations on the same actual source-history
family. No state-minimality assertion and no total-resource dominance
between them follows.

**Proof.** $S_R$ has depth one and is below the threshold. The two-state
selector has state one at $S_{RL}$ in both words: in the first word $A$ has
not occurred, and in the second word $B$ has already followed $A$.
The latch is already $z_0$ on the $B$-first word and
is $z_1$ after $B$ on the $A$-first word. The remaining claims are logical
scope restrictions: an observation-preserving simulation and a cost
comparison would require additional constructions and resource coordinates.
$\square$

## 3. Sharp incremental acquisition after paid stationary observation

**Definition 3.1 (the stationary prepass).** At a completed MarkedReady cut
of the same from-seed installation of AA Assumption 32.1, let
$s=|I(t)|$, $K=2s+1$, $m=|\nu|$, and

$$
J_t=\sum_{p\in\mathcal L(t)}|p|,
\qquad
D_\nu=\sum_{e\text{ occurring in }\nu}|\operatorname{addr}(e)|.
\tag{AA.143}
$$

The paid stationary prepass enumerates the present logical positions using
the Tag service and sends one Tag request for each of the $K$ positions. It
then sends FetchSelected$(1),\ldots,$FetchSelected$(m+1)$, stopping at the
first OutOfRange. It performs no source growth. This is the existing
AA §§20, 31 and 32 acquisition route; the prepass is a sufficient baseline,
not an asserted minimum.

After that prepass, consider either an ambiguous fibre in Theorem 1.3 or
an empty-word ambiguous fibre in Theorem 2.2. Let $D$ be the greatest
depth of a current logical leaf, with unary $\beta$ markers excluded, and
put

$$
g=\max\{1,n-D+1\},\qquad d^*=\max\{D,n\}.
\tag{AA.144}
$$

The requester has the complete original menu: Tag, $P$, $S$, both membership
queries, FetchSelected, NextSelected, refusals, BadFrame, all complete
payloads, End, acknowledgement and Return. It has no hidden control bit,
semantic oracle, reset, copy, external clock or free source field.
Its initial acquired information is precisely this paid $(t,\nu)$, the
common prepass transcript and public code; its policy and other initial
data are independent of which old history or control produced them.
Observations are the semantic replies of AA Definition 33.1, excluding
elapsed maintenance time, raw record/name reads and capacity telemetry.

**Theorem 3.2 (simultaneous sharp $G,R$ tariff).** For every actual
ambiguous fibre just specified, any deterministic effective finite-return
requester that returns a self-sufficient correct predictor for both possible
attained controls has, on each possibility,

$$
G_{\mathrm{inc}}\ge g,
\qquad
R_{\mathrm{inc}}\ge g+1,
\tag{AA.145}
$$

where $G_{\mathrm{inc}}$ counts successful $P/S$ events after the prepass and
$R_{\mathrm{inc}}$ counts every completed request after the prepass. A single
requester attains both equalities on both installations. If the stationary
fibre is a singleton, its incremental pair is $(0,0)$.

**Proof (lower bound).** Couple the two possible hidden controls at the
common actual $(t,\nu)$. The spent triggers cannot recur. Before the first
newly executed event of depth at least $n$, the controls have the same
complete replies and the same source and selected word. This remains true
for the whole menu: Tag and membership queries inspect the same source;
FetchSelected returns the same old word; refusals, BadFrame and OutOfRange
are identical; an addressed growth is the same legal source edit with the
same full reply; and NextSelected uses the same fetched old identity, the
same current left descent, and returns the same old and new identities. A
NextSelected call can grow once, but its reply does not expose the selection
bit of its new event.

Before the $h$th successful post-prepass event the greatest possible leaf
depth is at most $D+h-1$, because a split increases that maximum by at most
one and a promotion does not change it. The event's address is a current
leaf, so a threshold event requires $h\ge n-D+1$ and always $h\ge1$.
Thus at least $g$ growths are needed before any new selected discrepancy
exists. The request executing the first such event still has the same
complete reply in both runs. A further completed request is needed to
expose the new selected identity, for example FetchSelected$(m+1)$; using that identity as
the old input of NextSelected does not remove this extra request.

If a requester returned before that distinction, it would return the same
finite predictor on two reached tasks that Proposition 1.5 proves
inequivalent. Hence $G_{\mathrm{inc}}\ge g$ and
$R_{\mathrm{inc}}\ge g+1$ on each actual installation. This argument counts
all seven request kinds and complete replies, rather than restricting a
competitor to explicit growth commands.

**Proof (simultaneous upper bound).** The current source has a deepest
$\beta$ leaf $p$ at depth $D$. Issue the $g$ explicit split requests at
$p,pL,\ldots,pL^{g-1}$. Each is legal, and the last event has depth $d^*$.
The two controls agree on the first $g-1$ selection bits and differ on the
last: the high state selects it and the low state does not. Then issue
FetchSelected$(m+1)$. The high reply is the literal last event and the low
reply is OutOfRange. The requester now retains the reached source, its
literal selected word and the identified control, so AA §38's predictor and
AA §32's live continuation apply. Exactly $g$ growths and $g+1$ requests
were completed in this same run. $\square$

The upper-bound policy is uniform over this entire starting family: it
obtains $t,\nu$ by the prepass, applies the finite classification, and either
returns immediately or chooses the first deepest beta in source preorder.
Its retained predictor computes from earned finite data and public code,
without further live calls. No endpoint or successful old word is advice.

The pair in (AA.145) is an incremental optimum only. The stationary prepass
has not been optimized, and $R_{\mathrm{pre}}+g+1$ is a sufficient total
request count, not a total-request optimum. No optimum for bits, total work,
space, material, energy, weighted cost or lifetime is inferred.

**Corollary 3.3 (entry prediction versus reached live use).** Let
$(t_0,\nu_0)$ be the cut at which the prepass began and $(t_1,\nu_1)$ the
cut after the $g$ probes. The predictor returned by Theorem 3.2 is for
the reached task $(t_1,\nu_1,q)$. If the entrant also retains its paid
$(t_0,\nu_0)$ snapshot, the identified persistent control supplies a
service-free predictor for the entry task, with the same incremental probe
cost. That extra snapshot is memory and is charged; it does not restore the
old source or make the old cut callable. Actual subsequent requests use the
retained live binding and rights at $(t_1,\nu_1)$.

**Proof.** AA §38's normalization and AA §32's continuation are source-
relative. Proposition 1.5 makes the control persistent, so the same
identified control can be paired with a retained entry description. The
entry description is a separate object from the reached live source; no
operation in the contract rewinds the latter. For the entry target, the same
coupled-transcript lower bound applies because the two fixed entry tasks
are inequivalent; destructive probing does not change that target. Thus the
same $G,R$ pair is also incrementally sharp when the extra entry snapshot
is retained. $\square$

## 4. Exact same-run traffic and material contributions

**Proposition 4.1 (paid prepass traffic).** With the notation of
Definition 3.1, the prepass uses

$$
R_{\mathrm{pre}}=2s+m+2,\qquad G_{\mathrm{pre}}=0,
\tag{AA.146}
$$

and its request and reply payloads are

$$
\begin{aligned}
I_{\mathrm{Tag}}&=4K+2J_t,
&O_{\mathrm{Tag}}&=5K,\\
I_{\mathrm{Fetch}}&=\frac{(m+1)(m+2)}2+4(m+1),
&O_{\mathrm{Fetch}}&=5m+2D_\nu+3.
\end{aligned}
\tag{AA.147}
$$

Thus $I_{\mathrm{pre}}=I_{\mathrm{Tag}}+I_{\mathrm{Fetch}}$ and
$O_{\mathrm{pre}}=O_{\mathrm{Tag}}+O_{\mathrm{Fetch}}$.

**Proof.** A Tag request has the three-bit request tag and an address frame
$A(p)$ of length $2|p|+1$, hence $4+2|p|$ bits. A Tag reply has a three-bit
reply tag and a two-bit source tag, hence five bits. A FetchSelected request
at index $k$ has three tag bits and $U(k)$ of length $k+1$, hence $k+4$;
summing $k=1$ through $m+1$ gives the displayed triangular term. The first
$m$ replies are Recall payloads of length $5+2|\operatorname{addr}(e)|$;
the final OutOfRange reply has three bits. End, local acknowledgement and
root Return are separate service actions and are not hidden in these
payloads. $\square$

**Proposition 4.2 (probe traffic on the same run).** Let

$$
J=gD+\frac{g(g-1)}2.
\tag{AA.148}
$$

For the simultaneous upper-bound run in Theorem 3.2, the incremental
input bits and output bits are

$$
\begin{aligned}
I_{\mathrm{inc}}&=4g+2J+m+5,\\
O_{\mathrm{inc}}^{\mathrm{low}}&=5g+2J+3,\\
O_{\mathrm{inc}}^{\mathrm{high}}&=5g+2J+5+2d^*.
\end{aligned}
\tag{AA.149}
$$

There are additionally $g+1$ End symbols, local acknowledgements and
completed Returns.

**Proof.** The $i$th split request has address depth $D+i$ and therefore
input length $4+2(D+i)$ for $0\le i<g$; the successful reply has length $5+2(D+i)$.
Summing gives $4g+2J$ and $5g+2J$. The final FetchSelected$(m+1)$ request
has $m+5$ bits. Its low-control reply is OutOfRange with three bits; its
high-control reply is Recall for the last event and has $5+2d^*$ bits. The
frame conventions are exactly those of AA Definition 32.2. $\square$

**Proposition 4.3 (material and selector contributions).** In the same
probe run, the $g$ splits allocate exactly $2g$ new material source vertices
and $g$ new selected-record descriptors. They activate and initialize
$4g$ logical mark slots, perform $g$ event-mark writes and $g$ selector
evaluations. The high-control run appends exactly $d^*$ selected side cells
to ancestor tapes; the
low-control run appends none.

**Proof.** Each LAB split reuses the old unary marker as its left logical
$\beta$ root, allocates that child's new unary marker and the new right
logical $\alpha$ root, and AA §32 creates one descriptor at the
new branch and initializes two two-slot mark records. The selector is
evaluated once for each successful event, including an output-zero event.
The first $g-1$ probe events have depth below $n$ (or there are no such
events when $g=1$), so they are unselected in both runs. The last event has
depth $d^*\ge n$ and is selected only in the high run. AA §32's ancestor
maintenance appends one side cell per proper ancestor, giving $d^*$ cells.
These counts exclude pre-existing source, records, references, code,
workspace and grants, all of which remain charged. $\square$

The propositions deliberately withhold a total tariff. Candidate code and
classifier installation, prepass traversal, finite candidate simulation,
source navigation, address decoding, retained snapshots and indices,
buffers, counters, descriptor maintenance, fresh allocation, binding,
printing, End, acknowledgement, Return, clearing and all later calls have
their own actual widths and work. Finite selector code or a finite control
set does not bound the source, records or workspace. The formulas above are
same-run contributions, not separate coordinate optima combined into a
total-cost claim.

## 5. Earned predictor and the four meanings

**Definition 5.1 (the retained reached description).** After the
distinguishing FetchSelected call, retain

$$
b=(t_1,\nu_1,q),
\tag{AA.150}
$$

the public selector code, its classifier data, the predictor backing and the
original live source binding with current rights. The source and selected
records are earned descriptions reconstructed by AA §31; no empty late
archive, hidden raw field, reset, clone or new authority is installed.

**Theorem 5.2 (self-sufficient prediction and actual continuation).** On
every finite complete request word from the reached MarkedReady cut, $b$ computes
the complete reply and the corresponding successor without calling the live
service. Sending the same frame to the retained binding performs the actual
request on that source and yields the predicted reply and corresponding
successor. The two statements hold for adaptive finite request controllers
that choose later requests from earlier complete replies.

**Proof.** Theorem 3.2 gives the actual control and AA §31 decodes
$\nu_1$ from the earned source-local records. For a stationary request,
Tag, both membership queries and refusal guards are computed from $t_1$ and
AA (AA.67); FetchSelected is the literal indexed word, including checked
zero or missing indices. A successful explicit growth computes its actual
enabled event, updates $t_1$, applies the public selector once to the old
$q$, and appends the event to $\nu_1$ exactly when its bit is one. This is
AA (AA.106), with the event performed on the actual source in the live
service. The common frame parser also computes the unused-tag BadFrame
reply; a proper incomplete frame is still waiting, not a completed request.

For NextSelected, first decode the old selected identity from $\nu_1$. If
the index is absent, return OutOfRange with no growth. Otherwise navigate
that historical address in the current $t_1$, descend current left children
to a leaf, and execute its unique legal $P$ or $S$. The complete reply
contains both the old and new literal identities; only the new identity is
a selector receipt. This is exactly AA Definitions 20.4 and 32.2, including
old identities whose current positions are now branches.

Induction over complete requests proves equality of all replies and
successors. The predictor performs finite operations on the retained finite
description and public code; it is not a forwarding wrapper. The actual
continuation pays the original frame, source edit, record maintenance,
output, End, acknowledgement and Return costs on the same live binding.
Predicting a counterfactual does not execute it. $\square$

**Proposition 5.3 (independent expressions and route agreement).** On
the completed reached image, fix the installed public code and the actual
binding/authority roles as in AA Definition 33.1. The following four
observations retain distinct meanings. Their semantic content descriptions,
modulo fresh-name spellings and backing-layout choices, are mutually
recoverable through (AA.150), with route agreement and request-dynamics
compatibility:

1. **Space** is the oriented support of the actual source, including the
   material unary $\beta$ marker, together with source-indexed selected
   membership and branch-side annotations and the earned control.
2. **Boundary** is the actual terminal antichain with those source-indexed
   annotations and the earned control. It is not a chronology record.
3. **Time** is the labelled lifecycle causal order recovered from $t_1$,
   together with the literal selected serial chain $\nu_1$ and control. It
   omits the forgotten unselected linear extension, controller microsteps,
   elapsed durations and an external clock.
4. **Memory** is the actually retained $(t_1,\nu_1,q)$, predictor/code
   backing and callable binding/current rights. It is the declared memory
   observation, not the whole installation and not a uniform storage bound.
   Its semantic description keeps the fixed code and binding/authority
   roles; it does not expose arbitrary implementation bytes.

**Proof.** AA Theorem 17.2 converts the actual source to its causal event
order; AA Theorem 31.2 converts $(t_1,\nu_1)$ to the selected local marks
and side tapes; and AA Theorem 33.2 converts the oriented source and its
terminal antichain to the space/boundary pair. AA Theorem 38.2 preserves
the behavior kernel under the earned residual control, while AA §45 gives
the same-source prediction/continuation transport. Every route first
reconstructs (AA.150), so routes agree and each complete request has the
same legal reply and semantic successor. These are finite conversions of
descriptions on their actual images. AA Theorem 32.3 supplies the real live
objects and service, separately from those conversions. No installed
serializer for every view, creation of rights or callable handles,
reconstruction of arbitrary code backing, forgotten controller
microhistory, root, clock or source copy follows from a semantic inverse.
$\square$

The entry description $(t_0,\nu_0)$ from Corollary 3.3 may be retained as
an additional memory object when entry prediction is required. It is not
silently identified with the reached source, and its backing is an extra
same-run charge.

The information requirements are conditional on this task. Unequal sources
have a separating Tag request; unequal selected words have a separating
FetchSelected request. At a common ambiguous $(t,\nu)$, Proposition 1.5
forces two residual behavior classes, so any self-sufficient retained
summary must distinguish them. One binary control value suffices for that
remaining distinction; this is AA Definition 38.4's conditional bound,
not a proof of selector-state minimality or a one-bit memory installation.
Orientation, literal event kind/address and the alpha/beta distinction
retain their independent roles in source navigation, indexed recall and
the different $P/S$ guards. The live binding and rights are indispensable
operational supplies for actual edits, separately from enough information
to predict them. Bare support or boundary without the selected annotations
and earned control has not been proved sufficient.

## 6. C-dagger boundary and attribution

The fixed two-state selector $C^\dagger$ of AA §39 is a useful boundary
comparison, not a second acquisition theorem here. Its bounded simulation
table gives the attained-cut reduction and undecidability of AA Theorem
39.2 and Corollary 39.3.
Nevertheless, at a branch, following current left children reaches a
pure-left beta leaf: the first such child is born beta, and each further
left child created by splitting is again born beta. Its split is legal and
AA Definition 39.1 sends either old control to zero with output zero. If the
current source is a root leaf, its only possible prior successful event is
the root promotion; that event preserves initial control zero. Thus paid
source acquisition followed, when needed, by that ordinary split makes the
reached residual control known, without identifying the old control or
deciding the old static equality problem. The actually acquired old
selected word remains available and the new split adds no selected event.
This is the identification/homing distinction already made in
[Acquisition and Return §7](RECURSIVE_RELATIONAL_OBSERVATION_ARITHMETIC_ACQUISITION_RETURN.md#7-entry-identification-homing-and-literal-integer-return),
as applied to AA's explicit table. It adds no reset primitive, unknown-seed
claim or separate generic homing result.

The source-specific new content of this continuation is Theorem 1.3's
actual-image, all-interleaving fibre equality (including (AA.139)), the
non-conflated latch comparison, and Theorem 3.2's simultaneous sharp
incremental tariff with the complete original menu. AA §§17, 20, 31, 32 and
38 supply the LAB legality, full frames, acquired records, actual
NextSelected successor and continuation machinery. AA §§41–45 supply the
candidate/remaining-relation language and the known-alpha threshold baseline;
they do not supply the spent-trigger all-history fibre, its nonempty selected
word case, the $\max\{1,n-D+1\}$ tariff, or the full-menu lower bound here.
The coupled-transcript and final-fetch proof method itself is already
AA Theorem 42.2's method. Its known-alpha-root, unknown one-state-installation
tariff is $n+2,n+3$; here the unknown is an actually attained control of one
known selector, and the paid current source changes the sharp depth bill.
The new family classification is needed to identify exactly when that bill
is required rather than zero.

The existing [binary recut fibre declarations](../../../D5/S3/ObserverMemory/BinarySelectorRecutFibers.lean)
and [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/BinarySelectorRecutFibers.scribe.cs)
use two supplied length-$m$ binary words and a selector bit, with strict
append/delete experiments. Their fibre and supplement proofs are credited
methods; those parameters and legal experiments are not LAB histories.
[EnabledPathSwapConnectivity](../../../D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.lean)
and its [Scribe](../../../Blueprint/D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.scribe.cs)
give the abstract finite-poset extensions and legal swaps; AA §17 supplies
their actual LAB guard correspondence. The existing
[controlled behavior transport](../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean),
[predictive quotient](../../../D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.lean)
and [typed complete-response kernel](../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean),
with the owning Scribes linked in AA §35, require their specified finite
carriers or readout/update factors. Finite selector code does not make
this growing source/record installation a finite carrier.
[AdaptiveSeparationDepthUpperBound](../../../D5/S3/Observer/Budget/AdaptiveSeparationDepthUpperBound.lean)
and its [Scribe](../../../Blueprint/D5/S3/Observer/Budget/AdaptiveSeparationDepthUpperBound.scribe.cs)
assume a finite candidate set with pair-separating readouts;
[NativeFullSourceProducer](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean)
and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs)
acquire a stationary Native tree through Native reads. These contracts do
not provide the LAB spent-trigger fibre or its menu-specific tariff.
[ClosureUndecidable](../../../D5/S0/Computability/ClosureUndecidable.lean)
and its [Scribe](../../../Blueprint/D5/S0/Computability/ClosureUndecidable.scribe.cs)
apply Rice's nontrivial extensional-code criterion; they supply no active
acquisition impossibility for this fixed selector.

In [NCR §§5,8](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md),
recovery uses an earned Native seed and an actual primitive-prefix index,
or an acquired command-order complement. In
[SC §§2–5](RECURSIVE_RELATIONAL_OBSERVATION_SPATIAL_RECORDS_CHRONOLOGY.md),
the held precedence bit repairs overlapping marker records on its own
positive selected cell; the bare four expressions are not all independently
sufficient. These results credit retained-order and recovery methods, not
an unknown LAB trigger-state reader. [LAB Arithmetic Growth §§5,7](RECURSIVE_RELATIONAL_OBSERVATION_LAB_ARITHMETIC_GROWTH.md)
earns counts at a late source and retains synchronized arithmetic fields;
its scalar task does not recover source or the full LAB request menu.
At the separate immutable source
[`88c3790`, History–Clock Arithmetic Memory §§2,10](https://github.com/the-omega-institute/trureturing/blob/88c3790fe7f1f3a5fad7df772f431a7a459bba16/docs/develop/theory/AURIC_FIB_HISTORY_CLOCK_ARITHMETIC_MEMORY.md),
the positive initial source is known and the event index is supplied; its
unknown-seed common-initialization condition expressly does not acquire
the common residue. At that same revision,
[All-Response Finite-Fibre Geometry §§25–27](https://github.com/the-omega-institute/trureturing/blob/88c3790fe7f1f3a5fad7df772f431a7a459bba16/docs/develop/theory/FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md)
uses three actual real replies $(p,u,m)$ from a matrix source with one
polynomial gain and drift. Its collisions and local saturation do not
supply LAB selection records, growth depth or original-menu acquisition.

The pinned mathlib
[`Computability/DFA`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/DFA.lean)
defines `evalFrom` by a left fold and supplies `evalFrom_of_append` and
`evalFrom_append_singleton`; ordinary state iteration is reused here.
[Frohme, *Active Automata Learning with Adaptive Distinguishing Sequences*,
§8.1](https://arxiv.org/html/1902.01139v1) is `literature-attested` for a
symbol-query oracle with separate reset queries in a finite Mealy learning
framework. [Van den Bos–Vaandrager, *State Identification for Labeled
Transition Systems with Inputs and Outputs*, Definitions 5, 7–10 and
Lemma 6](https://arxiv.org/html/1907.11034v2) requires tests valid for the
states being distinguished and addresses finite suspension automata.
Their classic distinguishing methods supply neither resets nor
finite-state bounds to this unbounded LAB installation.
[Turing, *On Computable Numbers*, §8, printed p. 248](https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf)
rules out a uniform designated-symbol-printing decider; that existing
endpoint underlies AA's $C^\dagger$ reduction and gives no obstruction to
the positive theorem here. These are bounded supplier correspondences,
not a worldwide originality claim. Traversal, finite enumeration or
elimination and transport are reused. No new Lean certification or
executable enumeration is claimed.

The result remains bounded to an actually allocated alpha root, the declared
LAB requests, a stable completed MarkedReady cut, current exclusive rights,
sufficient finite material and no concurrent writer, revocation, crash or
observable capacity branch. It does not settle arbitrary unknown-seed
acquisition, full unselected chronology recovery, physical
age, universal four-expression reduction, state minimality, total-resource
dominance or a total-cost optimum. All earlier fixed-model and original
consumer obligations retain their original scopes.

## 追加锚（本行以下为增补区）
