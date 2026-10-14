# Recursive relational observation: autonomous serial literal delivery

## 1. The source, the cut and the two execution metrics

**Definition 1.1 (the unchanged original task).** Let $\mathcal T$ be the
free algebra of nonempty finite ordered full binary trees, with generators
$\alpha,\beta$ and pairing $\langle\ ,\ \rangle$. Put

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle v,w\rangle=\langle\rho v,\rho w\rangle.
$$

For public $h\ge1$ and $T\ge0$, the original $u$ ranges over **all**
$h$-leaf ordered full trees, with independently chosen labels
$\alpha=0,\beta=1$. Its shape is not supplied. Entry is $y=\rho^t u$,
where $0\le t\le T$ is unknown. The target is the original leaf XOR
$\pi(u)$, at the first fixed-bit Halt. Initialization is the same for
all $(u,t)$ in this promise.

For a whole materialized word $p\in\{L,R\}^{*}$, $r_y(p)$ follows the
address from the root, reports the reached constructor, and reports
absent if it attempts to continue beyond a leaf. The only source
operations are

$$
\operatorname{Read}(p):(y\mapsto y,r_y(p)),\qquad
\operatorname{Update}:(y\mapsto\rho y,\star).
$$

Read has four replies $\alpha,\beta,\mathsf{branch},\mathsf{absent}$;
Update has the constant acknowledgement $\star$. No reset, copy,
rerooting, inverse, source walk, partial-address query, historical row,
reference label, shape, epoch, size or timing observation is added.
Physical execution of these two primitives is a separate service. An
address transport does not construct their physical internals.

**Definition 1.2 (the macro supplier and its observations).** Write
SLHC for [Sparse Literal History Transport Continuation][SLHC12]. Its
Definitions 1.3 and 11.1 give the original complete macro observer:
$W\subseteq L_\ell$, where $L_\ell$ consists of length-$\ell$ binary
words without adjacent ones; one whole-word row selects one fixed
literal Read, Update or fixed-bit Halt. A primitive reply immediately
selects a hold or one-coordinate change $\delta(w,r)\in W$ and is
otherwise discarded. Every installed row counts, reachable or not.
The macro trace retains each selected row, each exact address, each
raw reply, each actual current tree and source successor, and the
first Halt. In particular the root routing Reads of SLHC Construction
11.6 are part of this trace. They are not silent local operations.

The positive regimes are $T=0$ for every $h$, and positive finite $T$
for even $h$. SLHC §§10–11 at [the fixed supplier revision][SLHC11]
provide complete correct macro controllers in those regimes. SLHC
§12 supplies capped variants and literal bounds on the same family.
These are conditional source and whole-word services, not an
implementation of selection or literal delivery with absent cursors.

**Definition 1.3 (an autonomous delivery frame).** Fix one immutable
installation, independent of the actual source. A complete composite
configuration $c\in\mathcal C$ includes all persistent sender,
mailbox, receiver, control, workspace, instruction and return counters,
ROM and work head positions, payloads, length fields, stage flags,
response latches and continuations. Immutable data contain bits, not
an advancing head or a source-dependent position. $S_{\rm inst}$ is
$|\mathcal C|$, including installed but unreachable configurations.
If configurations are encoded in $L_L$, then
$S_{\rm inst}\le F_{L+2}$, with $F_0=0,F_1=1$.

A Read frame starts at a returned macro cut with a selected original
Read. Until its final source-facing Read it is deterministic,
time-homogeneous and source-quiescent. Every step is selected by the
current counted configuration and the fixed installation. Local steps
can inspect only this configuration and installed bits. A transport
step carries at most one address letter. Delimiters, handoffs, local
work, initialization and any allocation are paid occurrences, too.
There is no external scheduler, advancing ROM head, clock or input
word position. No source reply, including a reply to a proper prefix,
occurs before commitment.

For an original Read$(p)$, the concatenation of address letters actually
arriving at the final receiver must be exactly $p$, in order. A compressed
wire program does not count as those letters: its local expansion and
subsequent literal arrivals must occur within the counted frame.
The receiver has an actual accumulated payload and a completed frame
boundary. A decoding of this receiver-owned information gives the
committed literal. At commitment that literal must equal the original
macro literal. A source-row name may select the sender's data; it may
not replace the received payload at the final call. The source sees
exactly one original Read after this frame. Updates and Halt have
finite local preparation followed by exactly their original operation.

This is a minimal sufficient interface contract, not an assertion of a
unique smallest machine. It permits compressed receiver representations
if they represent the actually arrived prefix and their updates,
decoding, persistent fields and final materialization are paid and counted. A nonreceiving output trace is not such a receiver.
A source-walk interface would be a different source contract.

**Definition 1.4 (separate resource coordinates).** On one run ending
at its first Halt let $Q,U$ count original Reads and genuine post-entry
Updates, $A=\sum_{i=1}^Q|p_i|$, and
$P_{\rm run}=\max_i|p_i|$, with maximum zero for an empty list. Let $E$
count letters arriving at the final receiver, and $I$ count all local
and transport occurrences, including delimiters and head movements but
excluding the $Q+U$ source calls and Halt itself. Distinguish these from
the worst-run suprema, the installed menu
$\mathcal M=\{p:\text{some installed Read row selects }p\}$, its
cardinality $M$, and $P_{\rm inst}=\max_{p\in\mathcal M}|p|$.

Complete mutable width $L$, installed configuration count, immutable
code/table/provider bits, compilation and installation peaks, native
calls, literal traffic, local work, and physical source-service costs
are distinct coordinates. There is no rule replacing an installed
union by one run's $A$, or a bit count by its logarithm without changing
the meaning of the coordinate. Initialization is a paid source-independent
service; its state is included in the peak allocation.

## 2. Literal bounds consumed at the serial cut

**Definition 2.1 (precise use of the literal supplier).** SLHC Theorem
12.3 is used with its all-shape domain, independent original labels,
common initialization, genuine adaptive Updates and full root-relative
literals. Its larger comparison class permits deterministic source-free
internal steps with all state counted and arbitrary local writes.
For every correct controller in a positive regime it supplies $Q\ge h$
on every promised run and **one** promised run satisfying

$$
P_{\rm run}\ge h-1+\lfloor T/2\rfloor,
\qquad
A\ge A_0(h,T):=\frac{(h-1)(h+2)}2+h\lfloor T/2\rfloor.
\tag{2.1}
$$

Here its $\lceil\max(T-1,0)/2\rceil$ equals $\lfloor T/2\rfloor$.
The statement includes $T=0$ and the $h=1,T=0$ boundary. With a
worst-run Update cap $v$, it also supplies

$$
M\ge 2^{h-1}\left\lceil\frac{T+1}{v+3}\right\rceil.
\tag{2.2}
$$

The same-run witness is the all-$\alpha$ comb at entry $T$, compared
separately against each one-leaf flip. Its first separating Read in
that leaf's original cone has suffix $s$ at the same accumulated
Update count $a$. The supplier's guarded windows give
$T+a\le\#_L(s)+2\#_R(s)+1\le2|s|+1$.
The distinct leaves give distinct occurrences on that fixed run.
Its cone argument does not require a reset, a shape port, a reply to a
prefix, or a stationary source across different source calls. This is
the premise correspondence for consuming (2.1), not a new literal
lower-bound theorem.

For a finite composite installation, every commitment configuration
selects one fixed finite decoded literal. Treat its earlier local
steps as the supplier's counted source-free steps. Thus (2.1)–(2.2)
apply to the composite as well as to the original macro supplier.
Only terminal configurations select fixed Halt bits. Deterministic
local transport contributes no new source distinction to the first
separation argument.

**Theorem 2.2 (source-specific autonomous progress and work).** In a
positive regime, every correct terminating finite autonomous serial
observer satisfying Definition 1.3 obeys

$$
\boxed{\quad S_{\rm inst}\ge h+\lfloor T/2\rfloor+2.\quad}
\tag{2.3}
$$

Consequently an encoding in $L_L$ obeys
$F_{L+2}\ge h+\lfloor T/2\rfloor+2$; in particular the weaker bound
$F_{L+2}\ge h+\lfloor T/2\rfloor$ also holds. With worst-run cap $v$,

$$
F_{L+2}\ge S_{\rm inst}\ge
2+\max\left\{h+\lfloor T/2\rfloor,
2^{h-1}\left\lceil\frac{T+1}{v+3}\right\rceil\right\}.
\tag{2.4}
$$

On every faithful run, $E\ge A$ and $I\ge E$. On the very same run
of (2.1), $E,I\ge A_0(h,T)$. These conclusions allow adaptive Updates
without a cap in (2.3) and in the work bound.

Proof. Choose the long-Read occurrence on the run supplied by (2.1)
and let its literal length be $p$. In its frame choose the complete
configurations immediately before its $p$ required arriving letters
and immediately before the final source Read. More generally, every
configuration from frame entry to that source-call cut is distinct.
If two were equal, deterministic time-homogeneous source-free
continuation from them would be equal. Following the earlier copy of
the segment would return to the same configuration forever, instead of
reaching its first source operation. A later copy cannot be the first
source-call configuration either: the earlier copy would already select
that same source instruction. Hence there are at least $p+1$ distinct
nonhalting configurations. Both target bits occur in the source family,
so there are at least two different fixed-output Halt configurations,
none among these $p+1$ configurations. Therefore
$S_{\rm inst}\ge p+3\ge h+\lfloor T/2\rfloor+2$.

The finite-configuration argument is the classical complete-configuration
argument: a head position belongs to the configuration, not merely its
finite control label; compare Turing, §§1–2, pp. 231–232 [TURING]. Its
application here is to the source-specific long literal, not to an
arbitrary new serializer result. It remains valid with arbitrarily
large but fixed parameter-dependent ROM: at a repeated configuration
the same ROM position sees the same bit. A changed position is a changed
counted configuration. Extra local steps only strengthen the count.

Each distinct installed committed literal requires at least one
commitment configuration. The two Halt outputs are disjoint from those
configurations. Combine this fact with (2.2) and (2.3) by taking a
maximum, not a sum of potentially overlapping nonhalting states.
Finally each actual payload contains all $|p_i|$ letters of that Read;
a one-letter transfer cannot deliver two of them in one occurrence.
Summation over the actual occurrences gives $E\ge A$. No installation
union or separately optimized input is used in this sum. ∎

**Corollary 2.3 (the surviving source-time/memory statement).** Uniformly
in every positive regime, a complete autonomous no-$11$ width satisfies

$$
L\ge\frac14\bigl(h+\log_2(T+1)\bigr).
\tag{2.5}
$$

For fixed even $h$, no bound on this width independent of $T$ can
hold, even with unrestricted genuine Updates and a fresh immutable
installation for each $(h,T)$. SLHC Theorem 10.3's active macro width
$\Theta(h)$ and SLHC Corollary 12.4's capped macro width remain claims
about their stated conditional macro services.

Proof. From (2.4), even without a fixed finite cap, the all-shape
comb union gives $S_{\rm inst}\ge2^{h-1}+2$: its proof needs only that
each tip has some separating literal. Equivalently use the finite
worst-run cap of this one installation; there are only finitely many
promised $(u,t)$ and each run terminates. Since $F_{L+2}\le2^L$,
$L\ge h-1$. Equation (2.3) gives
$L\ge\log_2(T+1)-1$ and also $L\ge2$. Writing
$X=h+\log_2(T+1)$, these imply $L\ge X/2-1$; for $X\ge4$ use
$X/2-1\ge X/4$, and for $X<4$ use $L\ge2$.

The old macro contract leaves literal delivery a conditional service
with no extra persistent field. Adding a real counted sender and
receiver changes the measured system. It does not refute the macro
construction or its one-bit responses. Increasing $U$ can reduce its
retained clock-cell information; it cannot make an autonomously
terminating source-quiescent long frame fit a bounded number of complete
configurations. ∎

## 3. Payload fidelity and obstructions to weakened refinements

**Definition 3.1 (trace erasure and the simulation obligation).** A
microtrace includes every paid local and transport occurrence and each
original source-call occurrence with its selected macro row, actual
literal, raw reply and source successor. Its erasure deletes only the
new local and transport occurrences. It keeps every macro routing
Read, every Update, each raw reply and the first Halt bit.

A refinement has a relation to macro configurations $(y,w)$ at every
cut. Before a source response it relates to the old $(y,w)$; at its
actual receipt it relates to $(y',\delta(w,r))$. Local cleanup must
maintain that latter relation while preparing the next returned cut.
A partially updated representation may use a counted saved old row and
reply latch to define this relation. Such a projection is proof data;
its computation is not a runtime port. The runtime must actually finish
the paid continuation it describes. At returned cuts the next selected
original instruction must be precisely the one at the related word.

Micro-observation labels may expose local instructions, head movements,
transmitted symbols and local fees. Before response receipt they must
be functions of the public installation and already acquired original
prefix. The same deterministic simulator, stopped at any cut, generates
these labels and consumes each raw source reply only at its actual
receipt. Source internals, duration and unreleased source data remain
outside this observation alphabet.

**Proposition 3.2 (paired failures of four apparent shortcuts).** Each
of the following weakenings loses a specified obligation of Definition
3.1, even on small ordered trees or finite literal frames.

(a) A sender declared to have one state emits $R$ whenever requested,
while an external head scans $R^n\#$ and stops it at the marker.
Compare the realizations with markers after $n$ and after $n+1$ letters.
Their declared sender states are identical, but their termination and
payload lengths differ. The omitted tape-head position or scheduler
position distinguishes their futures. Alternatively let that sender
feed an append-only receiver whose stored length is omitted from the
configuration. Identical declared configurations then have different
receiver lengths and different committed addresses. Immutable copies
of the two strings do not eliminate these mutable positions.

(b) Take the two $h=2,T=0$ sources
$\langle\alpha,\alpha\rangle$ and
$\langle\beta,\alpha\rangle$, and the committed address $LL$.
Both whole-address replies are absent. Feedback at the premature
prefix $L$ instead gives $\alpha$ and $\beta$. With equal initialization,
request and no earlier acquired reply, no prefix-causal simulator can
produce that distinction. Calling this feedback a transport
acknowledgement does not make it source-independent.

(c) On those same two sources, a nominal $\operatorname{Read}(LL)$
replaced at commitment by $\operatorname{Read}(R)$ returns $\alpha$
on both, instead of absent. Even if a downstream policy ignores this
reply and happens to output the same target, its raw trace and actual
address have changed. In a second realization emit $L$, then commit a
fresh row lookup of $R$: the accumulated payload is $L$, and on
$\langle\beta,\alpha\rangle$ its required reply is $\beta$ whereas the
lookup returns $\alpha$. Decorative output does not implement payload
fidelity. Receiver sufficiency requires a decoding from received
content, not merely a causal correlation with the sender's row name.

(d) On $\langle\alpha,\alpha\rangle$, insert an unreported Update
inside a nominal Read$(L)$ frame. Its answer becomes $\beta$ instead
of $\alpha$, and its successor is
$\langle\beta,\beta\rangle$ instead of the unchanged source. The
same failure occurs at a later committed address whose raw reply
happens not to change: the genuine source successor is still wrong.

Proof. In (a), equal complete deterministic configurations cannot have
the two described remaining times to first commitment; the differing
position must therefore be counted or the autonomous premise is false.
In (b)–(d), evaluate Definition 1.1 on the displayed trees. The resulting
pairs violate respectively precommit observational equivalence, exact
committed-address/reply preservation and source-successor preservation.
All source examples use the original ports. ∎

**Proposition 3.3 (receiver distinguishability versus flat capacity).**
Let $\mathcal P$ be a set of completed payloads possible at a specified
receiver cut in one installation. Suppose the committed literal is a
function of the receiver configuration alone, with fixed common decoder
data and no sender-row side information. Then different members of
$\mathcal P$ require different receiver configurations. In particular
receiver capacity is at least $|\mathcal P|$. This does not imply $P$
mutable bits from the occurrence of one word of length $P$.

Proof. If two different words had the same receiver configuration,
its decoded literal would have two values. For a counterexample to the
bit inference, a receiver for $\{R^0,\ldots,R^P\}$ can accumulate the
number of received $R$s in $\lceil\log_2(P+1)\rceil$ bits. It must also
count its receipt/termination control and any subsequent rendering
head; eventual flat materialization is an additional allocation under
an interface demanding literal cells. The configuration-progress
argument of Theorem 2.2 still applies during autonomous rendering.
This example is a representation distinction, not a complete compressed
solution of the all-shape parity problem.

If a receiver can receive all $2^P$ words of length $P$ with the same
other retained data, the distinguishability argument instead forces
at least $P$ bits in it. That premise has not been deduced from (2.1).
A receiver with $P$ individually mutable materialized cells has that
capacity by its chosen allocation, even if only one such word is ever
used. Neither statement identifies a sharp total-memory minimum. ∎

## 4. A delimited attainable refinement of the actual parity tables

**Definition 4.1 (the delimited macro input).** Choose one complete table
$C$ from SLHC §§11–12 in its positive regime. Let $\ell,W_*,P,n_R,n_U$
have that table's meanings, including all unreachable rows; take $P$
to bound **all installed** literals. The original table has four Halt
rows and $n_R=W_*-4-n_U$. Its explicit padded image, denoted $T_0$, has
length

$$
T_0=W_*\bigl(\ell+2+\lambda(P+1)+P+4\lambda(\ell+1)\bigr),
\qquad \lambda(a)=\lceil\log_2a\rceil.
\tag{4.1}
$$

Each response slot stores hold or the index of the single native bit
to flip. The native initial word uses $\ell$ additional immutable bits.
All literals and response slots are already fixed mathematical data.
No current shape, source epoch or source-derived position is an
installation input. For $P=0$, zero-length payload fields are allowed.

The refinement uses the **paid sequential interpreter mechanism** of
[Effective Acquisition Horizon, Proposition 8.1][PH81] and the **owned
copy mechanism** of [Transport Memory Completion, PR57.D7][PR57]. The
following parameterization specifies the parity consumer. It is not a
new general serializer or an application of those suppliers' different
source theorems.

**Definition 4.2 (the installed parity graph).** Enumerate the $W_*$
native words in the supplier's binary-bank order. Replace each word
by a block of $P+16$ graph nodes, including unused nodes; hence

$$
N=W_*(P+16),\qquad w_G=\max(1,\lceil\log_2 N\rceil).
\tag{4.2}
$$

For a Read word with literal $p=p_1\cdots p_d$, its block has these
nodes in this fixed order. Node 0 invokes RESET. Nodes $1,\ldots,P$
invoke PUT($p_i$) if $i\le d$ and NOP otherwise. Node $P+1$ invokes
COPY; node $P+2$ is ISSUE-READ. Nodes $P+3,\ldots,P+6$ test in order
$f_\alpha,f_\beta,f_{\mathsf{branch}},f_{\mathsf{absent}}$, stopping
at the first set bit; an all-zero or wrong-typed result goes to the
error control. Nodes $P+7,\ldots,P+11$ are the five typed LINK nodes.
The LINK for $r$ names the node-0 address of the block for
$\delta(w,r)$. The unused star LINK has an error successor. Nodes
$P+12,\ldots,P+15$ are error nodes. Tests have at most two successors;
all other used nodes have one.

For an Update word, RESET and the $P$ NOP nodes are followed by a
COPY bypass and ISSUE-UPDATE. The first response-test node tests
$f_\star$ and selects its LINK; other response nodes are unused error
nodes. For a Halt word, node 0 is HALT0 or HALT1 with that word's
fixed output; every other node of its block is an error node. ERROR
is a source-free nonhalting hold. Unused code fields and outgoing
slots are fixed zero padding. Node labels distinguish sixteen local
command/test/output labels, enough for RESET, PUT0, PUT1, NOP, COPY,
ISSUE-READ, ISSUE-UPDATE, four Read tests, the star test, LINK, ERROR,
HALT0 and HALT1. Thus $\sigma=4$ label bits suffice.

Use PH8.1's fixed row format: three opcode bits, three legality bits,
three $w_G$-bit successor slots, and a $\sigma$-bit label. Opcode and
label select the fixed local routine; source issues have their own
opcode. Four raw Read replies are handled by the five counted flags
and the binary tests, not by a nonexistent four-way PH response slot.
All fair-bit instructions are unused. A self-delimiting header $H_G$
gives $N,w_G,16,4,T_0,\ell,P$ and the initial node. Its bit length is
$|H_G|$. The retained graph and original dictionary length is

$$
T_G=|H_G|+N(6+3w_G+4)+T_0+\ell.
\tag{4.3}
$$

For example encode these eight nonnegative integers as Elias gamma
codes of their value plus one, in the displayed order. Offsets are
computed after parsing the header. No header-length fixed point is
used. Retaining $T_0$ is redundant but explicit, as in PH8.1.

**Definition 4.3 (local operations and complete fields).** The fixed
interpreter has sequential ROM and work access: read or write the
currently addressed bit, move a head by one cell, branch on one bit,
or make a fixed finite-control transition. There is no whole-word
random access. Seeking a row means moving through the intervening
cells. Registers containing a successor index are bit strings copied
one bit at a time; equality, increment, comparison, offset calculation
and bounded addition are bit loops with carry and loop state. ROM
fetching, routine entry/return and instruction selection have counted
PCs and heads. Each local instruction includes its finite-control
continuation in the same paid occurrence. A local move can change the
binary head encoding and PC in several coordinates; a local array write
can change its one data cell and the counted stage bits together.
These are charged local instructions;
**local instructions have no one-bit write restriction**. The one-bit
restriction below is imposed at actual source-response receipt.

There are three disjoint flat arrays of $P$ bits: sender $S$, mailbox
$B$, receiver $D$. Their cells remain allocated even when erased or
unreadable. They coexist with the entire installed image. For
$P=0$ each has no cells. The complete integer slots, each of width
$r$ specified in Definition 4.6, are the following thirty-two fields.

| Slot | Meaning |
| --- | --- |
| 1 | Current graph node |
| 2 | Pending graph successor |
| 3 | Saved graph/routine return node |
| 4 | Interpreter PC |
| 5 | Saved fixed-routine return PC |
| 6 | Code head |
| 7 | ROM head |
| 8 | Work head |
| 9 | Installation input head |
| 10 | Table address |
| 11 | Row base |
| 12 | Row offset |
| 13 | Field position |
| 14 | Field length |
| 15 | Row width |
| 16 | Sender occupied length $d$ |
| 17 | Sealed mailbox length $b$ |
| 18 | Receiver occupied length $a$ |
| 19 | Sender head |
| 20 | Mailbox head |
| 21 | Receiver head $q$ |
| 22 | Copy loop index |
| 23 | Clear loop index |
| 24 | Bit-operation loop index |
| 25 | Literal capacity $P$ |
| 26 | Graph node count $N$ |
| 27 | Graph index width $w_G$ |
| 28 | Image/table end |
| 29 | First arithmetic temporary |
| 30 | Second arithmetic temporary |
| 31 | Installation output head |
| 32 | Bounded routine/field continuation |

Sixty-four Boolean fields contain five response flags; current ROM,
work and transfer bits; carry, borrow and comparison bits; ownership,
seal, armed, idle, stage and validity flags; and fixed finite-control
scratch. Two of the already allocated stage bits encode the receiver
phase $\phi\in\{\mathsf{pre},\mathsf{ready},\mathsf{written},
\mathsf{sealed}\}$ as $00,01,10,11$, respectively. These bits are
reserved throughout a frame; bit-loop and return control use the listed
PC, return and continuation slots. Unused Boolean fields are also
allocated. There is no additional vector, saved response, call stack,
log or implicit interpreter control. A finite-control state is an encoding in these
fields, not an extra uncounted state. Each fixed routine is inlined or
uses the listed return slots without recursive nesting.

The mathematical current source is separate from this observer. Source
promise authentication, entry storage, and the physical Read/Update
provider are separate services with their own memory/work bills; they
are not included in $S,B,D$ or declared implemented by this interpreter.
Any address or handshake field persisting on the observer side of that
boundary belongs to the fields just listed.

**Definition 4.4 (the local routines and actual receiver).** RESET
clears all $3P$ array cells by complete scans, resets $d,b,a$ and copy
positions, clears response flags, and sets sender ownership. It makes
no source call. Each PUT scans to the sender end using its charged
head, writes the one label bit ($0=L,1=R$), and increments $d$ by a
bit loop. NOP performs only its charged control transition. The fixed
$P$ graph positions are traversed even for short literals.

COPY seals the sender and performs PR57.D7's two owned loops. First,
for each of the $d$ sender bits, it executes the four core occurrences
read sender, write mailbox, move sender one cell, move mailbox one
cell. It then seals the mailbox and hands over the token. Its length
$b=d$ is copied bitwise into the counted mailbox descriptor. Next,
for each of the $b$ mailbox bits, it executes read mailbox, write
receiver, move mailbox one cell, move receiver one cell. Each write
increments the receiver's **own** occupied length $a$ by a paid bit
loop. It then seals the receiver and acknowledges the handoff. Homes,
seeks, length-copying, increments, permission control and loop tests
are additional paid operations. Full arrays were allocated and zeroed;
no allocation is hidden in a write. The core copy count is exactly
$8d+4$, also for $d=0$.

The receiver phase specifies the following cut convention for these
same loops. At the common initial cut and on entry to each next macro
frame it is $\mathsf{pre}$; the final local node transfer sets this
phase together with entry to that frame. RESET and all sender/mailbox
preparation keep it $\mathsf{pre}$, including partial clearing of an old
payload or length. After the mailbox is sealed, its length copied and
both copy heads homed, $a=q=0$ and the receiver loop enters
$\mathsf{ready}$. The receiver head $q$ is the destination-cell index,
including the one-past-end position $b$; the separate work head in slot 8
performs all scans of the length bits. Within this loop:

- In $\mathsf{ready}$, $a=q$. If $q<b$, the mailbox head is also $q$.
  The read of that mailbox cell and all preparation for its write leave
  $q,a,D,\phi$ fixed, while retaining its bit in the transfer field.
- The receiver write stores that bit in $D_q$ and changes $\phi$ to
  $\mathsf{written}$ in the same paid local occurrence. This write is
  the letter arrival, even if it writes zero into a zero cell. The
  receiver head stays at $q$ throughout the following length increment,
  its carry/bit-index work, all routine returns and the mailbox move.
- Increment $a$ from its old value $q$ by a least-significant-bit-first
  carry scan. Clear successive one bits, then set the first zero bit
  and clear the carry. Individual data-bit writes, work-head moves,
  branches and returns remain paid steps. The routine must return with
  $a=q+1$ before the mailbox moves one cell. The receiver's subsequent
  one-cell move changes its head to $q+1$ and $\phi$ back to
  $\mathsf{ready}$ together in that paid move. No other instruction
  changes $q$ while the phase is $\mathsf{ready}$ or $\mathsf{written}$.
- At $q=a=b$, the loop test permits the existing receiver seal occurrence,
  which changes $\phi$ to $\mathsf{sealed}$. Acknowledgement, receiver
  homing, operand checks, source receipt and local response continuation
  keep this phase and $D,a$ fixed until entry to the next frame. An
  empty payload goes directly from $\mathsf{ready}$ to this seal.

Thus the phase changes use the already charged control transitions of
the copy body, seal and node transfer. They add no core occurrence, array,
slot or Boolean field. The detailed carry routine is part of the fixed
program charged in $I_0$. All intermediate instructions preserve the
phase, except the four specified transitions into $\mathsf{pre}$,
$\mathsf{ready}$, $\mathsf{written}$ and $\mathsf{sealed}$. No transient
PC, copied loop index or partially copied continuation is used as a
substitute for these retained phase bits.

For a complete counted configuration $c$, define the receiver projection

$$
\begin{aligned}
k(c)&=\begin{cases}
0&\phi=\mathsf{pre},\\
q&\phi=\mathsf{ready},\quad 0\le q\le P,\\
q+1&\phi=\mathsf{written},\quad 0\le q<P,\\
a&\phi=\mathsf{sealed},\quad 0\le a\le P,\\
0&\text{otherwise},
\end{cases}\\
\operatorname{received}(c)&=D[0:k(c)].
\end{aligned}
\tag{4.4a}
$$

The empty default makes this a function on every installed valuation;
its arrival interpretation is asserted only on lawful executions. It
uses receiver cells, its counted head, phase and length, never sender
cells or the native row. It is a mathematical projection at a cut, not
an additional readable source port or a free runtime decoding operation.

Before ISSUE-READ the interpreter homes the receiver head, finishes
all length and ownership checks by paid scans, sets the armed state,
and has zero response flags. The committed original operand is exactly

$$
\operatorname{payload}(D,a)=D_0D_1\cdots D_{a-1},
\qquad 0\le a\le P,
\tag{4.4}
$$

with the $0/1$ to $L/R$ interpretation above. These are the accumulated
receiver cells. The original table and graph row are not consulted to
replace them at commitment. Reading the flat literal at this boundary
is the original whole-materialized-literal service; its physical
consumption and source traversal costs are still separate. A whole-word
lookup is not being supplied as a free **local** operation.

At actual Read-response receipt only the corresponding one of
$f_\alpha,f_\beta,f_{\mathsf{branch}},f_{\mathsf{absent}}$ is set.
At Update-acknowledgement receipt only $f_\star$ is set. All other
bits, including the instruction counter, stay unchanged. The raw reply
has no other persistent copy. The ISSUE instruction with zero flags
makes its source call; the same instruction with one flag set continues
locally to the response tests. This removes any need for a simultaneous
unreported phase write. LINK retains the old graph node/selected link
while copying its fixed successor index to the pending-node slot,
clears the reply flag locally, and completes the paid node transfer.
The continuation slot distinguishes the old-node, pending-node and
next-block stages. No new source call is enabled during this transfer.

Every row fetch moves the ROM head to the row's first bit and copies
its fixed fields sequentially. Offset multiplication, if used, is
bounded repeated addition; an alternative is counting row boundaries
in a full scan from the header. The latter fixes a row-fetch routine
with no arithmetic oracle. For every graph-node transfer, first copy
the old node to slot 3, keep it fixed while slot 2 receives the next
node and slot 1 is rewritten, and use the counted continuation stage
to select which copy is authoritative. This applies to ordinary graph
edges as well as LINK edges; a partially copied node is never decoded
as the current macro row. Incrementing a field counter scans its
bits with a carry, and loop tests scan the compared fields. Homes
walk one cell at a time. Thus the listed routines specify finite
sequential operations rather than access to a computed address for
free.

**Proposition 4.5 (all rows, malformed states and response legality).**
The routine conventions admit a total finite composite instruction
system. It can install every binary valuation of the arrays and the
thirty-two slots and sixty-four Boolean fields, with all unused bit
patterns included. On every installed source-response row the actual
receipt changes at most one composite bit. On every promised run it
changes exactly one. This statement does not assert that local
instructions change at most one bit.

Proof. Give unused opcode/PC patterns a source-free ERROR hold. Two other
distinct fixed PC values are the fixed-output Halt instructions; every
other PC value is local except for the two issue values described below. Totalize
bit-loop arithmetic on malformed inputs by fixed-width arithmetic;
check overflow and bounds in the specified routines before using their
results on a valid run. A ROM or work head outside its allocated
interval reads zero, and a write there holds. A movement outside its
representable interval holds and enters ERROR by a local instruction.
These conventions introduce neither mutable cells outside the allocation
nor source observations. They are total rules for invalid configurations,
not extra available source operations.

Use two distinct fixed interpreter PC values for source issue. At
the Read PC with zero response flags, its source operand is (4.4) if the
receiver length is in range, and the empty materialized literal otherwise.
This last rule fixes a literal for otherwise malformed installed rows;
it is immaterial to every valid run, which completes the explicit
bounds scans. The physical operand service remains separately priced
for these rows too. It is not assigned a constant-time implementation.
At the Update PC with zero response flags the source instruction is
the original Update. The armed state is this PC value, not an
additional uncounted latch. With zero flags, the receipt sets just the typed flag. With
any nonzero flag the instruction is local continuation or ERROR, so
there is no new source response requiring a second bit. All other
source-row fields remain fixed at receipt. Thus every typed installed
response row is hold/one-bit legal, including unreachable rows.

For an encoding into the no-$11$ word, insert a fixed zero between
successive mutable bits, as in the displayed map in Cabello, Eppstein
and Klavžar, Proposition 3.1 [CEK]. Setting a single response bit changes
one coordinate of this word and cannot create adjacent ones. Multi-bit
local writes still map between admissible words; their adjacency is
not claimed. The map's use here needs no isometric embedding theorem.

The native macro successor at receipt is $\delta(w,r)$, which by the
chosen supplier is itself a hold or one-native-bit change. It is
represented then by the counted old-node identity and the one set
flag, rather than by an uncharged retained raw reply. The later LINK
implements the already selected successor by paid local work. This is
a stuttering refinement of that immediate macro response, with an
explicit one-bit **composite** receipt as well. ∎

**Definition 4.6 (simultaneous installation and width parameters).**
Let $I_0$ be the fixed bit length of the chosen PH sequential interpreter,
loader and the nonrecursive routines just specified, and let $I_c$ be
the fixed bit length of the block-graph writer below. These are fixed
program descriptions independent of $h,T$; their instructions are the
local bit/move/control operations of Definition 4.3. They are charged
constants, not a provider returning an online table. Put

$$
\begin{aligned}
Z&=T_G+I_0+I_c+N+W_*+P+\ell+16,\\
r&=\left\lceil\log_2\bigl(256(Z+1)^2+1\bigr)\right\rceil,\\
b_{\rm mut}&=3P+32r+64,\qquad L=2b_{\rm mut}-1,\\
S_{\rm inst}&=2^{b_{\rm mut}}.
\end{aligned}
\tag{4.5}
$$

The installed set is exactly the zero-interleaving image of all
$b_{\rm mut}$-bit words. This counts all malformed and unused valuations
of Proposition 4.5; no reachable-state quotient is used. Its transition
rows are specified by the finite interpreter and routines, not stored
as $2^{b_{\rm mut}}$ separate records. If a convention additionally
requires such an expanded composite table, its full storage must be
added; (4.3) is not its size. With the four distinguished PC values of
Proposition 4.5, the complete row counts are

$$
n_R^{\rm comp}=n_U^{\rm comp}=2^{b_{\rm mut}-r-5},\qquad
n_H^{\rm comp}=2^{b_{\rm mut}-r+1},\qquad
n_{\rm typed}^{\rm comp}=5\cdot2^{b_{\rm mut}-r-5}.
\tag{4.5a}
$$

The remaining rows are local. All five flags must be zero at an issue
PC, which explains the exponent. Each Halt PC fixes one output bit.
Even if no valid macro run ever updates, the unreachable Update-PC
rows remain installed and counted. The composite installed Read menu
contains every word of length at most $P$, because malformed arm
configurations allow arbitrary receiver cells and any valid occupied
length. Its size is $2^{P+1}-1$, despite the much smaller set reached
on actual runs. These extra rows do not alter the simulation assertion,
which begins at the single common lawful initialization.

Use PH8.1's allocation header $J_r$, with one width declaration for
each of the thirty-two slots, the sixty-four-Boolean allocation,
and the three array lengths. Gamma codes of $P+1$ handle empty arrays.
The explicit generous bound

$$
|J_r|\le 128r+128
\tag{4.6}
$$

covers these declarations and their fixed register identities. Resident
immutable storage is $T_G+I_0+|J_r|$. A sufficient simultaneous
installation peak, including a duplicate input image, the source table,
the graph writer, its two native-word scratch arrays and online RAM, is

$$
B_{\rm install}\le
4(Z+|J_r|)+L.
\tag{4.7}
$$

All headers, code and initialization bits are source-independent.
Initialization scans the headers, sets slot 1 to the installed initial
block, installs $P,N,w_G$ and the image end in their named slots,
zeros all payloads and response flags, homes the heads, and enters
the row-fetch PC. Other scratch/return slots begin at zero. The loader
makes no source call and cannot enter either Halt PC. Its finite work
is charged, and its temporary input image is included in (4.7).
These are sufficient allocations, not sharp minima.

**Theorem 4.7 (finite attained parity refinement and simultaneous bills).**
For the particular table $C$ of Definition 4.1, Definitions 4.2–4.6
give an autonomous serial refinement with the same original source
family and all original observations. Its erasure is the entire macro
trace of $C$, with the same common initialization, every root routing
Read, every literal, raw reply and genuine source successor, termination
and firstHalt. At every paid microstep cut of each Read frame, (4.4a)
is exactly its actual arrived prefix. Its actual receipt is one-bit
legal as in Proposition 4.5. On a run with original counts
$Q,U,A,P_{\rm run}$,

$$
\begin{aligned}
Q_{\rm serial}&=Q,&U_{\rm serial}&=U,
&P_{\rm serial}&=P_{\rm run},\\
E_{\rm receiver}&=A,&E_{\rm two\ channels}&=2A,
&I_{\rm copy\ core}&=8A+4Q.
\end{aligned}
\tag{4.8}
$$

There is a choice of the described bit routines for which initialization
and all local work up to firstHalt satisfy the deliberately coarse
simultaneous bound

$$
I+I_{\rm init}\le (Q+U+2)\,2^{40}(Z+1)^8.
\tag{4.9}
$$

The graph writer's installation work also has a polynomial upper bound
$2^{40}(Z+1)^8$ under the same bit/move convention. Width, all installed
rows, immutable storage and installation peak are exactly or bounded
as in (4.3)–(4.7). Source growth and physical-service costs are the
original supplier's on this very run, with the address operand now
coming from the receiver.

Proof. The graph writer reads the original table sequentially. For each
native row it emits its $P+16$ fixed graph records in order. It finds a
response's successor by copying the row's native key into a scratch
array, making the indicated hold/flip, and scanning the original table
for the resulting key. The key occurs exactly once and the successor
is an installed word. It writes the target block index in the graph
row's successor field, with zero padding elsewhere. At most five such
scans per native row suffice. Each row's literal symbols and padding
are read from its actual native row. This specifies all graph records,
including every error record, without an oracle or source access.
Two length-$\ell$ scratch words, a sequential output image, the input
native table and bounded index/bit-loop slots suffice during this work.
They fit (4.7). The writer is distinct from the online interpreter and
is paid whether its output is later useful or unreachable.

Every array index is at most $P$, every graph index at most $N$, and
every row offset and its repeated-addition intermediate is at most a
product of two quantities bounded by $Z$. PH8.1's generous squared
slot range covers these. Its allocation-header argument also covers
head positions through the loaded image and scratch. More explicitly,
$r\le12+2Z$, and all the image/header, slot and three-array positions
used by these scans are below the actual slot limit
$256(Z+1)^2$ for this installation: $N\ge16W_*$ and the retained
row images give $Z\ge T_G\ge10N$, while the direct sum of the header,
code, slots and arrays, including interleaving separators, is at most
$256r+32Z+2048$. For $Z\ge160$ this sum is less than $256(Z+1)^2$; the displayed
construction has at least that $Z$. Thus there is no unbounded numeric
workspace or circular allocation assumption.

For completeness, the following coarse work accounting fixes a
polynomial rather than merely asserting computability. A row fetch,
field test/copy, increment, or bounded-addition routine can use full
scans instead of shortcuts. It uses at most $2^{12}(Z+1)^3$ elementary
bit/move/control occurrences: each field has at most $r$ bits, the
occupied tape intervals total at most $256r+32Z+2048$, a field operation
uses a fixed number of scans per bit, and row seeking uses at most
$T_G$ unit moves. Allowing $2^{12}(Z+1)^2$ such routine invocations per
macro frame overbounds its at most $P+16$ graph visits, $3P$ clearing
writes, sender filling, both copies, all loop/length work and LINK.
No loops are nested except row/field scans, bounded addition, and
these bounded cell loops. Initialization has the same bound. The
product $2^{24}(Z+1)^5$ is below the looser per-frame allowance in
(4.9). During graph writing, at most $5W_*$ table scans with key
comparisons and $N$ record writes add at most two further loops of
length $Z$ to this bound. The allowance $2^{40}(Z+1)^8$ includes them.
No step in this estimate supplies a whole-word random lookup or an
advancing uncounted head. The constants are conservative analytic
bounds for the specified scan choices, not measured running times.

Induct on the $d$ PUT nodes: after them $S[0:d]=p$, and all other sender
cells remain reset. By PR57.D7's indexed copying induction, the sealed
mailbox satisfies $B[0:b]=p$, $b=d$. To cover every paid cut of the
receiver loop, let $H_c$ be the word of actual receiver arrivals in the
current frame up to cut $c$. This is proof notation, not another stored
log. The strengthened indexed invariant is:

- In $\mathsf{pre}$, $H_c=\varepsilon$; old cells and a partially reset
  length are irrelevant to (4.4a).
- In $\mathsf{ready}$, $|H_c|=q=a\le b$ and
  $D[0:q]=H_c=B[0:q]$.
- In $\mathsf{written}$, $|H_c|=q+1\le b$, the receiver head still
  names the just-written cell, and $D[0:q+1]=H_c=B[0:q+1]$.
  The length bits may be at any stage of the specified increment.
- In $\mathsf{sealed}$, $|H_c|=a=b=d$ and $D[0:a]=H_c=p$;
  receiver and work heads may be moving without altering that prefix.

Initially and throughout RESET/preparation the first clause holds.
The ready entry has $q=a=0$. In a ready iteration, only the receiver
write appends a letter to $H_c$; it stores exactly the bit just read
from $B_q$ and changes phase at that very cut, proving the written
clause even when the stored bit does not change. Neither another data
write to $D$ nor a new arrival is possible while written. All length
bit writes, carry changes, work-head and mailbox moves, loop-index
updates, tests and intermediate return/continuation copies therefore
preserve that clause: they change neither $D[0:q+1]$, $q$ nor $\phi$.

For termination and the stable length, suppose the old length is $q$
and its first zero bit is at position $m$. Such a position exists below
$r$ because $q<b\le P<2^r$, hence $q+1<2^r$. At the test of bit $j\le m$
after clearing the $j$ lower one bits, the current numeric length is
$q-(2^j-1)$. Clearing the next one bit changes it to
$q-(2^{j+1}-1)$, also at the cut before the work-head move. At $j=m$,
setting the zero bit gives $q-(2^m-1)+2^m=q+1$, including the cut before
carry clearing. Seeking, bit tests, carry clearing and return steps do
not alter that value. This proves the increment's endpoint for every
legal $q$; it does not pretend that its intermediate numeric value is
an occupied length. The invariant during those cuts instead uses the
unchanged receiver head and written phase. After the mailbox move,
the receiver move simultaneously advances $q$ and restores ready, so
$q=a=|H_c|$ again. The last iteration reaches $q=b$, the seal establishes
the sealed clause, and all homing/check/continuation steps preserve it.
At the next frame entry the phase becomes pre and the new frame's
arrival word is empty, even while old payload cells await RESET.
This proves $\operatorname{received}(c)=H_c$ at every paid microstep
cut of every lawful frame, including $d=0$ and $P=0$.

At increment-complete cuts, including ready cuts and the completed
seal, the ordinary view $D[0:a]$ agrees with this projection. It also
agrees after RESET has finished and before the first receiver write,
when $a=0$. During unfinished length increments or partial RESET it
has no such guarantee. The receiver remains unavailable to the source
until its seal; recovery as a projection does not enable a prefix
Read. At that seal $a=d$ and $D[0:a]=p$. Hence (4.4), not a fresh
unchanged lookup of the macro row, determines the committed original
Read. All frames, including root-literal frames,
terminate because their cell bounds and graph chains are finite.
The two loop bodies contribute precisely $8d+4$; all other local work
is included in (4.9). Each final receiver write is one actual letter
arrival. Summing proves (4.8).

At a returned cut suppose the current graph block is that of macro
word $w$ and the actual source is $y$. RESET, graph rendering, copies,
seeks and checks preserve $y$ and the macro relation to $w$. The final
Read submits exactly $I(w)$'s literal; Update performs precisely the
one prescribed $\rho$; no other node has a source action. The same
raw reply $r$ sets one counted flag. At that cut set the macro relation
to $(y',\delta(w,r))$. During response tests it is determined by the
old block and flag; in a LINK by that link's fixed successor; during
node transfer by the retained old/link node and pending successor.
The continuation slot keeps these stages separate until the next
block is installed. Clearing a flag therefore does not destroy the
pending continuation. The intermediate bit copies never enable a
source call. The new returned cut represents exactly the successor.
This gives a cutwise simulation relation, including the moment of
receipt, rather than just an equality of final parity.

Erasure now follows by induction on original calls. A macro routing
root Read enters its own Read block, has a sealed empty payload,
executes the real source Read and receives its actual raw reply. It is
not deleted. Halt blocks output their fixed bit at node 0, and no other
node outputs a Halt. Finite local frames combined with the supplier's
finite macro run yield finite firstHalt with exactly its parity.

Finally, a single prefix simulator starts from the common image and
initial node, executes these same local routines and transmitted
payloads, and pauses only at each original response receipt. It then
consumes that one acquired reply and sets the matching flag. Before
that point no local choice has depended on it. Induction on microsteps
gives all local instruction/head/availability/fee labels and their
prefix compatibility. The source transition itself is the unchanged
primitive, not simulated by address transport. This is the exact
specialization of PR57.T3's causal proof to the present observation
alphabet; it does not import PR57's coefficient response or guarded
source operations. ∎

## 5. What the upper bills do and do not exchange

**Corollary 5.1 (explicit parameter regimes).** The preceding refinement
attains $L=O(P+\log(T_G+N+\ell+1))$. In particular it attains
$L=O(h+T)$ for all of the following actual macro choices, with their
simultaneous source bills inherited unchanged.

For every $h$ at $T=0$, SLHC §11 gives

$$
k=h+3+\lambda(h)+2\lambda(h+1),\quad
\ell=4k+15,\quad W_*=2^{2k+8},\quad
P=h-1,
$$

$U=0$, $Q\le(2k+7)(2h-1)$ and
$A\le(2h-1)(h-1)$. Thus the serial width is $O(h)$, including
$h=1$, where all payloads are empty but reply, control and Halt states
still count.

For even $h$ and positive $T$, one choice is SLHC §11's active table:

$$
\begin{aligned}
B_0&=2\left\lceil\frac{T+2h}{2}\right\rceil,\qquad
k=h+3+\lambda(h)+2\lambda(h+1)+\lambda(2h),\\
\ell&=4k+15,\quad W_*=2^{2k+8},\quad P=h-1+B_0/2,\\
U&=B_0-t-\kappa(u),\qquad
Q+U\le(2k+7)\bigl(2B_0+1+2h(4h-2)\bigr),\\
A&\le(B_0+1)B_0/2+2h(4h-2)P.
\end{aligned}
\tag{5.1}
$$

Here $\kappa(\alpha)=0$, $\kappa(\beta)=1$ and
$\kappa(\langle v,w\rangle)=2+\kappa(w)$ is proof notation, not a
supplied epoch. The active macro width is independent of $T$ for fixed
$h$, while its serial flat-buffer width is not.

A second choice, using SLHC Theorem 12.2 at $\Delta=2$, has

$$
\begin{aligned}
J&=\left\lceil(T+2h)/2\right\rceil,\qquad
 g=\lambda(J),\qquad e=\lambda(2h+1),\\
k&=h+3+\lambda(h)+2\lambda(h+1)+e+g,\qquad
 P=h-1+J,\\
\ell&=4k+15,\quad W_*=2^{2k+8},\quad U=0,\\
Q&\le(2k+7)(g+1+8h^2-2),\qquad
 A\le P(g+1+8h^2-2).
\end{aligned}
\tag{5.2}
$$

The same refinement also applies to each even $\Delta\ge2$ with
$J=\lceil(T+2h)/\Delta\rceil$, $g=\lambda(J)$,
$P=h-1+J\Delta/2$, and the exact capped macro bills in SLHC.12.3.
When $\Delta$ is unnecessarily large, retain this displayed $P$;
do not claim an $O(h+T)$ bound uniform in arbitrary $\Delta$.

Proof. Equations (4.1)–(4.3) give
$\log T_G=O(\log W_*+\log(P+\ell+1))$, and (4.5) gives the first
assertion. Substitute the supplied values above. The macro native-call
polynomial in (5.2) is in $h+\log(T+1)$. Equation (4.9) instead is a
polynomial in **installed code size** $Z$: $W_*$ is exponential in the
macro width, and literal expansion contributes $P$. It is not a
polynomial-in-$h+\log(T+1)$ or polynomial-in-$h+T$ claim about total
serial work. All copy traffic, ROM scans and original root routing
Reads remain charged. ∎

**Proposition 5.2 (extra cost of this active alignment trace).** For
the active choice (5.1), every actual refinement transmits at least

$$
A_{\rm align}=(U+1)B_0/2
\tag{5.3}
$$

letters to its final receiver just for the original alignment polls.
On the permitted lag-zero all-$\alpha$ left comb with rightmost leaf
at depth one, for even $h\ge2$, $\kappa(u)=2$ and hence

$$
U=B_0-2,\qquad A_{\rm align}=(B_0-1)B_0/2.
\tag{5.4}
$$

The two-copy refinement's corresponding core occurrences are exactly
$8A_{\rm align}+4(U+1)$. Thus for fixed even $h$, this particular
alignment trace has $\Omega(T^2)$ literal/serial work. This is not a
universal parity-algorithm lower bound.

Proof. SLHC Construction 11.4 polls the same literal $R^{B_0/2}$ exactly
$U+1$ times. Each failed poll is followed by its genuine Update; all
intervening root routing Reads contribute zero address letters, but
remain real calls. Erasure preserves the full sequence, so each poll
needs a newly completed payload under the present frame contract.
The indicated original comb has $h$ leaves and rightmost leaf $\alpha$
at depth one, giving $\kappa=2$. Substitution into the supplier's exact
Update count gives (5.4). The linear-in-$T$ same-run bound (2.1) and
this quadratic trace-specific bill have different quantifiers. A
static or cell-search macro controller need not execute these polls. ∎

**Proposition 5.3 (source growth is another simultaneous coordinate).**
If the original contains $b_\beta$ beta leaves and the run makes $U$
Updates after lag $t$, its maximum current node count is

$$
V(t+U)=2\bigl((h-b_\beta)F_{t+U+1}
                       +b_\beta F_{t+U+2}\bigr)-1.
\tag{5.5}
$$

A whole-source traversal implementation of Update has input-node-volume
bill $\sum_{a=0}^{U-1}V(t+a)$, in addition to any allocation of successor
versions. Serial refinement changes none of these versions. It adds
its own address/work allocation, not a physical time bound on the source.

Proof. This is SLHC.11.16 on the preserved source trace. Source-free
frames leave the current version fixed, and each retained Update is
one actual application of $\rho$. The given Fibonacci expression is
nondecreasing in absolute epoch. Physical traversal and allocation
costs depend on the chosen source provider; the formula does not give
an extra observation of these costs. If that provider has immutable
code length $K_{\rm src}$ and transient workspace $M_{\rm src}(y,p)$,
these are additional coordinates, not parts of $T_G$ or free zeros.
Similarly the run carries the separate bills

$$
\sum_{\text{actual Reads }i} C_R(y_i,p_i),\qquad
\sum_{\text{actual Updates }i} C_U(y_i),
\tag{5.6}
$$

besides source entry, promise authentication, initialization and output.
No numerical bound on these physical-service functions or on source
representation bits is supplied here. Equation (5.5) counts nodes;
converting it into storage bits requires a representation contract.
The observer installation peak (4.7) therefore is not a bound on the
joint physical apparatus including the source. ∎

## 6. Boundary, memory and recoverable history at each cut

**Proposition 6.1 (which finite information is recoverable).** In the
flat refinement, the following recoveries and failures refer to the
same actual source and cut.

At every paid partial delivery cut, (4.4a) recovers exactly the arrived
address prefix from the receiver cells and the already counted
head/phase/length fields. The restricted view $(D,a)$ suffices after
RESET has completed and before the first arrival, at ready cuts, after
each length increment has returned and through the following head moves,
and at sealed cuts. It need not suffice during an unfinished increment
or partial RESET. In particular, on the $h=2,T=0$ all-$\alpha$ source,
the first delivery of $L$ with $P=1$ has $(D,a)=([0],0)$ both just before
and just after the receiver write. The prefix is respectively empty
and $L$. The phase changes from ready to written, with $q=0$, so (4.4a)
gives lengths zero and one at those very cuts. Arrival is the write,
not the later increment or seal. At a carry such as $3\mapsto4$, the
length may pass through $2$ and $0$, while $q=3$ and the written phase
continue to decode four arrived letters. Complete configurations are
different in the zero-write pair, so the nonrepetition bound is unaffected.

The sender's sealed cells can recover the whole selected literal
locally, but the receiver has no source reply for any prefix. At the
completed receiver seal, $(D,a)$ recovers the whole committed literal.
At actual source receipt,
the one set flag recovers the actual one of four raw replies or the
Update acknowledgement; together with the retained native row it
selects its legal macro successor. Later cleanup may erase this flag
and the old payload. The firstHalt output is only parity;
it does not recover the transcript, current tree or initial epoch.
This refinement may still retain the last payload in allocated cells
at that cut; those cells are not an additional output port.

In the active alignment construction, the accepted poll certifies the
current right clock $B_0$. In the capped construction, acquired cell
$j$ and accepted alpha/beta reply certify current clock $B_j$ or
$B_j+1$, where $B_j=(j+1)\Delta-2$. Cell search alone certifies only
the cell. With $\Delta=2$ there were no Updates, so this is the entry
clock; with larger cells it need not determine the entry clock or the
unretained number of Updates. None is automatically the historical
lag $t$.

Proof. The phase-indexed invariant and carry argument of Theorem 4.7
prove recovery through each write, length update, movement and
continuation cut; the displayed pairs evaluate that decoder directly.
At source receipt use the definition of the one-hot flags. The clock
statements use
`DelayedOriginalReadout.right_clock_iterate` and `right_clock_readout`
and exactly SLHC §§11.4, 12.5. A finite right-ray profile is mutually
recoverable with $\kappa(y)=2d+e$: it has branch before depth $d$,
leaf $\alpha$ or $\beta$ according to $e\in\{0,1\}$ at $d$, and absence
afterward. This is a representation of a **current** coordinate. Its
identity $\kappa(y)=t+U+\kappa(u)$ does not split the summands without
additional information. Proof annotations of absolute epochs or source
versions are not observer registers. ∎

**Proposition 6.2 (history obstruction and the unbounded-entry limit).**
For odd $h$ and $T\ge1$, no such serial refinement solves original
parity. For any fixed $h$ in a possible regime there is no one finite
complete autonomous installation handling all entry lags. Neither
larger local memory nor more faithful transport recovers an authentic
history that the source ports have already identified.

Proof. On any $h$-leaf shape let $A_S$ and $B_S$ denote the uniformly
alpha and uniformly beta originals. The histories $(A_S,1)$ and
$(B_S,0)$ have the same entry tree because $\rho A_S=B_S$. Under common
initialization and deterministic local behavior they have equal
microtraces until their next source response. Equal current sources
then give equal responses and equal genuine successors, so induction
keeps their entire observations equal. Their parities differ for odd
$h$. These are precisely instances of [Atomic Boundary Trichotomy,
Theorems 9.2–9.4][ABT], whose full fiber classification is not being
replaced by a statement about a known shape.

For even $h$ and unbounded entry, (2.3) contradicts a fixed finite
$S_{\rm inst}$ as $T$ increases. Equivalently a finite composite has a
finite installed decoded literal menu and the permanent-saturation
obstruction in SLHC §10.4 applies. For odd $h$ the preceding collision
already suffices. A pointwise terminating machine with growing counted
workspace and literals is outside this finite-installation assertion.

ABT's full-current-tree fiber theorem says more precisely that, for
known original leaf count, all nontrivial history fibers are the pairs
$\{(A_S,k+1),(B_S,k)\}$. Even complete acquisition of the current tree
cannot choose the authentic member of such a pair. It does recover
original shape and the pair, and mixed-label originals have singleton
history fibers. A separately authenticated record separates the
histories exactly when it takes different values on every such pair
(ABT Theorem 9.3). A common initialization, an address payload, or a
counter started after entry does not provide that record. In particular
same-source post-entry counters have equal values on the colliding
runs. Our parity controller does not acquire the whole current tree
merely by having an observer that could in principle describe it. ∎

**Proposition 6.3 (installed union, known shape and the unresolved sharp
memory problem).** The all-shape factor $2^{h-1}$ in (2.2) is an
installed union across different comb tips, not a per-run query count.
For one supplied fixed shape its own cone/lag bound remains applicable,
but it cannot supply this all-shape factor. Conversely, a known comb
shape still has a leaf at depth $h-1$ and is subject to the autonomous
long-frame obstruction; knowing a shape does not supply an advancing
head. A balanced known shape has a different depth term.

A bound on one run's sum $A$ does not bound the number of prefixes of
the installed menu. For example, add to a correct installation any
number of unreachable rows whose fixed literals are distinct. Every
actual run and its $A$ stay unchanged while the union of menu prefixes
increases. Write $\operatorname{Pref}(\mathcal A)$ for the union of
prefixes of words in $\mathcal A$, with the empty word included. For
the complete **native macro table** $C$, let $\mathcal M_{\rm nat}$ be
its fixed Read literals, including unreachable native rows. Then

$$
|\operatorname{Pref}(\mathcal M_{\rm nat})|
\le 1+\sum_{p\in\mathcal M_{\rm nat}}|p|
\le 1+|\mathcal M_{\rm nat}|P
\le 1+n_RP\le 1+W_*P.
$$

The same bound holds for any subset of those native literals, including
the literals selected on lawful executions of the refinement. It uses
the native installation, not a single run's $A$. The **totalized composite**
menu of Definition 4.6 is instead $\mathcal M_{\rm comp}=\{L,R\}^{\le P}$.
It is prefix-closed, so its separate exact count is

$$
|\operatorname{Pref}(\mathcal M_{\rm comp})|
=|\mathcal M_{\rm comp}|=2^{P+1}-1.
$$

For the active table with $h=2,T=100$, (5.1) gives $k=12$, $B_0=104$,
$W_*=4294967296$ and $P=53$. Thus the native bound is $227633266689$,
whereas the composite prefix count is $18014398509481983$. These are
different installed menus; the native bound is not a bound on the
composite menu. At $P=0$ both prefix counts are one.

The bounds proved here leave a genuine gap between the universal lower
order $\Omega(h+\log(T+1))$ and the attained flat-allocation upper order
$O(h+T)$. No sharp total-memory theorem, compressed-receiver attainment
of the lower order, or impossibility of such an attainment follows.
An improved receiver would have to preserve the exact original
commitments and raw trace, materialize the operand under the original
port, and charge its decoder, heads and intermediate storage. A
source-walk solution would answer a different interface question.

Proof. The first assertion is the supplier's equal-depth comb-cone
union argument; a single supplied shape removes that union. The
long-frame proof counts an actual chosen leaf depth, so persists for
a known comb. Unreachable added rows prove the prefix counterexample;
counting at most $P$ nonempty prefixes per native Read literal proves
the native bound. Definition 4.6 supplies every binary receiver word
of every length up to $P$, giving the composite geometric sum; the
phase convention imposes no restriction on those installed issue rows.
Finally Theorems 2.2 and 4.7
have precisely the two different allocation premises displayed above;
neither supplies the missing compression/materialization construction
or a matching impossibility proof. ∎

## 7. Supplier correspondence and mathematical scope

**Definition 7.1 (attribution and exact interfaces).** The mathematical
roles of the sources are as follows. The source-specific conclusions
of §§2–6 are repo-derived compositions and ordinary proofs, not a
claim of worldwide originality or Lean kernel certification.

| Source | Consumed result and limit |
| --- | --- |
| SLHC §§10–11, revision `f14a84e00297c51a63cec763f74f2a896c23c8f7` | All-shape parity tables, licensed delayed-image trials, complete native one-bit routing, active/static widths, exact active Update count, full installed table and source growth. These macro services remain conditional. |
| SLHC §12, revision `5798b485e4a9343f8e446c666b8966ffd71cdb5a` | Theorem 12.3's same-run comb literal bounds and Update-expanded separating windows; Theorem 12.2's cell-table parameters when (5.2) is chosen. The receipt lower bounds consume its mathematical premises, not publication status. |
| PH8.1, revision `3605ccfd6e273bf9d9bda2bc93009239cfdb961e` | Finite row format, sequential bit lookup, thirty-two counted integer slots, sixty-four flags, loader and simultaneous installation accounting. The parity graph has no stochastic track, sampled law, posterior, fair-bit call or synthetic source. Its four Read outcomes use counted flags and binary test nodes. PH's actual/synthetic and rendering slots are reassigned explicitly in Definition 4.3; extra payload arrays are added and charged. Its stochastic correctness or two-response source interface is not imported. |
| PR57.D7 and L4, same revision | Two owned bit-copy loops, simultaneous sender/mailbox/destination allocation, seals, handoffs, and exactly $8d+4$ core occurrences after positioning. Its indexed invariant supplies completed copy equality; Definition 4.4 and Theorem 4.7 specify the receiver head/phase projection through this consumer's length-bit updates and movements. Here destination is the actual Read literal; no provenance archive, verification snapshot or source identity is obtained for free. The original PR57 ports and tapes allow growing records; this finite refinement reserves all $3P$ cells and counts every head instead. |
| PR57.T3, same revision | The proof method of one uniform simulator consuming an original response only at its complete release. Here release is atomic native response receipt; no partial source-response block is exposed. Only local transport labels/fees and the original four-valued reply are observed. PR57's ordered-tree coefficient Read, guarded updates, contexts and full visible physical-source schedules are different contracts. No conformance of those source implementations is asserted for this Read. |
| `NativeSerialMachine.nativeStep`, `Run`, `replay_deterministic`, `operational_replay` | The source/reply/update chronology and source-blind local transition vocabulary. Its Read still takes an atomic whole address, and its proof configuration has epoch/source/trace components. Those components are not free finite observer memory. |
| `NativeSerialEffective.OriginalState`, `original_code_service_simulation`, `effective_service_inclusion` | The existing effective simulation has numeric workspace and, on its original interface, certified epoch and acquired history. It supplies no finite width or autonomous literal-delivery bill. It is not substituted for the counted graph construction. |
| `NativeSerialDepth.descriptor`, private `descriptor_eq`, `bounded_read_support` | The descriptor is explicitly noncomputable/proof-only. Bounded chronological support is not a paid row selector or receiver. |
| `DelayedOriginalReadout.right_clock_iterate`, `right_clock_readout`, `original_presence_guard`, `original_decoder_correct`, `original_decoder_service`; private `clock_step`, `original_query_bounds` | Same-source clock and image-licensed decoder suppliers already consumed by SLHC. Addresses false/true mean $L/R$; source true/false means $\alpha/\beta$, opposite to the numeric parity labels. The private declarations are existing content, not new proof gaps. |
| `NativeFullSourceProducer.sourceControl`, `native_source_producer`; private `traverse`, `production_reads` | The existing whole-source preorder supplier on its stationary contract. A retained subtree or unbounded traversal stack is not imported into this observer. |
| ABT Theorems 9.2–9.4 | Exact unknown-history fibers and future indistinguishability, with original leaf count fixed and historical epochs unbounded. A current clock is not an authenticated choice of historical origin. |
| Turing, *On Computable Numbers, with an Application to the Entscheidungsproblem*, §§1–2, pp. 231–232 [TURING] | Literature-attested automatic transition and complete configuration, including scanned-square number and the entire mutable tape. This underlies the repetition argument; it is not a theorem about this source's literal lengths. |
| Cabello, Eppstein and Klavžar, *The Fibonacci Dimension of a Graph*, Proposition 3.1 [CEK] | Literature-attested zero-interleaving map into no-adjacent-one words. Only its coordinate map is used; no isometric property or optimal Fibonacci dimension is asserted. |

**Definition 7.2 (remaining mathematical boundary).** The additional
service is local bit interpretation and owned one-letter transport.
The result proves no physical spacetime identification, no optimal
immutable code size, no sharp total observer memory, and no complete
compressed-receiver construction. Physical promise authentication,
initial source construction, source Read/Update internals and their
true costs remain separate premises. Finite examples cannot certify
these unbounded statements; their proofs are the arguments above.

[SLHC12]: https://github.com/the-omega-institute/trureturing/blob/5798b485e4a9343f8e446c666b8966ffd71cdb5a/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT_CONTINUATION.md
[SLHC11]: https://github.com/the-omega-institute/trureturing/blob/f14a84e00297c51a63cec763f74f2a896c23c8f7/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT_CONTINUATION.md
[PH81]: https://github.com/the-omega-institute/trureturing/blob/3605ccfd6e273bf9d9bda2bc93009239cfdb961e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_ACQUISITION_HORIZON.md
[PR57]: https://github.com/the-omega-institute/trureturing/blob/3605ccfd6e273bf9d9bda2bc93009239cfdb961e/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[ABT]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md
[TURING]: https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf
[CEK]: https://arxiv.org/html/0903.2507

## 追加锚（本行以下为增补区）

## 8. Exact literal support and a materialized immutable tail

**Definition 8.1 (parameters and physical meaning).** Retain Definitions
1.1–1.4, including whole materialization before the source call. Put
$H=h-1$. For $T=0$ choose the complete native table of SLHC Construction
11.6 with candidate width zero, and put $J=0$. For even $h$ and finite
$T>0$ choose SLHC Theorem 12.2 with $\Delta=2$, and put
$J=\lceil(T+2h)/2\rceil$. In both cases write $P=H+J$ and use the
corresponding $k,\ell,W_*,Q,U$ from Corollary 5.1. In particular $U=0$
on all promised runs, although the second native installation includes
unreachable Update rows.

A materialized letter cell need not be writable. A fixed cell containing
$R$ is an actual letter, whereas a binary integer meaning “repeat $R$”
is not a materialized string. The construction below has **$J$ distinct,
permanently read-only letter cells**, each containing $R$, on the receiver
side of the source boundary. They are physically installed and billed.
Their contents and protection are invariant on every installed control
valuation. Their allocation is not $\log J$ physical cells. The online
mutable count and the total physical storage are different quantities.

The operand will be one contiguous interval of actual letter cells:
a bounded writable prefix immediately followed by some of those fixed
$R$ cells. Its endpoints, every head used to produce it, and the retained
received information are mutable and counted. The source receives that
whole interval as its literal operand, just as (4.4) supplies a flat
array interval. It receives neither a repeat instruction nor a request
to follow a pointer into a compressed representation. There is no
source call while this interval is being prepared.

**Lemma 8.2 (the complete native menu, including unreachable rows).**
For these particular complete native tables the exact distinct literal
menu, and also its prefix union, is

$$
\begin{aligned}
\mathcal D_{H,J}
 &=\{pR^j: |p|\le H,\ 0\le j\le J\}\\
 &=\{p:|p|\le H\}\ \cup\
   \{xR^j:|x|=H,\ 1\le j\le J\},\\
\mathcal M_{\rm nat}&=\operatorname{Pref}(\mathcal M_{\rm nat})
 =\mathcal D_{H,J},\qquad
|\mathcal D_{H,J}|=2^H(J+2)-1,\qquad
P_{\rm inst}^{\rm nat}=H+J.
\tag{8.1}
\end{aligned}
$$

Proof. At $T=0$, every valid VALUE code permits every path of length
at most $H$: choose its padding zero and its independent branch, leaf
and parity counters zero. Its literal is that path. GUARD, POLL and
UPDATE are unavailable in this case; malformed codes and routing rows
read the root. Thus its exact menu is $\mathcal D_{H,0}$, including
$H=0$.

For $T>0$, inspect the total intermediate table $I_{12}$, rather than
only its lawful executions. At cell $c$ its installed candidates are

$$
N\in[\max(0,2c-2h+1),\ \max(0,2c-2h+1)+2h],
\qquad 0\le c<J.
\tag{8.2}
$$

Here $J\ge h+1$. The intervals for $c<h$ are $[0,2h]$;
subsequent lower endpoints increase by two, and the last upper endpoint
is $2J-1$. Their union is exactly $[0,2J-1]$. Hence VALUE supplies
every $pR^j$ in (8.1): choose a candidate with $\lceil N/2\rceil=j$
and choose that valid path $p$. For $j=0$ use $N=0$; for $j>0$ one
may use $N=2j-1$. Counter bounds do not impose a reachable-traversal
condition on these installed rows.

A GUARD literal is $p^-R^{\lfloor N/2\rfloor+1}$, with
$1\le |p|\le H$ and $1\le N\le2J-1$. Its prefix has length at most
$H-1$ and its right suffix at most $J$. SEARCH and POLL use respectively
$R^m$, $1\le m<J$, and $R^c$, $0\le c<J$. Invalid intermediate
codes use the empty literal. Construction 11.6 only adds root Reads:
in ready phases it exposes every intermediate instruction, including
each valid VALUE row; every other Read is a root Read. It introduces
no additional nonempty literal even on malformed bank/flag combinations.
This proves equality, not merely a reachable-menu containment.

To obtain the second description in (8.1), split a word at position
$H$ when its length exceeds $H$; the remaining letters are all $R$.
Conversely its full length-$H$ prefix can serve as $p$. Short words
contribute $2^{H+1}-1$, and each positive excess length contributes
$2^H$ disjoint words. Prefix closure and the attained maximum follow.
The actual D5 query syntax `originalQueries` has precisely the VALUE
and GUARD forms used here; its private `original_query_bounds` is
already a supplier of the length bound. ∎

**Construction 8.3 (receiver storage and actual operand).** Reserve two
disjoint writable arrays $X,Y$, each of $H$ letter bits. $X$ retains
the first $\min(d,H)$ arrivals in order. Place $Y$ at positions
$-H,\ldots,-1$ of an operand lane, and place the immutable string
$R^J$ at its positions $0,\ldots,J-1$. These are actual consecutive
letter positions of a single lane. Other registers and the $X$ lane
are elsewhere. Fixed wiring between letter positions does not select a
current position: its moving head and interval endpoints are counted.

When the arrived word has length $d$, set

$$
m=\min(d,H),\qquad n=\max(d-H,0).
\tag{8.3}
$$

After the end delimiter, compute these two integers by paid bit loops.
Copy $X_i$ into $Y_{-m+i}$ for $0\le i<m$, using two counted heads
and a one-bit buffer. Walk the operand head over all $n$ tail cells,
reading and checking each $R$; no tail cell is written. Walk back to
$-m$ and verify the assembled interval against the retained receiver
representation, one cell at a time, before setting its material seal.
The latter scan has length $m+n=d$. Its comparisons use $X_i$ in
the prefix and the constant letter $R$ in the tail. Neither scan
consults the sender's row, graph literal or source.

The source-facing value is now the whole flat word

$$
\operatorname{mat}(Y;m,n)
   =Y_{-m}\cdots Y_{-1}\,R_0\cdots R_{n-1},
\quad 0\le m\le H,\quad 0\le n\le J,\quad (n=0\ \lor\ m=H).
\tag{8.4}
$$

The subscripts on $R$ denote different installed cells, not a runtime
expansion operation. Empty intervals are permitted. The physical
source service consumes the same root-relative letters as before;
it is given no extra source operation, prefix feedback, decoder or
history. The receiver's interval descriptor is ordinary operand
framing, counted just like the length in (4.4). It is resolved on the
observer side into an already present interval before the call.
Relocating an operand within observer memory does not reroot the
source: its first letter still means an edge from the original root.

**Proposition 8.4 (materialization, and its exact information premise).**
Suppose $X[0:\min(d,H)]$ is the actually arrived prefix and all subsequent
arrivals are $R$, with $d\le H+J$. Construction 8.3 terminates using
$H$ further writable letter cells and a constant number of
$O(\log(H+J+2))$-bit slots. At its seal the entire materialized operand
equals the arrived word and is determined by receiver information
alone. Its mutable data do not include a length-$J$ tail.

Proof. The prefix-copy invariant is
$Y[-m:-m+i]=X[0:i]$ after $i$ copies; reading, seeking and the separate
write cuts preserve the already copied part. All $n$ other cells are
present and equal $R$ before and after every online step. Thus (8.4)
equals $X[0:m]R^n$. The stipulated received-prefix premise and (8.3)
identify this word with all $d$ arrivals. Each loop has its finite
bound in counted slots. The final verification and head homing finish
before the source instruction is enabled on a lawful run. ∎

This proposition uses the source-specific support theorem: past
position $H$, there is only one allowed letter. A received $R$ still
changes the receiver's represented length, and that length determines
how many **physical** tail cells belong to its operand. Removing an
arrival changes that boundary; changing an early letter changes a
writable cell and its copied operand letter. An unexpected late $L$
is retained as a pending letter and rejected before sealing. Thus this
is not a passive transmission followed by unrelated ROM row selection.
No complete-word dictionary is searched at commitment. The reusable
right tail is a fixed part of the receiver's material, selected only
through the number of letters it actually received.

If an additional interface required every operand cell to be writable,
this construction would not meet that additional requirement. Definition
1.3 requires actual arrivals, paid decoding and whole materialization;
it does not require writability of each materialized letter. Here the
entire word is simultaneously present, and its immutable cells are
billed as physical storage. Streaming $R^n$ into an uncounted output
tape, passing $n$ to the source, or calling a fixed $P$-cell writable
tail “logarithmic space” would not establish Proposition 8.4.

## 9. Arrival invariants through every local cut

**Construction 9.1 (transactional prefix accumulation).** Use one
single-letter mailbox, separate from both receiver arrays, and a
receiver-owned pending-letter bit $e$. Use two $r$-bit receiver count
banks $a_0,a_1$, an active-bank bit $v$, and a receiver phase
$\phi\in\{\mathsf{pre},\mathsf{ready},\mathsf{pending},\mathsf{sealed}\}$.
Put $a=a_v$ only in the mathematical description; it is not a third
register. On each frame entry set $\phi=\mathsf{pre}$ and clear the
material-seal bit in the same paid entry transition. RESET clears
$X,Y$, both count banks, all response
flags and mailbox control by scans. Only after those scans does it
enter ready with $v=0$, $a_0=a_1=0$. No arrival takes place in pre.

To receive a letter, the sender first writes the mailbox, seals it
and hands ownership to the receiver. The mailbox bit is read into
a local transfer bit by a paid instruction. The receiver arrival is
one paid write of that bit into $e$, simultaneously setting
$\phi=\mathsf{pending}$. This event counts as an arrival even if $e$
already held that bit. Until this occurrence the received word has
not changed. The active count $a_v$ and selector $v$ are held fixed
through the following routine.

If $a<H$, seek to $X_a$ and copy $e$ there; otherwise check $e=R$.
An overflow $a=P$ or a late $L$ enters a source-free error hold without
acknowledging another letter. On a lawful frame neither occurs, by
Lemma 8.2. Copy the active count into the inactive bank one bit at a
time, then increment that inactive bank by the ordinary carry scan.
Finish all its carry clearing, head motion, comparison and return work.
Finally, one paid local control transition flips $v$ and changes
$\phi$ to ready. These are permitted local multi-bit writes, not
source-response writes. Acknowledgement releases the mailbox for
the next letter. No next arrival can precede this acknowledgement.

The end delimiter is a distinct nonletter handoff. It can be accepted
only in ready, after the last acknowledgement. Its acceptance changes
$\phi$ to sealed. Construction 8.3 then uses the active count and
$X$, preserving both. Its additional material-seal bit is different
from the arrival phase. All materialization, source-receipt and response
continuation cuts retain the sealed receiver phase until the next
frame's pre transition. An empty frame follows this same delimiter
path with active count zero.

**Theorem 9.2 (every-cut recovery with pending writes and carries).**
On every lawful Read frame, let $A_c$ be the word of actual receiver
arrivals through cut $c$. This is proof notation, not a stored log.
Define

$$
\begin{aligned}
B(X,a)&=X[0:\min(a,H)]R^{\max(a-H,0)},\\
\mathcal R(c)&=
\begin{cases}
\varepsilon,&\phi=\mathsf{pre},\\
B(X,a_v),&\phi=\mathsf{ready}\text{ or }\mathsf{sealed},\\
B(X,a_v)e,&\phi=\mathsf{pending}.
\end{cases}
\tag{9.1}
\end{aligned}
$$

Use the empty default when a count is outside $[0,P]$. This makes a
total mathematical projection on installed valuations. Its claimed
arrival meaning is on lawful executions. At **every** paid microstep
cut, $\mathcal R(c)=A_c$. In particular it does not rely on a torn
counter, a routine PC or a moving materialization head for its length.

Proof. In pre, no new-frame arrival has occurred; partial reset of old
data is irrelevant. Entry to ready establishes the empty word. Suppose
ready represents $A_c$ of length $a$. Sender/ROM/mailbox work leaves
$(X,a_v,v,\phi)$ fixed. The arrival changes only $e$ and the phase
among the fields in (9.1), so immediately after it (9.1) equals the
old prefix followed by the actually copied letter.

When $a<H$, the only prefix-array write is at $X_a$; the pending
projection uses $X[0:a]e$, so its meaning is unchanged before and
after that write. When $a\ge H$, $X$ is unchanged and the pending
letter is $R$. The active counter and selector stay fixed during
every bit-copy, carry, branch, head move and return cut. Therefore
none of the inactive bank's intermediate values changes (9.1).

For completeness, if the old count's first zero bit is $j$, clearing
its lower $i\le j$ one bits in the copied inactive bank gives
$a-(2^i-1)$; setting bit $j$ gives
$a-(2^j-1)+2^j=a+1$. The scan terminates because $a<P<2^r-1$.
After the final selector/phase transition, the new active count is
$a+1$. For $a<H$, its longer $X$ prefix includes exactly the copied
$e$; for $a\ge H$, its right-run length increases by one. Ready
therefore has the same word as pending. Acknowledgement and arbitrary
head motions preserve it. The delimiter only changes ready to sealed;
its word is unchanged. Materialization writes only $Y$ and scratch,
so its every cut preserves the same whole received word. Source receipt
changes only a response flag. The next frame entry alone changes the
meaning to a new empty word before reset begins. This covers $H=0$,
$d=0$, the cut at $a=H$, all binary carries and partial clearing. ∎

The pending-letter bit is essential to this particular invariant. For
example an arrival of $L$ into an already zero bit changes the prefix
without changing that data bit. Ready and pending remain distinguishable
by their phase. Similarly $a=3$ need not be recoverable from a partially
incremented inactive bank passing through $2,0,4$; the still-active
bank says $3$ until the selector changes. Both banks and that selector
are charged even when one is semantically inactive.

**Proposition 9.3 (dynamic sufficiency and its failure fibers).** For
lawful prefixes in $\mathcal D_{H,J}$, (9.1), with the pending discipline,
supports the next arrival, termination, and paid production of (8.4).
It is dynamically sufficient for those operations, rather than merely
an injective code at completed cuts. It is not a receiver for arbitrary
words of length $P$.

Proof. Constructions 9.1 and 8.3 give the required operations and their
intermediate storage. Omitting $e$ from a pending cut identifies the
two possible next letters before position $H$. Omitting the phase
identifies the zero-write example. Omitting the count identifies
$xR^n$ and $xR^{n+1}$ and loses the materialized endpoint. A late $L$
cannot be incorporated as an $R$ without identifying distinct words;
the stated error behavior preserves it pending and makes no source
call. Retaining a count without the material lane would recover a word
mathematically but would not supply its whole physical operand. These
are distinct insufficiencies, not alternative encodings of one missing
bit. ∎

## 10. One autonomous complete installation

**Construction 10.1 (graph interpreter and finite inventory).** Keep
the exact padded native image $T_0$, graph nodes $N=W_*(P+16)$, graph
format, $w_G$ and $T_G$ of Definitions 4.1–4.2. Every native row,
including a routing row, still has its own block. Replace only the
local meanings of RESET, PUT and COPY. RESET is Construction 9.1.
Each nonpadding PUT actually sends its one installed letter through
the one-letter mailbox and waits for the receiver acknowledgement;
it does not build a sender array. NOP sends nothing. COPY sends and
accepts the end delimiter, runs Construction 8.3 and sets its material
seal. ISSUE-READ then submits (8.4). Update blocks bypass delivery
and materialization as before. Halt blocks retain their fixed output.

The expanded graph is an immutable sender program. Its moving graph
and ROM positions belong to the following forty-eight $r$-bit slots.
This inventory replaces the arrays and slots of Definition 4.3;
none of its old three $P$-cell arrays is retained.

| Slots | Persistent meanings, in displayed order |
| --- | --- |
| 1–8 | Current graph node; pending node; saved old node; interpreter PC; routine return PC; code head; graph/ROM head; work head |
| 9–16 | Table base; row base; row offset; field position; field length; row width; graph-node limit; image end |
| 17–24 | Receiver count bank $a_0$; count bank $a_1$; prefix head; operand head encoded with offset $H$; copy index; clear index; bit index; carry-scan index |
| 25–32 | $H$; $J$; $P$; final operand prefix length $m$; final tail length $n$; materialization position; verification position; bounded continuation |
| 33–40 | First arithmetic temporary; second arithmetic temporary; comparison position; saved transfer-node identity; first macro-row bank; second macro-row bank; next macro-row scratch; response-slot offset |
| 41–48 | Header input head; header position; allocation position; loader return; graph-index width; native-word width; bounded loop limit; saved field return |

There are ninety-six additional Boolean cells. They include the five
typed response flags; the mailbox, sender-transfer and receiver pending
bits; mailbox owner/seal/acknowledgement and delimiter flags; $v$;
the two bits of $\phi$; the material seal; macro-bank selector and
response-continuation stage; graph-transfer stage; carries, borrow,
comparison and bit-operation flags; current ROM/work bits and fixed
finite control. Reserve unused Boolean cells too. They introduce no
hidden data type. Only $X$ and $Y$, of $H$ bits each, are further
writable arrays. All routines are inlined or use the listed bounded
returns; no call stack, whole-address staging array or history persists.

Use the paid bit-read/write, unit head movement and finite-control
convention of Definition 4.3. Integer copying and arithmetic are bit
loops. A head's location is the numeric value of its named slot, never
an additional physical position excluded from the configuration.
A paid head move updates that encoding and its fixed continuation;
local multi-bit writes are allowed. Copying a variable-width index
still costs its bit loop. Row fetches scan the actual ROM distance.
Offset computation may enumerate row boundaries instead of multiplying.

The current native row is retained in the active one of slots 37–38
throughout the frame. Before a response, it supplies the macro
projection independently of partly copied graph indices. After a
response it and the one response flag supply $\delta(w,r)$. The selected
LINK contains its compiled successor block; a paid scan counting block
boundaries recovers that block's native row index in the next-row
scratch slot. Copy this index into the inactive macro bank while the
old bank and flag remain fixed. A local continuation transition marks
that completed bank authoritative before clearing the flag. Its selector changes
only after completion. Graph transfers use slots 1–3 and their own
stage in exactly the saved-old/pending manner of Definition 4.4.
All frame-entry and return operations use these counted stages.
Neither a torn graph field nor an erased flag supplies authority.

**Definition 10.2 (allocation and readonly protection).** Let $I_1$
be the bit length of fixed sequential interpreter, initializer and
nonrecursive routines implementing Constructions 8.3, 9.1 and 10.1;
let $I_c$ include the fixed graph writer and tail manufacturer. These
are fixed finite bit programs independent of $h,T$. Put

$$
\begin{aligned}
Z&=T_G+I_1+I_c+N+W_*+P+\ell+H+J+64,\\
r&=\left\lceil\log_2\bigl(2^{20}(Z+1)^2+1\bigr)\right\rceil,\\
b&=2H+48r+96,\qquad L=2b-1,\qquad S_{\rm inst}=2^b.
\tag{10.1}
\end{aligned}
$$

Install the zero-interleaving image of **all** $b$-bit valuations.
Separators are fixed zero. Thus $b$ is the number of independently
writable bit cells physically reserved, $L$ is the no-$11$ configuration
encoding width, and $2^b$ counts all installed composite states.
Neither unreachable states nor dirty scratch arrays are quotiented out.
The two $H$-cell letter lanes can be physically consecutive letter
positions while the configuration has this abstract zero-interleaving
encoding: separators encode states, not extra address letters. If
separators are physically realized as well, charge their $b-1$ fixed
cells separately; they do not create writable tail cells.

A self-delimiting allocation header $J_r$ declares the forty-eight
slot widths, ninety-six Boolean cells and two array lengths. A fixed
gamma format, with zero array lengths encoded by their value plus
one, has $|J_r|\le256r+256$. The resident immutable image has

$$
B_{\rm ro}=T_G+I_1+|J_r|+J
\tag{10.2}
$$

bits, before optional physical zero separators. The last summand is
the actual $R$ lane; it is additional to every literal copy in $T_G$.
The permission map is fixed by physical region, not a mutable owner
bit: every write addressed to code, headers, the $R$ lane or a fixed
separator holds that cell on **all** controls. The error continuation
may change counted local control, never readonly content.

All heads, counters, offsets, header scans and bounded arithmetic
intermediates used on lawful executions are below the slot bound
$2^{20}(Z+1)^2$. Indeed the original graph/table extents are at most
$Z$, extra readonly and writable lengths are at most
$2Z+400r+512$, and row-offset arithmetic is bounded by $Z^2$.
Here $Z\ge160$ and $r\le22+2\log_2(Z+1)\le24+2Z$; these inequalities
put the stated extents strictly below the chosen squared bound.
No numeric register is an unbounded natural-number workspace.

**Proposition 10.3 (total rows, exact composite menu and receipt).**
There is a total instruction rule on the installed set (10.1) with
the described lawful execution. Its complete Read menu is exactly
$\mathcal D_{H,J}$, not all words of length at most $P$. Every installed
source-response receipt changes at most one encoded bit. With one
Read PC, one Update PC and two fixed-output Halt PCs, its counts are

$$
n_R^{\rm comp}=n_U^{\rm comp}=2^{b-r-5},\qquad
n_H^{\rm comp}=2^{b-r+1},\qquad
n_{\rm typed}^{\rm comp}=5\,2^{b-r-5}.
\tag{10.3}
$$

Proof. Use ERROR holds for unused PC/opcode patterns; use fixed-width
arithmetic, zero for an out-of-range read, and a holding protected write
for out-of-range or readonly destinations. Out-of-range motion has a
local error successor. These rules are total and create no memory or
source information. Ordinary bit-loop branches inspect their named
bits. Lawful paths perform the bounds/permission scans before using
their results. Malformed paths need not terminate or simulate a promised
entry; they remain installed and counted.

At Read PC with all five response flags zero, select (8.4) when its
three range conditions hold, and the empty materialized interval
otherwise. This is the same total operand-framing convention as
Proposition 4.5, now for one mixed readonly/writable flat lane. It
does not decode $X$ or a repeat count during the source operation.
Even at an unreachable unsealed issue configuration, every selected
letter already exists in that lane. Validity of receiver provenance
at such an arbitrary configuration is not asserted. On lawful runs
the paid scans and material seal precede this PC.

Every selected word lies in $\mathcal D_{H,J}$. Conversely choose
any $p$ of length $m\le H$ by putting its bits in the last $m$ cells
of $Y$ and setting $n=0$; choose any $xR^n$ with $|x|=H$ by filling
all of $Y$ and selecting that $n\le J$. Set Read PC and zero flags.
These configurations are all installed, regardless of reachability.
They realize every member of (8.1), proving the exact composite menu
and its exact prefix union and longest installed literal.

At actual Read receipt set exactly its typed flag; at actual Update
receipt set only $f_\star$. The PC and every other bit hold. The issue
PC with nonzero flags performs local continuation or ERROR, never
a repeated source call. Wrong-typed, multiset or malformed flags enter
ERROR by local work. Thus all source rows, reachable or not, have
legal one-bit receipt; the zero-interleaving map preserves that one
coordinate change. Each of the two source PCs fixes $r$ bits and
requires five zero flags, giving (10.3). The two Halt PCs each fix
$r$ bits and their output. The remaining configurations are local.
The original native Update and Halt row counts remain the different
counts of Definition 4.1 and SLHC.12.5. ∎

**Theorem 10.4 (complete trace refinement and sharp encoded width).**
For $T=0$ and every $h\ge1$, and for finite $T>0$ and even $h$, the
installation above meets Definition 1.3 on the original all-shape
parity task. It has

$$
L=O\bigl(h+\log_2(T+1)\bigr),\qquad U=0,
\qquad
L_{\min}=\Theta\bigl(h+\log_2(T+1)\bigr).
\tag{10.4}
$$

The minimum is over complete encoded online mutable width under that
definition, with immutable and physical storage separately billed.
It includes online initialization. Erasure preserves every selected
native row, exact literal, raw reply, source successor, routing Read,
genuine Update and first fixed-bit Halt of the chosen native table.
The receiver projection is (9.1) at every local cut, and the actual
operand is fully materialized as (8.4) before each Read.

Proof. Lemma 8.2 guarantees every installed native PUT sequence has
only $R$ after position $H$ and length at most $P$. Each letter's
bounded receipt routine terminates and acknowledges before the next
PUT. Theorem 9.2 makes the sealed receiver word exactly the sequence
of these actual arrivals. Proposition 8.4 then supplies exactly the
original table literal in physical cells. This also handles every
routing Read, whose frame delivers zero letters but still commits
Read$(\varepsilon)$ and receives its real raw reply.

The explicit simulation relation uses the unchanged source $y$ and
the active macro-row bank before a source call. Source-free fetches,
mailbox operations, counter carries and materialization preserve
$(y,w)$. At actual receipt of $r$ it relates to
$(y',\delta(w,r))$: until the new macro bank is completed, its value
is determined by the fixed old bank and one-hot flag; afterwards by
the completed new bank and continuation stage. The flag is cleared
only in the latter case. Partial graph copies have their separate
old-node stage and do not change this macro projection. Finite local
cleanup arrives at the block of precisely $\delta(w,r)$. An Update
block performs the same one genuine $\rho$, with only its original
constant acknowledgement. Only the original Halt block's node zero
selects its fixed Halt bit.

Induction on native calls is therefore the simulation of Definition
3.1, with identity address map and same-source action map. It gives
the entire raw trace, not just equal parity. A single causal simulator
executes the fixed local program and pauses for each raw reply only at
its actual receipt, as in PR57.T3. All earlier labels and local fees
are functions of the installation and acquired native prefix. No
source-duration or source-work label is used. The native supplier's
termination and parity theorem then give finite firstHalt. Its
$\Delta=2$ choice has no reachable Update, and the $T=0$ choice also
has none.

Finally $k=O(h+\log(T+1))$, $\log W_*=2k+8$ and
$P=O(h+T)$. The displayed expanded graph gives
$\log(Z+1)=O(k+\log(P+\ell+2))=O(h+\log(T+1))$.
Equation (10.1) proves the upper bound, counting both dirty banks,
both arrays and every malformed valuation. Corollary 2.3 supplies
the lower bound for this same complete autonomous interface, even
allowing unrestricted genuine Updates. At $h=1,T=0$, $H=J=P=0$;
arrays and the tail are empty, while counted control and response
storage give a constant upper and the lower remains positive. ∎

## 11. Simultaneous bills, initialization and retained boundaries

**Proposition 11.1 (cost vector of this one construction).** Define
$C(Z)=2^{50}(Z+1)^{10}$. There are choices of the indicated sequential
scan routines such that, on every promised run,

$$
\begin{aligned}
Q_{\rm serial}&=Q,& U_{\rm serial}&=U=0,&
A_{\rm serial}&=E_{\rm receiver}=A,\\
E_{\rm two\ channels}&=2A,& P_{\rm run}^{\rm serial}&=P_{\rm run},&
P_{\rm inst}^{\rm comp}&=P,\\
M_{\rm comp}&=|\operatorname{Pref}(\mathcal M_{\rm comp})|
 =2^H(J+2)-1,\\
I+I_{\rm init}&\le(Q+U+2)C(Z).
\tag{11.1}
\end{aligned}
$$

Here $Q,A$ have simultaneously the explicit native bounds in Corollary
5.1: its $T=0$ row or (5.2). In particular the native $Q$ is polynomial
in $h+\log(T+1)$ for the positive-$T$ choice. The local work bound is
polynomial in **expanded installation size** $Z$, not in that binary
parameter size. Immutable bits are (10.2), writable cells are $b$,
reserved encoded span is $L$, and the materialized lane has $H+J$
physical letter cells of which exactly $H$ are writable.

Proof. One PUT has the following four distinguished paid occurrences:
mailbox letter write/seal, ownership handoff, receiver arrival, and
acknowledgement. Preparation of its transfer bit, all ROM fetches,
seeks, tests, receiver normalization and graph transitions are additional
paid occurrences. A Read frame also has end-marker handoff, receiver
end acceptance and final material seal. Under this explicit convention,

$$
I_{\rm handoff}=4A+3Q.
\tag{11.2}
$$

There are exactly $A$ letter events in each channel; end markers are
not letters. Materialization separately has $\sum_i\min(|p_i|,H)$
prefix-copy writes, $\sum_i\max(|p_i|-H,0)$ tail-check reads and
$A$ final interval-verification visits, with all positioning and
comparisons additional. RESET makes $2HQ$ array-clear writes on the
Read frames. These counts do not inherit the old $8A+4Q$, whose two
full-buffer copy bodies are absent here.

For a coarse work bound, sequential field operations and full seeks
cost at most $2^{16}(Z+1)^3$ bit/move/control steps each: slot widths
are $O(\log Z)$, physical extents $O(Z+r)$, and offsets can be
obtained by scans of the at most $Z$ graph bits. Each macro frame
visits at most $P+16$ graph nodes, has at most $P$ receipt loops,
clears $2H$ letter cells and runs bounded copy/compare/materialization
loops of length at most $P+H+48r+96$. Even allowing full-field scans
and repeated-addition offset work inside each, fewer than
$2^{16}(Z+1)^3$ such routine invocations suffice per frame.
Initialization satisfies the same estimate. Their product is below
$C(Z)$. The graph writer of Theorem 4.7 uses at most five native-table
scans per row plus $N$ record writes; two extra nested loops bounded
by $Z$ still fit $C(Z)$. Manufacturing the $J$ literal $R$ cells and
checking them is a further bounded sequential loop, also covered.
These are analytic upper bounds for finite routines, not unit-cost
arithmetic or measurements of a compiled interpreter. ∎

**Definition 11.2 (offline and online peaks).** Manufacture the fixed
graph, native image, code, header and $R$ lane before an online run.
A sufficient total simultaneous manufacturing/installation allocation,
including an input image, output image, compiler, two native-key scratch
words and the allocated online apparatus, is

$$
B_{\rm manufacture}\le8(Z+|J_r|)+L.
\tag{11.3}
$$

The writer is the sequential row enumerator of Theorem 4.7, followed
by writing $J$ fixed $R$ letters; its input/output/key storage and
bounded slots fit this allowance. Its work is at most $C(Z)$ for this
expanded-image convention. If compiling from binary $h,T$ also
enumerates the native table, its finite table-construction time is
an additional offline cost; (11.3) permits enumeration with the fixed
field rules and bounded native keys, without retaining all source trees.
One may bound that enumeration by a further polynomial in $Z$ using
bitwise field tests and the explicit SLHC response rules. It is not
a polynomial in the binary input length claim.

After manufacture the readonly regions are permanently protected.
The online initializer parses those regions with its listed heads,
zeros only the $b$ writable bits, installs the common graph/macro row,
and sets the pre phase. Its initialization path makes no source call
and enters no Halt. It needs no writable image copy and never converts
readonly cells into writable cells. Its peak writable allocation is
already $b$, simultaneously with all of (10.2). Thus online startup
is included in (10.4); the manufacturer's temporary writable output
image is separately included in (11.3). Counting all manufacturing
workspace as well as online workspace in one lifetime maximum gives
that larger bound, not (10.4). This distinction is also necessary for
the expanded immutable table of the macro supplier itself.

**Proposition 11.3 (source time, addresses and boundary information).**
The following maps refer to one actual run, with no new observation port.

1. At a sender cut, the installed native literal and counted graph
   position determine the remaining PUT letters. The sender is not
   represented by immutable code with an omitted moving position.
2. At each receiver cut, (9.1) recovers precisely the arrived prefix.
   The same prefix may occur in many native rows, so this recovery
   need not determine the sender row or future continuation. The
   separate retained macro bank supplies that continuation.
3. At material seal, the receiver's $(X,a_v)$ determines $(m,n)$ and
   the whole interval (8.4). Conversely, reading that materialized
   interval and its counted length recovers the arrived word.
   Irrelevant padding, inactive count bits and scratch are fibers of
   this recovery; they remain charged configurations.
4. At source receipt, the one-hot flag identifies the raw reply;
   together with the old native row it determines the macro successor.
   The reply alone generally identifies neither the address nor the
   historical source. Cleanup can discard that flag after transferring
   the required successor information.

For the positive-$T$ table, the acquired cell and accepted polling
reply identify the current right clock $K=2c$ or $2c+1$. Since $U=0$
this is also the entry clock, but still $K=t+\kappa(u)$. The completed
address code is not a certificate of either summand. Proposition 6.2's
identical-current-tree history fibers and its odd-$h$ obstruction are
unchanged. For even $h$, one fixed finite installation still cannot
handle unbounded lag: its finite $J$, heads and complete state set
contradict Theorem 2.2 as the entry bound increases.

Proof. The first four assertions use respectively the graph rule,
Theorem 9.2, Proposition 8.4 and the macro-bank receipt invariant.
The clock statement is exactly the supplier's $\Delta=2$ right-ray
law, not a measurement of hidden time. For example the histories
$(A_S,1)$ and $(B_S,0)$ retain the same current source, literal arrivals
and all future replies under common initialization. Their parity
differs when $h$ is odd. A materialized address cannot separate these
fibers. For unbounded even lag, Corollary 2.3 requires unbounded width
even if arbitrarily many immutable letters have been installed at
each separate finite parameter choice. ∎

The exchange established here is precise: a source-specific arbitrary
prefix of at most $h-1$ bits is retained, a repetitive spatial suffix
is represented during receipt by a counted length, and paid decoding
uses a physically present immutable run to restore the whole operand.
The $\log(T+1)$ mutable coordinate replaces no physical tail storage
or actual transmission time. Theorem 2.2 and (2.1) still force the
same long-frame configurations and same-run traffic. A run's $A$
still cannot stand in for (8.1)'s installed union. This is a resource
comparison for the stated observer/source boundary, not an
identification of physical space with time or memory.

## 12. Provenance and falsifiable scope of the materialization bridge

**Proposition 12.1 (what supplies the new conclusion).** The additional
source-specific bridge is the conjunction of the **exact full native
support** (8.1), an actually receiving representation with the
every-cut invariant (9.1), and a **whole physical operand** (8.4)
with only $H$ writable materialization cells. The inventory and total
rules make this bridge compatible with complete-state counting and
one-bit raw receipt. Removing any of these premises removes the
claimed proof of (10.4): a small dictionary alone says nothing about
operand production; completed-cut recovery alone says nothing about
pending arrivals; and a small online working tape alone says nothing
about an omitted output tape.

The exact existing-work correspondence is as follows.

| Source | Role and boundary in §§8–11 |
| --- | --- |
| SLHC Constructions 11.5–11.6 and Theorem 12.2 at [5798b485][SLHC12] | Complete native supplier on all unknown shapes, including its invalid-code defaults, bank routing, VALUE/GUARD syntax, cell-search rows, exact genuine Updates and native cost bounds. Lemma 8.2 derives the exact menu from these full rules; the supplier's looser menu bound alone would not give it. |
| SLHC Theorem 12.3 and this volume §§2, 5.3, 6.2 | Same-run long literals, autonomous complete-width lower order, unchanged source-growth/service coordinates and history/unbounded-entry obstructions. These results are reused, not newly proved here. |
| EA Proposition 8.1 at [3605ccfd][PH81]; this volume §§4.1–4.2, 4.4–4.7 | Paid finite graph fetch, bit loops, explicit heads, saved-old/pending graph transfers, graph writer and expanded immutable storage. The inventory, receiver routines, readonly tail, online allocation and event constants here are separately specified; the old flat-buffer allocation is not imported. |
| Transport PR57.D7/L4/T3 at [3605ccfd][PR57] | Owned copy induction and causal simulation proof. Its full growing archives and two complete-buffer protocol are different allocations. The letter mailbox has its own stated four-event handshake and prefix invariant; no $8d+4$ price is transferred to it. |
| `DelayedOriginalReadout.originalQueries`, `right_clock_iterate`, `right_clock_readout`, `original_decoder_correct`; private `original_query_bounds`, `clock_step` | Existing precise suffix syntax, current clock, image-licensed decoding and query-length facts. Private status does not make them new gaps in this prose application. |
| `NativeSerialMachine.nativeStep`, `Run`, `replay_deterministic`, `operational_replay`; `NativeSerialEffective.original_code_service_simulation` | Same-source chronological vocabulary and erasure preserving addresses/replies/Updates/Halt. The effective theorem's arbitrary numeric workspace and certified epoch/history interface do not supply the present finite-width result. |
| `NativeSerialDepth.descriptor`, private `descriptor_eq`, `bounded_read_support` | Proof-only descriptor and support constraints, not an autonomous receiver or materialization service. |
| Pinned Mathlib `Computability/TuringMachine/StackTuringMachine.lean`, `TM2.Cfg`, `stepAux`, `step`, revision `db584cd6d46c92f209a44c0f1c829460d327499d` | Generic configurations include the label, internal value and all stacks. This supplies a machine vocabulary, not a finite receiver allocation or a whole-materialized-literal theorem. No upstream simulation theorem is used as a substitute for the receiver proof. |
| Cabello–Eppstein–Klavžar, Proposition 3.1 [CEK] | The explicit zero-interleaving map; no isometric embedding or optimal coding constant is required. |
| Bille, Ettienne, Gagie, Gørtz and Prezza, *Decompressing Lempel–Ziv Compressed Text*, §1 and Theorems 1–2 [LZSPACE] | Their problem explicitly outputs a stream without storing it, and counts working space on top of input and output. Its small working-space decompression results therefore do not establish this whole-operand contract. No LZ theorem is needed to build the fixed right tail. |
| Turing §§1–2 [TURING] | Complete configuration and automatic progress; an immutable tape with an omitted moving head is not an autonomous small-state machine. |

These are ordinary mathematical derivations in the stated model, with
no new Lean certification or worldwide originality claim. The new
materialization argument uses readonly **letters** already paid in
physical storage, not a readonly state name masquerading as a payload.
The universal memory statement concerns the online mutable coordinate;
physical source Read/Update internals and their separate costs in
(5.5)–(5.6) remain premises. Since $U=0$ here, the source stays at its
actual entry tree throughout; the address routines do not construct
or copy that tree.

**Definition 12.2 (finite falsification targets).** A finite receiver
model can enumerate $\mathcal D_{H,J}$ and interrupt the specified
routines before and after each pending write, inactive-bank copy bit,
carry bit, selector change, head move, reset write, delimiter and
materialization step. Its assertions are equality of (9.1) with the
actual arrival trace, equality of (8.4) with the whole word at issue,
and absence of a source issue before material seal on an initialized
execution. Empty words, $H=0,J=0$, counts on both sides of $H$, and
all-ones counts immediately before a carry are mandatory instances.
Malformed range descriptors must select root; malformed response masks
must not reissue. Each of four Read replies and the sole Update reply
must set just its own zero flag, even if other scratch is malformed.
Writes addressed to the immutable tail must preserve every tail cell
regardless of control.

Such a receiver/string model does not execute a complete graph
interpreter, prove supplier parity, or exhaust (10.1)'s complete state
set. A further falsifiable full realization question is whether a
bit-level interpreter with exactly the inventory in Construction 10.1
realizes the stated routines and simulation on arbitrary parameter
instances without an extra persistent field. Its proof obligation is
the specified total transition refinement and allocation, rather than
finite agreement of final XOR alone. The ordinary construction and
proofs above do not claim that such a compiled interpreter has been
produced or kernel checked.

[LZSPACE]: https://arxiv.org/html/1802.10347

## 追加锚（本行以下为增补区）
