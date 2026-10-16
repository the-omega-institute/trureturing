# Native acquired input, the unfinished-request frontier, and actual replay

> This volume is append-only reference input. Its results are ordinary
> mathematical proofs for the declared ideal machine, with no new Lean
> certification claim. Corrections and additions to merged text belong after
> the canonical append anchor.

## 1. Scope and supplied mathematics

**Convention 1.1 (the question and the result).** An external choice becomes
part of a machine's acquired information when its input operation executes.
That occurrence can precede its tape write, a complete request, a source
response, a producer row seal, and acquisition by a different owner. The
results below concern those distinct cuts of one actual source execution.
They give a sufficient reconstruction code through every primitive cut of a
specified serial runtime, and a sharp conditional information requirement on
actual equal-clock unfinished-request families. They do not give four global
exact kernels for spatial support, time, continuation boundary, and callable
memory.

**Definition 1.2 (trees and the source).** Use the original free nonempty
ordered binary trees

$$
\mathcal T::=\alpha\mid\beta\mid\langle s,t\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

Let $\lambda(t)$ be the number of leaves. For a public $H\ge1$, put
$N=2H-1$ and $\mathcal T_H=\{t:\lambda(t)\le H\}$. The installed source is
the adapter's one private $2N$-bit block, with preorder tokens
`PAD=00`, `alpha=01`, `beta=10`, `PAIR=11`, padded after closure. Its
immutable preparation identity is $\xi$. Source identity, tree value, and
current generation are different objects. Addresses are finite words over
$\{L,R\}$, including the empty root. The literal response is
$\operatorname{tag}(p,t)\in\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.

Ordered pairing, root and child relations, substitution, tapes, finite
control, input ports, ownership, receipt construction and archive services
are explicit structures of the model. None is inferred merely from the
existence of two leaf labels.

**Convention 1.3 (supplier correspondence).** The following are mathematical
suppliers, with their original scopes. The paths name the sources themselves;
the new statements here do not enlarge those sources' certified conclusions.

| Supplier | Precisely reused fact and boundary |
| --- | --- |
| [Native Literal Journal Adapter](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LITERAL_JOURNAL_ADAPTER.md), Definitions 1.1–1.3, 2.1, 4.1–4.4; Theorems 3.3–3.4 and 4.5 | The same installed finite-capacity source, the added paid TagRead instrument, numerical ReadE as a different permission, guarded whole modifications, actual rejects, and raw source-busy states. The literal gate count is not total runtime. Noninterference fixes the submitted address; it does not equate costs of different addresses. |
| The same adapter, Definitions 5.1–5.2; Theorem 5.3; Proposition 5.4; Theorem 6.3 | Complete request fields, $E=A_P\mathbin{+\!+}P$, paid owned row access, and one actual joint history with its complete successor. An admitted uncommitted request belongs to busy work $B$, not to $P$. Joint closure is not an inverse or an individual exact-kernel theorem. |
| The same adapter, Theorem 7.2 and Corollary 7.3 | Capacity-safe Native realization and actual full-source acquisition: $2m-1$ TagReads and $2(m-1)$ branch-local markers for an $m$-leaf source. Every gate, tape, framing and delivery operation remains paid. |
| [Transport Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), §57, PR57.D1–D3, D5, D7, D9, L1, L2, L4 and T5 | Finite native control, IN/RD/WR/moves, constructed tapes and references, canonical private installation, one receipt/tick and two fee units per primitive, complete-prefix readout, seals, copies and progress. IN changes a latch and neither writes nor moves. The $8k+4$ channel expression counts the two payload bodies and their seal/handoff occurrences; explicit length-loop control must also be paid when that implementation is used. |
| [Native Clocked Recovery and Order](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md), Definitions 2.2, 5.2; Theorems 5.3, 6.3, 8.2–8.3 | Acquired-seed replay and separate exact task kernels on one fixed controller's hybrid history image, with atomic Native source calls; conditional enumerative coding of completed command order at sealed semantic cuts. Neither domain includes the independent unfinished input considered here. |
| [Atomic Boundary Trichotomy](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md), Theorem 12.1 and ABT.39 | The existing inverse from ordered unlabelled shape after two genuine rho updates, on its actual image. It is not reproved here and supplies no tree decoding of an invalid mid-write packet. |
| [NativeSerialMachine.lean](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean), `Op`, `Event`, `nativeStep`, `replay_deterministic`, `reached_prefix_replay`, `actual_register_execution`; [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs) | Source-blind Native control, unconditional Native substitution, full chronological locals/reads/updates and the exact hypotheses of reply-word replay. Stop is termination. An arbitrary supplied old trace in the last theorem is not an authenticated entrance. |
| [NativeFullSourceProducer.lean](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean), `sourceControl`, `productionTrace`, `native_source_producer`, including its private traversal invariant; [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) | The common traversal builds its output only from actual replies. Subtrees in the private proof invariant are proof parameters, not runtime advice. The no-update acquisition is reused directly. |
| [TypedFiniteViewKernel.lean](../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean), `response`, `behavior`, `typed_finite_view_kernel`; [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.scribe.cs) | Typed finite-path responses distinguish illegality and retain labels and terminal readout. Generic kernel reasoning does not supply the concrete separating experiment below. |
| [PredictiveMemoryMinimalQuotient.lean](../../../D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.lean), `predictive_memory_minimal_quotient`; [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.scribe.cs) | A minimal predictive quotient requires both readout and update factorization. Merely giving a recoverable tuple does not discharge the reverse task-kernel inclusion. |

The concrete additional relation is consumed external input, including a
phase-typed acquired-but-unwritten bit, together with its acquisition owner.
Generic deterministic replay, complements of projections, binary fiber
counting, actual seed acquisition, two-update shape recovery and completed
command ranking are credited tools rather than new general principles.

## 2. Actual entrance, input, operations and tasks

**Definition 2.1 (canonical paid entrance).** Fix public $H,\xi$, a finite
installed interpreter and dispatcher, its literal boot encoding, tape-port
assignments, descriptor conventions and native rule numbering. They are
source uniform. Install a valid source $u\in\mathcal T_H$ by PR57.D5's exact
canonical padded packet and fixed validation. There is no additional
source-dependent installer residue. Allocation uses the deterministic Base,
Allocate and descriptor routines; references name their actual creation
occurrences, with no arbitrary renaming.

Execute the supplied no-update producer on this source, materialize its
lossless seed code, and complete its paid delivery to the declared controller
owner. The traversal's return is a subroutine return: the surrounding
dispatcher continues after its output handoff. All return, output, seal and
token operations are included in this common installed preparation. A native
Stop internal to the producer is not interpreted as a globally stopped
dispatcher. Denote the resulting acquisition fence by $a(u)$. It need not
have a source-independent ordinal. The source at this fence is still $u$.

Let $\mathcal R_H$ consist of every subsequent primitive prefix of every
finite legal sequence of the source requests in Definition 2.4 under the
serial dispatcher below. It includes incomplete input, generation, private
gates and source writes, counter preparation, pending events, row prefixes,
both communication stages and acknowledgement. The absolute ordinal $n(h)$
counts all actual primitives from the original irreducible meter entrance,
including preparation and acquisition. No pre-acquisition inverse theorem is
claimed.

**Definition 2.2 (external actor and canonical request frames).** At a
prescribed public IN, an external actor in a common ready state has two
supply edges, 0 and 1, returning to that ready state. It has no private-source
argument or private read port. Its choices may be independent, or functions
of already acquired public data. Future choices are not part of the adapter
state and are not included in its reconstruction task.

A canonical source frame has a three-bit port tag, $U(d)=1^d0$, and a
$d$-bit payload. Fix the tags ReadE `000`, Rho `001`, TagRead `010`, Left
`011`, Right `100`. ReadE and Rho have empty payloads; a TagRead payload is
the submitted address, with 0 meaning L and 1 meaning R. A Left/Right
payload is the unique prefix code of its complete context tree: branch 0,
alpha 11, beta 10. These finite codes are supplied material; parsing and
converting them to the adapter's token format are paid public work. Context
names are generated canonically from their actual creation references. An
independently chosen name, program or schedule is additional input if an
interface admits it.

Only prefixes extendible to a canonical well-typed frame are needed in
$\mathcal R_H$. Every finite address and every finite context tree is
included, even when its whole source modification will reject. Canonical
framing removes encoding choices, not command choices. Repeated equal
commands remain different occurrences in their actual order.

**Definition 2.3 (serial paid dispatcher and retention).** At idle the
dispatcher reserves its ingress phase. It acquires the frame bit by bit,
parses it, and retains all its consumed material. A newly acquired bit stays
in a designated input latch until its corresponding WR; no other operation
overwrites that latch first. Its test latch is different. The complete frame
is sealed before dispatch to the adapter's legal source admission point.
No second source frame is acquired until the current request has committed,
its row has sealed, and mandatory delivery has been acknowledged.

The native control graph uses the finite expansion rules of PR57.D1.
Header recognition uses finitely many native states; lengths, trees,
addresses and dynamic programs are tape data. Parsing, public context
conversion, gate generation, source execution, row writing, allocation,
copying and acknowledgement use the cited terminating routines with their
actual primitive expansion. There is no independently chosen interrupt,
idle duration, allocator, local nondeterminism or scheduling decision.
For each legal finite frame the public dispatcher work terminates. In
particular no arbitrary potentially nonterminating selector is postulated.

Earlier frame blocks are retained immutably. Their physical representation
may consist of header, length and payload blocks with actual descriptors;
their chronological concatenation is determined by those created blocks and
the serial protocol. They are not a second log of private computation.
Lossless handoff to retained complete request material may replace this
retention, but only after that material has actually become available to the
same authorized owner. Optional diagnostic or archive-service choices, if
added to this runtime, must use their own canonical consumed frames and the
same retention rule. They are not inferred from the clock.

**Definition 2.4 (operation and failure menu).** The source ports are exactly
the adapter's TagRead($p$), ReadE, guarded Rho, Left($v$) and Right($v$).
TagRead and ReadE preserve the source. Rho accepts precisely when
$\lambda(\rho t)\le H$; Left and Right test their whole actual candidates
$\langle v,t\rangle$ and $\langle t,v\rangle$. An accepted modification
installs that candidate. A rejected modification retains the old tree and
still performs its prescribed work, response commitment and journal service.

The operative distinctions are as follows.

| Situation | Result and successor convention |
| --- | --- |
| Legal admitted source service, including rejection | `some(label, complete original successor)`; rejection changes work, receipts and records even when it preserves the tree |
| Literal descent beyond a leaf | An executed TagRead with response `absent` |
| Busy second semantic call, missing permission, or read of an unavailable destination | Illegal and unexecuted `none`; no new event or row |
| Paid row lookup at a sealed owned prefix, index outside that prefix | Executed typed `no-row`, with the actual scan/work/meter successor |
| Uninstalled or invalid preparation | No valid-source service permission; outside the valid-boot domain |
| Bounded evaluator misses in an optional effective interpreter | Local work, distinct from executed source reject |
| Completed dispatcher termination, if a terminal routine is installed | A typed terminal output; distinct from illegality |

The archive menu is the adapter's paid lookup of a complete row or complete
prefix using its existing descriptor, material references and ownership
token. A row's submitted address is its request field. It is not the index
or descriptor argument of Fetch. A receiver can read a destination only
after its final seal; a sealed immutable sender and, after its seal, a
mailbox can have their own continuing authorized reads.

**Definition 2.5 (full state and actual histories).** The endpoint $X(h)$
retains the source and scratch bits, every constructed cell including retired
versions, native and dynamic code, PC, marked heads, latches, request and
reply work, current and prepared counter versions, source token, pending
semantic event, partial producer rows, sender/mailbox/receiver contents,
origin and predecessor references, seals, permissions and actual meter.
The full prefix $h$ retains every actual primitive and its actual operands
and outcomes. The mathematical task's complete-successor coordinate is not
a new permission for the controller to inspect hidden coordinates.

During a modifying service the source block is unavailable and can be a
partial invalid packet. $X(h)$ then contains raw bits and phase, not a
fictional current decoded tree. The full-state carrier does not require a
tree at that cut.

**Definition 2.6 (continuation-and-audit task, before the views).** A primitive
experiment can Supply($b$) when the next instruction is IN, or Advance the
prescribed next non-IN primitive. A semantic experiment can run the finite
lawful protocols of Definition 2.4 at their admission points. It may finish
an already admitted request, wait by actual prescribed work for delivery,
and fetch a complete actual row. A finite adaptive experiment uses only
acquired public phase, availability and responses to choose its branches.
It has a finite decision tree, not a private-state test.

Responses retain legality, actual labels and released finite outputs, and
the complete original joint successor after every executed action. The
empty response retains running/terminal type and any terminal output.
All failure types in Definition 2.4 remain distinct. Write $h\sim_Q k$ if
every such finite experiment has equal responses at the two endpoints.
This task concerns actual continuation and authentic row audit, not a
request to output one of the views defined later. In particular, its public
row experiment below suffices for the lower bound even if the private
successor coordinates are omitted from the observable output.

## 3. A fully counted finite input reader

**Definition 3.1 (the payload graph).** A real unary length block $U(d)$
has its marked head at the first bit. A writable payload interval of $d$
zeroed cells and one following delimiter has been constructed, and its head
is at its first cell. The input and length-test latches are distinct. The
following five native rows are the entire loop:

| Native state | Primitive and successor |
| --- | --- |
| test | RD(length,test-latch); if 0 go to exit, otherwise go to input |
| input | IN(input-latch); go to write |
| write | WR(payload,input-latch); go to move-payload |
| move-payload | MR(payload); go to move-length |
| move-length | MR(length); go to test |

The zero/one successor test is part of the testing RD row permitted by
PR57.D1. The final MR's control successor is the test state. There is no
extra uncharged back-edge instruction and no bit-dependent payload branch.
The exit reached by the final RD(0) is a different phase, before any later
seal, descriptor construction or source work.

**Definition 3.2 (paid setup used for the equal-clock family).** Reserve
three ordinary public ports for tag, length and payload. Their empty
boundary pairs are constructed by paid boot and are untouched by the
preceding acquisition and warm-up. The common preamble has obtained their
Base references, the relevant token permissions, and any constant native
descriptors; their heads are at R. All preamble occurrences have their usual
receipts. Let $n_-$ be the actual ordinal at its end. Nothing depending on
the varying address bits has occurred.

The setup from that cut is this fixed finite graph.

1. Execute one reserve-phase CTL. For each of the three tag bits execute
   IN; EX(tag); WR(tag,input); MR(tag). Seal the tag by one CTL. Execute
   Home(tag); MR(tag), and three unrolled RD(tag); MR(tag) pairs to recognize
   the finite port code. For the family below this code is `010`.
2. Receive $U(d)$ on the initially empty length port. For each supplied bit
   execute IN; EX(length); WR(length,input); RD(length,test); MR(length).
   The RD branches to one of two identical MR opcodes: the 1 case returns
   to IN, the 0 case goes to a one-CTL seal. Thus the terminating bit and its
   exit control are paid. Run Home(length); MR(length).
3. Execute Allocate(payload,$d$) with that actual length tape, using its
   five-occurrence iteration and final RD(0). Append a delimiter by
   EX(payload); WR(payload,sep); MR(payload). Execute Home(length);
   MR(length), then Home(payload); MR(payload), and enter Definition 3.1.

No ordinal in this description is a primitive operand. Home finds the real
left boundary; Allocate consumes the real unary length. The acquired length
block is already its canonical wire representation. Complete payload
descriptors, parsing, payload seal and source dispatch follow the loop and
are charged there. Live work at a fixed port does not require an already
published complete-block descriptor. The prior Base references bind the
actual intervals before they are appended.

For subsequent frames in nonempty arenas use the same graphs with actual
Base/Seek positioning and complete descriptor work. Their cost is evaluated
by the occurrence rules in Definition 3.4, rather than reusing the
empty-port numerical formula.

**Theorem 3.3 (exact reader costs and cuts).** For every $d\ge0$ in Definition
3.2, the complete setup uses exactly $16d+56$ primitives. Put
$n_0=n_-+16d+56$, the ordinal just before the payload loop's first test.
After $r$ complete payload iterations, $0\le r\le d$, the ordinal is

$$
n_{\mathrm{body}}(d,r)=n_0+5r.
\tag{AIF.1}
$$

For $1\le r\le d$, the cut immediately after the $r$th payload IN, before
its WR, has ordinal

$$
n_{\mathrm{latch}}(d,r)=n_0+5(r-1)+2=n_0+5r-3.
\tag{AIF.2}
$$

The complete loop, including its final zero test, uses $5d+1$ primitives.
Hence setup plus loop costs $21d+57$ primitives, $21d+57$ ticks and
$42d+114$ fee units after $n_-$. Its later service costs are additional.
All these schedules are independent of the payload bit values.

Proof. The tag's input/append part costs 12; its seal costs 1. Its head is
then at position 4 relative to L, so Home costs 9 and MR costs 1. Three
RD/MR pairs cost 6. Thus tag supply, seal and recognition cost 29, and
reservation adds 1.

The length supply is $5(d+1)$, its seal is 1, and its head is at position
$d+2$ at R. Home/MR to its first bit costs $2d+6$. Allocate costs $5d+1$
and leaves the length head on its terminal zero at position $d+1$. The
payload delimiter costs 3 and leaves that head at R, position $d+2$.
The two final Home/MR operations cost $2d+4$ and $2d+6$. Their sum is

$$
1+29+5(d+1)+1+(2d+6)+(5d+1)+3+(2d+4)+(2d+6)
=16d+56.
$$

For $d=0$ the payload head is correctly at its delimiter and the first
length test exits; no data cell is accessed. In general one iteration is
exactly the five rows in Definition 3.1. Its second occurrence is IN.
Induction on $r$ gives AIF.1 and AIF.2, with a final single RD(0) giving
$5d+1$. A primitive has one receipt, one tick and two fee units. No control
edge, final test, header bit, length bit or initialization iteration has
been omitted. The varying data affect only the input latch and written
payload cells. ∎

**Definition 3.4 (whole-execution cost evaluation).** For every used native
graph, expand sequence by joining successor edges, public tests by actual
testing RD/CTL rows, and finite loops by their displayed rows. A native
row occurrence has cost 1; an edge which is only its successor field has
no separate cost. A separately executed CTL has cost 1. Parameter creation
uses the actual tape routines: Append costs 3; an actual Home at distance
$h$ costs $2h+1$; Seek costs $2h+3a+3$ plus positioning of its real address
string; Allocate's displayed length loop costs $5k+1$ plus its positioning
and descriptor work. Explicit loops around a body add their own testing
and counter movement occurrences unless already included in that body.

The cost of a sequence is the sum of its executed graph lengths, with each
operand head taken at its actual entry location. A public branch selects
its actually executed graph. A finite unary loop sums the graph at every
actual iteration and its terminating test. Dynamic gate execution uses
PR57.06 for every generated gate, plus its actual generator, positioning,
initialization and terminal-header work. Rows, frames, references and
numerals are constructed by these same graphs.

Consequently the exact ordinal of any cut is

$$
n(h)=C_{\mathrm{boot}}+C_{\mathrm{acquire}}
 +\sum_{\text{finished routines}}C_R
 +C_{\text{current routine prefix}}.
\tag{AIF.3}
$$

Each term is an actual finite graph evaluation with its actual inputs, not
an unspecified allowance. In particular $n_-$ includes canonical source
installation, fixed control encoding, paid seed acquisition, warm-up calls
when used, their rows and delivery, and the preamble's Base/token work.
It is common within a fiber, but is neither free nor asserted independent
of $d$ or of the acquired seed across different fibers. AIF.1–2 compare
full absolute clocks by adding that same actual paid prefix. No total
source-service cost is replaced by a count of input triples or Boolean gates.

## 4. Two residuals and a source-bound decoder

**Definition 4.1 (consumed input and its storage frontier).** For an actual
prefix $h$ after $a(u)$, let $I(h)$ be precisely the word of bits consumed
by public IN after that fence, in actual order. Fixed deterministic work
does not add to it. Let $L(h)$ be the chronological word of those bits whose
corresponding input WR has executed into retained frame material. Let
$Q(h)$ be the singleton current input bit exactly in the phase between its
IN and that WR, and empty otherwise. A stale value left physically in the
latch outside that phase is not a second pending bit.

Let $E(h)$, $A_P(h)$ and $P(h)$ have their original adapter meanings,
restricted to events after $a(u)$ when comparing input frames. Deterministic
local or return markers have no external source frame. Define $F(E)$ to
concatenate the canonical frames of externally requested source events in
$E$, in their actual order. Request references must be followed to their
actual retained complete material; a name alone is not a payload.

Let $D(h)$ be the consumed prefix of the one admitted input frame whose
source event has not committed. It can be empty, a proper prefix, or the
whole frame while source generation and execution are underway. After that
event commits, $D$ is empty until the next frame begins. This is a logical
partition of consumed input, not an atomic rewrite of all its physical cells.

**Theorem 4.2 (the two residual identities).** At every primitive cut in
$\mathcal R_H$,

$$
\begin{aligned}
I(h)&=L(h)\mathbin{+\!+}Q(h),& |Q(h)|&\le1,\\
I(h)&=F\bigl(A_P(h)\mathbin{+\!+}P(h)\bigr)
       \mathbin{+\!+}D(h),& |P(h)|&\le1.
\end{aligned}
\tag{AIF.4}
$$

The bound on $P$ imposes no bound on $|D|$.

Proof. At the acquisition fence all these relative input words are empty.
An IN appends one actual bit to $I$ and puts it in $Q$. No further IN is
enabled before its WR. Intermediate EX, tests or positioning preserve that
bit. Its input WR appends it to $L$ and makes $Q$ empty by phase. Moving
heads, parsing or executing the source does not acquire another external
bit. Retention preserves all earlier material. This proves the first
identity by induction, including the header's IN-to-EX-to-WR interval.

Before the current source event commits, exactly its consumed frame prefix
is appended to $D$ at each IN. Source work changes neither $I$ nor that
prefix. Commitment is enabled only after the full canonical frame has been
received and parsed. At commitment its entire frame passes from the logical
$D$ part to $F(E)$; thus their concatenation is unchanged. The committed
event enters $P$ with its actual request and result. Row-prefix writes
preserve the words. Its row seal moves that event from $P$ to $A_P$, as in
the supplied journal invariant, and again preserves the concatenation.
Copying and acknowledgement change physical state and receipts without
acquiring new input. Serial admission precludes two unfinished frames or
two committed unsealed events. Deterministic markers have empty $F$
contribution. This proves the second identity at every phase.

A single TagRead address may have arbitrarily many supplied bits before
any source event commits. The examples in Theorem 5.2 below make $|D|$
arbitrarily large with $P$ empty. ∎

**Convention 4.3 (the exact replay key).** Suppress the fixed public boot,
interpreter, descriptor convention and preparation binding in the notation,
and put

$$
K(h)=\bigl(\operatorname{code}(u),I(h),n(h)\bigr).
\tag{AIF.5}
$$

This is a mathematical code of actually acquired finite material and an
actual primitive position. It is not a promise that all fields are already
simultaneously readable by any chosen receiver. In the source-only serial
domain, AIF.4 gives the alternative sufficient code

$$
\bigl(\operatorname{code}(u),A_P(h),P(h),D(h),n(h)\bigr),
\tag{AIF.6}
$$

including the actual material backing request references. The code in
AIF.5 works as well for an explicitly extended dispatcher with additional
input frames. AIF.6 does not silently omit such choices: a Fetch frame,
for example, need not occur in the old source semantic word and must be
retained separately if that extended interface is used.

**Theorem 4.4 (actual all-microcut replay).** Under Definitions 2.1–2.5,
for every $H\ge1$, every actual installed $u\in\mathcal T_H$ and every
$h\in\mathcal R_H$, one effective finite decoder on the actual image of
AIF.5 returns the full original primitive prefix $h$ and its full joint
endpoint $X(h)$. This includes incomplete ingress, acquired-but-unwritten
latches, partial invalid source packets, accepted and rejected modifications,
pending events, incomplete rows and both copy stages. The decoder needs no
independently supplied source-response word or private workspace snapshot.

Proof. First decode the acquired prefix code into $u$. The canonical padded
packet, including every private installation bit and its order, is uniquely
determined by $u,H$. All other boot material is fixed public data. Reconstruct
the canonical installation locally, starting with the same fixed primitive
port and immutable preparation binding. This is computation on acquired
data; it is not a second installation or a new read port to the actual source.

Replay the exact paid boot and acquisition graphs until their declared
acquisition fence. The supplied producer terminates on this finite source;
the implemented traversal, output and handoff are deterministic. Hence their
entire prefix and absolute length $a(u)$ are computed. In particular the
decoder is not given a free physical snapshot of the acquisition endpoint.

Continue the literal transition interpreter until the total simulated
primitive count is $n(h)$. At an enabled public IN consume the next bit of
$I(h)$. At every other primitive execute the installed rule on the current
locally represented bits, marked cells, PC, latches and tokens. Never replace
an actual source fragment by one abstract source call. In particular Boolean
gates operate on their actual operand bits, and partial MUX/source writes
are ordinary bit rewrites even if the packet does not decode to a tree.

We prove equality with the original prefix by induction on this absolute
primitive count. The initial primitive-port states agree. Installation
inputs agree because their canonical source packet and fixed control bits
agree. Every acquired-input occurrence after the entrance consumes the same
next bit, including one not yet written at the target cut. At an ordinary
step the equal PC and public data select the same native row and operands.
Equal bits and latches give equal reads, Boolean results and writes; equal
marked heads and constructed bounds give equal movement and allocation.
The deterministic Base/descriptor routine constructs the same occurrence
references, rather than arbitrary isomorphic names. Receipt construction
and every actual fence are the same local side effects.

The same induction covers the complete source candidate, guard, private
scratch and successor writes. At release it obtains the actual read reply
or accept/reject, selects the same counter versions, and commits the same
semantic event. It then writes the same row prefix, seals it at the same
occurrence, and reproduces each mailbox/destination write, token transfer
and acknowledgement. Thus the joint state agrees simultaneously, including
permission and availability fields. There is no step choosing different
source and archive witnesses merely because their marginal values agree.

Because $h$ is actual, the supplied input word has exactly the bits consumed
before $n(h)$, and replay never asks for a future bit. Every individual
simulated primitive is a finite local transition on a finite representation.
Executing exactly this finite prefix therefore terminates. Its stored
simulation trace is the original full prefix, and the last represented
state is $X(h)$, proving the claim.

On an arbitrary proposed key, simulation may detect an invalid code,
prematurely exhausted input, surplus inconsistent input or termination
before the claimed position. No total authentic-history recognition is
inferred from success on the actual image; the theorem requires actual
entrance and acquisition provenance. ∎

**Corollary 4.5 (joint successor transport with input labels).** On the
actual key image, an enabled internal primitive transports
$K=(\operatorname{code}(u),I,n)$ to
$(\operatorname{code}(u),I,n+1)$. An enabled IN with actual chosen bit $b$
transports it to $(\operatorname{code}(u),Ib,n+1)$. Decoding the transported
key gives the complete original successor and an actual extended prefix
in the same joint image. An illegal action has no such extension.

Proof. Decode the actual state by Theorem 4.4. An internal row has a unique
next rewrite. At IN the actual interface has the two declared supply
edges, and transport carries the same $b$ on both sides. Append that very
primitive occurrence to the original prefix. It obeys the installed rule,
has the indicated acquired word and count, and is an actual member of the
same history image. The induction of Theorem 4.4 applied to the extension
gives its whole successor. No independently chosen next input is predicted
from $u$ or $n$. If the primitive is disabled there is no original admitted
occurrence to append. ∎

**Proposition 4.6 (semantic projection and its limits).** Projection of
actual completed source events retains their actual typed responses. On
capacity-safe TagRead/accepted-Rho runs it agrees with the adapter's supplied
Native macro correspondence. Internal source and record work stutters under
that projection but remains present in AIF.5 replay and in the actual clock.
Rejected Rho is not an unconditional Native update, and a graft does not
preserve a pure rho-orbit equation.

Proof. At each response commitment the adapter's conformance theorem gives
the original operation on that same installed source and its complete
response. The supplied Native realization applies exactly to its restricted
menu and capacity condition. Every other primitive adds no completed source
event, hence projects to stuttering in this particular semantic word. Its
receipt still increments $n$. Reject retains the tree while incrementing
the call/event counts; a genuine accepted graft changes the tree without
incrementing the accepted-Rho epoch. These cases prove both the positive
projection and its stated exclusions. ∎

Replay removes deterministic workspace from a sufficient *logical payload*.
It does not remove its original work or storage, reconstruct an authentic
row by minting a fresh origin, equate macro and micro clocks, or identify the
key's global minimum task quotient. Theorem 4.4 is one sufficient memory
decoder, not four natural view constructions.

## 5. A sharp actual unfinished-address fiber

**Definition 5.1 (one source, one common scaffold).** Set $H=2$ and install
the actual seed $u=\alpha$. Acquire it by Definition 2.1. Perform two real
guarded Rho calls, completing the ordinary journal/delivery service each
time. Their actual sources are

$$
\alpha\longrightarrow\beta\longrightarrow
t_*=\langle\beta,\alpha\rangle.
\tag{AIF.7}
$$

Both candidates fit capacity 2, so the actual accepted-Rho epoch is 2.
Fix any public $d\ge2$, supplied in the common unary header of Definition
3.2. Use its TagRead tag and its full paid setup. The accessible input actor
chooses the $d$ address bits independently. Before any source commitment,
write $h^{\mathrm b}_{d,r,x}$ for the cut after $r$ complete payload
iterations, with $x\in\{L,R\}^r$, $0\le r\le d$. Write
$h^{\mathrm l}_{d,r,x}$ for the cut immediately after the $r$th IN, before
its WR, $1\le r\le d$. In the latter the first $r-1$ letters are stored
and the last occupies the actual input latch. All these histories share
the same actual preparation, acquired seed and paid preamble, not merely
equal numerical source labels.

**Theorem 5.2 (equal-clock $2^r$ fiber and attained complement).** For each
fixed $d,r$ and either cut family in Definition 5.1, there are exactly
$2^r$ actual histories, one for each $x\in\{L,R\}^r$. They have the same
current labelled source, ordered support, leaf frontier, actual epoch,
absolute primitive ordinal, completed semantic word, sealed producer and
receiver prefixes, pending event $P=\varepsilon$, prior completed-command
histogram/rank, phase, marked-head locations, references and token layout.
Their task relation is exactly

$$
h_{d,r,x}\sim_Q h_{d,r,y}\quad\Longleftrightarrow\quad x=y.
\tag{AIF.8}
$$

Thus, conditional on these common coordinates, any sufficient supplement
must have at least $2^r$ values and needs at least $r$ fixed-width bits.
The acquired prefix $x$ attains that width. At a latch cut, its attaining
representation is the $r-1$ written letters and the occupied input bit.

Proof. The two warm-ups in AIF.7 are actual accepted modifications, and the
producer acquisition leaves the source unchanged. Setup depends on the
common tag and $d$ only. Definition 3.1 has a bit-independent five-row
control graph. By induction, every choice word $x$ is supplied by the
same accessible actor at those actual IN ports. Equal $d,r$ give the same
native states, head locations, allocated intervals, test values and receipt
pattern. Only the consumed payload values differ. Theorem 3.3 gives the
same full ordinal $n_0+5r$ or $n_0+5r-3$, respectively.

No TagRead response has committed at either cut, including the body cut
with $r=d$: its final length test and service are still ahead. Ingress has
not modified the source. Consequently its new request has added nothing
to $E$, $A_P$ or $P$; old complete-order data and all prior copied rows
remain common. The busy request belongs to $B$. Prior source-call,
modification and semantic-event counts are also common. This proves the
fiber and all the claimed equalities.

For separation, use one common continuation: supply L at every remaining
address position, finish the prescribed routine through its actual row
seal and delivery acknowledgement, and fetch the row of this request
from its authentic complete prefix. At a latch cut this first executes
the prescribed WR; it does not resupply the bit already acquired. The
submitted address is

$$
p_x=xL^{d-r}.
\tag{AIF.9}
$$

All such words have length $d\ge2$. The root of $t_*$ has two leaf
children, so every one returns the same literal response `absent`. The
source remains $t_*$ throughout. Nevertheless the returned row's complete
request field is exactly $p_x$. For $x\ne y$ these fields differ. There is
no hypothetical public read of a private latch or request buffer.

The lookup uses the delivered row's actual reference, or its index obtained
from the common preceding row ordinal by the paid counter routine. Its
complete-prefix descriptor and ownership token are those produced by the
completed delivery. Constructing and supplying these lookup arguments is
part of the experiment's paid work. The varying $p_x$ is a returned request
field, not a source-dependent choice of Fetch argument.

Each continuation terminates by the supplied finite service and row-access
theorems. A finite adaptive experiment can Advance while the publicly
indicated service is unfinished and then Fetch when its token is available.
For fixed $d,r$ there are finitely many $x$, so the maximum of these finite
run lengths and Fetch lengths gives a finite decision-tree bound common
to the family. Different intermediate labels, times or running/terminal
types would already separate the task; equality of later service clocks
is not needed. The eventual request field gives separation even when all
those earlier differences are suppressed.

Conversely, if $x=y$, the scaffold and every consumed input bit agree.
Induction through the explicit setup and loop gives the same full actual
prefix and endpoint, including old cells, latches and receipts. Every
common future experiment then has the same legality, labels, outputs and
whole successors by deterministic evaluation with its same future supplied
bits. This proves the other direction of AIF.8.

If a sufficient supplement merged two different prefixes, the equal common
side data and that supplement would have to determine the same response
to their separating experiment, a contradiction. Hence it has at least
$2^r$ values. A width-$b$ binary alphabet has at most $2^b$ values, so
$b\ge r$. Keeping $x$ supplies exactly $2^r$ values and, by the preceding
equal-prefix reconstruction, all task responses. It therefore attains the
conditional bound. ∎

**Corollary 5.3 (the missing one bit before WR).** At a fixed latch fiber
with $r\ge1$, the written address prefix alone has $2^{r-1}$ values while
the task has $2^r$ classes. Each written prefix has exactly two classes,
distinguished by the actual pending input bit. Written-address data plus
that bit has exactly the task kernel.

Proof. Fix the first $r-1$ choices and vary just the last IN. The two
histories have identical written request cells, source and common side
data. The common next WR writes different public request bits, and the
row experiment in Theorem 5.2 separates them without direct buffer access.
The reverse inclusion follows from the identical-prefix argument there.
There are $2^{r-1}$ choices of the fixed prefix and two choices of the
pending bit for each. ∎

**Corollary 5.4 (no capacity-only or completed-order repair).** For the
task of Definition 2.6 there is no sufficient supplement with an alphabet
bounded only by $H$, even when the entire current labelled source, acquired
seed, actual clock, completed command word and its rank, and $P$ are given
as side data.

Proof. Keep $H=2$ and AIF.7 fixed. Choose any $r$ and $d\ge\max(2,r)$.
Those side data are constant on its $2^r$ fiber, while Theorem 5.2 requires
$2^r$ supplement values. Letting $r$ grow contradicts every fixed bound.
In this witness there is one unfinished command and zero newly completed
source events. Its ambiguity is input *value* information before
commitment, not a permutation of a completed multiset. ∎

**Proposition 5.5 (four separate conditional kernel statements).** On each
fixed family of Definition 5.1, define the old bases

$$
\begin{aligned}
S_0(h)&=(\operatorname{Pos}(t_*),2,n(h)),\\
B_0(h)&=(\operatorname{LeafPos}(t_*),2,n(h)),\\
M_0(h)&=(\operatorname{code}(\alpha),n(h);\text{fixed interpreter}),
\end{aligned}
\tag{AIF.10}
$$

and let $T_{\mathrm{full}}(h)$ be the full actual ordered primitive word,
retaining acquired input values. For $r>0$, each of $S_0,B_0,M_0$ separately
fails task sufficiency. Each of $(S_0,x)$, $(B_0,x)$, $(M_0,x)$, and
$T_{\mathrm{full}}$ separately has exactly the restricted task kernel.
The opcode-only word and the ordinary receipt word fail sufficiency there.

Proof. The source support is $\{\varepsilon,L,R\}$ and its leaf frontier
is $\{L,R\}$. AIF.1–2 fix $n$, so each base in AIF.10 is constant. The
separating experiment in Theorem 5.2 proves that its kernel strictly
contains the task kernel when $r>0$.

For $(S_0,x)$, equal values force equal $x$, whence identical actual cuts
and all task responses. Task equivalence forces equal $x$ by the fetched
request fields, and its common $S_0$ is already equal. These are both
kernel inclusions for this view. The same two arguments apply independently
to $(B_0,x)$ with its common frontier and to $(M_0,x)$ with its common seed
and position. None uses an intersection of the views' kernels.

An equal full primitive word gives equal actual input values and therefore
equal $x$; equal $x$ gives that same full word by the deterministic prefix
argument. AIF.8 supplies the two kernel inclusions for $T_{\mathrm{full}}$.
Deleting input values leaves a common opcode word, and these ingress
receipts have the same ordinary/fence pattern. Their common words merge
task-distinct $x$. ∎

The supplemented expressions in Proposition 5.5 are conditional fiber
repairs. They are not proposed as a global spatial or boundary atlas, nor
as four copies of AIF.5. The all-cut sufficiency of AIF.5 does not add the
missing full-domain reverse inclusions to any natural view.

## 6. Publication, copy acquisition and callable backing

**Definition 6.1 (owner-relative acquired material).** An owner's materialized
record consists of the data actually acquired at its permitted reads or IN
occurrences, retained finite latches and cells, and its acquired metadata.
An inaccessible producer bit is not in a receiver's materialized record.
A callable-memory object can additionally contain a genuinely bound handle
with authorized backing material and future paid operations. Its mathematical
value includes that backing relation and permissions; it is not just the
pointer's wire string.

**Theorem 6.2 (publication lower bound on the actual source family).** At
the cuts in Theorem 5.2, suppose a receiver has acquired only the common
already sealed copied journal prefix, common code/metadata and common
clocks, and has no input-observation channel or authorized backing object
containing the new request. Its materialized record is identical for all
$2^r$ choices. It cannot determine the producer's continuation-and-audit
task at that cut. A repair reaching this receiver must give it at least
$2^r$ distinguishable acquired records. Under a fixed binary payload
channel with common metadata and schedule this requires at least $r$
payload bits.

Proof. The differing bits have occurred only at the ingress owner's IN
and request work. By hypothesis no varying information has reached the
receiver. The readable old copied prefix, every legal old-prefix access,
and its metadata and clocks agree. An unsealed destination has no legal
read. A function of that common acquired record is constant, whereas the
common completion/row experiment distinguishes all $x$ by Theorem 5.2.
Any sufficient received record must therefore distinguish every pair.
The binary payload count follows from $2^b\ge2^r$.

If timing, names, token choices or some other signal are allowed to vary
with $x$ at the receiver, they are additional acquired channels and must
be included in the distinguishable-record count. They cannot invalidate
that count by being omitted from its premise. ∎

**Definition 6.3 (a paid fixed-copy variant).** Add a prescribed ingress
operation after a complete $\ell$-bit payload is sealed and before its
source dispatch: copy that owned payload to a mailbox and then to a
receiver destination. This is an explicit ingress-record publication,
not a claim that the adapter's semantic journal already contains partial
requests. The same source and its prior journals are retained.

The sender is immutable and readable by its authorized owner. Allocate
and initialize the full mailbox and destination and construct their
descriptors. Supply a real $U(\ell)$ counter and actual positioning.
For each stage use this finite six-row loop:

| State | Primitive and successor |
| --- | --- |
| copy-test | RD(counter,test); if 0 go to copy-seal, else copy-read |
| copy-read | RD(source,data); go to copy-write |
| copy-write | WR(destination,data); go to copy-move-source |
| copy-move-source | MR(source); go to copy-move-destination |
| copy-move-destination | MR(destination); go to copy-move-counter |
| copy-move-counter | MR(counter); go to copy-test |
| copy-seal | CTL seal; go to handoff |
| handoff | TOK handoff/acknowledgement; return |

The first stage's source/destination are sender/mailbox; the second's are
mailbox/receiver. Its data and counter-test latches are distinct. Reposition
the same actual counter, and both relevant data heads, between stages by
paid Home/Seek. Payload intervals have a following constructed cell for
their last MR. The mailbox becomes readable at its seal and handoff; the
client destination remains unavailable until its own final seal. No rule
makes all sender, mailbox and destination simultaneously unavailable.

**Theorem 6.4 (full copy loop count and conditional remaining suffix).** For
each $\ell\ge1$ the two loop executions in Definition 6.3, including their
terminating tests, seals and token occurrences, use exactly $12\ell+6$
primitives. Their complete cost is

$$
C_{\mathrm{copy}}=
C_{\mathrm{alloc/init/descriptor}}
+C_{\mathrm{first\ position}}+(6\ell+3)
+C_{\mathrm{reposition}}+(6\ell+3).
\tag{AIF.11}
$$

The positioning and construction terms are the exact graph evaluations of
Definition 3.4. They do not include the two loop terms again. Relative to
the supplied $8\ell+4$ payload/seal/handoff bodies, this implementation adds
exactly $4\ell+2$ length-test and length-head movement occurrences.

Across all $2^\ell$ sender payloads with common length, layout and origin
metadata, the schedule is value independent. At a fixed receiver-copy phase
just after its $c$th payload RD, $1\le c\le\ell$, its acquired payload is
the prefix $z\in\{0,1\}^c$, including the current read latch. At the
corresponding pre-payload-read phase take $c=0$. Conditional on this prefix
and the common schedule, exactly $2^{\ell-c}$ sender payloads remain.
A supplement enabling reconstruction of the original payload, or of its
later complete request-audit behavior, needs $\ell-c$ fixed-width bits;
the remaining suffix attains the bound. This necessity is for decoding
from already materialized receiver data without further payload reads.

Proof. Each copied bit executes exactly the six loop rows, followed by one
terminal RD(0), one CTL seal and one TOK at stage end. Thus each stage is
$6\ell+3$. Subtracting the four data occurrences per bit and the seal/TOK
pair per stage leaves $2\ell+1$ counter occurrences per stage. Setup and
repositioning do not depend on payload values, and their actual lengths
are separately added as in AIF.11. Each stage has a complete finite bound,
so the supplied tape progress argument applies.

Induction through the first stage shows that the sealed mailbox is exactly
the original sender payload with its preserved binding. Induction through
the receiver stage shows that before its next payload RD no not-yet-read
payload bit has affected its local materialized record. Its control, heads,
test latch, receipt count and tokens follow the common schedule. After
the $c$th RD, the previous $c-1$ payload bits are written in its destination
and the current bit is in the data latch; hence its acquired prefix is
exactly $z$. At later phases before the next RD the same prefix is merely
materialized by WR. A stale latch is not counted as a new acquisition.

For any fixed $z$, each of the $2^{\ell-c}$ suffixes is realized by the
same lawful input actor, with the same source. Taking $\ell\ge2$ and the
TagRead use of the payload in Theorem 5.2, these distinct completed
requests have different authentic request fields, even though their
literal source replies are all absent. For $\ell=1$, the two possible
addresses still give distinct request fields, whether or not their source
replies differ. Thus that audit task also requires all the suffix
distinctions. A sufficient binary supplement must have at least that many
values. Keeping the suffix reconstructs the full sender payload, all
previous copy operands, and the deterministic copy remainder, and attains
the stated conditional width. ∎

**Proposition 6.5 (materialization and callable access are different).** The
suffix bound of Theorem 6.4 does not forbid deferred paid recovery through
an authorized handle to the sealed sender or mailbox. A handle with that
backing can supply the remaining suffix by later reads. A common pointer
string without its bound backing is not a sufficient substitute.

Proof. After the mailbox seal its token permits the receiver's prescribed
reads, each acquiring one actual mailbox bit. Completing those operations
and the destination seal gives all $\ell$ bits by the copy induction.
These are new paid acquisitions after the cut, not a decoder of the
earlier materialized prefix. If the entire callable object includes the
bound mailbox, different suffixes give different callable objects even
when their descriptors have the same wire representation. If only that
common string is given and no backing access is allowed, the two suffix
histories in Theorem 6.4 again have equal supplied data and different
required payloads. Hence the string alone cannot perform the recovery. ∎

The final destination may contain every payload bit before its seal while
still having no legal client read. Internal acquisition, complete writing,
publication and authorized client access are separate relations. Theorems
6.2–6.5 do not grant an arbitrary receiver the ingress owner's latch or a
free freeze of a busy cut.

## 7. Concrete finite instances and one-execution resource maps

**Proposition 7.1 (four prefixes with the same source and clock).** In
Definition 5.1 take $d=3$, $r=2$ and the latch cut. The four actual prefixes
are LL, LR, RL, RR. Their common payload-loop ordinal is $n_0+7$, and the
complete explicit setup gives $n_0=n_-+104$. Their written/latch data and
eventual request fields under the common L continuation are:

| Acquired prefix | Written payload prefix | Occupied input latch | Actual later submitted address | Literal reply on $t_*$ |
| --- | --- | --- | --- | --- |
| LL | L | L | LLL | absent |
| LR | L | R | LRL | absent |
| RL | R | L | RLL | absent |
| RR | R | R | RRL | absent |

All have source support $\{\varepsilon,L,R\}$, frontier $\{L,R\}$, epoch
2, no new committed source event, and $P=\varepsilon$. The conditional
supplement width is exactly 2 bits.

Proof. Substitute $d=3,r=2$ into AIF.1–2 and Theorem 3.3. The first input
letter has been written and the second is pending. AIF.9 gives the four
distinct length-three addresses. Each descends past a leaf. The request
rows and both task-kernel directions are those of Theorem 5.2. ∎

**Proposition 7.2 (a partial copy instance).** For $\ell=3$, a receiver that
has acquired the first bit L of the sealed payload has four compatible
payloads LLL, LLR, LRL and LRR. Their materialized-prefix residual needs
exactly 2 bits. The two complete copy loops cost 42 primitives before
adding their allocation, descriptors and positioning.

Proof. There are four length-two suffixes. Theorem 6.4 gives $\ell-c=2$
and $12\ell+6=42$. Their request fields are distinct and their source
responses on $t_*$ are all absent. ∎

**Definition 7.3 (resource coordinates).** Keep the following coordinates
separate on the same execution. The cost evaluation of Definition 3.4 and
the original purpose/opcode partition assign each executed occurrence
exactly once. Recording its constructed cell in storage is not a second
time charge.

| Relation or object | Actual owner, operation and resource boundary |
| --- | --- |
| Source capacity and installation | The producer owns the original private $2N$ bits. Canonical source ingress, validation and all surrounding descriptors are paid. There is no second physical source used by replay. |
| Literal instrument | TagRead uses the added same-source permission. $G(H)=(2N+3)4^N+3$ counts gate records only. At $H=2$, $N=3$ and $G(2)=579$, independent of unbounded submitted address length. Generator work, address scans, gate execution, framing and communication are separate. |
| Acquired seed | For an $m$-leaf seed the supplied traversal makes $2m-1$ TagReads and $2(m-1)$ local markers. Its parser code has $3m-1$ payload bits. Source acquisition, serialization, ownership transfer and retained traversal work are paid separately from installation. |
| Independent input | At the latch fiber, $r$ actual payload INs, $r-1$ WRs, $r-1$ payload moves, $r$ tests and $r-1$ length moves have executed: $5r-3$ primitives after $n_0$. The completed loop is $5d+1$; the chosen empty-port setup is $16d+56$. |
| Frame retention | The attaining logical prefix can already reside in existing request cells plus one occupied latch. It does not inherently require a duplicate $r$-bit log. Headers, length cells, descriptors, previous frames and all unused allocated payload capacity remain physical storage. |
| Semantic pending event | At response commitment the complete actual request and response enter $P$; row seal transfers its logical event into $A_P$. This is not a physical bulk copy. No uncommitted address prefix is made into a semantic event. |
| Archive and publication | Actual producer rows, immutable senders, sealed mailboxes and receivers have separate tokens and origins. AIF.11 prices the chosen full copy loops; allocation, unary identities, positioning, row access and printing are additional actual graphs. |
| Actual time | The meter has $n$ real receipts, $n$ ticks and fee $2n$. A stored $U(n)$ is obtained by a paid scan of an already closed fence; its readout adds later receipts. No primitive receives the mathematical meter count as an input numeral. |
| Replay | AIF.5 permits $n$ literal abstract-state simulations after reconstructing the fixed entrance. Parsing, finite-state representation, scans, code, arithmetic, workspace, key access and endpoint serialization all have their own implementation costs. This is not an $n$-primitive hardware runtime bound. |
| Macro correspondence | Complete source calls project to their actual typed semantic events; noncommitting work stutters only under that declared projection. No equality of macro and micro ordinals, costs or inaccessible views is inferred. |
| Callable memory | A usable handle consists of the real bound prefix/material, permissions and paid access operations. Its pointer width is not the payload capacity of its backing object. |

**Proposition 7.4 (storage versus conditional information).** In the
underlying retained-cell machine the simultaneous storage is

$$
S(h)=S_0+b_{\mathrm{ctl}}(h)+8A(h)+8n(h),
\tag{AIF.12}
$$

where $A(h)$ counts all constructed ordinary cells, including old versions,
and $b_{\mathrm{ctl}}$ counts installed control/token/latch bits. On the
address fiber, the already allocated $d$ payload cells alone contribute
$8d$ model bits, even when only $r<d$ bits have arrived. The sharp $r$-bit
bound is a conditional task-information bound, not a total storage optimum.

Proof. PR57.D1 constructs an eight-model-bit ordinary cell and one
eight-model-bit receipt cell for every executed primitive; PR57.D9 retains
all constructed cells and separately counts finite control/token/latch
storage. The new frame and copy operations use precisely those cell and
receipt constructors. Partitioning by actual construction therefore gives
AIF.12 without substituting separate maxima for coexisting objects. The
payload Allocate has constructed all $d$ cells before the varying ingress,
and Theorem 5.2 counts distinguishable values conditional on that common
layout. These are different quantities. ∎

## 8. Primary literature and exact applicability

**Convention 8.1 (literature status).** The specific source-bound residual
identities, paid ingress fibers, conditional local kernels, replay
application and owner/copy statements above are `repo-derived`: their
proofs use the explicit adapter and declared input runtime. The following
primary works are `literature-attested` suppliers of the indicated general
methods. No worldwide originality claim is attached to their concrete
application here. In particular an abstract complement or auxiliary
variable is not cited as a physical acquisition mechanism.

| Primary source | Exact correspondence and excluded inference |
| --- | --- |
| N. Lynch and F. Vaandrager, *Forward and Backward Simulations, Part I: Untimed Systems*, Information and Computation 121(2), 1995; [author manuscript](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf), §3.2, Lemma 3.8 and Theorem 3.10, PDF pp. 11–12 | A forward simulation matches from every related state by finite fragments with the required trace; its soundness is trace inclusion. This does not imply an inverse state decoder, exact task kernels, acquired input, identical clocks or equal costs. The primitive equality induction in Theorem 4.4 supplies the stronger concrete conclusion under its explicit hypotheses. |
| L. Lamport and S. Merz, *Auxiliary Variables in TLA+*, [arXiv:1703.05121](https://arxiv.org/abs/1703.05121), §§3.1–3.2 and 4.1, PDF pp. 15–17 and 22–23 | History variables remember the past; prophecy variables predict future transitions; stuttering variables add steps without the old state change. Hiding an auxiliary variable is a semantic device, not acquisition, retention or a paid memory service. $I$ changes only at actual consumed INs and contains no future input suffix. |
| M. Hofmann, B. Pierce and D. Wagner, *Symmetric Lenses*, POPL 2011; [author manuscript](https://www.cis.upenn.edu/~bcpierce/papers/symmetric.pdf), §2, PDF p. 2, discussion “Complements” | A complement retains information discarded by a projection so the two results can reconstitute the concrete value. The concrete $2^r$ and suffix fibers here are proved using actual request tasks. The lens complement supplies no owner, input port, publication fence or access price. |
| C. H. Bennett, *Logical Reversibility of Computation*, IBM Journal of Research and Development 17, 1973, pp. 525–532; [full text](https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html), introduction and reversible history/output construction | Reversible simulation saves intermediate results and output before reversing work. Theorem 4.4 instead performs ordinary forward local replay with actual external inputs fixed. It claims no physical uncomputation, archive erasure, reversible implementation or thermodynamic bound. |
| G. Winskel, *Event Structures*, Advances in Petri Nets 1986, LNCS 255, 1987; [author-hosted chapter](https://www.cl.cam.ac.uk/~gw104/Winskel1987_Chapter_EventStructures.pdf), Definitions 1.1.1–1.1.2, PDF pp. 2–3 | Consistency and enabling distinguish possible event configurations and prior causes. Here IN, WR, commitment, row seal and receiver seal are distinct actual occurrences in a specified serial history. General enabling relations alone do not supply their tokens, chronological bytes or paid communication. No concurrency composition theorem is substituted for this runtime's actual ownership proof. |
| N. Barnett and J. P. Crutchfield, *Computational Mechanics of Input-Output Processes: Structured Transformations and the epsilon-Transducer*, Journal of Statistical Physics 161, 2015; DOI [10.1007/s10955-015-1327-5](https://doi.org/10.1007/s10955-015-1327-5), [arXiv:1412.2690](https://arxiv.org/abs/1412.2690), §VI, equation (9), PDF pp. 12–13, and Proposition 5, p. 15 | Channel causal equivalence conditions future output on future input and the joint past, and joint unifilarity describes symbol-driven updates. The paper distinguishes the channel from a particular input process. Statistical predictive sufficiency and minimality do not give pointwise full-successor audit equivalence, actual retention, or minimum physical storage for this machine. |
| R. Beutner and B. Finkbeiner, *Prophecy Variables for Hyperproperty Verification*, CSF 2022; [arXiv:2206.01797v1](https://arxiv.org/abs/2206.01797v1), Definition 3 and Theorem 4, PDF pp. 7–8 | For a finite-state transition system satisfying a universal-then-existential HyperLTL property, finitely many QPTL prophecies suffice for its verification game. Those future-dependent predicates are not a causal input-acquisition algorithm. Finite source capacity does not make the present unbounded constructed-tape runtime finite-state, and no prophecy is used in AIF.5. |

The relevant primary passages support the distinctions just stated. No
general completeness theorem for refinement or prophecy is used to assert
that a missing input has already been acquired. No probabilistic assumption
is needed for the counting bounds: the full finite fibers are realized by
the two accessible supply edges. Search scope and these citations do not
establish absence of stronger results elsewhere.

## 9. Unresolved mathematical and operational boundaries

**Definition 9.1 (the remaining full-domain problem).** On the full adapter
history image, seek concrete spatial-support and continuation-boundary
relations for each actual cut, including invalid source-write packets,
accepted graft histories, pending row construction and incomplete copies.
Their allowed operations and outputs must be specified independently of
the proposed views. Each view must have both task-kernel inclusions
separately, and its memory interpretation must name actual ownership and
paid access at a named cut.

Theorems 4.4–4.5 give a joint reconstruction and successor witness from
acquired input under canonical deterministic dispatch. They do not define
the missing natural support/frontier relations. The last committed tree
replayed from $E$ is an abstract semantic state during a source overwrite;
calling it the current physical tree does not solve Definition 9.1.
Proposition 5.5 proves exact kernels only on its explicitly fixed input
fibers. No global minimum complement or four global exact kernels follows.

**Definition 9.2 (named-cut access problem).** At an arbitrary busy cut, a
callable reconstruction package requires an authorized way to retain its
live input latch, freeze an appropriate acquired prefix, bind its actual
seed and receipt position, and perform paid scans, seals and copies to the
intended owner. A set-theoretic tuple of those coordinates does not itself
provide such a protocol. The present retention rule preserves the inputs;
Theorems 6.2–6.5 delimit their publication and deferred access. A universal
paid arbitrary-busy-cut materialization service is not established here.

**Definition 9.3 (extensions requiring further acquired data).** Extra
installer residue, externally chosen allocator names, random bits,
asynchronous interrupts, waits, diagnostic requests and scheduling choices
must be fixed public data or retained as their actual acquired input if
the replay theorem is extended to them. An unrecorded such choice breaks
its determinism premise. Future values of the external actor are never
replay inputs. Arbitrary-entry authentication, fabricated transcript
recognition, crash recovery, hostile writers and physical noise remain
outside this ideal exclusive-owner domain.

**Definition 9.4 (unchanged wider objectives).** Finite $H$ is an explicit
capacity parameter, not one coherent infinite physical source. Pointwise
finite replay and source acquisition do not provide a uniform all-size
physical service. The stationary original-root problem
$F_D=\langle\alpha,v\rangle$, its late-target contract, $M_1(D)$, sharp
$\lambda$, and the original effective acquisition/certification objectives
remain separate unresolved tasks. An authentic integer $k$ is not a
genuinely executed rho event. The input repair changes the missing causal
relation in the composition problem without changing any of these goals.

## 追加锚（本行以下为增补区）
