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
They give a sufficient reconstruction code through every primitive cut of the
lawful canonical-frame histories of a specified serial runtime, and a sharp
conditional information requirement on actual equal-clock unfinished-request
families. They do not give four global
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
Allocate and descriptor routines, or the explicit port-local construction
of Definition 3.2; references name their actual creation occurrences, with
no arbitrary renaming.

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
serial dispatcher below, with their canonical frames from Definition 2.2.
This is the full lawful canonical-frame domain, not the set of all raw-input
runs. It includes incomplete input, generation, private gates and source
writes, counter preparation, pending events, row prefixes,
both communication stages and acknowledgement. The absolute ordinal $n(h)$
counts all actual primitives from the original irreducible meter entrance,
including preparation and acquisition. No pre-acquisition inverse theorem is
claimed.

**Definition 2.2 (external actor and canonical request frames).** At a
physically enabled prescribed public IN, an external actor in a common ready
state has two raw supply edges, 0 and 1, returning to that ready state.
Either bit is consumed into the input latch, takes the installed control
successor and appends its receipt, even if the consumed word is no longer
extendible to a canonical frame. IN does not validate that word, write a
tape or move a head. Such an occurrence is executed; it is not `none`.
The actor has no private-source argument or private read port. Its choices
may be independent, or functions
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

Let $\mathsf C$ be exactly this set of complete well-typed source frames,
and let $\mathsf P=\{p:\exists w\in\mathsf C,\ p\preceq w\}$, where
$\preceq$ is the word-prefix relation, including equality. At a prescribed
source-frame IN, let $p(h)$ be the already consumed prefix of
the current ingress frame, empty at its first IN. The admissible task-input
bits are exactly

$$
\operatorname{Adm}(h)=\{b\in\{0,1\}:p(h)b\in\mathsf P\}.
$$

This restricts the continuation task, not the physical raw supply edges.
It depends on the declared frame syntax and already acquired input, not
on the private source, its future reply or future input. No input filter or
new checking primitive is installed. Any implemented syntax check uses
and pays for public parsing work. Behavior after a consumed noncanonical
prefix is not specified here beyond the actual IN successor just described.

All actual ingress prefixes extendible to canonical well-typed frames are
retained in $\mathcal R_H$. Every finite address and every finite context
tree is included, even when its whole source modification will reject. Canonical
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
| Physically enabled raw IN whose bit leaves $\mathsf P$ | Executed latch/control/receipt successor; outside $\mathcal R_H$ and the task-input domain, not `none`; later malformed-frame behavior is unspecified |
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
task experiment can Supply($b$) at the next prescribed IN exactly when
$b\in\operatorname{Adm}(h)$, or Advance the prescribed next enabled non-IN
primitive. A physically enabled Supply outside this set is outside the
task-transport domain; the task does not invoke it or assign it an
illegal-unexecuted response. The physical actor can still execute it as
in Definition 2.2. A semantic experiment can run the finite
lawful protocols of Definition 2.4 at their admission points. It may finish
an already admitted request, wait by actual prescribed work for delivery,
and fetch a complete actual row. Source-frame inputs in these protocols
obey the same admissibility rule. A finite adaptive experiment uses only
acquired public phase, availability and responses to choose its branches.
It has a finite decision tree, not a private-state test.

Responses retain legality, actual labels and released finite outputs, and
the complete original joint successor after every executed action. The
empty response retains running/terminal type and any terminal output.
All specified failure types in Definition 2.4 remain distinct. Trials of
physically disabled or unauthorized operations retain their `none` response;
they do not execute a primitive. A physically enabled noncanonical Supply
instead leaves the experiment undefined on this lawful task domain. More
precisely, each endpoint gives a partial response map on finite experiment
trees, defined exactly when no executed branch attempts such a Supply.
Write $h\sim_Q k$ if these maps have the same domain and equal responses
there. Undefinedness is a mathematical domain distinction, not an output,
receipt, rejection or physical prevention of raw IN.
This task concerns actual continuation and authentic row audit, not a
request to output one of the views defined later. In particular, its public
row experiment below suffices for the lower bound even if the private
successor coordinates are omitted from the observable output.

**Lemma 2.7 (closure on the full lawful prefix class).** For every
$H\ge1$, every valid installed source and every $h\in\mathcal R_H$, each
physically enabled prescribed non-IN successor is in $\mathcal R_H$.
At a prescribed IN, the physical successor $h\cdot\mathrm{IN}(b)$ is in
$\mathcal R_H$ if and only if $b\in\operatorname{Adm}(h)$. This includes
all incomplete canonical tags, unary lengths and tree or address payloads,
all intervening work and all source accepts and rejects.

Proof. The complete-frame language $\mathsf C$ is prefix-free: the three-bit
tag and terminating unary length fix the payload length, so a strict extension cannot be another
complete frame. Thus the serial protocol identifies the current frame
prefix without choosing a future completion. Every proper prefix in
$\mathsf P$ has a next bit still in $\mathsf P$, by taking the next bit
of any witnessing complete frame. Every complete frame denotes one of the
finite requests in Definition 2.4. Its service and delivery terminate,
including when the whole modification rejects; syntax imposes no capacity
restriction on supplied context trees.

For a non-IN successor, keep a canonical completing request sequence that
witnesses $h\in\mathcal R_H$. The prescribed internal step is the same
next step of that run. If $h$ is at the final idle boundary of its witness,
append, for example, the canonical ReadE frame `0000`; its reservation work
supplies the extension. At IN, if $p(h)b\in\mathsf P$, choose any complete
frame extending it. Keep the already completed frames, supply that
completion and finish its prescribed finite service. No future bit affects
the earlier deterministic steps, so this is a lawful completed run with
the given physical successor as a prefix. Conversely, membership of that
successor in $\mathcal R_H$ would supply a canonical current-frame
completion extending $p(h)b$, proving $p(h)b\in\mathsf P$. This proves
necessity and sufficiency on the entire class, not a selected subfamily.

For concrete raw edges, tag prefixes `1` and `10` both extend the Right
frame `10011011`, whose payload is the code `11` of $\alpha$. After the
prescribed intervening work, supplying 1 yields `11` and `101`, respectively.
Neither extends any tag in `000,001,010,011,100`. In Definition 3.2 these
INs occur at $n_-+6$ and $n_-+10$. Each consumes the bit into its latch,
advances control and adds a receipt while leaving the tag tape and its head
unchanged at that occurrence. Both successors are physically executed and
outside $\mathcal R_H$. No later malformed-frame service is needed for
these counterexamples to closure under all raw edges. ∎

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
The exit reached by the final RD(0) is a different phase, before the later
payload seal, completed-frame parsing or source work.

**Definition 3.2 (paid setup used for the equal-clock family).** Fix the
public controller's owner code to $U(0)$ and reserve ordinary public ports
0, 1, 2, 3 and 4 for tag, length, payload, descriptor stream and metadata
template, respectively. All five are initially empty, with their heads at
R. The common paid prefix has installed their boundary pairs, the finite
native graph below and the controller's exclusive read/write tokens. It
has also copied the actual next source-request ordinal into otherwise
empty public port 5 by the paid unary copy below, sealed that copy and
executed Home; MR. Thus port 5 contains exactly $U(q)$, with its head at
the first bit; preceding counter versions remain retained elsewhere.
Positioning at the actual current counter version uses its real Base/Seek
reference and is part of that prefix; once positioned, copying, sealing
and positioning port 5 cost $5(q+1)+1+(2q+6)=7q+12$ occurrences.
Source-request ordinals start at 0 and advance once per actual source
call, including acquisition calls and rejects. They do not count archive
lookup as a source call. Ports 6, 7 and 8 are the respective initially
empty Base-counter destinations.
Here $q$ is acquired counter data, not a meter numeral, future input or
native instruction parameter.

Before appending anything to tag, length or payload, execute PR57.D2's
Base on each empty arena into a distinct empty public counter port. Each
Base executes Home; MR on its arena, RD(R), then EX; WR(0); MR on its
counter: eight occurrences. Seal that counter at R by one CTL. Home; MR
on it costs six more and puts its head on the actual $U(0)$. Thus this
Base preamble costs exactly 45 occurrences and leaves the three arena
heads at R and their three sealed Base heads at their first bits. Let
$n_-$ be its actual final ordinal. All other preceding boot, acquisition,
warm-up and request-counter work is included in that paid prefix. The
five frame/work ports and three Base-counter ports have not been used by
acquisition or warm-up.

A zero-terminated unary copy uses RD and two finite successor arms: for
1, execute EX(destination); WR(destination,read-bit); MR(destination);
MR(source) and return to RD; for 0, execute the same four occurrences and
continue to the next routine. It copies the terminal 0 too, so its cost is
$5(k+1)$ on $U(k)$ and its source head ends one cell past that zero,
at R when this is the port's sole word. A segment copy uses the same
five-row body on each bit, with RD testing for sep instead; the final
RD(sep) exits without copying or moving. It costs $5k+1$ on a $k$-bit
segment. These are explicit finite expansions of AppendWord's body, with
their terminal tests included. A literal bit or separator is appended by
EX; WR; MR, costing three occurrences. All source ports are sealed,
readable by this owner, and distinct from the destination. Data/test
latches are distinct from the retained input latch.

The setup from $n_-$ is the following one finite native graph.

1. Execute one reserve-phase CTL, setting the input-supply purpose tag.
   For each of the three tag bits execute IN; EX(tag); WR(tag,input);
   MR(tag). Seal the tag by one CTL. Execute Home(tag); MR(tag), and three
   unrolled RD(tag); MR(tag) pairs to recognize the finite port code.
   For the family below this code is `010`.
2. Receive $U(d)$ on the initially empty length port. For each supplied bit
   execute IN; EX(length); WR(length,input); RD(length,test); MR(length).
   The RD branches to two identical MR opcodes: the 1 case returns to IN,
   the 0 case goes to a one-CTL seal. Run Home(length); MR(length).
3. Execute one CTL entering the allocation/descriptor purpose. Construct
   the following template on port 4, in the displayed order; each sep is
   a real cell:

   $$
   \begin{aligned}
   D_t&=U(0)U(0)U(0)U(3)\,10\,U(q),\\
   P_l&=U(0)U(1)U(0),& S_l&=10\,U(q),\\
   P_p&=U(0)U(2)U(0),& S_p&=11\,U(q),\\
   W&=D_t\,\mathsf{sep}\,P_l\,\mathsf{sep}\,S_l\,
       \mathsf{sep}\,P_p\,\mathsf{sep}\,S_p\,\mathsf{sep}.
   \end{aligned}
   $$

   In each of the three prefix fields, obtain the base $U(0)$ by the
   unary copy from that arena's actual sealed Base counter. Obtain every
   $U(q)$ by the unary copy from the actual request counter, using
   Home; MR before its second and third copies. All remaining fields are
   the displayed fixed literal bits, appended by their finite unrolled
   rows. Seal W by one CTL, then Home(template); MR(template). The segment
   lengths are $q+10,4,q+3,5,q+3$, respectively.
4. Starting with length at its first bit and payload at R, execute the
   following zero-reservation graph: RD(length,test); on 1 execute
   EX(payload); WR(payload,0); MR(payload); MR(length) and return to RD;
   on 0 exit. Append exactly one sep to payload. This graph is specified
   directly by PR57.D1 primitives; it is not a call of PR57.D2's complete
   Allocate service. Its zero-fill body costs $5d+1$ and its one delimiter
   costs three more occurrences.
5. Construct three complete descriptor records on the initially empty
   descriptor stream. Copy segment $D_t$, append sep, and seal that record
   by one CTL. Move the template head once to $P_l$, copy that segment,
   and move once to $S_l$. Append a literal 1 to the descriptor stream.
   Execute Home(length); MR(length), and copy its whole $U(d)$, terminal
   zero included. Copy $S_l$, append sep and seal by one CTL. Move once
   to $P_p$, copy it and move once to $S_p$. Execute Home(length);
   MR(length), copy $U(d)$ again, then copy $S_p$, append sep and seal
   by one CTL. A segment copy leaves the template head at that segment's
   actual sep; exactly four template MR occurrences join the five copies.
6. Execute Home(length); MR(length), then Home(payload); MR(payload).
   Execute one CTL restoring the input-supply purpose and enter Definition
   3.1's first test. No token changes owner during setup.

The descriptors have PR57.D2's field order: unary owner, arena port,
actual Base offset, length, initialization bit, mutability bit and actual
request ordinal. They are, in full,

$$
\begin{aligned}
D_t&=U(0)U(0)U(0)U(3)\,10\,U(q),\\
D_l&=U(0)U(1)U(0)U(d+1)\,10\,U(q),\\
D_p&=U(0)U(2)U(0)U(d)\,11\,U(q).
\end{aligned}
$$

Appending 1 before the first length copy constructs $U(d+1)$ without
arithmetic advice. The tag and length data are initialized and immutable;
the payload's $d$ data cells are initialized to zero and remain writable.
Its sep is outside those $d$ cells. The descriptor records are immutable,
terminated by sep and bound to these actual construction/seal occurrences;
they do not assert that the mutable payload is already a complete request.
Their shared request ordinal does not alias their distinct arena ports.
The descriptor stream and template are fixed owner-local work ports, not
exported newly allocated data arenas. No descriptor grants another owner
access, and the payload's eventual seal and source dispatch remain later
service work.

No ordinal is used as a primitive operand. Every variable copy scans an
actual sealed source or actual terminating unary word. The Base offsets
are measured before construction, and every head movement, field bit,
terminal test, seal and accounting-tag change in this setup is displayed.
For subsequent frames in nonempty arenas use the general supplier's real
Base/Seek and complete Allocate/descriptor graphs, evaluated by Definition
3.4; the following empty-port formula is not their price.

**Theorem 3.3 (exact reader costs and cuts).** For every $d\ge0$ and actual
request ordinal $q\ge0$ in Definition 3.2, the complete setup after $n_-$
uses exactly $30d+40q+408$ primitives. Put
$n_0=n_-+30d+40q+408$, just before the payload loop's first test. After
$r$ complete payload iterations, $0\le r\le d$, the ordinal is

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
Setup plus loop therefore costs $35d+40q+409$ primitives and ticks, and
$70d+80q+818$ fee units after $n_-$. The Base preamble adds its separately
counted 45 primitives before $n_-$. Later payload sealing, parsing and
source/journal/delivery service are additional. All displayed schedules
are independent of the payload bit values.

Proof. Reservation plus tag supply, seal and recognition cost
$1+12+1+9+1+6=30$: tag ends at R, position 4 relative to L. Length supply,
seal and first positioning cost $5(d+1)+1+(2d+6)=7d+12$.

Template W has $3q+25$ bit cells and five sep cells. Outside its three
Base fields and three request-ordinal fields there are 19 literal bit
cells and five separators, costing 72 occurrences. Copying the three
actual $U(0)$ Base fields costs 15. Copying $U(q)$ three times costs
$15(q+1)$; the two counter Home/MR pairs cost $4q+12$. Template seal
costs 1. Its head is then at R, position $3q+31$, so Home/MR costs
$6q+64$. Template construction and positioning therefore cost
$25q+179$, including all its metadata-source reads and moves. Each Base
source ends at R; the request counter ends at R, position $q+2$.

The zero-reservation body and its one sep cost $5d+4$, leaving length
on its terminal zero, position $d+1$, and payload at R, position $d+2$.
The five template segment copies cost $5(3q+25)+5=15q+130$; their four
joining MR occurrences cost 4. The extra leading 1 costs 3. The two
length-copy positionings cost $(2d+4)+(2d+6)$; the two unary copies cost
$10(d+1)$. Three descriptor separators and seals cost 12. Thus descriptor
construction costs $14d+15q+169$. It produces exactly the three displayed
descriptors, containing $2d+3q+28$ bit cells and three separators. Both
length copies end at R. The last template head is on its final sep,
position $3q+30$, and the descriptor head is at R, position
$2d+3q+32$.

The final length and payload Home/MR pairs each cost $2d+6$. There are
two accounting-tag CTLs. Summing these disjoint executed graphs gives

$$
30+(7d+12)+1+(25q+179)+(5d+4)
 +(14d+15q+169)+(4d+12)+1=30d+40q+408.
$$

Every descriptor is correctly initialized when sealed. No constructed
interval overlaps another port; immutable source fields are only read.
At entry to the payload loop the length and payload heads are both at
position 1. For $d=0$ these are respectively the real terminal zero and
the sole payload sep: the first test exits without touching the sep.
For positive $d$, iteration $r+1$ tests length position $r+1$, consumes
one bit, writes payload position $r+1$ and moves each head once. Induction
gives AIF.1 and AIF.2, and after $d$ iterations both heads are on their
respective zero/sep positions $d+1$. One final RD(0) gives $5d+1$.
The complete setup constructs exactly $4d+6q+66$ new ordinary cells:
three tag cells, $d+1$ length cells, $d+1$ payload cells, $3q+30$ template
cells and $2d+3q+31$ descriptor-stream cells. Meter receipts are additional.
Each primitive has one receipt, one tick and two fee units. ∎

For the zero and small lengths, the exact setup and setup-plus-loop
counts at the same actual ordinal parameter are:

| $d$ | Setup after $n_-$ | Setup plus complete payload loop |
| --- | --- | --- |
| 0 | $408+40q$ | $409+40q$ |
| 1 | $438+40q$ | $444+40q$ |
| 2 | $468+40q$ | $479+40q$ |
| 3 | $498+40q$ | $514+40q$ |

**Definition 3.4 (whole-execution cost evaluation).** For every used native
graph, expand sequence by joining successor edges, public tests by actual
testing RD/CTL rows, and finite loops by their displayed rows. A native
row occurrence has cost 1; an edge which is only its successor field has
no separate cost. A separately executed CTL has cost 1. Parameter creation
uses the actual tape routines: Append costs 3; an actual Home at distance
$h$ costs $2h+1$; Seek costs $2h+3a+3$ plus positioning of its real address
string; Allocate's displayed zero-fill loop costs $5k+1$ plus its actual
positioning, one delimiter and descriptor construction. The explicit
port-local graph of Definition 3.2 has its own complete count. Explicit
loops around a body add their own testing and counter movement occurrences
unless already included in that body.

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
prefix $h\in\mathcal R_H$ after $a(u)$, let $I(h)$ be precisely the word of
bits consumed by public IN after that fence, in actual order. Fixed
deterministic work does not add to it. Let $L(h)$ be the chronological word
of those bits whose
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

**Corollary 4.5 (joint successor transport on the lawful task domain).** On
the actual key image of $\mathcal R_H$, a physically enabled prescribed
non-IN primitive transports
$K=(\operatorname{code}(u),I,n)$ to
$(\operatorname{code}(u),I,n+1)$. At a prescribed IN, every
$b\in\operatorname{Adm}(h)$ transports it to
$(\operatorname{code}(u),Ib,n+1)$. Each transported key is in that same
actual image, and its decoder gives the complete original joint successor
and extended primitive prefix. These are all the raw IN successors that
remain in this image. A physically enabled bit outside
$\operatorname{Adm}(h)$ still executes its raw IN but has no such
same-image extension. A physically disabled action executes no primitive.

Proof. Decode the actual prefix and state by Theorem 4.4. Lemma 2.7 proves
that appending each stated non-IN occurrence or admissible IN occurrence
remains in $\mathcal R_H$, for every prefix in that full class. A non-IN
adds no acquired bit; an IN appends exactly the same supplied $b$; either
adds one to the actual count. The extended prefix therefore has exactly
the displayed key. Theorem 4.4 applied to it gives its whole successor,
including latches, work, permissions and receipts. Lemma 2.7 also proves
that no other raw IN successor belongs to the class. In particular its
`11` and `101` edges are executed exits from the lawful domain, not disabled
actions. No future bit is predicted from $u$ or $n$, and no physical raw
edge is removed by this transport statement. ∎

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
same accessible actor at those actual IN ports. The fixed TagRead header
admits all $d$-bit address words, so both bits are in the task-input domain
at every payload IN in these families. Equal $d,r$ give the same
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
from its authentic complete prefix. Every such completion is a canonical
TagRead frame, so this experiment is in the task domain at every member
of the fiber. At a latch cut this first executes the prescribed WR; it
does not resupply the bit already acquired. The
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
future experiment tree therefore has the same domain membership at these
identical endpoints. On that domain it has the same legality, labels,
outputs and whole successors by deterministic evaluation with its same
future supplied bits. This proves the other direction of AIF.8.

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
and equal experiment domains and all task responses. Task equivalence
forces equal $x$ by the fetched request fields, and its common $S_0$ is
already equal. These are both
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
complete explicit setup gives $n_0=n_-+498+40q$, where $q$ is the common
actual request ordinal. Their written/latch data and eventual request
fields under the common L continuation are:

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

For this seed the acquisition makes one TagRead, and the two warm-ups
make two Rho calls. Hence Definition 3.2's source-request counter is
actually $q=3$: the setup costs 618 primitives, $n_0=n_-+618$, and the
four displayed latch cuts are at $n_-+625$. Setup plus the whole
three-bit payload loop costs 634 primitives after $n_-$.

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
| Independent input | At the latch fiber, $r$ actual payload INs, $r-1$ WRs, $r-1$ payload moves, $r$ tests and $r-1$ length moves have executed: $5r-3$ primitives after $n_0$. The completed loop is $5d+1$; the chosen empty-port setup is $30d+40q+408$, including its template, three descriptors and two accounting-tag changes. |
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
port-local zero-reservation graph has constructed all $d$ cells before
the varying ingress, and Theorem 5.2 counts distinguishable values
conditional on that common layout. These are different quantities. ∎

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
is needed for the counting bounds: the full finite address fibers are
realized by the two accessible supply edges, both admissible at each of
their payload INs. Search scope and these citations do not establish absence
of stronger results elsewhere.

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
acquired input on the full lawful canonical-frame history domain under
deterministic dispatch. Successor transport covers every enabled prescribed
non-IN edge and exactly the admissible input edges of Definition 2.2. They
do not define the missing natural support/frontier relations. The last committed tree
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

Physically enabled raw bits that destroy canonical extendibility leave
the lawful history and task-transport domains. Their actual IN successors
are retained as executed occurrences in the physical semantics, but no
malformed-frame continuation, response service or replay-image closure for
those runs is established. Studying such a domain requires specifying that
behavior; restricting task experiments does not physically prevent the input.

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

## 10. A paid two-owner acquisition bridge at every attained D0 cut

### 10.1. The target and the additional atomic basis

**Definition 10.1 (one original target, not the installed RCA dispatcher).**
Fix the controller of Definitions 2.1–2.5, including its actual finite
native row description, all boot routines and the canonical acquisition
of the seed. Call this controller $D_0$, its original primitive state
$X_0$, and its acquisition fence $a(u)$. Its input is the original public
IN, including the five-row payload loop of Definition 3.1. Its meter
counts its own original native rows, starting at the original irreducible
entrance. In particular the absolute target count is $n(h)$, not the
number of rows after acquisition. This is one prospective acquisition
flight: the initialized waiting consumer may choose any attained original
cut, and its capture token is consumed only when it chooses that cut.
Subsequent Calls use the one acquired historical package. The all-cut
quantifier does not request simultaneous overlapping acquisition flights.

Fix the port-local or general Base/Allocate implementations selected in
that description once and for all. All reference fields below use their
actual owner, arena, base and construction ordinal conventions. Choosing a
different allocation implementation would require a different $D_0$ and
its corresponding replay description.

The [Retrospective Cut Acquisition volume](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md),
here called RCA, supplies its finite word compiler (§11), literal row
interpreter (§12), and actual archive/channel/return routines (§13.4).
Its installed $D_1$, service-frame IN, retained port-38 input, activation
chain and Initialize parser are **not** this producer or its entrance.
Here there is no replacement of an original IN by RD(38); MR(38), no new
version field in an original producer row, and no RCA source-frame
activation. The consumer below interprets precisely the fixed $D_0$.

**Definition 10.2 (the changed apparatus $A^+$).** There are two finite
controllers, producer $P$ and consumer $C$. They have separate PCs, eight
latches each, purpose bits, finite token fields, native code and meters.
The original 64 tape ports, their cells and the original control fields
belong to $P$. One additional tape $J$, assigned port 64, is a consumed-input
mirror. Another 64 tapes belong to $C$: its local port $i$ has actual
port $65+i$, for $0\le i<64$. Local 32–39 are its RCA compiler lanes;
local 8 and 9 are its input and tally spools; local 40 and 48 are its
receiver and mailbox. Each controller's meter is its own designated meter
port, as specified in its finite description. None of these three spool,
receiver or mailbox choices is the compiler bank, scratch or meter.

All tape cells retain the structural encoding $G(c)=F_8[g(b_0),\ldots,
g(b_7)]$ of the [Structural Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md),
here called SSA, §§3–5: 47 vertices for one eight-bit cell. The ordinary
ordered-tree ports and the four old head ports remain
$P,L,R,O_0,H_0,O_1,H_1$. Enlarge this finite port alphabet by the two
reciprocal pairs $O_2,H_2$ and $O_3,H_3$. These are extra physical
incidences, not an interpretation of an old empty socket.

There are four fixed anchor occurrences, two for $P$'s meter and two for
$J$. At a captured tape, the first anchor's $O_2/H_2$ link names its fixed
end cell; the second anchor's $O_3/H_3$ link names its moving scan cell.
These links terminate at **cell roots**, never inside a $g$ bit. During
startup the same anchors may be used for public immutable seed-copy
scans; those links are all cleared before the acquisition fence. The
anchors and controller register bits have fixed finite scaffold sockets.
One may use a full ordered scaffold with at least 135 sockets: 129 tape
origins, the two finite register-component roots and the four anchors.
Register components expand to their actual finite numbers of encoded
bits. Changing a scaffold routing depth changes the structural bill;
no original tape or descriptor field acquires that depth as data.

Erasing the additional tape and controller components, the four new port
fields, and the additional finite control fields gives the original
primitive representation. Port selection for $P$ routes to the same
original port number. This erasure is denoted $\pi_P$. It is a specified
projection of tape/control data, not an assertion that the enlarged
scaffold has the same spatial shape as the old SSA scaffold.

**Definition 10.3 (explicit new rights and atomic rows).** The following
are added to the basis. Their bounded graph probes and assignments are
charged by Definition 10.27. Only their complete atomic successors are
cuts of $A^+$.

1. A post-acquisition source-frame IN has its original latch, PC and producer
   receipt effect and, in the **same row**, appends the supplied bit to
   $J$. At $J$'s current R it replaces the symbol by that bit, seals that
   data cell against further writes, constructs a new R, and moves only
   $J$'s append link to that R. The seal is the append-only row restriction:
   no row can later write that bit, so no uncounted per-cell seal flag is
   assumed. This costs the real cell construction and
   link work. It is not a second IN or an additional producer receipt.
   Boot and private-installation INs retain their original effects and
   are not source-frame input; the mirror is empty at the acquisition fence.
2. One consumer row, Capture, can follow the actual append links of both
   $J$ and the producer meter. In that same row it binds their current R
   cell occurrences to the two fixed-end anchors, binds the two scan
   anchors to their actual L boundary cells, and consumes a one-use
   capture token. It appends one receipt to **C's** meter. No numeral,
   prefix word, source packet or producer latch is returned by this row.
3. A consumer cursor row may follow its own scan/end links, compare
   their target occurrences for equality, read the eight-bit cell at its
   scan link when authorized, or move that link to an existing adjacent
   cell by the SSA local path. Each such test, read or move is a paid row,
   with a consumer receipt and its actual finite latch/PC successor.
   Equality is the alias case of two bounded followed links; it is not
   comparison of unbounded numerals or a search for equal payloads.
4. Startup grants read access to the already sealed acquisition sender
   and its actual sealed placement/descriptor records. Public boot
   constants are separately emitted during setup. The grant permits
   auxiliary cursor placement at
   the corresponding **fixed tape origins**, followed by paid local
   scans. It grants neither a private-source port nor direct placement
   at a numerically asserted seed offset. The source of the grant is the
   actual acquisition-output seal, as specified in Definition 10.5.
5. After startup, $C$ has read/cursor rights on $J$'s sealed bit cells,
   its captured end occurrence and the producer meter's cell topology.
   It has no right to change a producer symbol, old mark, latch, token,
   descriptor or control field. On the producer meter it needs no right
   to read receipt payloads. $P$ has append rights on $J$, no right to
   change a sealed bit there, and no right to clear $H_2,H_3$ on a cell.

The new row table also permits the two finite external consumer commands
Capture and Call in their respective phases. These are actual paid
entry rows, with no data payload. Their occurrence times are independent
choices. The only historical target selector is the prospective Capture
occurrence; no old target ordinal is supplied. The single-package Call
needs no package index or further command frame. Internal work after
either command is deterministic. All other new rows have finite PC,
symbol, token and local-alias guards. There is no row that snapshots an
unbounded word or performs a complete scan atomically.

These are stronger atomic/read grants than PR57's original row menu.
They are part of the changed apparatus and its tariff, not consequences
of old occurrence identity, the old empty-port premise, or source-blind
finite control. They are hypotheses of the constructive theorem.

### 10.2. Actual initialization and owner independence

**Definition 10.4 (physical rows and lawful rows).** A joint history is an
interleaving of complete $P$ and $C$ rows. When $P$'s next original row is
not IN, AdvanceP executes that exact row with Definition 10.3's preserved
extra fields. When it is a public IN, SupplyP(0) and SupplyP(1) are both
physically enabled. Their old latch/control/receipt effects and the new
mirror effect all execute. Lawful histories require the bit to belong to
$\operatorname{Adm}$ of Definition 2.2. A nonadmissible bit is an executed
raw exit from this lawful domain; it is not `none`. No syntax filter is
inserted in front of IN.

The producer cannot read $C$'s PC, scratch, latches, commands or meter.
After the fence its original enabledness never depends on consumer
progress, capture or call. The consumer cannot take a producer source
step. Its post-Capture internal enabledness never depends on another
producer step, input, complete frame, committed event or row seal.
There is no test requiring a producer Ready state. External P bits and
external C command times are separate choices; neither predicts the
other. Scheduling adds only joint interleaving, not an undisclosed input
to the original controller.

**Definition 10.5 (paid startup before the original acquisition fence).**
The actual common run begins with construction of the declared finite
scaffold, the two irreducible meters, all boundary pairs and all finite
code, register, token and grant bits. Each finite constant is emitted by
its literal finite sequence of writes. Each tape is built, not assumed
to have free cells. Original $P$ boot and valid-source installation are
exactly those of $D_0$, including its canonical private packet and its
actual full-source traversal. No source-dependent auxiliary advice is
installed in $C$. A paid finite startup-phase field selects the enabled
owner: first BootP, then SeedCopyC, then FinishAcquisitionP. At the
acquisition sender seal the new grant bits are set and startup enters
SeedCopyC; only C startup rows are then enabled. C's completed manifest
and cleared setup links enable its final SetupDone row, which hands the
startup permission back and enters FinishAcquisitionP. Only the remaining
original P acquisition rows are then enabled. The last acquisition row
sets Armed and enters Independent, where Definition 10.4's union of
owner edges applies. All these startup fields are additional finite
encoded fields; no original P token is transferred. This synchronization
is part of initialization, not a post-acquisition producer-progress
hypothesis.

During that traversal's ordinary acquisition output protocol, hold $P$
after its lossless seed sender and placement records are sealed, before
the original delivery/acknowledgement/return has completed $a(u)$. A sealed
immutable sender exists before its receiver's completed delivery; this is
the same two-stage channel distinction used in §6. The finite acquisition
return path is not source-frame input and cannot admit the first source
frame while held. The startup grant is attached to this actual seal, not
to a proposed seed word.

With $P$ held, C first executes RCA §11.4's native empty-bank prelude
on its own ports, constructing its sentinels, empty registers, initial
descriptors and seals. Its finite parser/word program is now physically
entered; parsing is not used to assume that prelude. C's local 10 and 11
are owned temporary data/counter tapes, distinct from the still-empty
local 8 and 9 capture spools. Then $C$ copies from the granted public
tapes as follows. It
places its auxiliary scan link at their real L boundary, advances to the
first ordinary cell, and reads/moves through the sealed descriptor
prefix, using its ordinary finite tuple parser. It retains the actual
acquisition sender's owner, arena, base, length and creation binding. If
the arena contains earlier records, they are really scanned. The sender
record is the completed acquisition-output record at the held protocol
stage; its binding is the actual original placement record, not a newly
chosen offset. Copy its unary base and length to C-owned scratch, clear
the auxiliary link, and place it at the sender arena's L. Advance once
to data offset zero; consume the copied base one mark at a time, taking
one adjacent move per mark. Then copy precisely the copied length by
paid read/append/move iterations, including every terminating test.
The counter and data latches are different. Auxiliary cursor reads use
C latch 0 for data and latch 1 for counter tests. RCA's compiler uses its
separate latches 4–6. Before invoking a word helper on a read bit, branch
on latch 0 to the literal-0 or literal-1 cons call; the helper need not
preserve that input latch. Direct spool copies instead preserve latch 0
through their matching WR. The immutable source block
and its sealed descriptor are unchanged throughout.

This routine reads and copies the actual framed seed payload. Parsing its
fixed acquisition-output codec yields $\operatorname{code}(u)$; its copied
placement records bind that output to this actual acquisition under the
common preparation $\xi$. It does not query $u$ again. The fixed public
$H,\xi$ and boot/descriptor parameters of Definition 2.1 are emitted by
finite literal C-installer writes. Their equality to P's fixed public
parameters is part of this canonical common installation, not an assumed
new public-record tape in $D_0$. Code $\Delta(D_0)$ and the fixed
entrance description are likewise emitted as finite constants, bit by bit; a
native-description read port is not postulated. The output seed is
variable acquired data; $\Delta(D_0)$ is source-independent code.

C builds its own sealed manifest with these ordered fields: the fixed
D0 description, public boot/descriptor parameters, $H$, $\xi$, the acquired
seed, and its actual acquisition-sender binding. Each variable field is
copied from the just constructed source block, with measured Base/length,
actual descriptor, delimiter and seal. There is a leading F sentinel and
one F after each field. The already constructed compiler banks retain
all setup versions and their actual descriptors. Import this manifest
with RCA's full-prefix
routine: Home; MR reaches the leading F, the **second MR** reaches the
first field, and finite field parsing includes empty fields. The parser
here expects the stated D0 fields. It does not require or strip RCA
Initialize's D1 field-zero tag 101, and does not obtain a D1 activation
chain. The word helpers and the importer operate only on $C$'s banks,
scratch and granted immutable manifest.

All setup cursor links on original public cells are cleared. Construct
$J$ as the empty L,R tape with its append link on R. The four capture
anchors are empty, both spools are empty, and the capture and invocation
tokens are actually encoded in their separate installed fields. The
invocation token is live but Call is still phase-disabled. Setup has not
modified an original head, latch, token, code bit, receipt or descriptor.
The seed read grant has been paid and exercised; possession of a numeric
code or a mathematical isomorphism is not used as acquisition.

Now resume exactly the remaining original acquisition channel,
acknowledgement and return rows. Their source and destination cells and
old tokens are as before the pause. At the original acquisition fence's
last row, additionally set C's phase to Armed. Call this joint fence $F$.
Thus

$$
\pi_P(X^+(F))=X_0(a(u)),\qquad J(F)=\epsilon.
\tag{AIF.13}
$$

C's setup rows precede this fence and have only C receipts. There is no
post-$a(u)$ interval in which $P$ has advanced but Capture is uninstalled.
The projection's original acquisition prefix is unchanged. The **joint**
startup chronology contains the paid extra setup rows and is not claimed
to equal that original prefix.

**Lemma 10.6 (startup is finite and actually acquired).** For every valid
finite seed $u\in\mathcal T_H$, Definition 10.5 reaches $F$ after finitely
many actual rows, with exactly the manifest values just stated and all
original $D_0$ acquisition fields preserved under $\pi_P$.

Proof. The original acquisition terminates by the supplier used in
Definition 2.1. At its held point all scanned source records and the
sender word are finite, sealed and retained. The descriptor traversal
consumes an unchanged finite prefix. Each unary skip/copy iteration
consumes a mark of an actually copied counter; no count is supplied by
the proof. Every copied bit comes from a cursor read of that immutable
sender. The acquisition-output codec is lossless on this actual domain,
so its parsed seed is $\operatorname{code}(u)$, not an independently
postulated seed. Finite constant emission terminates. RCA §§11 and 13.2's
word expansion/import terminate on the finite owned records; the stated
two entry moves give the correct first field even when a field is empty.
Their read/copy rights are the new setup grant, not a producer token.
Each setup row changes only new links or C-owned data and its meter.
The remaining original delivery therefore has its original preconditions
and successors. Its final row establishes AIF.13. ∎

### 10.3. Local realization and preservation of original rows

**Definition 10.7 (complete slot policy).** Every graph occurrence has all
11 ports. A newly constructed occurrence initializes all 11, including
empty entries. Existing-row assignments name individual slots and preserve
every unnamed slot. In particular the old bit-value template changes
only the four old slots of SSA's five-occurrence bit gadget: root L and
R, fork P, and singleton P. It leaves $O_2,H_2,O_3,H_3$ unchanged. Ordinary
head operations change just their old reciprocal pair; they do not clear
a cell's other incoming links. The meter's receipt operation changes its
old append pair and receipt bits, preserving the read pair **after** any
core read-head movement. It never uses core EX or WR on that meter.

The mirror append uses the same right-spine cell constructor. If $z$ is
the old trailing terminal beyond its old R cell, replace $z$ by the binary
node $\langle G(\mathrm{new\ R}),z'\rangle$. The old R cell is retained;
its symbol becomes the bit and it is sealed, with all its new link slots
preserved. The cell-root path to the next cell is $P R L$; the previous
cell path, when it exists, is $P P L$. No step detaches an old cell root
or rewrites an earlier right-spine node. A seal protects the bit value,
not an old head mark or every possible field of that occurrence.

Capture sets four reciprocal links, hence eight link slots, on its
anchors and the four target roles: two R ends and two L scan starts.
The L and R cells of an empty tape are distinct occurrences. The two
tapes are distinct. If a later cursor occupies an end, $H_2$ and $H_3$
are different slots. If an old read/append head is there too, its $H_0$
or $H_1$ is different again. Retargeting a scan clears only its old $H_3$
and anchor $O_3$, then sets the corresponding new pair. The initialized
reciprocal pair is treated as a single consistent assignment when two
roles coincide; there is no double incompatible assignment to a slot.

**Lemma 10.8 (finite bounded realization, including aliases).** The rows
of Definitions 10.3–10.7 have a finite table of bounded structural
patterns. They preserve the original row effects field by field under
$\pi_P$. No old empty-port switch lemma is required.

Proof. Static port routing, PC bits, latch bits and token fields belong
to fixed finite scaffolds. At a tape origin, an old head, append link or
new anchor link leads directly to its cell root. Reading a cell inspects
its fixed 47-vertex gadget. A next/previous move uses the displayed
three-edge tree route; neither length nor cell index affects its radius.
A receipt or mirror append inspects the old append cell and its trailing
terminal, and constructs one 47-vertex cell and one new terminal. The
new row cases inspect at most eight cell roots, their fixed gadgets,
the four fixed anchors and fixed finite registers. Their finite route
words, together with the static scaffold routes, give a finite radius
bound depending only on the installed apparatus. No route follows an
unbounded chain within one row.

For an ordinary original row, combine core and receipt effects by the
old SSA alias rule first. That rule already handles an old read head
coinciding with the old append cell. Then preserve all four new slots.
A P input row has no core tape write, so its extra mirror append and
producer receipt are on disjoint tapes. A C cursor row changes only its
own anchor's $O_3$, the corresponding $H_3$ fields, its own finite
registers, and C's receipt. Capture may meet old read/append marks, but
the new slot names are disjoint from those marks. A new endpoint/cursor
alias is handled by retaining both different incoming slots on that
same root. These exhaust the possible cross-role coincidences, since
producer, mirror and consumer tapes are disjoint.

There are finitely many old row cases, symbols, register states and
equality partitions of these finitely many roles. Enumerating their
consistent old-value dependencies produces the finite table; all
unmentioned ports are copied. It does not test whether all other ports
are empty. New occurrences are initialized with the full 11-slot table.
Thus the $g$-bit templates, append templates and head templates remain
valid with these extra incidences by their explicit assignments, rather
than by an application of SSA §13's stricter switch premise. Erasure
removes exactly the named extra effects. ∎

**Definition 10.9 (actual producer occurrence correspondence).** Delete
all C rows from a joint prefix and replace each augmented producer row
by its original D0 row. Call the resulting original prefix $p(z)$.
Original cell and record names are carried by their actual P-port
construction order and the old descriptor fields. $C$ allocates only
on different ports and has a separate descriptor list. An original
Base scan scans the same original arena; its creation scan scans the
same original record stream. It does not count C's meter or records.
The order-preserving injection of actual P rows into the joint history
is the witness for occurrence correspondence. There is no arbitrary
isomorphism or renumbering of stored original fields.

**Theorem 10.10 (exact original-interface projection).** From $F$ onward,
for every lawful joint prefix $z$, $p(z)\in\mathcal R_H$ and

$$
\pi_P(X^+(z))=X_0(p(z)).
\tag{AIF.14}
$$

For every physically enabled original row $e$,

$$
\pi_P\bigl(\delta^+_P(X^+(z),e)\bigr)
 =\delta_0\bigl(\pi_P(X^+(z)),e\bigr).
\tag{AIF.15}
$$

Original labels, output bits, legality, raw bits, permission fields and
complete successors agree. A C row stutters under $\pi_P$. Both raw IN
successors satisfy AIF.15; only the admissible one or ones preserve
membership in $\mathcal R_H$. Original disabled attempts stay disabled
and execute no row.

Proof. AIF.13 gives the initial state. Lemma 10.8 preserves every original
row field. In particular extra C work cannot alter an original allocation
base, head position, PC, latch, token, receipt count or construction name.
Induction on joint rows proves AIF.14 and AIF.15 simultaneously, using
Lemma 2.7 at the lawful-input cases. The original producer meter receives
one receipt per P row, never per C row. Therefore its absolute count is
exactly $n(p(z))$, including the unchanged projected boot/acquisition.
An inadmissible bit changes the original latch and control and appends
both the original receipt and the mirror bit; the same erasure equality
holds for that executed raw successor. Its later malformed behavior has
not been added to the lawful theorem. ∎

This is a projection of the **entire original interface**, including
current original actions at a busy cut. It is not just equality of the
last decoded tree or of completed source-event lists.

### 10.4. One capture binds two actual frontiers

**Definition 10.11 (consumer phases and the acquisition package).** The
consumer phases are Setup, Armed, InputPrime/InputTest/InputRead/InputAppend/
InputNext, MeterPrime/MeterTest/MeterAppend/MeterNext, Finish, Sealed,
CallBusy, and Ready. Append phases expand into their finite ordinary
native rows; a finite PC remembers the subphase and preserves the data
latch through its matching WR. A length/test latch is distinct. A consumer
step is enabled exactly at its current installed subphase with the
required actual token/links/read permission. There is no unbounded
subphase index in finite control.

Capture is enabled in Armed with its unused capture token and the actual
append/read grants. Its complete successor enters InputPrime and fixes
both frontier links. This unique occurrence defines $z_*$, its immediately
preceding attained joint cut, and

$$
h_*=p(z_*),\qquad r=|I(h_*)|,\qquad n=n(h_*).
\tag{AIF.16}
$$

These symbols are proof parameters, not Capture operands. The token is
consumed, so another Capture has no transition. Finish seals the actually
constructed input/tally spools, imports their words into C's compiler
banks, and creates a sealed package with actual Base, length, creation
record and manifest binding. Before this package seal no Call is enabled.
The package retains the acquired input word, the actual unary target
count and the manifest. Sealed and Ready permit Call with the live
invocation token. A Call entry performs the actual token handoff to the
handler and reserve; CallBusy disables another Call. The later return
restores the token and enters Ready.

An attempted unauthorized read, unavailable destination read, early Call,
repeat Capture, or Call while busy is illegal and unexecuted. Original
rejects and `absent` remain executed original outcomes. This construction
has no Crash or hostile-writer recovery rule. It does not infer a valid
source service from an uninstalled or invalid seed preparation.

**Lemma 10.12 (mirror and meter invariants before Capture).** At every
lawful joint cut at or after $F$, the sealed bit prefix of $J$ is exactly
$I(p(z))$, in consumed order. It is followed by its unique current R.
The producer meter has its original L, exactly $n(p(z))$ receipt cells,
and its current R. Each cell root already constructed remains at the
same position in that tape's right spine. All earlier mirror bit values
remain unchanged.

Proof. At $F$ the relative input word and mirror are empty. An augmented
public IN appends exactly the bit just consumed, atomically with the old
latch change. No other producer row changes $J$. This includes the
IN-to-WR interval: a bit is in $J$ already when the original retention
identity has it only in $Q$, not in $L$. Consumer rows preserve both the
mirror word and producer meter. The original meter receives one cell per
producer row by its common receipt stage; its core never EXs or WRs that
meter. Appending changes an old R's symbol and the trailing terminal,
not an earlier spine node or cell identity. Induction proves all claims.
The topology claim makes no assertion that every original receipt mark
bit is immutable. ∎

**Lemma 10.13 (same-cut frontier binding).** At Capture's complete
successor the end links name respectively the R immediately after the
$r$ captured bits and the R immediately after the $n$ captured receipts.
Those are the two frontiers of the **same** attained cut $z_*$.
Arbitrary later legal producer activity preserves those linked
occurrences and all captured mirror bit values. It may change either
linked endpoint's symbol and old marks.

Proof. Before the atomic row both append links have the values in
Lemma 10.12. Capture binds those exact two targets before any other row
can intervene. It obtains no independently sampled pair of optima or
marginally compatible words. Its receipt goes to C's disjoint meter.
Later producer appends can turn the linked old R into a bit or receipt;
the old root and its new link slots are preserved by Definition 10.7.
Earlier bit cells stay sealed. No producer row changes the end anchors,
and there is no second Capture. ∎

### 10.5. The forward scans, including changing endpoint symbols

**Definition 10.14 (the actual prefix scan).** A scan link starts on its
tape's actual L cell, as set by Capture. InputPrime takes **one** next
move $P R L$. InputTest follows both links and tests target-occurrence
equality **before reading a symbol**. On equality it performs no data
read and enters MeterPrime. Otherwise InputRead reads the bit into C's
data latch 0. InputAppend appends that latched bit to C's input spool by
EX; WR; MR, then InputNext moves its scan link once by $P R L$ and
returns to InputTest. Tests and moves each have their own C receipt.
No helper overwrites that data latch between InputRead and its WR.

MeterPrime takes one next move from its L. MeterTest likewise tests
occurrence equality first. On equality it enters Finish. Otherwise
MeterAppend appends the literal bit 1 to C's tally spool by EX; WR; MR;
MeterNext moves its meter scan link once by $P R L$ and returns to
MeterTest. It does not read receipt symbols, sequence numbers or moving
old read marks. Finish executes Append(tally,0), Append(input,sep),
Append(tally,sep), Seal(input), Seal(tally), in that order. Each Append
is EX; WR; MR and each Seal is one designated CTL. The spool heads are
already at their actual R cells, since every preceding append ended
with MR. Thus an empty bit word is an empty framed field. The count is
$U(n)=1^n0$, including when $n=0$.

In particular a symbol test for R is **not** the stop guard. A cursor
never moves from the captured endpoint. The receipt emitted by each scan
row belongs to C, so it does not lengthen either scanned prefix.

**Theorem 10.15 (actual finite prefix acquisition under arbitrary P).**
After any lawful Capture, under any subsequent legal P interleaving,
each scan has exactly its captured number of non-end iterations. It
constructs exactly $I(h_*)$ and $U(n(h_*))$. This conclusion needs no
further producer step or input, and no completion of an unfinished
producer frame, source write, row or copy.

Proof. Number the already existing cells of $J$ at capture as
$L,c_1,\ldots,c_r,e$. Prime reaches $c_1$ if $r>0$, and reaches $e$ if
$r=0$. At InputTest after $i$ completed iterations the spool is exactly
the bits of $c_1,\ldots,c_i$, and the cursor is $c_{i+1}$ when $i<r$,
or $e$ when $i=r$. For $i<r$, the current cell and its next neighbor
were constructed before Capture. Their spine route and the current bit
are preserved by Lemmas 10.12–10.13. The equality guard is false; the
read and matched append copy that exact bit, and Next establishes the
invariant for $i+1$. The induction remains true across any number of P
rows between those C rows.

At $i=r$, equality is true regardless of the current symbol of $e$.
The scan stops without reading it. This proves both that the last desired
cell was copied and that no later acquired bit is copied. For $r=0$,
Prime/Test stops immediately even if subsequent P input has already
turned $e$ into its first bit. A backwards scan from the mutable endpoint,
or a scan stopping on its current R symbol, would not have this proof.

For the meter, number its captured cells
$L,d_1,\ldots,d_n,f$. The identical invariant has tally $1^i$ and cursor
$d_{i+1}$ or $f$. Here the loop needs only the preexisting next route,
not immutable receipt bytes or a fixed old read head. At equality it
stops, then appends 0. No future P receipt is counted. The invariant also
covers the formal zero-prefix case, without trying to read a nonexistent
first receipt.

Every iteration has a fixed finite number of C rows before its next
Test. The two loops therefore have finitely many C rows. Their spools
are disjoint from their scan sources, and all guards used are established
by the invariant. This proves acquisition, not merely existence of a
word equal to a mathematical prefix. ∎

**Definition 10.16 (C-progress).** On a continuation with internal C work
pending, every next enabled prescribed C row occurs after finitely many
joint rows. The producer may take zero rows, finitely many rows, or
arbitrarily many rows between C rows. No bound on those delays or on
physical elapsed time is imposed. Once a Call is issued the same
condition applies to its prescribed receiver, printing, ACK and return
rows, which are controlled by C. A receiver awaiting an independently
chosen external ACK would require an additional progress hypothesis;
that is not this installed receiver.

**Corollary 10.17 (sealed, bound acquisition under C-progress).** Under
C-progress the complete Capture-to-Sealed routine terminates with an
actually sealed package whose decoded fields are

$$
(\Delta(D_0),\mathrm{boot},H,\xi,
 \operatorname{code}(u),I(h_*),U(n(h_*)),\mathrm{origins}).
\tag{AIF.17}
$$

Its origins bind the real startup seed copy, the unique Capture, both
fixed frontier occurrences, the actual spool seals and the package's
construction. The stored anchor names are fixed literal role/port tags,
whose actual links persist; they are not unbounded occurrence identifiers
read by a new primitive. Other placement fields are the copied actual
descriptors. Capture has a unique one-flight role, so binding to it needs
no supplied joint-time ordinal. The package is available to its installed C owner; a
pointer or its numeric descriptor alone is not that availability.

Proof. Theorem 10.15 provides the actually written spools. No import or
package code reads an unsealed spool. RCA §11's finite word construction
and Base/descriptor routines terminate on finite C-owned tapes and
retain their old versions. They scan those **actual** words, append
complete framed fields and the actual descriptor, and seal only after
the last field. Lemma 10.6 provides the other fields and their source
binding. Each routine has finitely many own rows independent of P;
C-progress therefore reaches the package seal. No new seed, target
count or package key has been supplied as input. ∎

### 10.6. Later actual Call, output and complete return

**Definition 10.18 (the D0 prefix computation).** On a sealed package,
Call imports its actual fields and uses RCA's word language and literal
`Step`, specialized to the D0 description. Reconstruct the canonical
private installation packet from the acquired seed and public $H$;
prepare the fixed boot/control reservoir and the captured external-input
reservoir. Initialize the represented original irreducible entrance,
not the consumer's current native state. Copy the acquired unary target
into a private countdown. While that countdown has a leading 1, execute
one literal represented D0 row, append its complete represented event,
and remove that 1. Stop before the next row when the terminal 0 is
reached. Input reservoirs are selected by the represented boot/acquisition/
source-frame phase, as in RCA §12. There is no D1 activation branch.

The actual word bank operations are RCA §§11–12's finite scans and
rewrites. Simulated permission bits are data, never physical TOKs.
The resulting HistoricalImage is the complete original $D_0$ native
history and raw endpoint, with $(D_0,\xi,n)$ binding. Pending ingress,
invalid source packets and unsealed original destinations are encoded
as such, not replaced by completed semantic states.

**Definition 10.19 (actual publication and return).** Use RCA §13.4's
Publish graph, with all ports renamed by $i\mapsto65+i$. Its sender is
C's local service archive 39, mailbox is local 48, receiver is local 40.
Base and length are measured on the actual current C arenas; complete
Allocate and descriptor construction precede each copy. The payload is
the HistoricalImage from Definition 10.18, framed as one actual result
word with its target and package binding. There is no free read from a
word register.

The sender is sealed. The first real copy, with its length tests, seal
and token handoff, constructs a mailbox. Only after that mailbox seal
and handoff does the second copy construct the receiver. Only after the
receiver seal is its read token available. Recover the actual receiver
base and payload length by the staged records and paid Seek/counter
copy. Execute the prescribed RD(length); RD(receiver); OUT; MR(receiver);
MR(length) loop, including its final zero test. Thus its released
serial output is the receiver's actual payload. Both length and data
positioning are performed from their actual current heads.

The receiver/client and handler are two installed operational roles of
C, with distinct finite token fields. The invocation token moves to the
handler at Call entry; the mailbox availability token moves to channel
setup and back. The actual receiver ACK is a prescribed C-controlled
row after printing and delivery completion. The completion record and
handler return updates precede the actual invocation TOK back to the
client, then the Ready CTL. Publish does not itself enter Ready.
Retained package/read tokens and returned invocation ownership are
separate fields. No original producer token is borrowed or minted.

**Theorem 10.20 (continued callable use, actual output and return).**
Let Capture occur at any lawful attained joint cut at or after $F$.
Let C-progress hold until the package seals, and issue Call at any later
Sealed or Ready cut with its live invocation token. Under C-progress,
that Call terminates with actual sealed sender, mailbox and receiver,
serial output

$$
\operatorname{HistoricalImage}
 (D_0,\xi,n(h_*),h_*,X_0(h_*)),
\tag{AIF.18}
$$

an executed ACK, the invocation token actually returned to the client,
and C's actual Ready state. This holds for every legal subsequent
producer continuation, including the continuation with **no producer
step at all**. No future producer bit, source response, completion or
frame is required by the consumer computation.

Proof. Corollary 10.17 authenticates the input of the actual Call, not
just a tuple asserted in the proof. Theorem 4.4 identifies that tuple's
D0 replay with exactly $(h_*,X_0(h_*))$. RCA §12's per-row transformation
has the same original pre-state, row, reservoirs, old-value dependencies,
core effect and common receipt at each simulated step. Its word/compiler
expansion gives an actual finite C routine for each of the $n(h_*)$
steps. The countdown includes the absolute boot/acquisition rows, so it
stops at the exact original row boundary. It consumes no input beyond
$I(h_*)$. A source packet invalid at that cut is an ordinary represented
bit list and availability phase; nothing calls a semantic source on it.
This proves the value actually written into C's result bank.

For publication, the length counter is constructed from that real finite
word. Induction on each of the two copy loops shows that after $i$
iterations its destination has exactly the first $i$ sender bits, while
it is unavailable before its seal. The final tests, seals and actual
TOKs establish the receiver value and read right. The print-loop invariant
has output equal to the first $i$ receiver bits and the matching remaining
length. It finishes with exactly AIF.18. The prescribed ACK and return
rows then execute and restore the live invocation token. These are
physical native token updates, unlike historical token bits in AIF.18.

All Call loops scan finite immutable owned words, and only C's tapes can
grow during them. Each has finite C work by the compiler, copy and return
suppliers. C-progress suffices for their termination. Projection
Theorem 10.10 lets any P continuation proceed independently throughout;
none of these arguments reads its future input or waits for its phase. ∎

**Definition 10.21 (the full successor, not a restored old world).** Write
$E^+$ for the actual joint row list from the irreducible common foundation
to this returned Ready, and $z_R$ for its endpoint. Its complete successor
is obtained by the following fixed row recurrence: apply the row's
old-value core assignment, its specified extra-slot/mirror assignment,
its own controller's common receipt assignment, and preserve every
unnamed field. Allocate fresh vertices by their actual controller/arena
construction occurrences. This defines every intermediate and final raw
field, including old versions and partial objects, rather than only the
printed payload.

In particular, if $w_P$ is the actual list of P rows after Capture through
$z_R$, then

$$
\begin{aligned}
\pi_P(X^+(z_R))&=X_0(h_*w_P),\\
\mathrm{package}(z_R)&=\mathrm{package}(\mathrm{Sealed}),\\
\mathrm{OUT}_{\mathrm{Call}}(z_R)&=\text{AIF.18},\\
\mathrm{invocationOwner}(z_R)&=\mathrm{client},\qquad
\mathrm{phase}_C(z_R)=\mathrm{Ready}.
\end{aligned}
\tag{AIF.19}
$$

Here $h_*w_P$ uses the original projected rows and their actual supplied
bits. The latest mirror word is $I(h_*w_P)$; the end links still name
the captured occurrences; the stopped scan links name those same ends.
C's actual meters, dirty scratch, both copy destinations, all completed
and retired bank/descriptor versions, package and completion records
remain in $X^+(z_R)$. The result does not set them to their startup values
or to historical simulated values.

**Lemma 10.22 (complete-successor consistency).** The row recurrence in
Definition 10.21 gives one actual common successor satisfying all of
AIF.19. It preserves intermediate source rows and partial-copy states.

Proof. Lemma 10.8 gives a single consistent assignment to every touched
slot, including aliases, at each row. Original P effects project by
Theorem 10.10; mirror effects follow Lemma 10.12. End links and the sealed
package are not assigned after their respective creation/seal, so they
remain fixed. The scan and print invariants prove the other value
coordinates. The final token and PC assignments are exactly Definition
10.19's ACK/TOK/Ready sequence. All other fields are preserved at each
step, not discarded because their objects are dead for a later task.
Induction on the actual joint list therefore proves simultaneous
agreement of source, work, storage, output and live permission fields.
There is no choice of separate source and archive successors with only
matching marginal values. ∎

### 10.7. The quantified all-cut bridge and agreement of routes

**Theorem 10.23 (all attained lawful producer cuts, paid acquisition and use).**
For the changed finite apparatus of Definitions 10.1–10.7, for every
$H\ge1$, every actual canonically installed $u\in\mathcal T_H$, and
every lawful joint interleaving reaching any post-$F$ cut $z$ while C
is Armed, Capture is enabled there. It binds precisely $p(z)$, without
a Ready or completed-frame premise. Every continuation with C-progress
reaches its actual package seal. Every subsequent token-authorized Call
with C-progress has the actual output, ACK, token return and complete
successor of Theorems 10.20–10.22, for arbitrary later legal P activity,
including zero P activity.

Conversely every original $h\in\mathcal R_H$, including $a(u)$ itself,
is attained as $p(z)$ at such an Armed cut of an actual initialized run.
The assertion is pointwise over all finite attained cuts; it does not
require a preselected upper bound on their lengths or an a priori
bounded input history.

Proof. Startup reaches $F$ with C Armed and all required grants. Holding
C Armed does not change any producer enabledness. Theorem 10.10 realizes
any original finite continuation to $h$ by the same producer rows and
bits. No C row is needed during it. Capture's finite guard concerns only
its installed token, grants and actual links, which still hold at every
such cut. It does not inspect source validity, producer phase or an
unfinished row/copy. Lemma 10.13 and Theorem 10.15 prove the actual
prefix binding and acquisition on every subsequent legal interleaving.
Corollary 10.17 and Theorems 10.20–10.22 give the claimed seal, use and
successor. Thus both the universal actual-run statement and coverage of
every original cut hold, rather than just a witness family of favorable
post-IN cuts. ∎

**Proposition 10.24 (route agreement and exact scope of updates).** At a
Capture cut the following three routes have identical original values:
projecting that actual cut by $\pi_P$; decoding the actually acquired
package by the original Theorem 4.4; and parsing the delivered historical
image of an actual later Call. They give the same $h_*,X_0(h_*)$ and,
therefore, the same original raw source, work, row-prefix, copy, output
and historical-permission coordinates.

For a currently executed original action, the dynamic projection square
is AIF.15 and its actual-key update is Corollary 4.5: non-IN increments
$n$; admissible IN appends its supplied bit and increments $n$. These
are statements about the same actual producer successor. The sealed
captured package does not follow that update: it remains bound to
$h_*$. It is not a live-source actuator or an evolving current key.

Proof. Theorems 10.10, 10.13, 10.15 and 10.20 identify all three routes
with the same attained original prefix and state, including their actual
reference conventions. AIF.15 identifies the actual next original
state; Corollary 4.5 identifies its replay key and domain. A package seal
permits no later field update. Historical source-token bits are only
represented data in the replay bank and output, and never authorize a
physical producer operation. ∎

**Definition 10.25 (four meanings and the chronology boundary).** On this
one actual process, spatial storage means the current ordered scaffolds,
constructed cell gadgets and their actual incidence/mark fields, including
all retained material. Time means the actual ordered list of primitive
occurrences, their owners and receipts. Boundary means the current
terminal antichains of the primary ordered scaffolds together with the
separately specified live port/token/availability relations controlling
allowed actions. Memory of C means its acquired, retained material **with
its actual read/call rights and installed access routines**. These are
independent definitions; none is defined as an inverse of the others.
A primary leaf boundary alone does not encode a live read permission.

On an original D0 image, SSA's full structural support/frontier decoding
and the [Callable Storage Atlas](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md),
here called CSA, §§3–7's view interpretations may be applied under their
own original representation/retention premises. The historical image
here supplies that complete original raw image by an actual C procedure.
This gives agreement of those already defined **original-image**
interpretations along the three routes of Proposition 10.24. It does
not supply new spatial or boundary kernels on the enlarged apparatus.
C's callable memory arises only after its actual acquisition/package
seal and rights; the fact that P earlier retained a word was not C's
acquisition of it.

In particular $h_*$ is an actual reached **producer projection** of a
joint cut; $E^+$ is the complete joint chronology; the delivered image
represents the old original state $X_0(h_*)$; and current source actuation
is controlled by the current P tokens and phase in $X^+(z_R)$. They
are four different objects. AIF.18 does not encode the interleaving of
all C rows with P rows. Extra C command times and schedules have not
been mirrored as a joint replay input. A universal full joint-chronology
recovery theorem would require that additional acquired relation and
has not been proved here.

### 10.8. Resource evaluation on the same actual run

**Definition 10.26 (space with live and dead backing).** Let
$E_{\rm found}$ be the actual finite foundation-construction prefix,
$V_0$ its endpoint's vertex count, and $E_{\rm tail}(z)$ the subsequent
rows through $z$. The irreducible atoms and all foundation initialization
are included in the paid foundation cost. Let $\nu(e)$ count the new
vertices of a subsequent row $e$. With no reclamation,

$$
V(X^+(z))=V_0+\sum_{e\in E_{\rm tail}(z)}\nu(e).
\tag{AIF.20}
$$

Each vertex has 11 port fields, including empty fields. Model-bit cell
capacity and incidence storage are different coordinates: an ordinary
$G$ cell carries eight model bits and 47 vertices, while its represented
links may target previously constructed occurrences. Retained references
are charged as incidence fields, not counted as zero-sized payload
substitutes.

The foundation term and the disjoint tail sum include the original
source/code/seed acquisition, both meters,
the mirror, all spools, manifests, bank versions, Base/length scratch,
descriptors, senders, mailboxes, receivers and partially constructed or
retired records. A record dead for future Call is still in the sum.
There is no deletion or reuse of its vertices. C's finite control does
not bound this retained storage as cuts grow.

**Definition 10.27 (a fully evaluated structural tariff).** For an actual
row $e$, let $p(e)$ be its number of port probes, $a(e)$ its number of
slot assignments (including unchanged assigned values), and $\nu(e)$
its initialized new vertices. Fix the following concrete evaluation:
read guard/register fields in their listed finite field order; visit
cell gadgets by ordered depth-first traversal; follow each named route
in its displayed order; resolve role equality on the resulting bounded
pattern; perform consistent core, extra-link/mirror and receipt slot
assignments in that order. Count every traversed slot as a probe and
every initialized slot as an assignment. A route or field probed twice
is charged twice. Clearing and setting different link slots are separate
assignments. The resulting tariff is

$$
W(E^+)=\sum_{e\in E^+}\bigl(1+p(e)+a(e)+\nu(e)\bigr).
\tag{AIF.21}
$$

Here $E^+=E_{\rm found}E_{\rm tail}(z_R)$ is the **one** actual
foundation-to-return run, not separately optimized stages. Foundation is
its finite literal construction prefix, charged once by the same
probe/assignment/initialization rule; any initial irreducible-atom cost
is included in that prefix's fixed constructor charge. AIF.20 separates
its space term only to avoid counting those vertices twice. Native tick
and fee coordinates are separately
$N_P,N_C$ and $2N_P,2N_C$, with one receipt per row of its own controller.
AIF.21 is the additional concrete structural operation tariff; it does
not assert that an enlarged atomic row costs one old native fee.

Variable word work is evaluated by RCA §11's complete native expansions,
not by counting a word assignment as one row. In particular Base scans
actual existing arenas; descriptor ordinals count actual completed
descriptors; the manifest import includes both entry moves; each bank
update constructs its dry length, new version, delimiter, descriptor,
seal and parity change. Apply those expansions in their actual order
from the preceding complete successor. The same applies to startup
copies, spool import, the $n$ simulated rows, both delivery copies,
printing, ACK and return. This specifies a finite evaluated cost for
any supplied finite actual run without an unsupported closed polynomial.

**Lemma 10.28 (concrete footprint and finiteness of the bill).** One
right-spine cell append constructs exactly 48 vertices. In the 11-port
basis its initialization accounts for 528 slot assignments, and changing
the old trailing terminal's L and R adds two existing-slot assignments.
Thus the constructor alone accounts for 530 assignments, before any
old-symbol/head/control/receipt work. A mirror input row constructs one
mirror cell and one producer receipt cell: 96 new vertices. Capture
constructs its one C receipt cell and sets eight new link slots, in
addition to its finite register/receipt work. Every running row of this
construction has at most 100 new vertices. Its probe/assignment footprint
has a constant finite bound depending on its installed finite scaffold
and controller, independent of $r,n$, input length or P's later growth.
Capture, the two prefix scans and the displayed Finish-to-spool-seals
body use exactly

$$
N_{\rm acquire\ body}=6r+5n+16
\tag{AIF.22}
$$

C rows. This excludes startup, spool import, package construction, Call
and delivery, and excludes intervening P rows. All foundation-to-return
costs in AIF.20–21 are finite under the progress hypotheses of Theorem
10.23; no bound on arbitrary scheduling delays is claimed.

Proof. SSA's cell has 47 vertices, and appending adds one new trailing
terminal, giving 48. Initialization writes 11 slots at each of these
vertices, giving $11\cdot48=528$; the existing expanded terminal has
exactly its two child assignments, giving 530. Old link retargeting and
cell-bit changes are separate. A producer IN has no core tape write,
so its new mirror cell and its ordinary receipt are the two constructors
just counted. Capture sets four reciprocal pairs and has only its own
receipt constructor. An ordinary EX row has at most an ordinary cell
and its own receipt; a bootstrap bit constructor may instead add the
four fresh bit-gadget vertices and its receipt. The row schemata do not
combine that bootstrap case with another ordinary EX; allowing both
48-cell constructors and four bit vertices gives the stated safe bound
100. Fixed-scaffold construction is its explicitly charged finite
foundation prefix, not one running row with unbounded construction.

Lemma 10.8 bounds the inspected cell roles and all static route lengths.
Finite register and code sizes therefore bound their probes and
assignments. Scan length increases the **number** of these rows, not
a row's footprint. Startup and each compiler helper terminate on finite
actual tapes; Theorem 10.15 supplies finite captured loops; Theorem
10.20 supplies the finite simulation/publication/return. C-progress
allows only finitely many joint rows before each of these finitely many
C rows, so the actual return prefix is finite even with arbitrary
producer work between them. Summing the evaluated finite contributions
proves the cost claims and counts every retained vertex once at creation.
For AIF.22, InputPrime and its last equality test cost two rows; each
of its $r$ iterations costs Test, Read, EX, WR, MR and Next, or six.
MeterPrime and its last equality test cost two; each of its $n$
iterations costs Test, EX, WR, MR and Next, or five. Capture costs one.
Finish has three three-row Appends and two one-row Seals, or eleven.
Their disjoint sum is $1+(6r+2)+(5n+2)+11=6r+5n+16$, including both
zero-prefix branches. Those rows' structural charges are still the
actual AIF.21 evaluations; AIF.22 is not their old-native-fee price.
These calculations prove neither an optimum nor a bound uniform over
all cut lengths. ∎

### 10.9. The acquired relation, suppliers and remaining limits

**Proposition 10.29 (strict busy-cut capability and its price).** The
bridge of Theorem 10.23 is not merely the post-IN case or a delayed
Ready acquisition. For example take an actual canonical TagRead frame
with payload length at least two and Capture immediately after its
first payload IN, before its matching WR. Then let P take zero further
steps. The consumer still seals, actually Calls, prints the exact
historical IN-before-WR image and returns its invocation token under
C-progress. The theorem also applies at all other lawful cuts, including
raw invalid source-overwrite packets and either unsealed copy stage.

Proof. The example is an actual prefix in $\mathcal R_H$ by Definitions
2.2–2.3; the first bit is in $Q$ and already in $J$. Capture has no
producer-phase guard. Theorems 10.15–10.23 require no later P work.
For the other listed cuts, Theorem 10.10 retains their raw phase and
state; the same phase-independent Capture and endpoint-scan proof
applies. ∎

The additional information relation is a sealed consumed-bit mirror joined
atomically to the original receipt frontier, with persistent occurrence
links, an actual copied seed binding and live C access rights. Each
component has a distinct role. Data without a cut join does not identify
which meter/input pair was attained together. A cut ordinal without the
consumed input cannot separate §5's equal-clock input fibers. A symbolic
key without the actual seed/input copy and rights is not callable memory.
These observations justify the roles of the resources in this mechanism;
they do not prove that a duplicate mirror or these particular four links
are universally minimal. Indexing original request cells with a separately
captured pending latch would be a different mechanism with its own
permissions, invariance and same-cut proof obligations.

The old AIF theorem supplies information sufficiency after the key is
given; it does not supply the busy-cut capture and actual C acquisition.
RCA's compiler, Step and Publish supply the reused finite computation
and return machinery. RCA §§14–15's installed service instead obtains
its covers after finite lawful completion/installation and uses its own
D1 input/clock convention. It cannot finish that acquisition on the
zero-P continuation of Proposition 10.29. SSA supplies the original
bounded structural encodings and append/alias templates; its switch
lemma's empty ports do not authorize the new links. CSA supplies scoped
original-image interpretations and installed serial callable routines,
not this independent C entry at every producer phase. The new theorem's
delta is the proved **actual all-cut acquisition-to-use bridge in this
explicitly stronger paid basis**, not those interpreters, kernels or
renamed interfaces.

The same distinction excludes replacement by a historical owner protocol
requiring a future complete frame and SourceReady service interval
([Owner-Control Historical Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OWNER_CONTROL_HISTORICAL_ACQUISITION.md),
§§7–8), by the completed-predecessor cover of
[General Cut Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_CUT_ACQUISITION.md),
§§1–2, or by a local open-row completion atom without an interior
consumer acquisition callback
([Open Row Completion and Authority](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_OPEN_ROW_COMPLETION_AND_AUTHORITY.md),
§§5,8). Mixed successful-history incidence covers do not establish these
new seed/mirror/frontier rights either
([General Target Incidence Cycle](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GENERAL_TARGET_INCIDENCE_CYCLE.md),
§§18–20). Concurrent atomic Read/rho snapshot contracts, including those
in [Concurrent Native Cut Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md),
are different interfaces; no impossibility claim about them follows.

At the declaration level, `NativeSerialMachine.replay_deterministic` and
its reached-prefix applications use a supplied actual reply history;
`NativeFullSourceProducer.native_source_producer` and its private traversal
supply the original stationary source acquisition. The owning Scribes
make those scopes explicit. `TypedFiniteViewKernel.typed_finite_view_kernel`
supplies typed partial experiment semantics, not the new read grant.
`NativeSerialEffective.original_code_service_simulation` assumes its
actual original-code realization correspondence; it is not a proof of
this bounded capture row. `NativeAcquiredPrefixCylinder` supplies its
transaction-specific acquired-prefix/resumption facts, not D0 mirror
installation or alias preservation. These actual statements, including
their private proof auxiliaries, are reused at their stated scopes;
the proof of Lemmas 10.8 and 10.12–10.17 is an additional concrete
construction.

Pinned mathlib `Computability/StateTransition.lean` at revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, `StateTransition.Respects`,
`tr_reaches` and `tr_eval`, provides transition/evaluation transport
under a supplied state relation and matching fragments. It does not
supply the acquisition relation or the cost/permission realization here.
No external Lean package or private axiom is used to assert those facts.
This prose construction claims no Lean certification.

Herlihy and Wing, *Linearizability: A Correctness Condition for Concurrent
Objects*, ACM TOPLAS 12(3), pp. 464–468
([author copy](https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf)),
supplies the mature distinction between process histories and a legal
linearization. The atomic Capture has a unique actual cut by its
explicit row semantics; linearizability alone would not give its
C-progress acquisition proof or complete joint chronology.
Driscoll, Sarnak, Sleator and Tarjan, *Making Data Structures Persistent*,
JCSS 38(1), pp. 86–88
([author copy](https://www.cs.cmu.edu/~sleator/papers/another-persistence.pdf)),
supplies the fixed-field/access-pointer formulation of retaining versions.
Its update/time/null conventions are not substituted for this machine's
11-slot initialization, retained-cell accounting or live ownership.
These are `literature-attested` methods at those scopes. The concrete
bridge proved here is `repo-derived`; no worldwide novelty or exhaustive
absence of a stronger supplier is inferred.

The hypothesis changes are essential and visible: two controllers and
two meters, extra tapes and reciprocal ports, atomic mirrored IN,
atomic two-frontier binding, cursor/equality reads, an acquisition-sender
setup grant, and the installed C seed/code/channel/token foundation. Each fixed public
capacity/description has a finite apparatus uniform in its source value;
no uniform finite storage bound over all capacities or histories is claimed.
The result leaves the original fixed-apparatus named-cut problem open
when those grants are absent. It does not solve the original fixed
$G_{gc}$ or parked-consumer tasks under unchanged initialization. It
does not equate the current source with an invalid packet's old semantic
tree, reconstruct current live source authority from historical bits,
or identify $E^+$ from AIF.18. It proves no enlarged four-kernel theorem,
no universal alpha/beta reduction, no physical or hostile-memory claim,
no reclamation theorem and no cost optimum. The wider four-expression
programme and its unrestricted recovery obligations remain open.

## 追加锚（本行以下为增补区）
