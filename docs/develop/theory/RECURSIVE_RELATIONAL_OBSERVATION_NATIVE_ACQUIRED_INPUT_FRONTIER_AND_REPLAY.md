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

## 11. Exact joint endpoint fibres and the chronological distinction

### 11.1. One initialized process and two different continuation questions

**Convention 11.1 (fixed apparatus and the whole reached domain).** Fix
$H\ge1$, $\xi$, the literal $D_0$ description, its chosen allocation and
descriptor routines, the scaffold, and all finite startup and C routines
of Definitions 10.1–10.7. These are the published apparatus $A^+$; no row,
port, token, input channel or naming convention is added here. For each
canonically installed $u\in\mathcal T_H$, write $\sigma_u$ for its complete
common startup through $F$, and put

$$
n_F(u)=n(a(u)),\qquad c_F(u)=N_C(F).
\tag{AIF.23}
$$

The first number is the absolute original P ordinal; the second is the
absolute C receipt count at $F$. Both include their actual paid startup
work. They are finite functions of the acquired seed and fixed apparatus,
not source-independent constants or free runtime numeral registers.

Let $\Omega^+$ contain every finite lawful executed joint prefix at or
after $F$, over every such $u$, every admissible producer input choice,
and every lawful owner schedule and Capture/Call choice. Include $F$
itself, all Armed cuts, every interior acquisition, import, bank update,
descriptor, package, simulation, source-overwrite, partial-copy, printing,
ACK, invocation-TOK and Ready-CTL cut, and any finite number of later
Calls. A cut is between complete atomic rows, as in Definition 10.3.
No final-seal, valid-current-source-packet, completed-request or consumer
Ready restriction is imposed.

An unexecuted trial is not an additional row in such a prefix. Waiting
without a row adds neither a receipt nor an event. The external input
actor is exactly Definition 2.2's common ready actor. There is no extra
retained caller transcript, deadline, acknowledgement choice or policy
state in this apparatus. Schedules and future supplied bits remain
choices, not controller inputs supplied in advance. A physical
noncanonical IN has its actual one-row successor, but its later
continuation lies outside $\Omega^+$, exactly as in Definitions 2.2 and
10.4. Startup permission fixes $\sigma_u$: it admits no alternative P/C
interleaving before $F$. Its construction and seed-copy work are retained.

**Definition 11.2 (raw state, space, chronology, boundary and acquired memory).**
Write $X^+(z)$ for the complete raw state given by Definition 10.21's
row recurrence, at any $z\in\Omega^+$. It contains all 129 tape
components, both meters and controllers, all eleven slots of every
constructed vertex, every mark, latch, PC, seal, origin and descriptor,
all old versions and partial objects, the four anchors, grants, live
tokens and availability fields. An invalid mid-write source packet is
represented by its actual bits and phase. The chronological list used
to define the recurrence is not an additional field of its endpoint.
In particular there is no globally ordered output archive or allocation
counter unless the specified rows actually construct it; these rows do
not construct one across the owners.

Keep the four meanings of Definition 10.25 independently:

- $S_{\rm now}(z)$ is the actual current rooted ordered storage with its
  cell/register gadgets and every labelled incidence, including access,
  capture and scan links. It retains the fixed origins and actual
  occurrence identities, not an arbitrary graph isomorphism class.
- $T_{\rm exact}(z)$ is the actual total chronology $E^+(z)$ from the
  common foundation: all primitive occurrences, owners, inputs,
  commands, receipts and functional outcomes in their executed order.
  When complete intermediate raw states or structural audit data are
  requested, retain those as additional historical observations.
- $B_{\rm now}(z)$ is the current primary terminal-antichain observation
  together with the live port/token/availability relations specified in
  Definition 10.25. It is not defined by a proposed decoder.
- $M_C(z)$ is C's actually acquired retained backing, partial material,
  grants and bound references, with its current read/call rights and
  installed access routines. A partial destination is retained with its
  actual unavailability. This does not give C all P data or a global scan.

SSA §§3–5's cell decoding applies componentwise to $S_{\rm now}$:
the eight ordered bit gadgets decode each cell, finite register gadgets
decode control and rights, and the eleven labelled slots give the
remaining links. Conversely those raw fields construct precisely that
storage description. Thus $S_{\rm now}$ and $X^+$ are lossless
representations of the same current material, with their actual names.
This elementary representation correspondence claims no historical
chronology inverse. A released OUT word and a stored word are distinct;
owner-local output records, where constructed, remain in the raw state.

**Definition 11.3 (the current native continuation task).** Define
$Q_{\rm now}$ before introducing its sufficient coordinates. Its named
primitive trials are AdvanceP, SupplyP($b$), Capture, Call, and AdvanceC
of the next prescribed internal C row. AdvanceC does not select an
arbitrary cursor operation or issue a command in place of internal work.
Capture and Call have precisely Definition 10.11's phase/token guards.
The installed original finite semantic, row-audit and delivery protocols
of Definition 2.6 are experiments made from their actual primitive rows.
There is no new selector, source request or arbitrary C helper entry.

A response retains actual enabledness/authority, native functional label,
released outputs, the complete raw joint successor after each executed
row, and that future row's evaluated structural tariff and owner tick/fee
charge. The complete successor is mathematical audit data, as in
Definition 2.6; it is not an acquired public value on which the controller
may secretly branch. Empty responses retain running/terminal type.
Finite adaptive experiments branch only on their acquired public phase,
availability and responses. All finite such experiment trees are allowed;
no predetermined interleaving or fixed future producer word is assumed.

The response and domain distinctions are exact:

| Trial situation | Task value and physical effect |
| --- | --- |
| Enabled prescribed row, including a source reject, `absent` or paid `no-row` | Executed label, outputs, charge and complete $X^+$ successor, with the actual receipt |
| Disabled or unauthorized trial, early/busy Call, repeated Capture, unavailable read | Unexecuted `none`; no receipt and no raw state change |
| Physically enabled SupplyP($b$) with $b\notin\operatorname{Adm}$ | Undefined on the lawful experiment domain; nevertheless its actual latch/control, mirror and receipt successor physically executes |

An experiment is defined exactly when none of its executed branches
attempts the last kind of Supply. Write $z\equiv_{\rm now}w$ for equality
of these partial finite-experiment maps, including their domains.
$Q_{\rm now}$ starts at the compared cut. It does not request the already
elapsed $E^+$, past complete joint successors, or accumulated past
$W(E^+)$. Those remain legitimate, different tasks. Nor does it identify
two differently ordered future experiment words: responses to a fixed
word keep that word's chronological output and successor sequence.

### 11.2. Material coordinates and actual occurrence identity

**Definition 11.4 (the joint material coordinates).** For $z\in\Omega^+$,
let $n(z)=n(p(z))$ be the absolute P receipt count, let
$I(z)=I(p(z))$ be the full consumed source-frame input word in $J$, and let

$$
m(z)=N_C(z)-c_F(u).
\tag{AIF.24}
$$

Set $\kappa(z)=\bot$ before Capture. After Capture, set $\kappa(z)$
equal to the number of P receipt cells strictly before the cell root
named by the persistent meter fixed-end anchor. Put

$$
\mathcal K(z)=
 \bigl(\operatorname{code}(u),I(z),n(z),\kappa(z),m(z)\bigr).
\tag{AIF.25}
$$

This is an auxiliary mathematical extraction, not a newly installed
natural view or C input. On this domain $m=0$ precisely while Armed,
and then $\kappa=\bot$. Otherwise $m\ge1$ and
$n_F(u)\le\kappa\le n$. Lemma 10.13 identifies $\kappa$ with the
absolute P count immediately before the unique Capture. Counting cells
strictly before its linked root continues to give that number even
when the root's symbol is no longer R. It does not require an immutable
receipt byte. The captured input length need not be supplied separately:
it is the consumed-input length in the original prefix through
$\kappa$.

**Lemma 11.5 (extraction includes provenance and unfinished material).**
There is a finite mathematical extraction $\mathcal E$ on the actual
raw-state image with $\mathcal E(X^+(z))=\mathcal K(z)$ for every
$z\in\Omega^+$. The extraction uses no current-tree decoder at an invalid
source packet, no future input and no new live read grant.

Proof. The retained sealed startup manifest gives the actually acquired
seed and its source binding. Equivalently, SSA Proposition 2.1 extracts
that seed from the original retained acquisition rows under $\pi_P$.
It is not reconstructed from a currently overwritten private packet.
The fixed boot and seed-copy graphs determine $n_F(u),c_F(u)$ by finite
evaluation. Lemma 10.12 gives $I$ as precisely $J$'s sealed bit prefix,
including an original input bit still between its IN and WR. Count P's
meter receipts to obtain $n$, and C's receipts to obtain $N_C$ and hence
$m$. Detect Capture from its consumed token and fixed-end links; before
it the anchors are empty. Afterwards enumerate the P meter from its L
up to, but excluding, the root at that end link. Persistent spine/root
identity and Lemma 10.13 make this count exactly $\kappa$. None of these
finite inspections reads a receipt payload to infer its past position.
Dirty banks, partial descriptors and unavailable destinations stay in
the input raw state; the extraction neither completes nor discards them.
These operations prove the assertion on authentic reached material. ∎

**Lemma 11.6 (local construction identities survive an exchange).**
In $A^+$ the name of a constructed occurrence is fixed by its actual
controller/arena construction occurrence and fixed constructor role.
Its descriptor fields and any original reference to it are unaffected
by changing only the interleaving of two fixed post-Capture owner words.
There is no additional global allocation-order coordinate in $X^+$.

Proof. Definition 10.9 preserves P-port construction order and its old
Base and descriptor streams. C has different ports and its own streams;
its receipt count is not an input to an original Base/creation scan.
Definition 10.21 uses these controller/arena construction occurrences
also for fresh C vertices. Within one constructor the template roles
are fixed. An expanded trailing terminal retains its identity; it is
not replaced by a vertex named by the new global row position. Thus
one can identify a row by its owner and absolute owner-local receipt
ordinal, and its fresh vertices by their actual arena/constructor roles,
without renaming any stored field. The local descriptor ordinal counts
completed descriptors on that owner's actual stream, not all joint rows.

During startup these conventions give one fixed $\sigma_u$. At Capture
the roots are existing P-meter/J occurrences and the anchors are fixed
roles. Corollary 10.17 binds the package to that unique flight through
literal anchor role/port tags and their actual persistent links, not a
supplied joint-time numeral. Later simulated histories use original D0
references; their target is that captured original prefix. All other
C creation/binding records come from its owned routines. These exhaust
the sources of references in the declared apparatus. Interleaving
therefore cannot introduce an extra name into those fields. This is a
correspondence of the specified actual occurrences, not permission to
replace the allocation convention by a convenient isomorphic one. ∎

### 11.3. The guarded exchange on every post-Capture phase

**Lemma 11.7 (complete native P/C diamond).** At every reached
post-Capture cut $x$, take a lawful next P row $e$ and an enabled next C
row $f$, including a token-authorized Call entry. Then each remains
enabled and lawful after the other, with the same native functional
operands, read/test results, owner-local receipt and released output.
The complete two-row endpoints satisfy

$$
\delta_C(\delta_P(X^+(x),e),f)
 =\delta_P(\delta_C(X^+(x),f),e).
\tag{AIF.26}
$$

This includes every interior expansion row and the final ACK, invocation
TOK and Ready CTL. It excludes Capture itself. It asserts equality of
endpoints, not of the two ordered response lists or their intermediate
complete successors. In particular it asserts no equality of past
structural probe traces or accumulated tariffs.

Proof. First partition the actual fields. A P core row reads/writes only
its original ports, registers and rights. Its common receipt is on P's
meter; its public IN additionally appends to $J$. It neither reads C's
control/work nor tests C's tokens. C's core work, receipt, ordinary head
marks, source/destination cells, compiler banks and tokens are on its
ports/registers/meter. Only the two forward scans access P's meter or
$J$ after Capture. The complete remaining cases are these:

| C row family | Information it can use outside C-owned material | Assignments outside C-owned material |
| --- | --- | --- |
| InputPrime, InputNext | Existing next-cell spine route, strictly before the captured end when moving from a data cell | Only that scan anchor's $O_3$ and the old/new targets' $H_3$ |
| InputTest | Equality of the persistent scan/end target occurrences, before a symbol read | None |
| InputRead | Captured strict-prefix mirror bit | None |
| MeterPrime, MeterNext | Existing next-cell spine route up to the captured end | Only its scan $O_3/H_3$ pair |
| MeterTest | Equality of persistent target occurrences; no receipt-byte read | None |
| InputAppend, MeterAppend and their EX/WR/MR subrows | None; the matched data latch or literal 1 is already C data | None |
| Finish, spool seals/import and every partial package/descriptor row | None; manifest and spools are C-owned acquired data | None |
| Call entry, literal simulation and every bank/scratch update | None; represented P bits and permissions are C data | None |
| Archive, Allocate/Base, both copies, print OUT, ACK, completion/return, TOK and Ready CTL | None; actual arenas, channel roles and live invocation/read tokens are C-owned | None |

The Capture end links are never reassigned in this table. Later imports
or Calls may retain the fixed anchor role binding; they do not sample a
new P value or follow a live append head. The consumer has no further
external data input. The displayed families include subroutine entry,
terminal tests and purpose-changing CTLs; the RCA word expansions do
not insert a hidden access to P. Their local port renaming is $i\mapsto65+i$.

Check the shared reads before reasoning about disjoint writes. At a
non-end InputTest, the cursor is strictly within the captured prefix by
Theorem 10.15's invariant. InputRead therefore reads the same sealed bit
in either order. Any later P mirror append is at the captured end or
to its right; it cannot change that bit or its existing next-cell route.
At the end, InputTest compares occurrence identity first and reads no
symbol. Thus even a P IN turning that very former-R root into a bit
cannot change its branch. InputPrime from L, including the empty-input
case, follows the same preexisting edge to the same root. InputNext
never moves from the fixed endpoint. On the meter the argument is
topological: each used next route already existed at Capture, and C
never reads changing receipt bytes or old meter marks. A P receipt
may change the fixed endpoint's symbol, but not its root or the equality
test. These statements hold at every scan subphase, not just loop ends.

Now check assignments and aliases. A P bit rewrite uses the old four
bit-gadget slots of Definition 10.7 and preserves $O_2,H_2,O_3,H_3$.
P ordinary heads and meter append/read heads use the old reciprocal
pairs. C cursor movement changes only its own $O_3/H_3$ slots; it does
not change symbol or old mark tracks. If the scan target, fixed end and
old P read/append head coincide, these are still different slots. In
particular clearing an old scan $H_3$ cannot clear a P $H_0/H_1$ or the
fixed-end $H_2$. A P append preserves a scan slot left on its old R.
The seal on a mirror bit is a write restriction, not a claim that every
slot of that cell is frozen.

For the spine, a P append changes its trailing terminal's child slots
and attaches new vertices. C's guarded routes stop at the already
existing captured cell root; none follows the newly extended suffix.
The append therefore changes no traversed prefix edge. C changes none
of P's read/append marks, guards, symbols, latches or current-frame
syntax. In particular a chosen admissible Supply remains admissible.
The compiler, copy and return rows have no shared data assignments at
all. Each owner's receipt construction is on its own meter. Fresh
vertices on the disjoint arenas have exactly the same identities by
Lemma 11.6; allocating one owner's cell does not consume a name needed
by the other. Unnamed slots, even on aliased roots, are preserved.

It follows that both rows see the same functional data and authority
in either order, take the same native branches and make the same
consistent slot assignments. Combining those assignments gives the
same eleven-slot raw state, including every dirty/retired object and
live token. This proves both enabledness preservation and AIF.26.
It also gives reverse reordering legality: in an actual adjacent pair
$ef$, $f$ was already enabled before $e$, since $e$ changed none of its
guards; likewise for $fe$. An early/busy Call or unauthorized operation
is preserved as an unexecuted trial, not inserted as a successful event.
Capture is absent from the table because it reads current append ends;
its order-sensitive case is proved in Proposition 11.14. ∎

### 11.4. Normal evaluation and the exact complete-state fibre

**Lemma 11.8 (determined local words at every partial cut).** A realized
$\mathcal K=(\operatorname{code}(u),I,n,\kappa,m)$ determines the entire
original P word through $n$. If $m>0$, it also determines the exact
post-$F$ C word of length $m$, starting with Capture, through whatever
partial acquisition or Call row it ends at. No fixed whole producer
word is an additional hypothesis.

Proof. Apply Theorem 4.4 to $(\operatorname{code}(u),I,n)$ and the
projection of Theorem 10.10. This recovers all original P rows, their
actual input bits, outcomes, references and source/work states, not
just completed semantic calls. Take its prefix through $\kappa$ and
extract its already consumed $I_*$. This step uses no future input:
replay stops at that count, even when the reservoir $I$ contains later
bits. The same fixed startup evaluation gives the actual $\sigma_u$.

With P held at this captured prefix, execute Capture and then C alone.
The scan invariant and Lemma 11.7 give exactly the same C observations
as any continued P schedule. After those scans, C reads only its owned
manifest/spools and deterministically constructed data. Its next
internal row is prescribed. At Sealed or Ready, the only next
*executed* C entry is the payload-free Call; at Armed it was Capture.
An optional delay or unsuccessful command trial contributes no C row.
The finite native word compiler, literal simulator and return graphs
fix all subsequent subrows. Hence the first $m$ executed C rows are
fixed, including every latch, half-written bank, descriptor and token
subphase, and any number of complete or incomplete Calls.

Every needed finite C prefix exists with P paused: acquisition and each
chosen Call have finite own work by Theorems 10.15–10.20, and Call can
be chosen again after its actual token return. That fact proves
existence of finite local words; it supplies no fairness or inevitable
external Call. Comparing with an actual interleaving uses Lemma 11.7,
or equivalently the scan invariant followed by deterministic C-only
work, so no local C row depends on a future P row. ∎

**Theorem 11.9 (exact raw-state fibres on $\Omega^+$).** For all
$z,w\in\Omega^+$, including different valid installed seeds,

$$
X^+(z)=X^+(w)
 \quad\Longleftrightarrow\quad
\mathcal K(z)=\mathcal K(w).
\tag{AIF.27}
$$

For a realized captured key set $p=n-\kappa$ and $q=m-1$.
Its complete raw-state fibre consists precisely of the histories

$$
\sigma_u\ ;\ P_{n_F+1}\cdots P_\kappa\ ;\ \mathrm{Capture}\ ;\
\operatorname{Shuffle}
 \bigl(P_{\kappa+1}\cdots P_n,\ C_2\cdots C_m\bigr),
\tag{AIF.28}
$$

where $P_i$ is its fixed absolute original P row and $C_j$ its fixed
post-$F$ C row. Empty chains are allowed. Every indicated shuffle is a
lawful execution with literally the same complete raw endpoint. Every
history in this fibre is connected to every other by adjacent exchanges
of one P row with one non-Capture C row strictly after Capture. An Armed
key instead has just $\sigma_u;P_{n_F+1}\cdots P_n$.

Proof. Equal raw states have equal extracted keys by Lemma 11.5,
including the seed and captured root rank. Conversely fix a realized
key. If Armed, no post-$F$ C row has executed, so Theorem 4.4 and fixed
startup give the unique joint word. In the captured case every actual
word has the fixed startup, exactly P rows through $\kappa$ before its
first C row Capture, and the two remaining owner projections of
Lemma 11.8. There is no earlier non-Capture C row while Armed.

Normalize any such word by moving each remaining C row left past
post-Capture P rows. Every exchanged pair is actually reorderable by
Lemma 11.7, preserves its owner-local functional result and name, and
has the same complete two-row successor. A shared suffix therefore
continues from exactly the same raw state. A finite inversion count
terminates this reordering at

$$
\sigma_u\ ;\ P_{n_F+1}\cdots P_\kappa\ ;\ \mathrm{Capture}\ ;\
 C_2\cdots C_m\ ;\ P_{\kappa+1}\cdots P_n.
\tag{AIF.29}
$$

Lemma 11.8 fixes every row in this representative and its endpoint.
In particular its producer suffix is lawful after the C work, since
that work changed no original P field or input prefix. Thus all histories
with the key have the same complete $X^+$, proving AIF.27.

For exactness rather than only inclusion, use the finite occurrence
poset with the two displayed owner chains and
$P_i<\mathrm{Capture}$ for $n_F<i\le\kappa$,
$\mathrm{Capture}<P_i$ for $\kappa<i\le n$, with startup before them.
Its linear extensions are exactly AIF.28. The already proved native
guards and diamond realize every exchange of its incomparable P/C
occurrences. Generic finite-poset swap connectivity, as in Context
Theorem 13.6 and `EnabledPathSwapConnectivity.result`, now applies:
no absent event's owner predecessor can be skipped, and both minimal
remaining owner events are enabled at each lower cut. Alternatively
induct over a proposed shuffle, choosing its next owner row; the
shared-read invariant and independent guards give that same row and
outcome. Both arguments realize every listed extension and exclude
any additional one. The fixed words, actual occurrence identities and
Capture rank preclude any further history in the raw-state fibre. ∎

**Corollary 11.10 (finite mathematical reconstruction of the endpoint).**
On the actual key image there is a finite decoder $\mathcal D$ given by
AIF.29, and on the actual raw-state image

$$
\mathcal E\mathcal D=\mathrm{id},\qquad
\mathcal D\mathcal E=\mathrm{id}.
\tag{AIF.30}
$$

Proof. Decode the producer word and startup by Lemma 11.8, evaluate the
finite normal representative, and retain its entire raw successor.
All routines used are literal finite-prefix evaluations. Theorem 11.9
identifies this with the actual endpoint of every representative.
Re-extraction gives its prescribed key; reconstruction after extracting
any actual endpoint returns that endpoint. No authentic-history
recognizer on arbitrary fabricated keys is required or asserted. ∎

### 11.5. Both continuation-kernel directions and actual updates

**Theorem 11.11 (the exact current-continuation kernel).** On the entire
$\Omega^+$ domain,

$$
\begin{aligned}
z\equiv_{\rm now}w
&\quad\Longleftrightarrow\quad \mathcal K(z)=\mathcal K(w)\\
&\quad\Longleftrightarrow\quad X^+(z)=X^+(w)\\
&\quad\Longleftrightarrow\quad S_{\rm now}(z)=S_{\rm now}(w).
\end{aligned}
\tag{AIF.31}
$$

The at-most-one-primitive response maps already have this kernel.
There is no public-output-only rigidity assertion in this theorem.

Proof. Equal keys give equal complete raw states by Theorem 11.9.
From equal raw states, the same named trial has the same physical
and task-domain status, guard, native output/label, tariff and complete
successor. In the enabled noncanonical Supply case, both lawful maps
are undefined there; both physical raw edges still have their actual
equal successors. In a disabled case both trials are unexecuted `none`.
In an executed lawful case the successor remains in $\Omega^+$ by
Lemma 2.7, Theorem 10.10 and the installed C phase rules. Induction
on finite experiment trees proves equality of the partial maps and
all their response coordinates. This proves sufficiency, including
future acquisition completion, repeated Calls, printing, ACK and
actual invocation-token return.

For the reverse direction choose one lawful next P action at $z$.
Such an action exists at every cut: Lemma 2.7 supplies the prescribed
non-IN step or at least one admissible bit, and Definition 10.4 makes
its enabledness independent of C. The dispatcher continues at a final
idle boundary; it is not a globally stopped producer. If AdvanceP
executes, equality of the one-action response maps requires the same
successful action at $w$, with equal complete raw successors.
Extracting AIF.25 from these successors gives

$$
(\operatorname{code}(u_z),I_z,n_z+1,\kappa_z,m_z)
 =(\operatorname{code}(u_w),I_w,n_w+1,\kappa_w,m_w).
\tag{AIF.32}
$$

Cancel the increment to recover equal predecessor keys. If the chosen
action is SupplyP($b$), the same response at $w$ cannot be disabled or
undefined. It must be an admissible executed Supply, with equal raw
successor. Its extracted equality is AIF.32 with $I_zb,I_wb$ in place
of $I_z,I_w$. Right cancellation of the known last bit and cancellation
of the count again give equal predecessor keys. Capture status and
C count are unchanged by either P action. This proves necessity
without a free empty-experiment state read. The representation
correspondence in Definition 11.2 proves the last equivalence in both
directions. It does not give the missing independent kernels for
$B_{\rm now}$ or $M_C$. ∎

**Proposition 11.12 (whole-edge transport, with raw exits kept distinct).**
On the actual key image the updates for each executed lawful row are

$$
\begin{aligned}
\text{P non-IN}:\quad &(u,I,n,\kappa,m)\longmapsto(u,I,n+1,\kappa,m),\\
\text{P IN}(b):\quad &(u,I,n,\kappa,m)\longmapsto(u,Ib,n+1,\kappa,m),\\
\text{Capture}:\quad &(u,I,n,\bot,0)\longmapsto(u,I,n,n,1),\\
\text{other C row}:\quad &(u,I,n,\kappa,m)\longmapsto(u,I,n,\kappa,m+1).
\end{aligned}
\tag{AIF.33}
$$

Here $u$ abbreviates its code. An update is available only at that
named action's actual guard; the numerical formula alone does not
authorize a row. Disabled trials have the original `none` response
and identity state effect. Recovering the state, taking the action and
extracting its key equals the displayed update. Decoding the updated
key gives the complete actual successor, with the same label, outputs,
rights and future-row charge. These statements include every partial
C phase and repeated Call.

Proof. Every P row appends exactly one P receipt. Only a public IN
adds one mirrored consumed bit. Neither changes the fixed-end rank
or C's count. Capture samples the current P end, consumes its token
and appends precisely its first post-$F$ C receipt. Every other C row
preserves P's original state, mirror and fixed ends, and adds one C
receipt. These are exactly AIF.33. Closure for the stated lawful
P cases is Lemma 2.7; closure for C is its installed row semantics.
Theorems 11.9–11.11 identify all guards, outputs, costs and complete
successors from the recovered raw state, proving the update square.

At an enabled Supply with a nonadmissible bit, reconstructing the
current raw state still gives its one actual physical IN successor,
including its extra mirror cell and P receipt. No $\mathcal D$-image
claim for that successor's later malformed continuation follows:
AIF.33 is a same-image theorem only for admissible bits. It does not
turn an executed exit into `none` or erase its physical raw successor.
No historical permission in a simulated image becomes current P
actuation authority by any of these maps. ∎

### 11.6. An independently specified partial time and its recovery routes

**Definition 11.13 (owner-event time with the captured read cut).** Define
$T_{\rm cut}(z)$ directly from actual event occurrences. Retain the fixed
startup word $\sigma_u$, followed by the two post-$F$ owner chains.
A row is located by its owner and owner-local receipt ordinal and
carries its opcode, actual input bit or command, native functional
read/test/output result and its owner-local construction/reference
roles. Repeated equal commands are different occurrences. For $m>0$,
retain additionally which P frontier Capture sampled: order every P
row through $\kappa$ before Capture and every later P row after it.
Taking transitive closure gives a finite occurrence poset. Equivalently
retain its two bracketing inequalities, omitting a nonexistent endpoint.
For $m=0$, only the P chain follows startup.

This temporal observation has an independent operational meaning:
it keeps each owner's executed succession and the actual shared
read-version cut. It forgets other post-Capture cross-owner placement.
It does not retain past whole joint successors or structural
probe/assignment traces as row labels. Such traces need not commute.
The upper Capture bracket is an exact read/append exclusion, not an
assertion that P waits for a C message. Thus $T_{\rm cut}$ is a different
partial-time task, not a renamed $T_{\rm exact}$ or a claim that its
edges are exactly Lamport's message-based happened-before relation.

**Proposition 11.14 (the captured frontier is indispensable).** At every
actual Armed cut $x$ and every lawful next P row $e$, both
$x;\mathrm{Capture};e$ and $x;e;\mathrm{Capture}$ are lawful. Their
$\operatorname{code}(u),I,n,m$ coordinates at the displayed endpoints
are equal, but their captured ranks are respectively $n(x)$ and
$n(x)+1$. A future allowed C acquisition/Call experiment separates
them by released output alone.

Proof. Capture has no producer-phase guard, and P preserves its token
and grants while Armed. Conversely Capture changes no original P
field or admissible-input condition. The two orders therefore execute.
Each P row appends one receipt, including a non-IN row which consumes
no new bit. Capture hence attaches its meter end to two different
permanent roots, giving the stated ranks. An input frontier alone
would miss this distinction for any such non-IN row.

Park P after each displayed prefix. Run prescribed C work until its
package seals, issue Call with its actual invocation token, and run
through printing, ACK and token return. Theorems 10.17 and 10.20 give
finite C work under C-progress for both histories. These form one
finite public-phase-driven experiment: take a bound exceeding the
sum of the two finite acquisition/Call work lengths and branch on
Sealed/Ready availability, rather than assuming a uniform bound over
all cuts. Both release authentic HistoricalImages, one with target
$n(x)$ and history $p(x)$, the other with target $n(x)+1$ and history
$p(x)e$. The lossless target/history fields differ. No private-state
read or live P token is used by this separator. Dropping the captured
incidence therefore fails an actual future-use task, even when every
other coordinate in AIF.25 is supplied. ∎

**Theorem 11.15 (space/partial-time recovery and route agreement).** On
$\Omega^+$,

$$
T_{\rm cut}(z)=T_{\rm cut}(w)
 \quad\Longleftrightarrow\quad \mathcal K(z)=\mathcal K(w)
 \quad\Longleftrightarrow\quad z\equiv_{\rm now}w.
\tag{AIF.34}
$$

There are finite recovery maps between the actual images of
$S_{\rm now},X^+,\mathcal K,T_{\rm cut}$. They are mutually inverse,
agree around every triangle, and transport each same named next action
with its complete successor, current guards, functional outputs and
future charges. These are mathematical maps on authentic descriptions,
not installed acquisition/conversion routines.

Proof. From $T_{\rm cut}$, the canonical startup input/acquisition
records determine $u$; its P chain determines absolute $n$ and all
post-fence supplied bits $I$. Its C chain determines $m$; the Capture
bracket determines $\kappa$, or absence of C gives $\bot$. Thus this
observation determines AIF.25 without using a desired inverse as its
definition. Conversely Lemma 11.8 fixes the startup and both complete
local functional row words from that key. Lemma 11.6 fixes their actual
occurrences and reference roles. Adding the prescribed bracket returns
exactly the observed $T_{\rm cut}$. Theorem 11.11 gives AIF.34.

For explicit routes, decode cell/register gadgets to pass between
$S_{\rm now}$ and raw $X^+$. Use $\mathcal E$ for $X^+\to\mathcal K$;
use normal evaluation $\mathcal D$ for the reverse. Extract the local
words from that evaluation to obtain $T_{\rm cut}$; use the preceding
chain/count extraction in the other direction. Each procedure returns
the view of the same reached endpoint fibre. Theorem 11.9 makes all
these values independent of its chosen chronological representative.
It follows pointwise on actual images that, for any three such views,

$$
R_{WV}R_{VW}=\mathrm{id},\qquad
R_{WZ}R_{VW}=R_{VZ}.
\tag{AIF.35}
$$

For updates, append the actually executed event to its owner chain;
at Capture install its bracket at current $n$, and after Capture put
a new P event above that fixed read cut. All other C events extend
the existing C chain. The extracted coordinate changes are exactly
AIF.33. Proposition 11.12 then gives
$R_{VW}\overline\delta_V=\overline\delta_W R_{VW}$ on each actual
lawful action domain, with identical physical/task guard distinctions,
labels, outputs, future charges and complete raw successors. Induction
gives the same claim for finite experiments. It does not equate
responses to reordered words, transport a policy based on unretained
past chronology, or insert either $B_{\rm now}$ or $M_C$ into AIF.35
without its own missing kernel proof. ∎

### 11.7. Exactly how much total chronology is left undetermined

**Theorem 11.16 (the complete chronological ambiguity).** For a realized
captured key the number of different executed joint chronologies in
its raw-state fibre is exactly

$$
L(\mathcal K)=\binom{n-\kappa+m-1}{n-\kappa}
             =\binom{p+q}{p},\qquad p=n-\kappa,\quad q=m-1.
\tag{AIF.36}
$$

An Armed fibre has size one. A captured fibre has size one exactly
when $p=0$ or $q=0$. On each such singleton fibre normal evaluation
recovers the actual chronology; on the full domain no function of
$X^+$, or even the joint current value of $S_{\rm now},B_{\rm now},M_C$,
recovers $T_{\rm exact}$. Non-singleton fibres occur also at actual
returned Ready endpoints with their live callable rights.

Exact time always has a finite forward recovery to the current raw
state and to $T_{\rm cut}$ on their actual images. The first evaluates
the actual chronological rows; the second retains their owner chains
and actual Capture bracket. These two forward routes agree with the
endpoint/partial-time maps of Theorem 11.15.

Proof. Theorem 11.9 gives fixed startup, pre-Capture P word and Capture.
For the remaining two fixed chains, choose the $p$ P positions among
$p+q$ positions. This gives a bijection with all shuffles, each lawful
by that theorem. Different choices differ in owner-labelled occurrence
order, even if some functional symbols coincide. Therefore they are
different total chronologies and give exactly AIF.36, with no quotient
by equal opcodes. The binomial coefficient is one when a chain is empty.
When both are nonempty, putting its first P row before or after its
first C row gives at least two extensions, so it is greater than one.
The Armed statement follows from the unique word in Theorem 11.9.

For the forward claim, the chronological word includes its canonical
installation inputs and all later supplied bits and commands. Apply
the complete row recurrence from the common foundation in that exact
order. Each finite row has its unique actual successor, so induction
returns $X^+(z)$ with every intermediate state retained when requested.
Projecting the same actual event word to its two owner chains and
captured cut gives Definition 11.13. Theorem 11.9 identifies evaluation
of any of its linear extensions with that same endpoint, proving route
agreement. This does not select the actual extension from the poset.

For a parameterized reached witness, take any valid $u$ and its $F$,
then execute Capture. Choose any lawful next P row $e$, and let $f$
be the now enabled InputPrime. Both

$$
\sigma_u;\mathrm{Capture};e;f
\quad\hbox{and}\quad
\sigma_u;\mathrm{Capture};f;e
\tag{AIF.37}
$$

are lawful and have identical complete endpoints by Lemma 11.7.
Their owner order differs. InputPrime releases no data output, so
even their released output streams coincide. Append an identical
C-only suffix completing acquisition, an authorized Call, printing,
ACK, invocation-token return and the Ready CTL. Theorem 10.20 makes
this suffix finite when C takes its prescribed rows. Determinism from
the common endpoint makes the returned raw states, live rights and
complete released streams equal. The distinct old owner orders remain
in their $T_{\rm exact}$ values. Since $S_{\rm now},B_{\rm now},M_C$
are observations of that identical current state and rights, they
coincide as well. A chronological inverse on their joint current
value would assign two different histories to that one value, which
is impossible. This also shows that later installed state-based work,
given the same future choices and no additional previously retained
record, cannot learn which old ordering occurred. It produces the
same future acquisitions and outputs from both states. ∎

**Corollary 11.17 (history sequences and additional records).** Within a
captured raw-state fibre, the complete historical sequence of raw
joint states has the same $L(\mathcal K)$ ambiguity. Any additional
record $Z$ for which $(X^+,Z)$ determines exact chronology must separate
all those $L(\mathcal K)$ histories. A fixed-length binary supplement
therefore requires

$$
2^b\ge L(\mathcal K).
\tag{AIF.38}
$$

Proof. The fixed startup and fixed local chains evaluate to a unique
complete raw-state sequence for each shuffle. Conversely that sequence
reveals, at every post-$F$ step, which owner's meter acquired the next
receipt. Thus it reveals the owner mask and hence that shuffle. In
particular the two middle corners of a P/C diamond differ in their
pair of meter lengths. The histories counted in AIF.36 therefore
remain different as full-state sequences, even though their last
states are equal. A sufficient $Z$ must be injective on this finite
fibre, yielding AIF.38. This is the finite-fibre separation principle
of `MinimumRollbackAlphabet.minimum_rollback_alphabet` on this actual
fibre. It neither constructs an online logger nor identifies binary
width with physical incidence, acquisition work or a cost optimum. ∎

If one instead observes the past globally ordered OUT stream, a retained
caller transcript, complete intermediate successors or accumulated
structural work, the equivalence to classify is the fibre of
$(X^+,\text{that historical observation})$. AIF.28 still enumerates
its candidate histories, but they must be partitioned by their actual
values of the additional observation. Those observations are not
silently discarded by AIF.31 or AIF.34. In particular an arbitrarily
chosen linear extension of $T_{\rm cut}$ is a compatible chronology,
not identification of which extension was executed.

### 11.8. Same-run resources, inherited use and the remaining bridges

**Proposition 11.18 (what the fibre preserves in the actual bill).** For
any $z\in\Omega^+$, its actual owner native counts and fees are

$$
N_P(z)=n(z),\qquad N_C(z)=c_F(u)+m(z),\qquad
\mathrm{fee}_P=2n(z),\qquad \mathrm{fee}_C=2(c_F(u)+m(z)).
\tag{AIF.39}
$$

Equal raw-state fibres have equal retained vertex counts under AIF.20
and equal these owner-count/fee coordinates. Each history still pays
its own complete evaluated AIF.21 structural tariff. Endpoint exchange
alone supplies no interchange invariance for that past tariff.

Proof. The receipt rules count one row only on its executing owner's
meter, including startup, Capture and every Call subrow. Definitions
AIF.23–25 give AIF.39. Literal endpoint equality includes every retained
vertex and all eleven slots, so AIF.20 gives equal final retained space.
It includes dead banks, unused allocation, partial records, references,
source acquisition, copies, printing and return material; none is
removed by proof normalization. AIF.21 is evaluated along each actual
history, using the actual old-value alias/probe/assignment cases at
that history's intermediate states. Equality of its final endpoint is
not an additive-cost-square proof. To descend any accumulated tariff
one would additionally need, for each exchanged pair at its actual
start $x$,

$$
w_e(x)+w_f(\delta_e x)
 =w_f(x)+w_e(\delta_f x).
\tag{AIF.40}
$$

Process Geometry Theorem 9.2 supplies this separate criterion. No
AIF.40 assertion is made for the present structural tariff. Identical
current raw states do give identical costs for a fixed future row,
which is the different assertion used in $Q_{\rm now}$. ∎

The finite fibre and transport statements require no fairness: they
concern finite actually executed prefixes and all finite lawful choices.
When acquisition or a chosen Call is required to finish, retain exactly
C-progress of Definition 10.16. The existing constructive service is
Theorems 10.17–10.23: C really acquires the captured original package
and later prints its historical image with ACK and token return,
without subsequent P progress. Its acquisition-body subtotal remains
$6|I_*|+5\kappa+16$, with precisely AIF.22's exclusions. Startup,
imports, package building, literal simulation, allocation, both copies,
printing and return remain additional actual work. Normalizing a proof
of a fibre does not reschedule an actual run or reduce its bill.

The mathematical key AIF.25 is not this acquired C package. It also
contains *current* P input/progress and C's current progress. This
section installs no authorized collector of that whole current joint
key. Nor does it prove separate global kernels for the independently
defined $B_{\rm now}$ or $M_C$. Common current raw-state sufficiency,
actual historical-package acquisition, current-joint acquisition, and
four individual natural-view kernels are distinct conclusions. The
first and the precise partial-time correspondence are established
here; the existing second is reused; the last two remain unproved.

### 11.9. Suppliers, primary correspondence and exact mathematical gain

The new source-specific content is Lemmas 11.6–11.8's complete
alias/guard/phase and actual-occurrence correspondence, Theorem 11.9's
whole-domain raw-state fibre, its reverse continuation-kernel argument,
and the concrete distinction between an indispensable captured frontier
and erased subsequent cross-owner chronology. The five-coordinate
extraction adds no runtime generator or log. Original producer replay
alone does not determine C's current partial work or justify exchanging
its rows. A complete supplied joint schedule would determine them,
but AIF.28 proves exactly which of those distinctions the present
continuation task does not need. Two owner chains without their Capture
attachment fail by the actual future experiment of Proposition 11.14.
No claim of least hardware, memory or operational acquisition cost is
attached to this sufficient organization.

| Existing supplier | Use and hypothesis boundary |
| --- | --- |
| AIF Theorems 4.4–4.5 and 10.10–10.23 | Exact original D0 replay/projection, actual copied seed, persistent frontiers, acquired original package and later paid callable use. All canonical entrance, atomic grants, ownership and C-progress conditions are retained. The joint endpoint diamond and exact fibre require the additional proofs above. |
| SSA §§3–5; CSA §§5–7 | Lossless cell/register storage and original retained extraction; four exact kernels on CSA's different serial installed domain. Its history-injectivity is not assumed for the present two-owner fibres, and its existing four-view result is unchanged. |
| RCA §§11–13.4 | Finite owned word expansions, dirty/retired bank representations, literal original-row simulation, actual allocation/copy/print/ACK/return. Its D1, port-38 input and activation conventions are not substituted for D0. |
| Context §§13.6,13.8,13.10; Process Geometry §§9,43; Atlas Stable Core Holonomy §§3,6 | Legal extension/swap, route, individual task-kernel and separate cost-square principles. Their generic machinery supplies no AIF shared-slot independence, acquired grant or reverse natural-view kernel by itself. |
| `EnabledPathSwapConnectivity.result` and its owning Scribe | Finite occurrence-poset execution/linear-extension correspondence and legal adjacent-swap connectivity. It is applied only after Lemma 11.7 and Theorem 11.9 identify native guards and common successors at the relevant lower cuts. |
| `AdjacentIncomparableSwapInvariance.evaluateOrder_adjacent_swap` | Endpoint preservation under a supplied commuting pair. Its parent-coordinate hypotheses are not automatically an allocating, multi-slot, partial native runtime; the native field proof supplies the required correspondence here. |
| `TypedFiniteViewKernel.response`, `behavior`, `typed_finite_view_kernel` and its owning Scribe | Typed partial experiment semantics and kernel reasoning. Undefined noncanonical task input is kept separate as in AIF Definition 2.6; the generic result is not an acquisition theorem or a substitute for Theorem 11.11's reverse inclusion. |
| `NativeSerialMachine.replay_deterministic`, `reached_prefix_replay`, `actual_register_execution`; `NativeFullSourceProducer.native_source_producer` and their owning Scribes | Supplied-history replay and actual stationary acquisition at their original scopes. Private `traverse`, `production_reads` and `stationary` invariants supply no runtime subtree advice or joint schedule. |
| `NativeIndependentExecution.native_history_correspondence`, including private `recover_word` and `active_history_relation` | The supplied timed word retains all writer placements, including before locals and Return. Its chronology variables do not acquire an AIF schedule and are not erased by the present, explicitly different temporal observation. |
| `MinimumRollbackAlphabet.minimum_rollback_alphabet` and its owning Scribe | Finite-fibre separation/counting; the actual AIF fibre to which it is applied is AIF.28. Its existential finite label construction supplies no installed logger or free reference capacity. |

These suppliers apply only at their stated hypotheses; their private
proof helpers grant no additional runtime input. No new Lean certification
is claimed. Pinned
mathlib `Mathlib/Computability/StateTransition.lean`, revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`, `Respects`, `tr_reaches` and
`tr_eval`, transports a supplied relation through matching fragments;
it supplies neither the native diamond nor a chronological inverse.

The following primary texts supply mature methods and distinctions.
The concrete AIF correspondence and fibre are `repo-derived`, not a
claim of worldwide novelty or exhaustive absence of other results.

| Primary text | Correspondence to the declared apparatus |
| --- | --- |
| L. Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, CACM 21(7), pp. 558–560, [author copy](https://lamport.azurewebsites.net/pubs/time-clocks.pdf), “The Partial Ordering” and “Logical Clocks” | Actual process order is a partial-order generator; a logical clock respecting it does not supply the converse or identify an unrecorded actual total order. Here owner chains are actual receipt successions. The additional Capture bracket is proved from the exact frontier read, and is expressly a read-version constraint rather than an inferred message edge or physical-time law. |
| G. Winskel, *Event Structures*, LNCS 255, pp. 326–328, [author chapter](https://www.cl.cam.ac.uk/~gw104/Winskel1987_Chapter_EventStructures.pdf), Definitions 1.1.1–1.1.2 and Examples 1.1.5–1.1.7 | Consistency/enabling, conflicting choices and concurrent squares are distinct. For each realized key the fixed occurrence fibre is consistent and its owner minimal events really execute by Lemma 11.7. Alternative input bits and Capture cuts are not amalgamated into a conflict-free global poset, and no static independence relation for every command pair is assumed. |
| M. Herlihy and J. Wing, *Linearizability: A Correctness Condition for Concurrent Objects*, TOPLAS 12(3), pp. 464–468, [author copy](https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf), §§1.2,2.1–2.2 | Their equivalence preserves process subhistories while sequential object legality and real-time precedence remain separate obligations. The register/queue examples explain why owners alone do not justify swaps. Here the native footprint proof justifies only the post-Capture exchanges, and Proposition 11.14 retains the concrete shared read/append distinction. Linearizability does not supply C acquisition, liveness or actual total chronology. |

All previous fixed-model results and open obligations keep their original
hypotheses. In particular this section does not change original
$G_{gc}$, original-Q, parked-consumer or unchanged-initialization tasks,
CSA's serial kernels, or AIF's historical producer-image service.
Exact past chronology and complete historical state sequences remain
strictly stronger observations on the exhibited fibres; accumulated
structural work retains its own unproved square condition. Native
current-joint acquisition, separate enlarged boundary/C-memory kernels,
unrestricted observer recovery, uniform physical realization and the
full space/time/boundary/memory programme remain unproved. A different
partial-time observation advances that programme only with these exact
recovery conditions and chronological limits retained.

## 追加锚（本行以下为增补区）

## 12. Paid two-meter joint-cut acquisition with an initialized Armed collector

### 12.1. Target, new apparatus and supplied mathematics

The target here is an actually visited joint state, including the
collector, immediately **before** a new Pin row. It is not the state at
return. The original producer and consumer may then be in any phase
allowed by §11. The new collector must still be Armed. Its subsequent
acquisition, interpreter, copy and return phases are outside this inverse
domain. This asymmetry is a hypothesis, not an elimination of those
subsequent physical states.

Write $A^+$ for the apparatus of §§10–11, with its actual fixed primary
scaffold, not an isomorphic replacement. Write $D_+(\mathcal K)$ for the
complete actual-identity decoder of Theorem 11.9 and Corollary 11.10. Its coordinate is

$$
\mathcal K=(\operatorname{code}(u),I,n,\kappa,m),
\qquad m=N_C-c_F(u).
\tag{AIF.41}
$$

The old seed, source binding and fixed public preparation have their
original meanings. We use the all-phase owner-word determination of
Lemma 11.8, the update rules of Proposition 11.12 and the chronology fibres
of Theorem 11.16. These are suppliers, not new assertions about a smaller
Ready-only domain. In particular $m=0$ is exactly the old Armed branch;
otherwise Capture is the first post-fence C row and its meter attachment
persists through every subsequent C phase and every repeated Call.

**Definition 12.1 (the disjoint-scaffold apparatus $A_R$).** Retain the
entire actual $A^+$ primary component: all its old vertices, tape numbers
0–128, eleven slot types, register locations, code, two meters and local
allocation conventions. Adjoin a separate primary component $F_{68}$,
using SSA's fixed ordered scaffold construction with 68 sockets. Its
sockets, in order, hold 64 R tapes, one finite register component and
three distinct anchors $a_P,a_C,s$. The R tapes have actual numbers
129–192; local number $i$ means actual number $129+i$. The R meter is
local 63. Register and token bits have their actual finite bit gadgets;
one socket does not mean one vertex or one bit.

Every vertex has these **fifteen** slots:

$$
P,L,R,O_0,H_0,O_1,H_1,O_2,H_2,O_3,H_3,O_4,H_4,O_5,H_5.
\tag{AIF.42}
$$

There is a fixed reciprocal bridge between
$(\mathrm{root}_R,O_4)$ and $(\mathrm{root}_+,H_4)$.
These two scaffold roots are distinct from all tape-cell roots and
anchors. Each end anchor uses $O_4/H_4$; the sole moving anchor $s$ uses
$O_5/H_5$. Thus the complete port graph is connected, but its ordered
primary $P,L,R$ forest has **two** components. Neither a 203-socket
replacement scaffold nor extra simultaneously resident scan anchors are
part of this construction.

Local 0 is a sealed code-source capsule, local 1 is its separate
source-dependent seed/manifest copy, local 8 is the demanded-input spool,
9 and 10 are P and C tally spools, and 11 is the optional Capture tally.
Ports 32–39 have RCA §11's bank, scratch, descriptor, staging, retained
input and archive roles; 40 is the result receiver and 48 its mailbox.
The other tapes are initialized unused tapes. The archive may contain
several physically distinct records; no record is an uncharged register.
These roles do not overlap local 63 or one another.

**Definition 12.2 (slot, constructor and naming discipline).** Every old
or new vertex constructor initializes all fifteen slots, including empty
ones. Every lifted old row has exactly its old eleven-slot assignments,
with the old core/receipt alias resolution, and preserves every unnamed
added slot. It also retains its original symbol, latch, code, token and
control effects. R rows change no old eleven-slot field, old symbol,
old head, old latch, old descriptor, old token or old receipt. Their
foreign assignments are exclusively their added reciprocal pairs.
The startup gate and final R-Armed assignment below are new R fields,
not replacements for old fields.

Names are tuples of owner, arena, constructor ordinal and template role.
All old tuples are preserved literally. R uses a disjoint owner namespace
and owner-local ordinals. There is no joint allocation clock or global
receipt index. The old descriptor ordinals still count their own old
record streams. Initial scaffold names and finite bit-gadget names are
fixed constructor names in the same convention.

Let $\pi$ delete the R primary component, the bridge and the four added
slot types, and erase the new R startup guards. It preserves every
remaining occurrence and field on that same occurrence. This is an
old-identity-preserving projection, not a relabelling map.

### 12.2. Rows, grants and alias consistency

**Definition 12.3 (new bounded rows and rights).** R has finite control,
eight latches, its own receipt on every executed controller row, and the
RCA word instructions expanded below. Its additional external entry is
Pin, enabled only at Armed with its one-shot pin token live. In **one**
old-value row Pin follows both actual current meter append links, binds
their two cell roots to $a_P$ and $a_C$, consumes that token and enters
CountC. It appends one R receipt. It does not bind a J endpoint, read a
meter numeral or payload, sample the old C phase, or sample $\kappa$.
The target $x$ is the complete state immediately before that row.

The other new row families are the following finite cases.

- PlaceL($q$) clears the cursor's previous reciprocal pair, if any, and
  puts $s$ at the actual L cell of the named granted tape $q$.
- Prime and Next follow the existing adjacent-cell path $PRL$. A
  Previous row, where used in descriptor work, uses the old $PPL$ route.
- TestEnd compares the cursor's target occurrence with a designated
  saved end target; it branches before any cell-symbol read.
- ReadJ reads the fixed eight-bit gadget at a granted sealed J cell into
  latch 0. It is enabled only in the prescribed demand-reader phase.
- The optional Capture scan may follow the old persistent fixed-end
  $O_2/H_2$ attachment, and compare the cursor with its target.
- ClearCursor, finite phase/purpose changes, seals, ACKs and the new
  invocation token operations have their literal bounded effects.

PlaceL has finitely many static tape cases, including the temporary
startup sources. The new post-fence read rights are only: J's sealed
bits and adjacent topology; P/C meter topology and append links; and the
old persistent Capture-end attachment. R cannot read meter payloads,
old latches or banks, private source cells, old commands, or arbitrary
old helpers. It never borrows an old writer token. The right to inspect
a root for equality is not a right to read its changing receipt symbol.

Pin and these cursor rows are additional apparatus primitives, with the
structural tariff below. They are not old PR57 instructions derived from
an empty-extra-port theorem. Their semantic size is bounded because
only a fixed number of finite routes, roots and gadgets are involved;
no row follows an unbounded spine or reads a word atomically.

**Lemma 12.4 (finite alias-safe realization).** Definitions 12.1–12.3
have a finite table of bounded old-value patterns. Lifted old rows remain
well-defined with any lawful R anchor/cursor incidences, and vice versa.
They preserve $\pi$ field by field.

**Proof.** Resolve the original core plus its original receipt first,
as in Definition 10.7. Preserve the post-core meter read head; do not
restore its entry head over an executed read-head movement. The bit
rewrite changes only the four listed old slots of its five-occurrence
bit template. An append changes the old trailing terminal's two child
slots, constructs a new cell and terminal, and preserves all incidences
on the retained old cell root. Thus none of these operations clears
$H_4$ or $H_5$ as a side effect.

The P and C end targets are on distinct tapes, so the two assignments
of $H_4$ cannot compete. The bridge's $H_4$ is on a scaffold root,
not either target. A cursor may meet an end, an old capture end or an
old read/append head, but its $H_5$ differs from $H_4,H_2,H_3,H_0,H_1$.
When PlaceL's old and new targets coincide, compute the final reciprocal
pair from the entry values and assign each resulting slot once; do not
clear a pair after setting that same pair. The same rule applies to
all simultaneous role identifications. No foreign row writes $H_5$.

There are finitely many roles per schema, equality partitions of those
roles, symbols, finite controls and slot labels. For each partition,
coincident assignments agree by the preceding distinct-slot argument
and the old alias rule. Births use fresh owner-local names. Enumerate
these consistent partitions; reject inconsistent patterns. All routes
have fixed length in the installed finite scaffold and in a cell gadget.
The resulting finite table is independent of tape lengths. It initializes
fifteen slots at each birth and copies every unnamed old slot. Erasure
therefore returns exactly the original row. No SSA §13 switch premise
about empty extra slots is used. $\square$

### 12.3. Canonical code supply and physically entered startup

An installed description and an executable image are different objects.
Write $\Delta(G)$ for a framed finite row/effect description and $E(G)$
for its actual native installation image. The serializer of RCA §12.2
removes list/framing tags and emits the row fields and fixed effect bits
in installation order. It does not turn an arbitrary binary string into
a correct description of its reader. This construction adds the following
specific matching-code supply; it does not assume an old reflective read.

**Definition 12.5 (finite loader basis and matching capsule).** Fix a
finite constructor/loader basis $B$ consisting of SSA cell/bit/scaffold
constructors, literal bit emission, finite-controller-store installation,
sealing, the fifteen-slot policy and the following loader loop: read the
next supplied installation bit; write that bit at the next raw code-store
location; advance; at the copied length counter's zero finish and
activate the installed table. Its active bootstrap rows and partially installed raw
store are different fields. Until the final DONE, lookup uses $B$'s
active rows. After DONE it uses the completed R table. The loader is
used only with the declared canonical image; it does not infer semantic matching from a successful parse. Its installation loop
uses the actual raw-store cursor and the counter's real terminal 0, without
an assumed initialized word bank. All its fixed metadata is emitted by
literal finite construction. The later R validator runs only after R's
empty-bank prelude. Concretely the private installation packet is
$U(|E(G_R)|)E(G_R)$. B copies its initial unary 1s to an actual counter
on local 2, then appends its terminating 0, delimiter and seal and
positions that counter from its real L. At each counter 1 it consumes
one installation bit, writes/advances one raw code location and moves
the counter; at its 0 it executes DONE. Packet acquisition, counter
construction, each IN, each write/advance and the final test are paid
native rows. The fixed capsule is emitted on local 0 by the same
finite literal-source/counter-copy construction, with local 3 as its
separate counter. Both counters and all loader scratch are retained.
These are bootstrap routines using literal appends and actual heads;
they do not call an uninitialized bank helper. Their private constant
input is distinct from later unknown source-frame input.

First form R's finite program from the word/effect recipes in this
section. It contains a general parser/interpreter, not a literal copy of
its own table. Apply the finite compiler to obtain its actual row table
$G_R$. Then apply the stated serializer to $\Delta(G_R)$ to obtain
$E(G_R)$. The source-independent capsule is the following fixed tuple:

$$
\mathsf{Caps}_R=[\Delta(G_R),E(G_R),\Delta(A^+),B,\Lambda,H,\xi].
\tag{AIF.43}
$$

Here $\Lambda$ is the fixed layout and entrance table: the two scaffolds,
owner/arena/constructor naming, static routes, port numbers, effect
schemas and the canonical boot recipes. $\Delta(A^+)$ includes its
source-independent bootstrap and all row/effect variants, not merely
$\Delta(D_0)$. No field of $\mathsf{Caps}_R$ contains $u$, a later input, a target
ordinal, a target state or a history. $B$ and $\Lambda$ describe generic
finite constructors with a packet operand; they do not contain $\mathsf{Caps}_R$
as a literal subword.

The canonical installation source supplies the bits of this particular
$\mathsf{Caps}_R$ and $E(G_R)$, bit by bit, to $B$. This is an explicit added supply
of matching code, not a promise about arbitrary externally provided
programs. A finite source-independent source emits any fixed word by
its finite chain of literal writes. Each such write, construction, move,
raw-store update, delimiter, descriptor, seal and receipt is charged.
No test success is used to infer that two arbitrary descriptions match:
matching here follows from forming both from the same actual finite
row table. The table is constructed before its data source is emitted,
so there is no code-quotation fixed-point equation.

The resulting capsule is physically retained on R local 0 with actual
Base, length, descriptor, F delimiters and seals. The loader basis table is retained separately from the new raw main
code store; DONE changes the active-table selector without erasing the
basis. All loader store, selector, descriptor and scratch material remains
part of R's carrier. The fixed constructor
basis is an expressly declared foundation basis, not an unspecified
computer whose entire state is claimed to be reconstructed. Every
material register or word of this basis that remains in the apparatus
is included in $\Lambda$'s carrier and in the target codec. The external
finite literal-emission prescription is a foundation construction,
not a later free read of the controller or an unrestricted history source.

**Definition 12.6 (startup schedule and acquisition).** Construct the
old actual foundation and the separate R foundation in fixed recipe
order, with the bridge, empty anchors, all fifteen-slot initializations,
loader material and code capsule paid. The fixed priming construction
builds the R scaffold, basis register/control store and local-63 L/R
meter before activating any B row. Thereafter every executed B row has
an R receipt, including its code/capsule-installation rows; its active
code source and raw destination are separate. The other tape origins,
L/R cells, anchor/register gadgets and empty fields are constructed in
socket order, then the capsule and main raw code in their fixed wire
order. Fixed constructor priming is charged as foundation construction;
it is not a row executed without a required receipt. Execute the old
canonical startup until C's SetupDone, after C has sealed and imported its authentic
manifest and cleared its setup links. At that point hold P and C using
an added startup gate stored in the R register component. The old states
are unchanged. This is before P's remaining original acquisition-return
rows. The old seed sender and C manifest are already finite and sealed.
The extra gate has the finite cases BootP, SeedC, RSetup, FinishP and
Independent. The old seed-seal transition selects SeedC as before;
C's old SetupDone additionally selects RSetup. FinishR selects FinishP;
the old final fence additionally selects Independent and sets R's
finite PC and phase to Armed.
In each startup case only that named owner's prescribed rows execute;
Independent restores the old P/C union and the guarded R entries.
All these extra assignments are on R's finite register component. Main
R code is activated at its Prelude entry during foundation loading,
but its execution is gate-disabled until RSetup. WaitingF has no R row.

R now executes the native empty-bank prelude of RCA §11.4 on its own
32–39: literal bank sentinels, the literal finite register-count word,
the initial empty fields, Base/length/creation descriptors, seals and
parity. It does not run a word assignment before this entry relation
exists. R scans the actual local-0 capsule and imports its framed fields
using the finite field/list parser. The full-prefix entry is Home, MR to
the leading F, a second MR to the first field; consecutive Fs retain
empty fields. No mathematical word is silently substituted for this scan.

A temporary startup grant gives R cursor access from the fixed C origins
to the sealed manifest prefix on C local 37 and its placement records
on C local 36. It grants no private P-source read or old C execution
token. A startup-only cell-read row distinguishes 0, 1, F and R at its
foreign cursor; this is not a post-fence old-bank read right. At this
hold, port 37 has exactly the leading-F, ordered-field prefix of
Definition 10.5, with no later staging blocks. R starts from its actual
L, Prime to the leading F and Next to the first field. It copies binary
symbols into R local 1 until F, appends that actual field's F and seal,
and advances to the next field; at R it stops. It first constructs its
own leading sentinel. Consecutive Fs copy distinct empty fields. Field
counters are actual unary marks appended while scanning, and the
fixed field count is validated after this finite traversal. Thus a
single whole-manifest source descriptor is **not** assumed to exist.

At the source leading F the offset is the actual empty unary word;
every adjacent move consumes that cell and appends one mark, including
moves past F delimiters. Each field base is the offset at its first bit
or following F when empty; its length is the counted binary-bit word.
R scans the finite C descriptor prefix from its actual L, with finite
tuple parsing, retaining the actual owner/arena/base/length/creation
records for the physically recorded manifest fields, in particular the
variable acquired seed. A fixed literal field needs no invented placement
record: its actual field position/seal and checked content identify it. The grant identifies the real sealed
prefix, not a proposed numeral. Comparisons use the just measured words;
positioning a reread consumes the copied base from the actual origin.
Only those source-bound records are selected, rather than assuming an
arbitrary matching offset. R creates its own real Base, length,
descriptor and seal for each destination field, and retains its source
bindings and all scan scratch. Parsing the copied lossless manifest
gives $\operatorname{code}(u)$, the old fixed parameters and the original
acquisition-sender binding actually stored by C. Those parameters are
checked against the imported fixed capsule. The seed comes from these
physical reads, not from the code installer. No extra original C record
or whole-manifest descriptor is created for this new grant.

The compiler's latches 4–6 are separate from data latch 0 and counter
latch 1. Before a word helper uses a source bit, the physical read branches
to the literal-0 or literal-1 cons entry. Direct copies preserve latch 0
through their matching WR. Thus no helper is assumed to preserve an
unlatched source value. The same convention is used later for J.

R clears the foreign $H_5$ cursor incidence, leaves both Pin anchors
empty, seals its startup records, revokes all temporary source/loader
write grants and enters WaitingF. Revocation, token state and historical
descriptor flags are separate represented fields. FinishR hands the
startup permission back. P executes exactly its remaining old acquisition
return. Its final old fence row also sets the new R PC/phase to Armed
and opens the independent phase. There is no post-fence idle R row before
Pin. Pin is disabled during construction, boot, import and WaitingF;
it is enabled already at the common fence $F$.

All new startup work is in this fixed order. There is no nondeterministic
startup retry, parser choice, hidden call or forgotten temporary arena.
The foundation and startup recipes retain all created bank versions,
scratch, code and descriptor records. An implementation choosing another
loader or retaining another host would be another apparatus.

**Lemma 12.7 (actual entry, projection and complete startup replay).**
For every valid finite seed $u$, Definition 12.6 terminates at $F$.
Its projected old startup is exactly $\sigma_u$, with the same
$c_F(u)$ and actual old sender binding. There is a finite word procedure
$\operatorname{Start}_R(\mathsf{Caps}_R,u)$ which reconstructs the complete reached
fifteen-slot state at $F$, including all R backing, marks, latches,
active/raw code, grants, tokens, retired records and receipts.

**Proof.** The finite priming recipe terminates by its literal
constructor list. In B's loader loop, after $j$ consumed counter marks
the main raw store is exactly $E(G_R)[0:j]$ with its actual next write
location; induction on the read/write/advance rows proves this invariant.
At the counter's 0 the whole image has been installed. The capsule-copy
loop has the identical bit-prefix invariant for $\mathsf{Caps}_R$. Thus DONE enables
precisely the table whose description is actually retained in the capsule,
without a reflective read or a parser-based inference of matching. Both
constant loops terminate on their constructed counters.
The old prefix through SetupDone terminates by Lemma 10.6.
At the hold, every source for R is already finite, immutable and reached
from a granted fixed origin. Each descriptor/field traversal consumes an
actual finite prefix, and each skip/copy iteration consumes a mark from
an actually copied unary word. The empty-bank prelude is a finite literal
construction; subsequent compiler operations terminate by RCA §11.4.
The initial two manifest moves and the F cases include zero-length fields.
The old codec identifies the same $u$ and binding actually acquired by C.
Temporary grant revocation and clearing are finite bounded rows. The
remaining P return has precisely its old preconditions and successors.
Erasing R work and guards therefore gives $\sigma_u$ and does not add a
C or P receipt. The final R field change is not an R receipt.

For reconstruction, initialize the explicit finite carrier from
$\Lambda$ and run the constructor, loader and startup rows just specified,
using $\mathsf{Caps}_R$ as source-independent data and the original canonical boot
reservoir generated from $u$ and the old entrance parameters. That
reservoir is the existing canonical-startup supplier, not a history input.
At each represented native row the adapter of §12.6 below updates every
actual field, births its actual named cells and appends its owner receipt.
The fixed gate order selects the next owner; hence there is no schedule
parameter to guess. Copy-source positioning and descriptor ordinals are
computed by these same represented scans. In particular the result
contains all inactive bank versions, partial scratch remnants, cleared
links and revoked grants, not just the parsed live registers.

This computation terminates because it follows the proved terminating
startup. Its induction invariant is equality of the whole represented
carrier after each prefix with the actual carrier after that prefix.
Constructor, copy, read and loader cases use identical old-value effects;
DONE switches the same completed table. This proves the assertion for
the final fence. The startup procedure itself never calls this
reconstruction procedure: it only loads, scans and imports. There is no
recursive demand for the state currently evaluating its own startup.
$\square$

### 12.4. The authentic Armed domain

**Definition 12.8 (domain and common target).** Let $\mathcal D_R$ be all
lawfully reached post-$F$ states of this fixed $A_R$ in which R is still
Armed. All valid canonically acquired seeds, lawful input prefixes and
old owner schedules are allowed. Old C may be Armed, in any unfinished
capture scan, manifest import, dirty bank, descriptor, simulation,
publication, copy, print, ACK, token/Ready phase, or between any finite
number of Calls. There is no restriction that P or C be Ready.

Before Pin, R executes no row. Its R-owned material is therefore the
actual $R_F(u)$ constructed in Lemma 12.7, with the constant bridge and
empty foreign cursor/Pin anchors. Old P/C steps preserve $\mathcal D_R$.
Pin exits it, and there is no rearming in this apparatus. All later R
maintenance cuts are real reached cuts of $A_R$ but are not elements of
$\mathcal D_R$ or inputs to the inverse claimed here.

**Lemma 12.9 (literal coverage and unique Armed lift).** Projection maps
$\mathcal D_R$ onto the entire old $\Omega^+$ of §11. Each old reached
state has exactly one Armed lift for its actual seed. In particular,

$$
\pi(\delta^{R}_{e}(x))=\delta^+_e(\pi(x))
\tag{AIF.44}
$$

for every old lawful action $e$ at $x\in\mathcal D_R$.

**Proof.** At $F$, Lemma 12.7 gives the old canonical state. Thereafter
Lemma 12.4 erases each old step to exactly its old step, including raw
IN successors; nonadmissible Supply still executes physically but exits
the lawful domain. Conversely insert the fixed R startup into any old
canonical history and park R after $F$. Its entire old continuation is
still enabled with its old guards and bits. Thus every old cut, including
all listed interior phases, is attained under $\pi$.

R remains unchanged. The only extra incidences on old material are the
constant bridge at the old scaffold root; all other $H_4,H_5$ fields on
old vertices are empty before Pin. Old births initialize them empty and
old rows preserve them. Hence the complete lift is fixed by the old
state and the actual startup $R_F(u)$. Different shuffles with the same
old endpoint create no new R state or global names. $\square$

### 12.5. Counting a common cut and acquiring only its inputs

Write $z=\pi(x)$ for the target, $n=N_P(z)$ and $c=N_C(z)$.
These are proof coordinates until the following scans have produced
actual words. Pin stores occurrence links, not these numbers.

**Lemma 12.10 (persistent two-meter prefix).** After Pin, the strict
prefix before each saved end is exactly its target meter prefix and
remains so under arbitrary later lawful P/C work. CountC and CountP
terminate without any further old-owner row.

**Proof.** Pin's two right ends are resolved in the same old-value
pattern. Thus both refer to this one actual predecessor $x$. Each old
meter append preserves its old R cell root, converts its symbol and
expands only its trailing terminal. Its ancestors and existing adjacent
paths are unchanged. No lifted old row clears the added end incidence.
R scans from actual L: Prime to the first counted position, TestEnd,
and, on inequality, append 1 to its owned tally, Next, and repeat.
When equality holds it reads no symbol there and never takes Next from
that root. The visited non-end cells are exactly the $c$, respectively
$n$, preceding receipt cells. Their receipt bytes may change; this
routine never reads those bytes. Future appends cannot add a cell
strictly before the saved root. The finite variants are the numbers
of unvisited roots in these already attained strict prefixes. They are
proof variants, not native loop bounds. $\square$

Sequentially reading two current counts is not an implementation of
this lemma. For example, sample P at $n$, then execute a P row, then a
C row, then sample C at $c+1$. The pair $(n,c+1)$ need not have occurred
anywhere in that run. Pin avoids this problem by its declared single
bounded row, not by appealing to a compatible reordered execution.

**Definition 12.11 (delayed Capture branch).** Import the sealed tally
words, execute the old canonical startup evaluator on the acquired seed,
and construct its actual $c_F(u)$ as a unary word. Cancel one mark from
$c$ and $c_F(u)$ until the second is empty, retaining the remaining word
$1^m$. A premature empty $c$ is typed invalid; it never occurs here.
Test that actual remainder. If it is empty, set the represented branch
$\kappa=\bot$ and do not read the old Capture attachment. If it is
nonempty, PlaceL on the P meter and count up to the root named by the
old persistent meter fixed-end attachment, obtaining $1^\kappa$.

**Lemma 12.12 (delayed branch correctness, including later Capture).**
This procedure obtains exactly $m$ and $\kappa(z)$ without an old phase
sample, including the case $m=0$ at Pin followed by Capture before the
branch computation.

**Proof.** Lemma 12.10 gives the target $c$, not C's later count.
Startup replay gives the same $c_F(u)$ by Lemma 12.7 and the old canonical
entrance. The difference is therefore precisely AIF.24. If it is zero,
C had executed no post-fence row at Pin; its target branch is Armed.
A later Capture cannot change that subtraction result. Ignoring its
now-present link is required, not an exceptional failure.

If $m>0$, Capture already occurred before Pin, because it is C's first
post-fence row. The old meter fixed-end root was set by that Capture and
is never retargeted by any later C phase, package or repeated Call.
Following it later therefore obtains the same root. Lemma 12.10's
strict-prefix argument applies to this additional P-meter count, even
if the root is now a non-R receipt cell and even if it is also P's Pin
end. Distinct $H_2,H_4,H_5$ slots preserve every coincident role. Its
rank is exactly $\kappa(z)$ by Lemma 10.13. No readiness/status read or
future old-owner progress is used. $\square$

**Definition 12.13 (replay-directed J acquisition).** Start the original
$D_0$ prefix evaluator with the actually copied seed and fixed canonical
boot data. Its represented input stream consists of two distinct kinds:
the known boot/private reservoirs and a demand continuation for the
source-frame public INs. Give it the actually counted unary countdown
$1^n$. Place the one external cursor at actual J.L.

For each represented original row, first inspect its actual row kind.
At a source-frame IN: Next once on J, ReadJ its bit, append that bit to
the R-owned input spool, and feed that bit to the represented IN. Do
not read another J bit at another kind of row. Then complete the
represented row and tail the countdown once. At zero stop before row
$n+1$, irrespective of P's current state or the next source frame.
The demand-reader native phase and represented row continuation are
retained across all intervening word-helper rows. Seal the input spool
with its delimiter on exit; it contains the forward word $I$.

**Lemma 12.14 (exact already-attained demand and finite termination).**
This procedure reads exactly $r=|I(z)|$ J bits, in order, all already
attained at Pin. It reconstructs the target original P prefix through
$n$, including consumed-but-unwritten input, and requires no J endpoint,
future P step, frame-completion signal or historical response oracle.

**Proof.** Induct on the represented row count $j\le n$. The invariant is:
the represented state is the actual original P state after $j$ rows;
the input spool is exactly the source-frame bits consumed in that prefix;
and the external cursor is J.L if that word is empty, otherwise the
cell of its last consumed bit. Known boot and private INs use their
proper supplied canonical reservoirs and do not move J.

For a source-frame IN at row $j+1\le n$, the induction hypothesis
identifies the same row as the actual original one. Its next bit was
consumed by the target history no later than $n$. Definition 10.3's
mirror appended that bit **in that same original IN row**, before its
successor existed. Thus the next cursor move reaches an already
existing J bit, even when the corresponding next original WR had not
occurred at Pin. That cell's bit is immutable under later P/C work.
ReadJ obtains this actual bit, the direct append retains it, and the
represented IN has the actual latch/control/receipt successor. Non-IN
rows use the same acquired row description, old values and reservoirs,
so they preserve the invariant without a source read.

After exactly $n$ represented rows, the countdown is empty and the
spool is precisely $I(z)$. Its number of reads is $r$, with none for
future inputs and none for boot/private input. Each represented row
is finite word work by the adapter below. Each external demand uses
bounded rows and an existing cell, so P or C may remain parked throughout.
The finite countdown and the finite inner word/list loops prove
termination. $\square$

### 12.6. An explicit enlarged-state word/effect adapter

RCA's original 64-port Step is not a simulator for $A_R$. The following
adapter supplies the missing carrier and row semantics. It uses RCA's
word language and compiler, not an enlarged uninterpreted Step opcode.

**Definition 12.15 (finite carrier and effect grammar).** A represented
state is a framed tuple of: a finite list of occurrence records; the
actual roots and named origins; active table and raw installed-code
fields for each owner/bootstrap; finite PC, purpose, phase, token,
grant and latch fields; and the actual pending supplied-input cursors.
An occurrence record has its name, template role, fixed finite bit/tag
fields, and exactly fifteen slot fields, each empty or a framed target
name. Model symbols, head marks, control bits and rights are decoded
from their real gadgets; a record cache, if used during a lookup, is
recomputed from those fields and is not an alternative source of truth.
The serialized result includes all raw fields, not only that cache.

Record order is canonical owner/arena construction order with fixed
finite-role order inside a constructor. Names are computed from actual
preceding constructors in that arena, including initialized foundation
occurrences. No field is a host pointer. Code tables, old inactive
banks, scratch, sentinels, unsealed material, dirty descriptors and
unavailable receivers are ordinary occurrence records. There is no
chronological state list or unrestricted history reservoir in this codec.

A framed row describes finitely many roles, guards and effects. The
role constructors are a fixed named origin, a finite labelled-slot walk
from a resolved role, a designated finite bit-gadget location, and a
fresh owner/arena/template role. Guards are fixed symbol/finite-bit
comparisons, role equality, named token/grant tests and finite Boolean
combinations. The effects are finite lists of slot assignments, fixed
bit/tag/control assignments, the SSA finite birth templates, source-bit
latch assignment of the declared IN kind, and released functional labels.
The old row schemas supply their original finite effect tags; the new
Pin, cursor, gate, mirror and receipt tags are precisely the bounded
patterns of Definitions 10.3 and 12.3. There is no effect named
"recover", "copy history", "evaluate a word", or "scan to a numeral".
A receipt template is appended after the core effects as specified below.

**Definition 12.16 (actual word algorithm EvalRow).** Use RCA §12.1's
ReadList/ReadFrame/ReadUnary, Equal, Nth, Replace, AppendItem, Cat,
Reverse and finite tuple operations. Their natural operands are actual
unary words. The algorithm is as follows.

1. Scan the active finite row list, comparing its framed PC with the
   stored PC, and retain the unique matching row. Bootstrap lookup
   uses the active loader until its actual DONE. Reject absent/duplicate
   labels or malformed finite fields as typed invalid data.
2. Copy the entire finite entry record list into an immutable word bank
   operand. Resolve each role by scanning names with Equal; traverse
   each finite route one slot lookup at a time on this operand. Evaluate
   guards, equality partition and all old-value right sides there.
3. Construct a finite assignment list of pairs (field name, value) and
   a finite birth list. Scan the assignment list to merge equal-field
   entries only when their values agree; a conflict is typed invalid.
   Check fresh birth names against the entry list and earlier births.
   Initialize every fifteen-slot record, then Replace each assigned
   field. For births, extract the fixed owner/arena sublist, AppendItem
   in its constructor order, Replace that sublist, and concatenate the
   fixed ordered arena lists. Thus list order is canonical owner/arena
   order, not the order of cross-owner allocations in the history.
4. Resolve the owner's receipt from this **post-core** carrier, preserving
   its post-core read mark. Apply its explicit append/mark/finite-control
   effects by the same snapshot/assignment procedure. An atomic mirrored
   IN includes its mirror birth in the core stage; Pin includes its two
   simultaneous old-value links there. It is one represented row, not
   two separately interleavable samples.
5. Update the represented PC, raw/active code switch, pending reservoir
   and functional output fields exactly as those finite effects prescribe.
   Return the complete new record list and the row's typed label.

All list traversals are word-language loops. Name equality is Equal on
actual framed words; lookup does not invoke a native occurrence oracle.
Fresh ordinals are constructed by a fold over the relevant actual
constructor records, not by a free unbounded counter in finite control.
Slot walks consume their finite encoded route words. The enlarged table
validator additionally checks the finite slot/owner/latch ranges and
successor labels. Authentic reached inputs pass these checks.

For native structural accounting the expander keeps the original ordered
probe and assignment event list as an auxiliary **per-row computation**.
It charges repeated probes and even unchanged assignments. Consistency
merging for a simultaneous field is not permission to discard an event
that the concrete row's tariff lists twice. This ephemeral accounting
list is not supplied past history or a stored new natural view.

**Lemma 12.17 (finite correct evaluator with real bank entry).** On a
represented reached state, EvalRow returns exactly the actual enlarged
native successor, its guard outcome and functional labels. It is a
finite word program whose physical RCA expansion starts from the actual
initialized bank of Definition 12.6. Every invoked loop terminates.

**Proof.** Lookup is a finite list traversal. Each role lookup traverses
a finite record list, and each route consumes a finite word. The
assignment and birth consistency passes traverse finite lists, including
finite comparisons. Each tuple update is Nth/Replace with its actual
index. Equal, Cat and framing have the decreasing word/list variants
of RCA §12.1. Thus one EvalRow call has no unbounded search for a missing
name. Missing names and malformed fields have finite typed failures.

On an authentic input, row lookup selects the installed actual row.
Every guard and old-value right side therefore equals that row's actual
value. Lemma 12.4 proves its alias partition consistent. Birth names
and full slot initialization match the actual constructors. The
post-core receipt stage preserves the correct moved read head, so core
and receipt do not accidentally cancel. The final list is the literal
actual successor, including raw partial code and every unchanged slot.
This proves the one-row statement; induction proves any finite supplied
prefix, including canonical startup.

There are finitely many word variables after hygienic expansion of these
finite helpers and finite case tables. Allocate them their first-use
indices and use the old-bank snapshot assignment convention: even
self-cons and self-tail read the previous complete bank. The actual
R empty-bank prelude has already established the compiler's boundary
relation; parsing never substitutes for it. Every assignment has its dry
length scan, real emission, descriptor, seal and parity switch. RCA
§11.4 therefore compiles this algorithm to a finite native graph, with
all partial bank phases present between boundaries. It asserts no
constant space or atomic word operation. $\square$

The physical external cursor is not a represented-word variable.
Demand/scan phases occupy finitely many native PC/purpose cases.
Compiler latches 4–6 and R-bank work preserve data/count latches 0–1,
the saved demand continuation and all foreign incidence pairs. Data
bits are branched to literal cons or retained through direct WR before
any helper. The compiler touches 32–39; the foreign cursor uses the
new slots and the input/tally spools use 8–11. Any helper that moves a
local source head subsequently repositions from its actual successor.
This gives actual entry positions for every interleaved source read;
no pseudo-instruction is allowed to resume at an assumed old head.

**Definition 12.18 (whole-target evaluator).** From the acquired capsule,
seed and $\mathcal K$, execute Start$_R$ through the canonical fence.
Then execute the old normal representative supplied by Theorem 11.9:
P through the captured $\kappa$, Capture, the remaining $m-1$ C rows,
and the remaining P rows through $n$; in the $m=0$ branch execute only
P through $n$. These are absolute old receipt endpoints: starting at
$F$, P through $\kappa$ means $\kappa-n_F(u)$ additional P rows, its
final segment has $n-\kappa$ rows, and the Armed branch has $n-n_F(u)$.
The subtraction words are computed by the same finite unary cancellation.
All old rows are lifted by Definition 12.2, with R parked.
Use the demand-acquired input word for original public source INs and
the old canonical reservoirs for boot/private input. The interpreter
knows the finite row countdowns as words, not as unbounded PC labels.
Write the resulting complete fifteen-slot record word as
$\mathcal L_R(\mathcal K)$.

When Capture is absent, the old C startup still occurs in Start$_R$.
When Capture is present, C's later external Calls are the payload-free
entries determined by its represented phase and its actual countdown,
as in Lemma 11.8. No extra timing history is supplied. The finite C
word may end inside any bank, descriptor, copy, print, ACK or token row.
The interpreter stops at that actual row, retaining its incomplete work.

**Lemma 12.19 (complete Armed reconstruction).** For every
$x\in\mathcal D_R$,

$$
\mathcal L_R(\mathcal K(\pi(x)))=x.
\tag{AIF.45}
$$

The evaluator terminates and reconstructs actual R code/startup backing,
not just $\pi(x)$ or a symbolic unspecified R complement.

**Proof.** Start$_R$ gives the actual full fence state by Lemma 12.7.
Theorem 11.9 gives the same literal old endpoint for the displayed normal
representative as for the target history, on its full initialized domain.
EvalRow realizes each lifted row with its actual names and fields by
Lemma 12.17. It does not rename old occurrences or combine independently
chosen owner states. Lemma 12.9 says the Armed lift of that old endpoint
is unique: R remains the same reached $R_F(u)$ and all added incidences
are its constant bridge and empty anchors/cursor. Thus the whole result
is $x$.

Every startup segment terminates. The remaining loops consume the actual
finite P and C countdown words. Each EvalRow terminates, so the whole
computation does also. The original key decoder and its shuffle theorem
are being applied, not reproved or extended to R maintenance cuts.
$\square$

### 12.7. Acquired package, actual publication and return

**Definition 12.20 (physical package and invocation).** Import the
count/input spools, retain the obtained canonical content
$\mathcal K$, and append a package on the R archive with the acquired
fixed apparatus identifier, seed/source binding, Pin-anchor binding,
actual sender owner/arena/Base/length/creation descriptor and completed
seal. Its Pin binding is an actual one-shot invocation role plus the
two saved roots. An unacquired global chronology ordinal is not written
into that binding. The package includes the source-derived code/seed
inputs or live owned references to their immutable retained intervals;
those intervals and their access rights are part of its physical backing.
All metadata, delimiters, Base/length measurements, descriptors and seals
are actual rows. Package availability is set only after these finish.

The mathematical content $\mathcal K$, this physical package, its
provenance and its live invocation capability are distinct objects.
Equal contents do not identify two allocations or create a live token.
A historical field saying "writable" records the old placement stage;
it does not re-enable a sealed interval or transfer an old permission.

CallR is a payload-free actual entry, enabled at package Ready with its
own live invocation token. It runs Definition 12.18, serializes **all**
fifteen-slot target records into a fresh R sender on local 39 and
performs the RCA §13 channel with actual numbers shifted to R's owner.
The three placement records are the sender, local-48 mailbox and
local-40 receiver. Allocation, zero filling, metadata and seals are
not compressed into the payload-copy body.

Stage each endpoint descriptor on 37, measuring its source before that
staging appends another descriptor. Before each payload copy recover
both real bases from the staged records and Seek each endpoint.
Re-copy the sender length to 35 **after** allocation/staging and position
that newest length word. Execute the actual six-row per-bit copy body
for sender-to-mailbox, then mailbox-to-receiver, with its terminal tests.
Append the sealed completion records with actual owner/arena/base/length/
origin and flags 10. Historical setup flags 11 do not assert a current
write right. Make the receiver available only at its real completion.

After completion-record work, the printer copies the payload length
again from the retained sender placement record to 35 and positions
that latest unary word with LastScratch(35,0). It recovers the receiver
base from its retained placement record and Seeks it anew; no earlier
head survives by assumption. At each iteration RD(length) tests the
next actual mark. On 1 execute RD(receiver), OUT, MR(receiver),
MR(length) and loop; on its actual 0 terminate. The counter word is
unchanged: its moving head consumes one mark per emitted bit. OUT is
released output, not a stored word silently relabelled as a print.
Execute ACK, the mailbox completion/token row, invocation-token return
and Ready. All receiver/acknowledgement roles are installed finite
roles of this R protocol. There is no assumed future old-owner callback.
The immutable package remains available for any later finite number of
sequential Calls, each with new allocations and these same paid stages.
There are no overlapping R invocations or new Pin flights.

**Theorem 12.21 (paid internal acquisition and callable whole-Armed use).**
Fix any valid canonical seed, any $x\in\mathcal D_R$ and its enabled Pin.
After Pin, assume each next prescribed enabled R row occurs after
finitely many joint rows. P and C may take no further rows, or arbitrary
lawful finite bursts between R rows. Acquisition terminates with an
actually sealed package whose content is
$\mathcal K(\pi(x))$. After any authorized CallR, with the same progress
condition for its installed roles, the complete target record word
$\mathcal L_R(\mathcal K(\pi(x)))=x$ is actually copied, printed,
acknowledged and returned to Ready. The assertion holds for any finite
number of sequential Calls of this package.

**Proof.** The count scans terminate and retain the same target ends
under all intervening old work by Lemma 12.10. The actual seed and
fixed capsule are already acquired at startup. Lemma 12.12 gives the
correct delayed branch, even when Capture happens after an $m=0$ Pin.
Lemma 12.14 gives exactly the needed input without waiting for any
old row. Spool imports, arithmetic, package fields and their seals are
finite initialized-bank computations. Thus acquisition terminates after
a finite number of prescribed R rows, with the stated actual content.

Lemma 12.19 and the finite serializer compute the whole target word.
Every allocation/position/copy loop consumes an actually measured finite
word, prefix or length. The staged-descriptor and renewed-counter entry
invariants are those of RCA §13, on disjoint owned ports; they include
both copies, completion records and all final token rows. The printer
uses its actual positioned heads and finite length, so it emits exactly
the sender word and terminates. Old work cannot change these owned
sealed inputs, banks or invocation tokens. By progress, only finitely
many joint rows occur before each of finitely many required R rows;
hence each claimed return prefix is finite. Induct on the number of
sequential Calls, keeping the same immutable package but the actual
newly enlarged arenas and descriptors. No Call is forced to occur,
and no uniform scheduling-delay bound is assumed. $\square$

### 12.8. Both inverses, continuation task and action routes

Define $K_R(x)=\mathcal K(\pi(x))$ on $\mathcal D_R$. On its authentic
image, extract by projecting a decoded target to its old carrier and
applying §11's actual coordinate extraction. Lemma 12.19 and the old
round trip give both identities

$$
\mathcal L_R K_R=\mathrm{id}_{\mathcal D_R},\qquad
K_R\mathcal L_R=\mathrm{id}_{K_R(\mathcal D_R)}.
\tag{AIF.46}
$$

These equations concern authentic attained keys, not all syntactically
well-formed tuples. The interpreter is not asserted to decide whether
an arbitrary tuple is attainable. Physical use of the left route is
Theorem 12.21; mathematical extraction on a raw target is not an extra
public read operation.

**Definition 12.22 (independent continuation trial task $Q_R$).** On the
actual enlarged transition system, before defining a kernel, allow the
old named trials of Definition 11.3 and the new Pin, prescribed AdvanceR
and CallR trials with exactly their installed phase/token guards.
Responses retain enabledness, authority, functional label, released
output, complete fifteen-slot successor and that future row's structural
and owner charge. Complete successors are mathematical **audit** data.
A controller has only its installed public reads and cannot branch on
this audit serialization. Finite adaptive trials use only actually
available public responses; disabled trials are unexecuted `none`.
Noncanonical executed Supply remains an exit from the lawful experiment
domain. These rules define $Q_R$ independently of $K_R$.

**Theorem 12.23 (task kernel and compatible routes on Armed).** For
$x,y\in\mathcal D_R$,

$$
Q_R(x)=Q_R(y)
\quad\Longleftrightarrow\quad K_R(x)=K_R(y)
\quad\Longleftrightarrow\quad x=y.
\tag{AIF.47}
$$

For every old lawful action $e$, decoding and executing its unique
Armed lift agrees with the old key update followed by $\mathcal L_R$.
All routes preserve actual identity, guards, outputs and complete future
successors; future fifteen-slot charges are evaluated on that successor
route. Pin exits the domain and is not an Armed key-only update.

**Proof.** Equal keys reconstruct equal complete states by AIF.46.
Identical actual states have identical partial future experiment maps,
including labels, enabledness, raw exits and future tariffs. Conversely
Pin is enabled at every compared state. Equality of the one-Pin audit
response implies equality of its old projected successor. Pin changes
no old eleven-slot field, old receipt or old controller, so that
projection is exactly $\pi(x)$, respectively $\pi(y)$. Equal old states
give equal old keys; AIF.46 gives $x=y$. This cancellation does not
interpret Pin's own receipt as an old receipt and does not expose an
audit response to an acquiring controller.

For the action square use Proposition 11.12 and Lemma 12.9. A non-source-IN
P row increments $n$; a source IN appends its actual bit to $I$ and
increments $n$. Capture changes $(\bot,0)$ to $(n,1)$; another executed
C row increments $m$. Startup seed and fixed source binding persist.
The unique Armed lift of the updated old endpoint is precisely the
executed enlarged endpoint. Evaluating that same concrete row gives
the same new tariff. Disabled trials do not change either side; raw
noncanonical IN successors obey the projection equation but leave the
lawful domain. Pin's successor includes new R receipts and acquisition
phases, so AIF.46 is not applied to it. $\square$

The target returned by CallR is historical. Its old tokens, heads,
permissions and grants are represented as they were at Pin. Printing
them does not reinstate a live right. Nor does CallR invert its own
later acquired backing or recover the joint state at its return.
The pre-Pin inclusion of R in AIF.45 does not change this domain limit.

### 12.9. Independently meaningful space, time, boundary and memory

**Definition 12.24 (the views and their domains).** Define the following
observations directly on reached $A_R$ histories, before applying a
recovery map.

- $S_R$ is the actual rooted ordered storage forest, with both primary
  components, their cell/register gadgets, actual occurrence names and
  all fifteen labelled incidences. The added bridge makes its port graph
  connected; it does not merge its primary roots.
- $T_R^{\rm exact}$ is the actual total chronology of construction and
  all P/C/R rows, operands, released outputs and receipts. When complete
  historical audit states or charges are requested, those are extra
  historical observations as in §11.
- $B_R$ is the primary terminal-antichain observation for each of the
  two actual roots, together with the current live access/capture/
  cursor/token/availability relations of Definition 10.25 extended by
  the specifically added bridge, two end pairs, one cursor pair and R
  invocation/gate relations. It is not defined as $K_R$ or a decoder
  output, and does not grant a global cursor to its mathematical reader.
- $M_C^{\rm old}$ is the old C's actual acquired backing, partial and
  completed records, bound references and currently held read/call
  rights under the old interface. Merely adding R does not make R's
  package part of this observation.
- $M_R$ is R's actual retained backing, including code capsule, source
  copies, all banks, scratch, descriptors, partial objects, packages,
  receivers, bound references, provenance and its current live rights.
  At interior phases it includes actual unavailability and dirty data.
  Its canonical package content is an obtained field of this observation
  only after the completed acquisition, not at every R cut.

Primary terminal paths have their ordinary spatial meaning: finite
prefix closure reconstructs their primary ordered tree. Their extra
labelled access incidences are a separately declared boundary component,
not information produced by prefix closure. Likewise a sealed receiver
and its released OUT word have different definitions.

**Proposition 12.25 (exact gained directions and compatible triangle).**
On $\mathcal D_R$, $S_R\leftrightarrow x\leftrightarrow K_R(x)$ are
lossless actual-image correspondences. After completed acquisition,
$M_R$ with its live invocation capability provides actual acquired use
of the historical $x$ through Theorem 12.21. From that recovered $x$,
evaluation gives its target $S_R,B_R,M_C^{\rm old},M_R$ and the old
partial-time view of §11. All paths returning a target view agree.
None of these statements asserts an inverse from old $M_C^{\rm old}$
or an individual boundary alone, or a four-view inverse from exact time
to and from the current endpoint.

**Proof.** Decode each fixed cell/register gadget and each of the fifteen
slot labels to obtain the same complete occurrence record list, and
conversely construct that storage from the list, using the actual names.
This is the SSA representation supplier componentwise, not a new
acquisition theorem. Compose with AIF.46 to obtain both $S_R/K_R$
directions. The physical $M_R$ invocation assertion is Theorem 12.21.
Every displayed target view is a deterministic readout of the very
same recovered complete state; the old partial-time view is obtained
by $\pi$ and Theorem 11.15. Therefore two such routes agree at that
target. Their guards and old action routes agree by Theorem 12.23.
A forward readout does not prove that its fibres determine the source.
No reverse-kernel claim for the independent $B_R$ or $M_C^{\rm old}$,
or for all maintenance-phase $M_R$, is used. $\square$

Exact chronology retains its established ambiguity. The actual R startup
has a fixed insertion point and order and there is no R row between $F$
and Pin. Thus any nontrivial old post-Capture shuffle fibre from
Theorem 11.16 lifts to distinct $A_R$ chronologies with the same Armed
endpoint. Its old shuffle cardinality remains

$$
\binom{n-\kappa+m-1}{n-\kappa}\qquad(m>0),
\tag{AIF.48}
$$

with the original domain and empty-chain conventions. Fixing the added
startup does not choose which shuffle actually happened. A recovered
endpoint therefore gives the published partial order, not an unrecorded
total order. No binomial factor is asserted for later R/P/C maintenance
interleavings. An extra chronology supplement, acquired with its own
resources, would be another observation.

### 12.10. One-run rows, structural work and retained space

**Definition 12.26 (evaluated full bill).** Let $E$ be the one actual
foundation-to-last-claimed-return run. Use the literal construction
prefix and irreducible charge convention of Definition 10.27, now for
fifteen slots. Keep native controller coordinates
$(N_P,N_C,N_R)$ and fees $(2N_P,2N_C,2N_R)$, one receipt per executed
row of its owner. Foundation initialization and irreducible atoms are
paid once in their finite constructor prefix, not assigned fictitious
old meter ticks. Actually executed B installation rows are still R
controller rows: their R ticks, fees and receipts are included in
$N_R$ even when those rows lie in the foundation prefix. The initial
fixed priming construction precedes activation, as in Definition 12.6;
its literal structural events and irreducible charge remain in $W_{15}$
and $V_{\rm found}$.

For each actual structural event use ordered guard/field reads, ordered
depth-first gadget traversal, the written route order, alias resolution,
then core/link and post-core receipt assignments as in Lemma 12.4.
Let $p(e)$ count every traversed/probed slot, $a(e)$ every assigned
slot including initialization, unchanged values and listed repetitions,
and $\nu(e)$ every initialized new vertex. Then

$$
W_{15}(E)=\sum_{e\in E}(1+p(e)+a(e)+\nu(e)),
\qquad
V(E)=V_{\rm found}+\sum_{e\in E_{\rm tail}}\nu(e).
\tag{AIF.49}
$$

The foundation term includes both primary scaffolds, all finite
register/code/token/grant material, the matching-code source and its
loader backing. Tail includes every startup import, source copy,
retired bank and descriptor, target serialization, mailbox, receiver,
completion record and partial destination. Nothing is reclaimed or
counted twice at creation. Storing an incidence costs its slot; it is
not a zero-sized substitute for the cells to which it refers.

This bill is effective from the actual preceding successors. Use RCA
Definition 11.5's opcode/purpose recurrence with these owners and slots:
primitive row takes its literal successor and one unit in its opcode
coordinate; sequence adds the second recurrence at the first successor;
test adds its actual guard row then only its selected continuation;
Home/Tail, Field, Base, LastScratch, descriptor count and unary copy
use their displayed actual-head scans. Assignment expands all five
steps of RCA §11.3, including dry length, real bank emission, descriptor
ordinal, flags, seal and parity. A while adds the actual test and, if
nonempty, its body plus recurrence at its new actual bank. New Pin and
cursor cases expand their finite role/slot event lists of Definition
12.3. Their structural coordinates are the explicitly counted
$p,a,\nu$ for those same events. The loader consumes each installation
bit with its write/advance/DONE successor and counts all source writes.
The serializer is a word program and is expanded in this same way.

Consequently this recurrence contains no free per-virtual-Step cost:
EvalRow's list lookup, equality, replacement, consistency passes and
emission are word instructions, each with actual bank expansion. Full
publication expands Base/Allocate, descriptors, staged copies, renewed
length positioning, both channel copies, printing, ACK and return.
Intervening P/C rows are evaluated at their own actual successors and
included in $E$. Neither their structural cost nor R's cost is obtained
by summing costs of separately optimized runs.

**Lemma 12.27 (constructor price and an exact limited subtotal).** One
cell append constructs 48 vertices: its 47-vertex cell and new trailing
terminal. Its fifteen-slot initialization costs 720 assignments, and
the two child assignments on the old terminal give **722 constructor
assignments** before symbol, head, control or receipt work. The old
530-assignment eleven-slot constructor subtotal is not its price.

For the following direct scan/spool recipes only, let
$d=1$ if $m>0$, otherwise $d=0$, and $r=|I(z)|$. Their disjoint R-row
subtotal is

$$
N_{\rm pin+direct}=5(n+c)+5r+26+d(5\kappa+10).
\tag{AIF.50}
$$

It excludes every word/helper operation, setup, package and delivery
stage listed below. It is not the acquisition or whole-run price.

**Proof.** There are fifteen initialized slots at each of 48 births,
so $15\cdot48=720$; append's old terminal has its two listed child
assignments. Every running row also has its own receipt constructor,
and any ordinary EX/mirror constructor is charged separately. No bound
on all foundation work is obtained from this per-cell calculation.

For a target rank $t$, with the cursor already at actual L, the direct
count uses Prime once, TestEnd $t+1$ times, Append(1) $t$ times, and
Next $t$ times. Append means EX, WR, MR, so this is
$1+(t+1)+3t+t=5t+2$ rows. PlaceL is one row, Append(0) and Append(sep)
are six rows, and Seal one, giving $5t+10$. PlaceL includes clearing
the previous cursor pair by old-value semantics. CountC and CountP,
the optional Capture-rank count and Pin therefore give
$5(n+c)+21+d(5\kappa+10)$.

The demand J scan uses PlaceL once, then Next, ReadJ and the three-row
Append(bit) for each of $r$ bits, and Append(sep), Seal on exit. This
is $1+5r+4=5r+5$. These rows are disjoint from the count and Pin rows;
word operations that decide to demand or continue do not occur in either
subsequence. Adding gives AIF.50. Any final ClearCursor row is additional.
The formulas include every terminating TestEnd; no changing receipt byte
is tested in place of endpoint identity. $\square$

AIF.50 excludes: both foundations; code/source literal emission and
installation; loader state and capsule import; the actual manifest and
seed copy; empty-bank construction; $c_F$ evaluation, subtraction and
branching; all spool imports and word assignments; every represented
row/record/effect lookup; package metadata and seals; whole-target and
self-startup evaluation; serialization; Base/Allocate, zero filling and
descriptors; both copies and renewed positioning; OUT, ACK, completion,
mailbox/invocation TOK and Ready; all old P/C work. Every one of these
is included in AIF.49 and the successor-dependent recurrence. The
channel's $12l+6$ two-copy-body subtotal, where applicable to its payload
length $l$, retains RCA's exclusions and is not substituted for the
full return price. This section asserts no additional closed polynomial
for the entire bill.

**Proposition 12.28 (finiteness and resource limits).** Under Theorem
12.21's pointwise progress, each claimed finite number of returns has
a finite full native/structural bill and finite retained space. Finite
programs give no uniform memory bound or elapsed-time bound. The two
meter samples give no full-resource optimality or dominance over a
three-frontier/status collector, and no universal pointer minimum.

**Proof.** Lemmas 12.7, 12.10, 12.12, 12.14, 12.17 and 12.19 prove
termination of all variable loops from their actual finite inputs.
Definition 12.20's channel loops have their real finite counters and
positioned heads. Finitely many prescribed R rows, each preceded by
finitely many joint rows, give a finite actual prefix. Every structural
row has a bounded pattern in this fixed installed apparatus; its finite
number of probes, assignments and births is evaluated by AIF.49.
Retained space counts all those births, including unused and retired
material. As target counts and repeated-call arenas grow, neither this
argument nor finite control bounds their number. Arbitrarily long finite
old-owner bursts also preclude a uniform delay bound. No cross-model
optimization or past structural-cost square has been proved. $\square$

The resource reduction established here is specific: two jointly bound
meter ends suffice; an extra J end and a trigger-time phase/Capture
sample are absent. The delayed branch and demand invariants justify
those omissions. They do not show that two endpoints are necessary in
all encodings. A restricted sample-deletion lower bound would need an
explicit deletion class and common-source commuting witnesses; none is
claimed by this construction. In particular a later pointer, code word,
receipt or audit field cannot be called free merely to improve a bound.

### 12.11. Contribution and exact remaining boundaries

**Theorem 12.29 (assembled scope).** On the different canonical $A_R$
apparatus defined above, every actually reached pre-Pin Armed collector
state, with arbitrary advertised old P/C phases, is physically captured
by two simultaneous meter incidences, acquired with the paid startup
and cursor/word program, reconstructed in its entirety and available for
actual finite callable copying/printing/return. The actual-image inverse
and old-action routes are AIF.46–47. All setup, retained backing and
same-run costs have the definitions and exclusions in AIF.49–50.

**Proof.** Lemma 12.9 supplies coverage of the full old domain rather
than a Ready projection. Lemmas 12.10–12.14 supply the stable common
cut, correct delayed branch and source-derived input. Lemma 12.7 and
§12.6 supply actual entered code/seed acquisition and whole-state
startup/effect replay. Theorems 12.21 and 12.23 supply actual use, both
inverse directions and action compatibility; Proposition 12.25 states
only the gained natural-view directions. Lemma 12.27 and Proposition
12.28 establish the asserted resource claims. $\square$

The new content is the source-specific operational bridge: two common
meter endpoints, delayed recovery of the old Capture branch, demand of
exactly the already attained mirror bits, and complete canonical Armed-R
startup reconstruction with an explicit enlarged effect adapter. The
joint-state key, owner-word/chronology fibre theorems and normal replay
representative are the existing AIF §11 suppliers. SSA supplies the
ordered-tree/cell constructors and their decoding; RCA §§11–13 supplies
the initialized word compiler, finite framing operations and real
staged channel. CSA's selected memory across owners is not substituted
for possession by C. PVC's installed verifier domain, GrowingPaidViewCycle's
historical memory cycle, GTIC's fixed-Ready and successful linked-history
inverse domains, and TargetAndCurrentRecovery's old-target/current-input
distinction keep their original hypotheses.

The D5/owning-Scribe suppliers NativeFullSourceProducer (including its
private traversal/source-read argument), NativeSerialMachine's reached
prefix/deterministic replay and actual-register results, and
NativeSerialEffective's explicit code-realization bridge support only
their declared stationary-source, supplied-word and realization scopes.
TypedFiniteViewKernel and RealizedImageKernelFactorization supply typed
finite-trial and realized-image factorization principles, not new access
rights. The mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`,
`Computability/StateTransition`'s transport results, likewise requires
matched starts and transitions. They do not install Pin, code
supply, seed grants or a physical simulator for fifteen slots. No existing
private helper is being renamed as the contribution.

FARG's substitution/port-fibre framework supplies relational vocabulary,
not a derivation of these native patch, loader and capability assumptions
from alpha/beta alone. Chandy–Lamport's
[*Distributed Snapshots*](https://lamport.azurewebsites.net/pubs/chandy.pdf)
§4, Theorem 1 permits a consistent recorded state to occur in a permitted
permutation rather than in the executed sequence; its cooperative
recording/FIFO hypotheses do not install this Pin. Herlihy–Wing's
[*Linearizability*](https://cs.brown.edu/~mph/HerlihyW90/p463-herlihy.pdf)
§§1–2 supplies the operation-interval distinction,
not this source acquisition or its cost. Here the actual Pin predecessor
is specified and proved directly. These are literature-attested methods;
the combined apparatus and proofs are repository-derived paper
mathematics, without a claim of literature priority or new Lean
certification.

The additional assumptions are substantive: the disjoint scaffold and
fifteen-slot constructors, one atomic two-end Pin, narrow foreign
cursor/read grants, canonical matching-code supply and finite loader
basis, a temporary seed-manifest grant, the entered startup gate/fence,
and pointwise R progress for an invoked protocol. They are not
capabilities of unchanged $A^+$. Restoring a represented old permission
never supplies a present capability. The complete new R maintenance
domain, arbitrary noncanonical initializations, current-at-return joint
recovery, independent original $B_{\rm now}$ and $M_C$ kernels, exact
chronology without a supplement, original fixed-$G_{gc}$/original-$Q$/
parked-consumer obligations, universal physical realization and the full
four-expression programme remain unsettled in their original scopes.
No prior settlement is changed by this conditional construction.

## 追加锚（本行以下为增补区）
