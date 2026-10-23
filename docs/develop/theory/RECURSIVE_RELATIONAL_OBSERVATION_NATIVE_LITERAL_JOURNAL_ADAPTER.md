# Native literal access and a paid journal on one installed source

> This volume is reference input, with ordinary mathematical proofs for an
> explicitly declared ideal machine. It makes no new Lean certification claim.
> Its merged text is append-only; corrections belong after the append anchor.
> The definitions and source correspondences use public revision
> `b7d37ca0fee9638f28af45d4a63f7f0eb974c972`.

## 1. The supplied structures and the additional permission

**Definition 1.1 (source and capacity).** Let $\mathcal T$ be the free nonempty
ordered binary-tree algebra on the distinct leaves $\alpha,\beta$, with pairing
$\langle s,t\rangle$. Write $\lambda(t)$ for its leaf count. Fix a public integer
$H\ge1$, put $N=2H-1$, and set $\mathcal T_H=\{t:\lambda(t)\le H\}$.
The substitution is

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

An address is a finite word in $L,R$, including the empty root address.
The literal response $\operatorname{tag}(p,t)$ is the labelled leaf or branch
at $p$, and is `absent` if descent encounters a leaf before the word ends.
All finite addresses are legal. Pairing, order, addresses, substitution, control,
tapes and permissions are declared additional structures; alphabet minimality
is not a universality theorem about two relations.

**Definition 1.2 (positive suppliers).** The following suppliers have distinct
interfaces. The accompanying Scribe in each listed directory owns the stated
Lean exposition; reading these sources supplies no new compilation claim.

| Public source | Exact use and boundary |
| --- | --- |
| `D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean`, `Address`, `Reply`, `readout`, `source_foundation`, `acquisition_foundation`; owning `Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs` | The four literal replies, actual-tree separation, and truthful traversal/reconstruction are existing results. Its `Strategy` returns the Boolean `Positive U`, meaning $U=\rho^3T$ for some actual $T$. That target is unchanged here. |
| `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean`, `Op`, `Event`, `nativeStep`, `Run`, `Replay`, `actual_register_execution`; owning `Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs` | Actual same-register literal Read and unconditional substitution, including every native local step. Control sees only control. The source equation and supplied old trace in `actual_register_execution` do not authenticate arbitrary entry history. |
| `D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean`, `sourceControl`, `initialControl`, `productionTrace`, `native_source_producer`; owning `Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs` | One common stack traversal already returns the entire ordered tree and visits every real node once. Both local actions at each branch occur in its trace. |
| `D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.lean`, `sourceName`, `numericTick`, `sourceService`, `FullSourceAcquisition`, `effective_source_producer`; owning `Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.scribe.cs` | The stronger existing partial-recursive selector returns a lossless numeric syntax name. Its external history omits producer locals. Its `sourceDecoder` uses classical choice, and the module supplies no particular installed evaluator code or paid access bill. |
| `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.lean`, `OriginalState`, `OriginalCodeRealization`, `original_code_service_simulation`; owning `Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.scribe.cs` | An actual supplied code and its genuine-state realization equation connect effective selection to execution. Bounded-evaluator `none` is local work; accessible finite history in this interface is not a paid history-storage implementation. |
| `RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md` §57, PR57.D1–D9, L1–L4, T1–T5 | TM57 supplies paid installation, actual ReadE, guarded whole substitution/grafts, gates, tapes, metering, ownership, append/seal/copy, and record verification for its own row language. It has no literal-address Read port. These are ordinary mathematical suppliers. |
| `RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md` §§34,43 | Full/run-next concern one actual joint history, including complete successors and failures. Mutual view recovery and sufficiency do not alone establish individual task minimality. |

**Definition 1.3 (declared extension).** Extend the TM57 producer with the public
request `TagRead(p)`. Its new permission allows the producer, while exclusively
owning the existing private source arena, to evaluate the circuit of §3 on that
arena. The actor acquires only its complete two-bit result. The original ReadE,
guarded $\rho$, `Left(v)` and `Right(v)` remain separately typed ports with their
original responses. No source navigation, physical inverse or reroot is added.

The extension also installs a typed journal writer, controller-local and terminal
markers, and a verifier/consumer mode specified below. Its finite description,
inputs, code generation, descriptors, work and communications are paid TM57
occurrences. This is an added source instrument and record language, rather than
a derivation of literal access from numerical ReadE or an unchanged old verifier.

The control description is common to all $H$ and sources. Expand its fixed
sequences, public tests and public while/for loops by PR57.D1's finite graph
rules; public tree/stack processing uses constructed frames, not native recursive
calls. Enumeration, locator, `Emit`, copy and row routines have fixed finite
nesting and reuse PR57.D2's service graphs. Their integer parameters, dynamic
gate tapes and stack depths are data on constructed tapes, not a family of
native states indexed by $H$. Public $H$, priors and program descriptions are
fixed independently of the hidden actual source within their declared domain;
their actual ingress and retention are charged.

## 2. Literal representation and public address computation

**Definition 2.1 (the installed block).** Use TM57's token encoding
`PAD=00`, `alpha=01`, `beta=10`, `PAIR=11`. A valid block consists of preorder
tokens of one tree, followed by PAD to exactly $N$ tokens, hence $2N$ bits.
Before closure PAD is forbidden; after closure every token is PAD. The complete
packet is installed by the original private bit ingress and fixed validation.
No second tree is installed for the literal service. The initial source identity
names this actual preparation occurrence, independently of its value.

PR57.T1 gives a bijection between valid packets and $\mathcal T_H$. Its parser
transduction is PAIR to `[false]`, alpha to `[true,true]`, beta to `[true,false]`;
the resulting active word is the code of the same `FreeMagma Bool` source.
In particular the two-bit token alphabet is not that parser's bit code.

**Definition 2.2 (public candidate locator).** For a valid *public candidate*
packet $z$, compute $\operatorname{loc}(z,p)$ as follows. Initially the cursor
is at token zero. If no address letter remains, return that token's kind. If the
cursor is a leaf and a letter remains, return `absent`. At PAIR, the left child's
root is the next token. To find the right child's root, scan the left subtree
starting with `need=1`; PAIR adds one and a leaf subtracts one. Stop when need
first reaches zero; the following token starts the right child. Consume the
chosen letter and repeat. An `absent` result remains absent for remaining letters.

The stored $p$ and $z$ are public finite strings. Cursor offsets, need counters,
increments and tests use the unary tape routines of PR57.D2. Every scan and every
address-field construction is executed and charged. This locator is not run with
private source-dependent control on the installed packet.

**Lemma 2.3 (locator correctness and termination).** For every valid public $z$
and every finite address $p$,

$$
\operatorname{loc}(z,p)=\operatorname{tag}(p,\operatorname{decode}(z)).
$$

Its computation is finite, including for the root and arbitrarily long absent
addresses.

**Proof.** The preorder word of a branch is PAIR followed by the complete left
word and then the complete right word. In a nonempty subtree word, need counts
unfilled child slots. Before its final token there is a slot still to fill, and
at its final token need becomes zero. Consequently the scan stops exactly at the
end of the left word, within the valid packet, and the next token is the right
root. The left-root step is immediate. Induction on the consumed address letters
therefore preserves the correct subtree root. At a leaf, any further descent is
absent by the definition of `readout`; at the end the token kind is exactly the
root response of the remaining subtree. Each scan consumes part of a finite
candidate, and there are at most $|p|$ scans. Unary operations terminate by
PR57.L1. This proves both assertions. $\square$

## 3. An explicitly paid same-source literal instrument

**Definition 3.1 (response encoding and public enumeration).** Encode literal
replies as alpha `00`, beta `01`, branch `10`, absent `11`, the binary codes
$0,1,2,3$ used by `originalReplyCode`. This is separate from the source-token
encoding. Enumerate all $4^N=2^{2N}$ token packets $z$ in base-four order using
PR57.D8's increment routine. Completely parse each public candidate. For a valid
candidate let $b(z,p)$ be the two-bit encoding of its locator result. For an
invalid candidate put $b(z,p)=00$.

The generator receives $H,p$, public descriptors and already acquired history;
it does not receive the private packet $x$. Both $4^N$ and its loop counters are
actually constructed unary strings, for example by repeated multiplication by
four. Enumeration, parsing and locating are public computation on every row.
Public invalid candidates are processed too; they are not possible actual sources.

**Definition 3.2 (direct gate tape).** Use the already installed source interval
and allocate all fresh result bits after it in the same producer-owned private
arena addressable by the existing PR57.D4 gate interpreter. Source cells retain
their original fixed descriptor and are never gate destinations. All scratch
descriptors are obtained
by `Base`/`Allocate`, never by converting a mathematical cursor into a free number.
Allocate and zero a shared dummy operand cell first. Emit directly, without a
recursive expression-expansion wrapper, the following finite tape:

1. One constant-zero gate for the shared zero value, and one constant-zero gate
   for each of the two output accumulators.
2. For every enumerated packet $z$, emit a fresh constant-one $e_{z,0}$. For each
   private bit position $i<2N$ emit one gate

$$
e_{z,i+1}=
\begin{cases}
e_{z,i}\land x_i,&z_i=1,\\
e_{z,i}\land\neg x_i,&z_i=0.
\end{cases}
$$

3. Emit two fresh OR-fold outputs. For response coordinate $j$, OR its previous
   accumulator with $e_{z,2N}$ if the public $b(z,p)_j=1$, and with the shared
   zero otherwise. Both gates are emitted for every row, including invalid rows.
4. Append the terminal program header. Execute all records in order. The final
   two accumulator bits form the response; seal the complete typed block before
   releasing its availability token.

Each expression in step 2 is one permitted Boolean truth table; NOT is inside
that table. References to $x_i$ are operand addresses and add no projection
gate. Every gate destination is fresh. Unused operand fields reference the
constructed zero cell. The two output bits and every equality value remain private
until the complete response commits. Transmission and journal writing are subsequent
paid actions. Preallocating a zero cell is initialization, not a fourth constant
gate hidden in the count below.

**Theorem 3.3 (literal instrument, gate count and source preservation).** For
every $H\ge1$, every valid installed block $x$, and every paid finite address $p$,
Definition 3.2 has a finite execution and returns exactly
$\operatorname{tag}(p,\operatorname{decode}(x))$. It leaves all installed source
bits unchanged. Its Boolean tape has exactly

$$
G(H)=(2N+3)4^N+3
$$

gate records and one end header. This is a gate-record count, not a runtime,
fee, code-length or workspace bound of $G(H)$.

**Proof.** Induction on $i$ gives
$e_{z,i}=1$ exactly when $z$ and $x$ agree on their first $i$ bits. Enumeration
contains $x$ exactly once. Since $x$ is valid, that row's public locator gives
the true literal tag by Lemma 2.3. The final OR accumulator at coordinate $j$
is $\bigvee_z(e_{z,2N}\land b(z,p)_j)$; exactly the actual row can contribute.
Thus it equals $b(x,p)_j$, including the all-zero alpha result. Invalid rows
cannot equal the valid $x$ and cause no ambiguity.

Three initial constants and, per row, one constant, $2N$ conjunction gates and
two OR gates give the stated count. End-of-program is a header, not a gate.
The enumerator has a fixed finite row count. Public parsing and the locator
terminate, and each record has four finite constructed unary addresses. The
generator writes each record through `Emit`/`AppendWord`; PR57.L1 and the literal
interpreter then give finite execution of the finite tape. No gate writes a
source cell, so all source bits are preserved. $\square$

**Theorem 3.4 (noninterference until commitment).** Fix equal public boot
parameters, public acquired history, arena-layout descriptors and next address
$p$ in two valid executions. Up to literal-response commitment, the extended
public microtraces agree: instructions, touched addresses, availability, allocation,
control, ticks and fees agree. At commitment the only new source-dependent public
value is the complete literal reply. Thereafter public computations are functions
of acquired responses and public inputs.

**Proof.** The enumeration, parser branches, locator branches, record masks,
destination allocation and all instruction addresses depend on public $H,p,z$
and the common layout. Hence the generated code and its construction schedules
agree. During private execution every loop bound and seek comes from that code.
Private latches only feed `BF` and private bit writes; they never choose a control
edge, port, address or stopping test. The response has two fixed positions, and
the same complete-write/seal/release schedule runs in both executions. Induction
on primitive occurrences proves the precommit equality. At release Theorem 3.3
supplies the one newly available literal response; every later test is public.
$\square$

Public microtrace here has TM57's privacy convention: it reveals a private
write's opcode and location, not its private bit value or latch contents.
Full actual histories retain those private values. Theorem 3.4 is not equality
of those full private histories. Giving a public observer private scratch
equalities would violate the declared interface.

**Corollary 3.5 (enlarged causal observation correspondence).** One source-uniform
prefix-causal simulator reconstructs every public primitive label from public
initialization, actually supplied public input and the extended committed-response
stream. It consumes a ReadE value, TagRead value or modification accept/reject
only at that call's response release. Restricting requests to the old ports
preserves their source responses and successors, with the extension's additional
paid boot and journal overhead.

**Proof.** Use PR57.T3's simulator for the original schedules and Theorem 3.4
for TagRead. Before a release both use only the existing public prefix. At
release conformance supplies the appropriate typed response, which determines
all subsequent public response-dependent work. Induction on occurrences, with
this single extension at each release, gives the simulator. Its restriction to
any finite prefix is the same simulation truncated there. No representative
source or future response is used. $\square$

## 4. Requests, partial work, counters and complete outcomes

**Definition 4.1 (serial phases).** A source request is admitted only at an idle
cut with the source token and the completed previous row available. Its phase
sequence is request ingress/validation, busy generation/execution, complete
response commitment, counter/row construction, row seal, serial delivery and
acknowledgement, then idle. Only the prescribed next primitive transition is
enabled at an unfinished service cut. A scheduler does not admit a second
semantic event before row seal, and this implementation additionally waits for
delivery acknowledgement before the next source request.

A modifying source block is unavailable from its first write until the complete
successor block is written. During those writes it need not decode as a tree.
Its actual bits, remaining code, heads, latches and phase are part of the busy
state. The old and candidate trees used in a correctness proof are proof
parameters, not automatically available second source registers. At idle and
response-commit cuts the source block again decodes to a valid tree.

**Definition 4.2 (distinct indices and their actual material).** Let $q$ count
completed source calls, including ReadE, TagRead and executed rejects; let $g$
count accepted modifications of any kind; let $e$ count accepted $\rho$ calls;
let $j$ count all completed semantic events, including exposed controller-local
and Halt markers. The primitive meter counts $n$, separately. At boot they are
zero. All accessible names use actual unary strings and complete descriptors.

An increment is not a one-step integer primitive. Before a commit, construct
both old and incremented versions of needed public counters using PR57.D2.
For a modification, prepare both possible next $g,e$ versions without testing
the private guard. After response release, the acquired accept/reject selects
the applicable version through paid public copying/descriptor work. At cuts
within that work, the old and prepared strings, committed response and phase
specify which version represents the semantic count. The row is written only
after the selected fields are fully materialized. The finite release `CTL`
changes availability, not an unbounded numeral. Event indices in proofs do not
supply their stored wire representations for free.

**Definition 4.3 (typed outcomes).** The semantic source labels and successors
are as follows; every result in the table is an executed call.

| Port | Complete response | Source and counters at response commitment |
| --- | --- | --- |
| TagRead($p$) | one of alpha, beta, branch, absent | same source; $q+1$, same $g,e$ |
| ReadE | exact current Clifford $E$ in its complete coefficient encoding | same source; $q+1$, same $g,e$ |
| $\rho$ | accept if the whole $\rho t$ has at most $H$ leaves, otherwise reject | accept installs $\rho t$ and gives $g+1,e+1$; reject retains $t,g,e$; both give $q+1$ |
| Left($v$), Right($v$) | accept/reject for the entire actual candidate | accept installs $\langle v,t\rangle$ or $\langle t,v\rangle$ and gives $g+1$; reject retains $t,g$; both give $q+1$ and unchanged $e$ |

Every row in this table also increments $j$. Rejection exposes no candidate
value. The complete context packet, name and code reference are retained for
grafts, even when the candidate is too large. Equality at capacity accepts.

A `NativeLocal` marker commits after one declared controller instruction has
actually completed; it changes its encoded control/workspace, increments $j$,
and changes none of $q,g,e$ or the source. Its many tape microsteps are distinct
from this one marker. A `Halt(o)` marker commits only when the complete finite
output block $o$ is written and sealed. It increments $j$ but is not a Native
`Event`; terminal recording/delivery still finishes before global halt.

**Definition 4.4 (failure and availability types).** An idle legal source call
has a total finite service under this model. Its complete step is
`some(label, actual successor)`, including reject. A busy semantic source call,
an unavailable destination read, or a write without its ownership token is
illegal and unexecuted: its step is `none`, with no event or row. A request
waiting before response commitment is pending work, not a completed event.
TagRead absent is a valid response, not a missing source or an illegal operation.

Before valid installation the state is `uninstalled` or `boot-busy`, with no
source-call permission. Malformed preparation finishes in a separate
`invalid-preparation` outcome and yields no valid-source receipt. A bounded
evaluator miss is local control work and may lead to another attempt, without
an external reject. Stop is a complete typed terminal output; Native
`nativeStep` returning `none` at Stop expresses termination and must not be
read as the adapter's illegal-call convention. No crash-recovery or arbitrary
interruption-resume service is assumed.

**Theorem 4.5 (same installed source and finite service progress).** For every
valid paid boot and every finite lawful extended request sequence with finite
public control and supply work, there is a unique finite service execution.
At each completed call its current tree, response and complete successor have
exactly Definition 4.3's values, on the same preparation occurrence. ReadE
and TagRead do not mutate the source. All partial service cuts have the types
of Definitions 4.1–4.4.

**Proof.** Boot is the original actual packet installation. PR57.T1 establishes
validity and fixes its decoded source and occurrence identity. Theorem 3.3
handles TagRead on that very block. PR57.T2 handles ReadE and each whole
modification, including rejected in-place MUX writes that retain all old bits.
No routine changes the preparation identity or substitutes an independently
installed tree. Counter work consumes finite sealed unary strings. The row and
delivery routines consume finite constructed payloads and closed earlier fences;
PR57.L1 and L4 give termination. These arguments apply call by call, and every
prescribed routine is deterministic with a unique next primitive occurrence.
During generation, writes, append and copying the explicit phase and token
rules give precisely the stated unavailable/pending types. Only after complete
writes does a response commit. Induction on the finite sequence proves all
assertions. $\square$

## 5. The actual journal and its pending complement

**Definition 5.1 (row language).** A producer row is a length-framed tuple with
these complete fields:

1. Extended model/control version, $H$, immutable preparation identity and
   `INITIAL-SOURCE` occurrence reference; its event ordinal $j$ and predecessor
   sealed-row reference.
2. A port tag distinguishing TagRead, ReadE, Rho, Left, Right, NativeLocal and
   Halt; the complete submitted $p$ or context packet/name/code reference, or
   controller-instruction reference or full terminal-output block reference.
3. The exact committed response, or local marker/terminal output; before/after
   $q,g,e$; the actual source-block descriptor and its unchanged preparation identity.
4. Schedule/template identity, earlier start and response-commit fence references,
   and the row creation reference. The final seal is an actual occurrence in the
   row's external availability/descriptor chain, not an in-row numeral naming a
   future receipt. Context/output references point
   to actually sealed complete material delivered with the row when needed.

Strings use `U(length)` followed by that many bits; fixed tuples have fixed
arity, and port tags have separate fixed codes. The parser rejects a TagRead
row with an E payload, a reject with a candidate value, or a Halt substituted
for a literal reply. Natural fields use the actual unary strings of §4.
No field contains its row's own future complete fee total or its full successor
archive recursively. Creation and final seal identify actual occurrences by
ownership/descriptor chains; closed-fence numerical readouts refer to earlier
cuts. Serializing a seal's occurrence number, if requested, is a later paid
readout referring to that already closed cut. Later copies preserve the origin
chain rather than inventing a new origin.

Only the producer writer can append this language. After commitment it reads
the acquired response and retained request, materializes the fields, and appends
them with the existing paid routines. Earlier sealed rows are immutable. There
is no arbitrary external transcript-import operation.

**Definition 5.2 (three different words at a microcut).** For a full actual
primitive history $h$ from valid boot, let $E(h)$ be its ordered completed
semantic events, committed as in §4. Let $A_P(h)$ be the event word decoded
from complete sealed producer rows. Let $P(h)$ be empty unless one event has
committed and its row has not sealed; in that phase it is the singleton event
with its complete retained request, result and counter interpretation. A
request admitted but not yet committed lives in a separate busy-work field
$B(h)$ and contributes nothing to $E(h)$ or $P(h)$.

The archive coordinate includes actual producer, actor, mailbox and verifier
intervals, their physical partial contents, and their seal/copy phases. A
receiver's readable prefix is only the contiguous prefix whose complete
framing/material has sealed there. An incomplete destination is unavailable.
A copied row preserves its origin and is not a new source event. No equality
between all archive lengths is imposed during transit.

**Theorem 5.3 (journal coupling at every primitive cut).** At every actual cut
of the adapter,

$$
E(h)=A_P(h)\mathbin{+\!+}P(h),\qquad |P(h)|\le1.
$$

Every completed producer row describes the event actually committed on that
installed source; every readable receiver prefix is its designated sealed
producer prefix bit for bit. At a quiescent cut $P(h)$ is empty. Source epoch,
source-call count, semantic-event count and archive/copy progress remain distinct.

**Proof.** Valid boot has empty event and row words. Request ingress,
generation, execution and any partial successor writes precede commitment;
they change actual work and receipts but add no semantic event or sealed row.
At commitment append the one actual event of Theorem 4.5 to $E$ and put it
in $P$. For NativeLocal or Halt use its completed controller or complete-output
commitment, respectively. The admission rule prevents a second event while
this pending event remains. Counter materialization and proper row-prefix
writes preserve $E,A_P,P$. The final row seal appends precisely that pending
event to $A_P$ and empties $P$, preserving the equation. Its fields come from
the retained actual request and response, not a claimed transcript.

Each copy begins with a sealed immutable sender and an allocated inaccessible
destination. The serial loop copies exactly each designated bit; PR57.L4
therefore supplies equality at final destination seal, with unchanged framing
and origin identities. A partial copy changes no readable receiver prefix.
An executed reject follows the same commitment/row sequence, whereas an
unexecuted illegal action has no transition and contributes nothing. Induction
over primitive cuts gives the invariant and authenticity assertions.

The counters follow their different cases in Definition 4.3. Repeated reads
and rejects advance $q,j$ without advancing $e$; locals advance only $j$;
copies advance the primitive meter and destination progress without adding
source events. Thus none of those counts can replace the others. $\square$

**Proposition 5.4 (paid journal access).** A sealed journal prefix, complete
material references and its ownership token constitute callable finite memory:
a caller can request the $i$th row or a complete prefix, obtain its complete
typed payload, and continue with the same source/version binding. Invalid
indices return a separately declared `no-row` result without a source event.

**Proof.** Install a public scan routine driven by the constructed $U(i)$ and
the already sealed end descriptor. Scan complete length-framed rows in order,
advancing a paid unary counter and skipping each payload by its stored finite
length. Stop at the requested row or the closed end. Copy a found row and its
required material through a fresh allocated mailbox and destination using
PR57.D7. Each loop consumes a sealed finite bound, so PR57.L1 gives termination;
PR57.L4 and Theorem 5.3 preserve its bits and binding. The end case yields
`no-row`, a memory-service outcome rather than TagRead absent. Its complete
successor includes changed scan/work/copy/meter state. These service events
are retained in the primitive history; they do not masquerade as Native locals
or additional source calls. All scans, comparisons, allocations, copies and
output writes are actual paid occurrences. $\square$

## 6. One joint actual history image and successor closure

**Definition 6.1 (concrete joint carrier).** An endpoint carries the installed
root occurrence and model identity; phase/type; all actual tape contents,
marked heads, PC, latches and constructed counter versions; archive intervals
and partial copies; actual descriptors and predecessor/copy references;
owner/availability tokens; meter and last primitive label. Its logical
source/generation tags are decoded from the source at available cuts and from
the committed/pending phase data elsewhere, as specified in §4. Full actual
histories additionally determine $E(h)$, $A_P(h)$ and $P(h)$.

Define $\mathsf{Compat}$ by the following simultaneous conditions on this
carrier: descriptors name actual constructed intervals of their declared
owner; initialized/sealed flags match the actual interval; writable and readable
tokens follow the serial phases; every completed row has its actual predecessor,
port type, counter transitions and preparation identity; readable copies equal
their designated sender prefix; the source is decoded only in available phases;
and the pending/busy fields satisfy Theorem 5.3 and the corresponding code cursor
in the retained finite routine. Its values are taken from one history $h$, not
from independently selected possible sources, archives, references or permissions.

Let $\mathsf J_H$ be the compatible endpoint image of actual histories from valid
boot. References and permissions have their concrete encoded interval/token types,
including unavailable types. Boot-busy, invalid-preparation and terminal-service
states form separately tagged components when those histories are considered.

**Definition 6.2 (concrete next relation).** For each primitive opcode, the
next relation rewrites precisely its addressed adjacent cells, latch, head,
finite PC and token as in PR57.D1; appends the one mandatory receipt; and applies
the phase transitions of §§4–5 at commitment and seal. All other cells and
descriptors remain unchanged, except the specifically written counter/row/copy
prefix. At semantic calls the relation is the finite prescribed fragment
through row seal/delivery, labelled with its complete response and complete
endpoint, including work, archive, reference and permission changes. Illegal
requests have no admitted fragment.

**Theorem 6.3 (Full, NextCompat, run-full and run-next).** Every actual valid-boot
history supplies one compatible joint endpoint. For every enabled primitive
transition its full successor is again in $\mathsf J_H$, and the pair satisfies
Definition 6.2. Every executed semantic success or reject has its complete
successor in the same image; an illegal unexecuted action has no such event.
Consequently these concrete coordinates satisfy the Full and NextCompat
obligations, including PG.3402-run-full and PG.3402-run-next, for this extended
runtime and its declared types.

**Proof.** Choose the references and permissions actually carried at the
endpoint of $h$. They have the required types: `Base` constructs a finite
existing offset before allocation; allocation appends fresh intervals and
their complete descriptors; positioning checks their constructed bounds;
the actual token transitions alone grant each read/write/copy permission.
At boot the valid packet and empty journals satisfy every compatibility
condition. For ordinary code/arithmetic/gate steps the local opcode rules
preserve disjointness, descriptor bounds and ownership, and their actual code
cursor gives the unfinished-work condition. Busy source writes preserve the
busy type; their completion satisfies Theorem 4.5. Theorem 5.3 handles event
commitment, row prefixes, seal and serial copies. Meter preservation is PR57.L2.
Thus induction on actual primitive transitions proves compatibility jointly,
including partial work and unavailable receiver states, not just at idle cuts.
This constructs the Full witness for every $h$.

If its next primitive is enabled, append that occurrence to obtain the actual
history $h a$. The local rewrite, receipt and any specified commitment change
are exactly Definition 6.2, and the preceding preservation argument supplies
the compatible successor witness. Any compatible witness carrying $h$ has
these actual endpoint references/tokens by definition of compatibility, so the
same successor works for each such witness. This proves run-next as well as
the endpoint next relation. Composing the finitely many primitive pairs through
a legal service fragment gives its full semantic successor by Theorem 4.5;
on reject the unchanged tree coexists with the new row, work, references and
meter. No projected successor is substituted. An illegal operation has no
enabled first primitive or admitted fragment, as required. $\square$

This realizes a joint runtime image. It does not prove that the sealed semantic
journal alone reconstructs private gate scratch or every raw private write, nor
that any of its coordinate projections has the exact kernel of a chosen task.

## 7. Capacity-safe Native correspondence and actual acquisition

**Definition 7.1 (Native cuts and controller requirement).** Restrict the source
menu to TagRead and accepted $\rho$, together with declared NativeLocal and
Halt markers. Start from the actual boot source $u$, epoch zero and empty
authenticated journal. A finite Native run is capacity-safe if every current
tree and every substitution candidate in that run belongs to $\mathcal T_H$.
The abstract register at a completed semantic cut is the decode of the same
installed TM block. The abstract control is the fully acquired controller
workspace, $e$ is its rho epoch, and the Native trace projection maps TagRead
to `read(e,p,y)`, accepted Rho to `update(e_before)`, NativeLocal to `localStep`,
and omits Halt while retaining its complete output separately.

For implementation the controller has an actually supplied finite effective
description over finite encodings, with terminating computation at each reached
instruction. A general $\delta:C\to\operatorname{Op}(C,O)$ with arbitrary types
and no effective finite representation is not asserted to have a tape
implementation. A general selector backend additionally consumes its actual
code and genuine-state realization equation; the existence of a `Partrec`
certificate or a classical code choice does not install that description.

**Theorem 7.2 (finite capacity-safe Native realization).** Every finite
capacity-safe Native run of such an installed controller has a finite paid
adapter execution with the same literal replies, accepted updates, complete
Native trace and whole output. At each corresponding completed cut

$$
t_{\rm current}=\rho^e u,
$$

and the acquired journal has the actual binding of §5. Every primitive
microcut of the realization remains in the full history of §6.

**Proof.** At valid boot the relation holds with $e=0$. For a Native local
instruction, execute its actual finite public computation on acquired control
and commit its one local marker, with no source change. For a Native Read,
Theorem 3.3 produces exactly `readout p` on the related register; its acquired
reply selects the same encoded continuation. Both cases preserve epoch and
the source equation. For ApplyRho, capacity safety makes the whole guard
accept. PR57.T2 installs exactly $\rho$ of that register and advances $e$, so
the equation becomes $\rho(\rho^e u)=\rho^{e+1}u$. The journal retains its actual
old-epoch update label. For Stop, write/seal the complete encoded output and
commit Halt, then finish its record and delivery. Halt adds no Native event.
Induction on the finite Native `Run` concatenates the finite fragments of
Theorem 4.5. Their trace projections are the stated Native constructors, so
all locals, repeats, epochs and replies are preserved. Theorem 5.3 supplies
authentic recording, and Theorem 6.3 retains every intervening cut. $\square$

The abstract trace projection is not identity of Native instructions with
PR57 gate/evaluator microsteps. On this subinterface $g=e$; outside it an
accepted graft changes the source while leaving $e$ unchanged, so the displayed
Native source equation is not claimed there. A rejected rho cannot be labelled
as an unconditional Native update.

**Corollary 7.3 (paid realization of the existing strongest source producer).**
For every actual $U\in\mathcal T_H$ with $m$ leaves, the adapter can execute the
existing common full-source producer from root and empty stack. It returns
the entire labelled ordered $U$ and makes exactly $2m-1$ TagRead calls,
$2(m-1)$ NativeLocal markers and no source update. Its source-call transcript,
full producer chronology and complete terminal output have authentic paid rows.
The numeric producer can instead return its existing lossless `sourceName U`
through additional paid numeric workspace computation and output writes.

**Proof.** Directly implement `sourceControl`: a visit reads its stored
address; alpha or beta constructs that acquired leaf; a branch pushes the
right address and visits the left. Deliver with a pending right address saves
the acquired left subtree and switches; deliver with a saved left subtree
constructs their ordered pair. Empty stack stops. Append/copy scans implement
finite address and stack operations, so this is one common finite effective
controller, with no unknown subtree in its input. `native_source_producer`
already supplies its actual run, truthful order and exact reconstruction for
every finite $U$. The run has no updates and hence is capacity-safe at $H$.
Theorem 7.2 realizes it on the installed packet. A full binary tree has
$m-1$ branch nodes and $2m-1$ total nodes; its supplied `productionTrace`
contributes one read per node and two locals per branch. These give the exact
counts. The actual tape work inside each TagRead and each controller operation
remains additional paid work.

For a numeric output, reuse `NativeEffectiveSourceProducer.numericTick` and
its name/instruction correspondence: leaf names are 0 and 1, and pair names
are `Nat.pair(left,right)+2`. These operations on acquired finite naturals are
implemented by finite paid arithmetic/encoding routines. The supplied
`effective_source_producer` proves losslessness and actual external
acquisition. No classical `sourceDecoder` is executed: if a tree-valued
delivery is wanted, the direct acquired preorder serialization is already
available. $\square$

For an $m$-leaf acquired tree, its active TM token serialization has $4m-2$
payload bits, and its `AtomicPrefixParser.code` serialization has $3m-1$.
Choosing either output requires writing, framing and copying those actual bits.
The padded private packet still has $2N$ bits, regardless of $m$.

**Proposition 7.4 (Boolean acquisition retains its original target).** After
the same truthful acquisition, an optional Boolean consumer decides exactly
$\operatorname{Positive}(U)\iff\exists T,\rho^3T=U$. This does not relabel the
tree-output or numeric-output producer as the original Boolean strategy.

**Proof.** Substitution never decreases leaf count. Every actual preimage
$T$ therefore has at most $m$ leaves. Enumerate those finitely many labelled
ordered trees, compute their third substitutions as local acquired syntax,
and compare to the acquired $U$. The exhaustive answer is true exactly when
one equality holds. This is the finite-decision argument already supplied by
`acquisition_foundation`; executing the finite enumeration and comparisons
adds its own paid bill. `Positive` and the Boolean return type remain exactly
the original ones. $\square$

## 8. An extended record verifier with an actual consumer

**Definition 8.1 (admissible snapshots and replay language).** Install mode
$V^+$ for a frozen, completely copied producer prefix of Definition 5.1. Its
domain consists of snapshots delivered through the actual ownership transitions,
with complete public initialization, declared prior $D\subseteq\mathcal T_H$
and required context/control/output material. It has no live source port and
no arbitrary-string authenticity oracle. Missing material, wrong port/payload
types, inconsistent identities, ordinals, generation transitions or sealed
predecessor/copy references produce a refusal.

For each of the $4^N$ public packets, parse completely, retain valid candidates
in $D$, and replay the source rows from that candidate initial tree. A TagRead
row uses Definition 2.2 at the actual recorded $p$ and compares the exact tag.
A ReadE row computes the exact Clifford response. Rho and graft rows compute
the entire candidate and whole-capacity guard, compare accept/reject, and advance
the current replay tree only on acceptance. Reject has no candidate-value field.
The recorded requests are the actual inputs to this replay, not freshly chosen
requests that agree on a marginal invariant.

NativeLocal/Halt rows have their own grammar and do not change the replay tree.
For a controller-generated prefix, $V^+$ additionally runs the copied installed
controller on public inputs and the acquired reply sequence, checks its submitted
requests and local markers, and compares the complete terminal output if present.
For the producer of Corollary 7.3 this is the explicit finite stack computation.
An arbitrary controller is accepted in this mode only with an effective
interpreter and pointwise termination of these finite-prefix replay segments.
A source-call-only snapshot need not claim controller correctness.

All enumerations, arithmetic, parsing, comparisons, replay work and refusal
outputs are executed and paid. Opaque occurrence references are checked against
the actually owned copied blocks and their chains; row strings alone do not
prove the ideal ownership premises. Optional validation of micro-fence schedules
can use the causal simulator on the same acquired prefix; it adds work and does
not inspect private source scratch.

**Definition 8.2 (whole-fiber receipt and consumer).** Fix one of the two target
types `INITIAL-SYNTAX+` or `INITIAL-qH+`, with target functions respectively
$s\mapsto s$ and the unchanged $s\mapsto q_H(s)$ of PR57.02. From the surviving
initial sources $F$, accept a proposed $\tau$ exactly if structural/controller
checks for the chosen mode succeed, $F\ne\varnothing$, and every $s\in F$
has that target value $\tau$. Empty or ambiguous fibers refuse.

The receipt contains the extended model/type, immutable preparation identity,
initial-target type, complete $\tau$, frozen-prefix end, prior description,
verification occurrence and actual snapshot reference. Copy the receipt and
any required source serialization through newly allocated mailbox and consumer
destination. The consumer checks its exact type, identity, prior and snapshot
references and complete payload before sealing/serially outputting $\tau$.
These are distinct extended receipts; the unchanged PR57.D8 parser/consumer
is not asserted to recognize TagRead or syntax receipts.

**Theorem 8.3 (exact replay fiber and record-only soundness).** For every
authentic extended prefix from an actual $t_0\in D$, the candidate source
survivors in $V^+$ are exactly

$$
F=\{s\in D:\text{the recorded source requests from }s
\text{ give exactly the recorded typed responses in order}\}.
$$

The actual $t_0$ survives. Controller-mode checks succeed for an authentic
prefix produced by the declared terminating controller. Every accepted receipt
and completed consumer output equals the selected initial target of $t_0$.

**Proof.** PR57.T1's valid-packet enumeration is complete and duplicate-free.
For a retained candidate, induction over rows keeps its replay tree equal to
the result of the preceding actual requested operations on that candidate.
Lemma 2.3 gives exactly its next literal response; PR57.T2's ordinary source
formulas give exactly ReadE and the whole modification result, including
unchanged source on reject. Comparing those values is therefore precisely
membership in the displayed fiber, in both directions. Local and terminal
rows do not alter this source replay. Theorem 5.3 supplies the actual rows,
so $t_0$ passes every response comparison.

The copied controller sees the same public inputs and acquired responses as
at its actual execution. Determinism gives the same request/local/output
sequence. Each authentic replay segment terminates by its declared finite
computation, so those checks succeed. For any candidate in $F$, its identical
reply word gives the same controller behavior. These checks therefore do not
silently select a different source fiber.

For either target type, nonempty whole-fiber constancy and $t_0\in F$ imply
$\tau$ is its actual initial target. The receipt's identity and target type
are copied as part of the same sealed payload; PR57.L4 preserves every bit.
Complete consumer checks and paid output then yield that same $\tau$.
No live source query, initial-target oracle or chosen representative is used.
$\square$

**Corollary 8.4 (source recovery after authentic acquisition).** On a no-update
complete producer traversal from boot, the fiber $F$ is $\{t_0\}$. Thus $V^+$
can accept its actual initial syntax, or compute and accept the original
initial $q_H$ on it, and deliver either through its corresponding consumer.

**Proof.** Any surviving source has every recorded leaf reply at the producer's
actual leaf addresses. The existing `source_foundation` tree-separation clause
forces it equal to the acquired tree; equivalently apply the supplied truthful
traversal/reconstruction argument. The actual source survives by Theorem 8.3,
so the fiber is precisely that singleton. Computing either finite target on it
and applying Theorem 8.3 gives the receipt and delivery. This invokes the
existing reconstruction supplier rather than declaring a new acquisition
theorem for the old numerical-only menu. $\square$

## 9. Resources on the same actual execution

**Definition 9.1 (complete charges).** Extend PR57.D9's disjoint occurrence
purpose tags to literal generation/execution, journal service and $V^+$.
Each occurrence has one purpose and one primitive opcode; inherited seek or
append helpers retain their caller's purpose. If $r$ has $n(r)$ core occurrences,

$$
T(r)=n(r),\qquad F(r)=2n(r).
$$

For a cut $c$, with $A(c)$ actually constructed ordinary cells and $n(c)$
receipts, simultaneous storage is

$$
S(c)=S_0+b_{\rm ctl}(c)+8A(c)+8n(c).
$$

Source, gate/code/address tapes, every scratch/counter version, retained output,
producer/actor archives, mailboxes, verifier and consumer copies coexist where
their transitions require them. Erased cells remain counted. A source-dependent
program, input, timing or retained name cannot be supplied free of charge.

**Proposition 9.2 (what the gate and copy counts actually price).** The gate
bill inside a literal call is the sum of PR57.06 over its $G(H)$ gate records,
plus the end-header read and exit. For a gate with $v=(a,b,c,d)$ it is

$$
I(g)=18+5\sum_{r=1}^4(v_r+1)
+\sum_{r=1}^4(2h_{g,r}+3v_r+3)+4+1+P_g,
$$

where $P_g$ consists of its actual address-field positioning and sealing
occurrences. Its code-record length is $13+d+a+b+c$, not one cell. Public
enumeration/parser/locator work, materialization of $p,H$, instruction generation,
allocation/zeroing, descriptors, final response framing/commitment and all archive
or output services are additional disjoint occurrence counts.

A $k$-bit sealed sender/mailbox/receiver copy has the reused exact body
$8k+4$, with allocation, homes/seeks, descriptors, identity fields and serial
printing additional. Private source ingress has $2N$ actual `IN; WR; MR` bodies,
plus boot, allocation and validation. Literal raw-call count, gate count, full
runtime, retained name width, simultaneous storage and archive access count are
separate resource coordinates.

**Proof.** Directly expand the interpreter: header/truth-table fetch, copying
all four unary fields, four seeks, three operand reads, one result write, one
`BF` and the explicitly prescribed positioning give PR57.06. The direct
generator of §3 emits exactly the gate records counted in Theorem 3.3; every
code bit is actually appended. The two channel loops copy each of $k$ bits
using four occurrences per side, followed by seal/token and seal/acknowledgement,
giving $8k+4$ as in PR57.13. None includes earlier destination construction or
later printing. Each ingress bit has its separate input, write and move. The
purpose partition places every other executed occurrence in its own actual
routine exactly once. Summing those finite event words proves the accounting
without replacing it by gate count. $\square$

The circuit is exponentially inefficient and has large unary-address overhead.
This volume supplies a finite correct bridge, with no query/runtime optimality
or polynomial-resource assertion. A memory allowed to retain the live TagRead
permission can pay for later queries; it is a different contract from acquiring
the entire source before handoff.

## 10. Boundary instances and falsifiable finite checks

**Example 10.1 (distinct Read ports).** For
$t_L=\langle\langle\alpha,\alpha\rangle,\beta\rangle$ and
$t_R=\langle\alpha,\langle\alpha,\beta\rangle\rangle$, the leaf words and
numerical evaluations agree, while TagRead($L$) returns branch and alpha.
This is the existing TM shape-collision witness. Paid ownership/copying of
numerical rows does not add the missing distinction; the new literal
permission acquires it. Theorem 3.4 does not hide it after commitment.

**Example 10.2 (capacity, absence and failed parsing).** At $H=1$, $N=1$,
alpha and beta are the only valid packets. The gate count is $G(1)=23$.
Root TagRead separates the leaves; TagRead($L$) returns absent on each.
The actual first $\rho$ on alpha accepts and installs beta without increasing
leaf count. The next $\rho$ rejects and leaves beta, because its candidate has
two leaves. Unconditional Native ApplyRho instead installs that branch;
Theorem 7.2 therefore cannot extend to that overcapacity run. Reject advances
$q,j$ but not $g,e$. At $H=2$, `PAD,alpha,PAD` fails preparation while
`alpha,PAD,PAD` succeeds; ignoring PAD-before-closure invalidates the model.

**Example 10.3 (the necessary pending field).** Cut a TagRead execution just
after complete response release and before its row's final seal. Then
$|E|=|A_P|+1$, and the receiver still lacks that row. At seal the lengths become
equal; during its later copy the destination remains unavailable. Thus an
invariant $E=A_P$ at all cuts, or equality of all in-flight archive lengths,
would be false even in this deterministic ideal model.

**Verification scope 10.4 (bounded checks).** The following in-memory checks
passed with exit code zero. Public fixed-token parsing and locating were compared
to a separate recursively generated tree domain and recursive readout; the
gate check executed each emitted Boolean gate, rather than replacing the
conjunction/OR construction by a direct lookup.

| Check | Exact finite domain and result |
| --- | --- |
| Public parser and locator | $H=4,N=7$: all 16,384 token packets, exactly 102 valid trees, and all 63 addresses of lengths zero through five; all 6,426 literal comparisons agreed. PAD-before-closure cases were included. |
| Whole-candidate boundaries | The same 102 sources, rho and both graft directions with every context of at most three leaves: 219 accepted and 4,371 rejected candidates; accepted codes decoded to the actual whole candidate. |
| Full Boolean tape evaluation | $H=3,N=5$: all 1,024 enumerated rows, 22 valid installed sources and 15 addresses of lengths zero through three, giving 330 complete circuit evaluations. Every tag agreed and every tape had exactly 13,315 gate records. |
| Journal phase model and source replay | All 7,546 length-three command words on 22 sources, over root/L/R TagRead, rho, left-alpha graft, right-beta graft and local marker: 249,018 phase cuts satisfied the pending/seal/copy-prefix equations; the actual initial source survived each complete recorded-response replay. This checks the declared phase equations, not literal tape code. |
| Complete producer fibers | All 102 trees at $H=4$: truthful root-relative preorder responses had singleton source fibers and exactly $2m-1$ calls. The $H=1$ accept/reject and 23-gate boundaries were also checked. |

These checks cover precisely those finite cases. The universal claims are the
ordinary proofs above; enumeration does not prove unbounded actual-source
realization, exercise the paid tape interpreter, or establish Lean certification.
No experimental program or data is retained in this theory source.

## 11. Literature, reuse and the precise remaining programme

**Literature status 11.1 (primary sources and hypothesis maps).**

| Primary source | Applicable statement and required conditions |
| --- | --- |
| Nancy Lynch and Frits Vaandrager, *Forward and Backward Simulations, Part I: Untimed Systems*, Information and Computation 121(2), 1995, 214–233; [author manuscript](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf), §3.2, Lemma 3.8 and Theorem 3.10 | `literature-attested`: a forward simulation from $A$ to $B$ requires related initial states and, for every $A$ step and every related $B$ state, a finite $B$ fragment with the same trace and related endpoint. In the finite lifting here, take $A$ to be the Native macro system and $B$ the adapter with its Native trace projection: actual boot supplies the related starts and Theorem 7.2 supplies the matching fragments at its declared entry cuts. Corollary 3.5 separately accounts for implementation micro-observations; those observations are not Native labels. Trace inclusion supplies neither permission, costs, authenticity nor exact task kernels. |
| J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce and Alan Schmitt, *Combinators for Bi-Directional Tree Transformations: A Linguistic Approach to the View Update Problem*, ACM TOPLAS 29(3), 2007, Article 17; [author manuscript](https://www.cis.upenn.edu/~bcpierce/papers/lenses-toplas-final.pdf), Definitions 3.1–3.3 | `literature-attested`: get/putback laws are partial-definedness laws unless totality is separately supplied. Putback receives the updated abstract view **and the old concrete object**. These laws do not acquire a hidden tree, bind its installed occurrence, authenticate a journal or make ReadE into literal Read. |
| Martin Fowler, [*Event Sourcing*](https://martinfowler.com/eaaDev/EventSourcing.html), “Complete Rebuild”, “External Queries” and “External Updates” | `literature-attested` operational background: replay requires the external query responses that actually influenced the execution; replayed updates must be distinguished from new live external effects. Here exact TagRead replies are retained in owned rows, and candidate replay in $V^+$ is local acquired computation with no live source port. This article supplies no formal ownership, capacity or resource theorem; those are the explicit model/proofs above. |

The applicable source producer, tree reconstruction, Boolean acquisition,
gate interpreter, channel copy, finite replay and generic joint-image framework
are credited suppliers. The repository-derived addition is the producer-side
literal instrument on the *same* installed private block, its enlarged causal
observation interface, and the typed actual event/row/pending/copy coupling
with an extended record consumer. The exact minterm gate count concerns this
specified implementation. Truth-table synthesis, tree traversal, event replay,
fiber constancy and lens laws are not claimed as new mathematics. The cited
literature does not establish global originality of this particular composition;
no such originality claim is made.

**Open obligation 11.2 (individual four-expression task kernels).** This
adapter supplies one acquired dynamic source and callable authentic journal,
not four individually minimal expressions. A next construction must declare
natural spatial incidence/support, ordered executed events, continuation boundary
and callable-memory maps on the same actual history image, and a nonempty task
family with its complete output/record/selector and original successor fields.
For each map it must prove both sufficiency and nonredundancy, hence equality
with the task kernel, and lawful transport of enabled choices and success/reject
successors. PG43's common-kernel inclusion alone is insufficient. Private scratch,
microcosts, pending events and live-source permissions must be retained whenever
that task observes them, or excluded by an explicit task contract.

**Open obligation 11.3 (entry, growth and unrestricted effective execution).**
The authenticated history begins at this actual paid boot; importing a supplied
old Native trace needs its own provenance contract. The direct producer needs
no chosen partial-recursive evaluator code, but arbitrary effective-service
execution still needs its actual installed code, genuine-state correspondence
and paid history/workspace access. Fixed $H$ realizes precisely the capacity-safe
Native runs; growth/reinstallation would require a separately priced source
action and identity/copy proof. A finite construction for every public $H$
does not establish one actual infinite coherent thread.

**Scope 11.4 (unchanged stationary objectives).** The original stationary
$F_D=\langle\alpha,v\rangle$, height bound, source-blind paid preparation before
the late address, charged original-root literal Reads, complete retained name,
R-starting target range, at most one late original-root Read before reply,
authentic $k$ and prediction for every $k\ge0$ are unchanged. The original
$M_1(D)$, sharp $\lambda$ and effective all-size certificate goals remain
unresolved here. Installing TagRead inside a finite-cap dynamic TM runtime
adds neither a free original acquisition service nor a new stationary endpoint.
The next research action enabled by this volume is to use the explicit
source-bound port and pending journal as the concrete acquisition/record
interface for a separately proved four-expression observer.

## 追加锚（本行以下为增补区）
