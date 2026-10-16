# Native clocked tree recovery and the acquired order complement

> This volume is an append-only mathematical reference input. Existing merged
> statements and anchors remain fixed; corrections and extensions belong after
> an append anchor. Its numbered statements have ordinary proofs, with no new
> Lean certification or digestion-state claim.

## 1. The concrete component and its suppliers

**Convention 1.1 (scope).** The observer below has one actual evolving ordered
tree, one source-uniform deterministic installed controller, actual paid
acquisition, and owned callable records. Its four expressions are current
unlabelled ordered support, actual ordered events, current leaf boundary, and
acquired seed-and-replay memory, each with the explicitly specified clock
information. Their individual kernels equal the kernel of one continuation and
audit task. This result concerns that closed controller, including its busy
tape cuts. Independent command ingress is a different interface, treated in
Section 8. Neither interface changes the original stationary task.

The following sources are used at the common public revision
`b7d37ca0fee9638f28af45d4a63f7f0eb974c972`. Paths in this table identify their
owning declarations and narrative sources, rather than a new compilation.

| Supplier | Exact use and boundary |
| --- | --- |
| [NativeSerialMachine.lean](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean), `Op`, `Event`, `nativeStep`, `Run`, `Replay`, `replay_deterministic`, `operational_replay`, `reached_prefix_replay`, `actual_register_execution`; [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs) | One register, source-free control, literal address replies, actual substitution and chronological appending. The last theorem assumes a certified entry iterate and arbitrary supplied old trace; it does not authenticate that old trace. Here the native trace starts empty at a declared entrance. |
| [NativeFullSourceProducer.lean](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean), `Frame`, `Control`, `sourceControl`, `initialControl`, `productionTrace`, `native_source_producer`; [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs) | The stronger existing actual producer returns the entire input tree under common control, with one literal Read per actual node and two producer local actions per branch. This supplies acquisition directly. Its unbounded semantic workspace is expanded into paid tape work below. |
| [ActualTreeReadoutAcquisition.lean](../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean), `acquisitionTrace`, `restore`, `acquisition_foundation`, `source_foundation`; [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs) | The producer's read projection is the existing truthful preorder. `restore` and the reconstruction inside `acquisition_foundation` already supply reconstruction; that theorem's original terminal result is the third-image-membership Boolean, which is not renamed as the present output. |
| [AtomicPrefixParser.lean](../../../D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.lean), `code`, `parse`, `decode`, `result`; [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.scribe.cs) | Literal leaf code `[true,b]` and branch code `false::left++right`, with exact remainder, injectivity and complete decoding. This is an acquired/source-supply representation, not an access port. |
| [Atomic Boundary Trichotomy, Theorem 12.1 and equation ABT.39](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md) | The effective bijection $C(t)=\operatorname{sh}(\rho^2t)$ onto the explicit shape grammar, and its forward transport $\Theta$. These permit genuinely unlabelled spatial and boundary expressions after two updates. |
| [Process Geometry, Theorem 44.6](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md); [GenealogicalFiberTransport.lean](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean), `fiberMap`, `result`, and [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.scribe.cs); [IntrinsicSubstitutionCoordinates.lean](../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean), `intrinsic_coordinates`, and [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.scribe.cs) | Actual substitution injectivity and inverse recognition are existing tools. `result` exports injectivity of the composition-fiber maps; its global injectivity proof is local, and the coordinate module's corresponding lemma is private. No new public raw-inverse declaration is asserted. Executed epoch is distinct from intrinsic ancestry depth. |
| [NativeSerialEffective.lean](../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.lean), `OriginalState`, `OriginalCodeRealization`, `original_code_service_simulation`, and [owning Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.scribe.cs) | Acquired history and effective selectors already exist. General effective-code simulation requires supplied code and the genuine-state realization equation. The present explicit finite routines need no arbitrary-selector oracle. Bounded evaluator `none` is local work, not an executed external failure. |
| [Transport Memory Completion, Section 57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), PR57.D1–D3, D7, L1, L2, L4 | Constructed tapes, a receipt per primitive, closed-cut clock readout, finite scans, append/seal and owned copying. Only these runtime components are reused. Its source `Read` returns Clifford $E$, and its source modifications have a whole-candidate capacity guard. Neither is identified with the Native literal Read or unconditional update. |
| [Process Geometry, Sections 34, 39 and 43](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md); [TypedFiniteViewKernel.lean](../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean), `typed_finite_view_kernel`, and [owning Scribe](../../../Blueprint/D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.scribe.cs) | Actual joint images, complete response/successor fields, selector descent and the separate nonredundancy inclusion. Generic kernel factorization and typed finite-path closure are credited tools. |

The additional mathematical work is the particular acquired, clocked joint-state
reconstruction and its individual task-kernel proofs, plus the conditional
chronology fiber and its causally acquired complement. Acquisition, substitution
recognition, deterministic replay as a general idea, and enumerative coding are
not claimed as discoveries.

## 2. One source and a fully specified clock convention

**Definition 2.1 (trees and literal calls).** Let
$\mathcal T::=\alpha\mid\beta\mid\langle t,t\rangle$ be nonempty finite ordered
trees. Equality retains every bracket, left/right occurrence and leaf colour.
An address is a finite word over $L,R$. Literal $\operatorname{Read}(p,r)$ returns
$\alpha$, $\beta$, $\mathsf{branch}$ or $\mathsf{absent}$ according to the node
at $p$. Every finite address is a legal Native request, including one below a
leaf. Define the same actual substitution as the suppliers:

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

Fix public integers $H,J\ge1$, a fixed preparation-occurrence identity $\xi$,
and one installed deterministic program $P_{H,J}$, identical on every initial
$u\in\mathcal T_H$. All comparisons below fix these public parameters and the
same port origins and initial owner assignments. Across different preparations,
their complete identity tags must instead be retained in every view.

**Definition 2.2 (declared hybrid primitive model).** The source is a Native
register, not TM57's private Clifford source port. It admits literal Read and
unconditional actual $\rho$ as in Definition 2.1. Ordinary workspace, archives,
mailboxes, references and outputs use the finite-symbol constructed tapes and
core occurrences of PR57.D1–D2. There is one serial prescribed next primitive;
no concurrent actor, random bit, external scheduler choice, unrecorded interrupt
or imported archive is present.

The following primitive assumptions are explicit parts of this model.

1. The initial source is actually installed at root $\xi$, with native epoch
   zero and empty native trace. Source supply is charged separately: any finite
   source code and its private ingress, construction and installation are a
   source-supply bill, not public controller advice. For a definite logical
   representation one may use `AtomicPrefixParser.code`, whose length on an
   $m$-leaf tree is $3m-1$. A canonical supplied packet is a function of $u$;
   any additional installer choices or scratch residue would be extra state
   and are excluded here. This is a specified Native input boundary, not a
   proof of a TM57 literal-port implementation or of free physical source
   assembly. Histories under study start at this boundary.
2. Fixed public boot bits, $H,J,\xi$, tape boundaries, interpreter instructions
   and initial tokens are actually installed by paid finite bit writes using
   the PR57 boot convention. Their descriptions are fixed before $u$ and are
   not source-specific programs. Only the constant primitive bootstrap is
   irreducible initial machinery. No unbounded numeric register is primitive.
3. Every selected primitive, including a Native source invocation, appends one
   receipt cell atomically with its declared effect. This extends PR57.D1's
   receipt convention to the two Native source opcodes. A source-update receipt
   has a distinguished finite symbol $\mathsf U$; ordinary and fence receipts
   have their own symbols. A receipt contains no address, reply, private value
   or choice word. Source calls have a separate source-operation price and one
   receipt-construction price. Tape occurrences retain PR57's two fee units.
4. Native Read commits its one finite reply and source update commits its
   actual successor atomically at this primitive granularity. The source has
   no partially rewritten tree at an intervening tape cut. A bit-level
   implementation of either source call would require a different simulation
   theorem retaining its additional source-busy cuts.
5. Ownership, immutable seals and token transfers have the ideal exclusive
   meaning of PR57.D7. Fresh block placement uses deterministic `Base` and
   allocation, never an allocator-selected fresh name. The controller sees
   only its acquired reply latches and tapes, not the source or inaccessible
   native trace.

Thus the native part has the exact `Op`/`nativeStep` meaning on projection;
every paid tape primitive is a native `localStep`. The projection does not
erase native Reads or actual updates. The rich tape label and receipt side
effect are extra runtime structure, with their separate costs. No original
TM57 source call, guarded graft, candidate value or source rejection is used.

**Definition 2.3 (actual clocks, not free numerals).** At a primitive cut $h$,
let $n_h$ be the length of its actually constructed receipt chain from the
declared entrance and $e_h$ its number of $\mathsf U$ receipts. These are
mathematical coordinates of acquired finite material. They are not elapsed
physical time, an update-only chronology, or automatically accessible binary
integers. The tape epoch counter can lag $e_h$ while its new version is being
written. All such versions and their phase flags remain in the joint state.

An ordinary fence closes a receipt prefix. PR57.D3's paid scan produces its
actual unary length. Counting the $\mathsf U$ symbols in that same fixed prefix
by paid increment produces the actual epoch there. These scans terminate at
the old fence although their own work adds later receipts. If a reader is
authorized to fence immediately after a target primitive cut, its fence has
ordinal length $n_h+1$; paid subtraction of one reports $n_h$, and that fence
does not change $e_h$. Such instrumentation is a readout of a named old cut,
not a new free live clock or an operation silently inserted into $P_{H,J}$.

The four views below are functions of all actual primitive cuts. Paid
materialization and recovery consume acquired data for a named closed cut.
They do not produce an instantaneous full snapshot without work, and their
execution is not included recursively in the old cut they describe. Allowing
arbitrarily interleaved diagnostic calls inside the controller would add
independent input and is outside the fixed-flight theorem.

## 3. The installed evolving-tree observer

**Definition 3.1 (row and callable prefix).** A sealed row is length framed and
contains $\xi$, original-root and port tags, a row ordinal, the preceding row's
actual reference, the full request, full finite response, actual before/after
epoch, and its start, commitment and seal provenance. Original and current
source identities are distinct fields. Numerals and wire references are
constructed with paid scans and copies. The port tags are `NativeRead`,
`NativeRho` and `ArchiveFetch`; none is `ReadE`.
The row body uses only already closed start/commit fence numerals. Its own
seal provenance is the actual seal flag and creation/copy relation, not a
printed future numeral that already counts the row's own serialization.

A descriptor $d$ names one already sealed finite producer prefix with $a$ rows.
The actual service $\operatorname{Fetch}(d,j)$, for any constructed finite
index $j$, scans that fixed prefix. If $0\le j<a$, it makes a complete owned
copy of row $j$ through a separate mailbox, preserves the identity/framing and
returns that row and its copy reference. Otherwise it executes a finite checked
return $\mathsf{ArchiveIndexReject}(d,j,a)$ with its actual successor. The
service has an admission phase, copying/checking phases and one response
commitment. Its response is subsequently recorded in a fresh row after $d$.
It never scans its own growing output as input.

Only the prescribed microtransition is enabled during a busy service. Missing
ownership or a request submitted at a busy phase is illegal-unexecuted. That
case has no event or successor. An admitted out-of-range index executes the
rejection; it is not illegal, source absence, a source-update reject, or a
failed evaluator attempt. Complete row copying and a real caller make this
memory an acquired callable interface, not merely a history-valued definition.

**Definition 3.2 (the common program).** $P_{H,J}$ performs the following finite
algorithm, with every finite data operation expanded into the paid routines of
PR57.D2 and its finite sequence/test/loop expansion rules.

1. Run the existing `NativeFullSourceProducer.sourceControl` from
   `initialControl`, serializing every actual literal Read into the producer
   journal before resuming its saved continuation. Represent its frames and
   acquired subtrees on constructed tapes. Its two local actions at each
   branch have their actual control markers and paid tape implementation.
   At the supplier's empty-stack delivery state, retain the returned tree by
   paid serialization, rather than ending the host observer. The terminal
   delivery is an internal return, not an extra Native Read.
2. Seal that acquired seed code and acquisition prefix. Execute and journal
   two actual Native $\rho$ calls, one at a time. Seal their rows and all
   current counter/descriptor versions. Close an acquisition fence. Let its
   cut index be $a(u)$. The four-view domain begins at this cut.
3. For $i=0,\ldots,J-1$, construct $p_i=L^{i+1}$. Execute one literal
   $\operatorname{Read}(p_i)$ on the current register and journal its actual
   reply $y_i$. Execute one actual $\rho$ and journal it. Freeze the currently
   sealed prefix $d_i$ with row count $a_i$. If $y_i$ is a leaf reply, call
   $\operatorname{Fetch}(d_i,0)$; otherwise call
   $\operatorname{Fetch}(d_i,a_i)$. Journal the complete success or rejection.
   This choice uses the acquired reply, not the private current tree.
4. After the rounds, perform one Fetch of row zero from the then-sealed prefix,
   journal its successful complete copy, then Fetch the first out-of-range row
   of the next sealed prefix and journal its executed rejection. Thus every
   source exercises both recall and executed failure, even if the earlier
   reply-dependent branch always made the same choice.
5. Freeze the resulting data archive and make one complete owned copy to the
   consumer. Halt with this full framed archive and its original identities
   and descriptors as the terminal output $O(u)$. It includes the truthful
   acquisition rows. It excludes its own later serialization and transmission
   events; those are still in the actual primitive event word.

Rows follow source-response commitment, so cuts exist at which a source event
has executed but its row is only partially written. There is at most one
completed semantic event awaiting its row seal. Copy destinations remain
unavailable through their last bit and final seal. The program has no
self-extending archive scan and no row that contains its own full successor
archive.

The source producer is reused by continuation composition: its actual read
and branch-local sequence is unchanged on projection. Added writer work is
paid `localStep` work between those instructions. The complete acquired tree
is already the supplier's output, so no new source-reconstruction theorem is
being substituted for it. The explicit stack, frame tags, address append,
finite tree-code concatenation and tests are finite string algorithms; their
stack data may grow, but their instruction descriptions are fixed. There is
no atomic string operation or integer-indexed control family.

## 4. Actual joint histories and complete successor closure

**Definition 4.1 (joint state).** A state $x_h$ includes the actual register
$r_h$, its actual epoch, the native trace, the receipt tape and both meter
heads; every constructed ordinary cell and head mark; control/phase and
finite latches; installed code and acquired seed; the producer frames,
addresses, arithmetic versions and scratch; complete and incomplete producer
rows; all mailbox and receiver intervals; ownership/availability tokens;
constructed typed references and their creation/copy chains; pending request
and response latches; the last event; and running or complete terminal output.
Private scratch is included, even when it has no public observation port.
Retired constructed cells remain part of this state and of storage costs.

Let $\mathscr H_{H,J}$ consist of all actual histories generated by Definition
3.2 from the declared entrance whose endpoint is at or after $a(u)$ and no
later than halt. Write $h_{u,n}$ for their unique prefix of length $n$, whenever
$a(u)\le n\le L(u)$, where $L(u)$ is the total number of primitive occurrences
before the terminal control state. Native `stop` is terminal output, not a
fourth `Event` constructor or an anonymous failed transition. If a halt `CTL`
is used in the tape expansion it is the last metered local occurrence; the
subsequent terminal readout has no unexecuted phantom tick.

**Theorem 4.2 (finite actual execution and joint invariant).** For every
$u\in\mathcal T_H$, $L(u)$ is finite, each reached unfinished cut has exactly
one prescribed next primitive, and at every cut from the entrance:

$$
r_h=\rho^{e_h}u,\qquad
|\operatorname{receipts}(h)|=n_h,\qquad
\#\mathsf U=e_h.
\tag{NCR.1}
$$

Let $E(h)$ be the ordered completed semantic events of types `NativeRead`,
`NativeRho`, `ArchiveFetch`, $A(h)$ the same events decoded from sealed
producer rows, and $Q(h)$ either empty or the single completed event whose row
is pending. Then

$$
E(h)=A(h)\mathbin{+\!+}Q(h),\qquad |Q(h)|\le1.
\tag{NCR.2}
$$

Every readable receiver block equals its designated sealed sender block;
references, ownership, busy phases, rows and source/epoch/type tags belong to
this same execution. An admitted but not committed Fetch remains in pending
work, rather than $E(h)$.

Proof. The source producer theorem supplies termination, exact node preorder,
and the returned actual $u$ with no source update. A finite acquired address,
frame, subtree or row can be serialized by finite scans/appends. The inserted
writer routines terminate by PR57.L1; they leave the saved producer
continuation and source unchanged. Induction along the supplier's finite run
therefore supplies the actual expanded acquisition run. Two subsequent source
updates are finite primitives on finite trees. Each later round has finite
address construction, two finite source calls, finite row writing and a Fetch
on a fixed finite sealed prefix. The final two Fetches and final complete copy
are finite for the same reason. There are exactly $J$ rounds. All earlier
objects referenced by a new row already exist, so none of these loops acquires
an increasing bound from its own work. Deterministic finite routines give a
unique next core occurrence until terminal control.

At the entrance the native epoch and both words are empty and $r=u$. A tape
occurrence leaves $r,e$ unchanged and appends its one receipt. A Native Read
returns $\operatorname{Read}(p,r)$, changes neither source nor epoch and appends
one ordinary receipt. A Native update changes $(r,e)$ to $(\rho r,e+1)$ and
appends one $\mathsf U$ receipt. These cases prove NCR.1 by induction, including
cuts before a tape epoch numeral catches up.

For NCR.2, a noncommitting admission or tape occurrence changes no completed
semantic prefix. At source-call or Fetch response commitment, the actual
response and its exact request are saved in the pending latch and the same
event is appended to $E$; no new semantic call is admitted until its row is
sealed. Partial row writes do not change $A$. Its final seal adds precisely
that latched event to $A$ and removes it from $Q$. The source epoch fields are
obtained from the already maintained old counter and the actual update flag;
the new numeral is written before another source request. Rejection follows
the same commitment/row protocol as success. Thus each row's fields describe
the actual event, without reading the inaccessible native trace.

For an ordinary append, `Base` and allocation supply the actual fresh interval
and stored descriptor. A seal removes its write permission. During copying,
only the designated sender owns the mailbox and only the receiver owns the
inaccessible destination. The two loops copy each bit once, including framing
and original identities; PR57.L4 gives equality at destination seal. Token
handoffs and acknowledgement are the prescribed actual transitions. Induction
also retains partially copied cells, pending latches, old counter versions and
the appropriate unavailable flag. These are simultaneous invariants of the
one run, rather than separate existence assertions. ∎

**Corollary 4.3 (concrete PG34 witnesses).** Define joint compatibility by
NCR.1–2, correct typed descriptor intervals and predecessor/copy chains,
row/phase availability, actual token ownership and agreement of all fields
with their endpoint. Define `NextCompat` by the prescribed opcode's finite
tape/latch/control rewrite, receipt append, source effect if any, token
transfer and commitment/seal rules of Theorem 4.2. Then this observer satisfies
`run-full`, `run-next`, and their all-success restrictions `Full_R` and
`NextCompat` on its actual history domain.

Proof. For a history $h$, use the references and permissions actually
constructed in $x_h$. Theorem 4.2 proves that the single tuple consisting of
its archive, work, references, permissions, $\xi,e$, phase type and last event
satisfies compatibility. This is the required full witness. At an enabled
primitive, take the actual extended history and its actual endpoint tuple.
The transition cases in the same proof establish exactly the indicated
`NextCompat` equations and preserve compatibility. Hence the successor is in
the same joint image, including a completed Fetch-rejection successor. On
illegal-unexecuted input there is no extension. Restricting to all-success
histories gives the corresponding success-only statements. ∎

This discharges the named obligations for the model in Definition 2.2. It does
not assert an already compiled PG34 client, validate a submitted external
transcript, or recover scratch from the semantic archive alone.

## 5. Four concrete expressions and exact reconstruction

**Definition 5.1 (spatial and boundary objects).** Let
$\operatorname{Pos}(r)\subset\{L,R\}^{<\omega}$ be all actual node addresses,
including the root, with their ordered prefix incidences. It is the whole
finite ordered support, not a fixed-radius prefix or a leaf word. Let

$$
\operatorname{LeafPos}(r)=
\{p\in\operatorname{Pos}(r):pL,pR\notin\operatorname{Pos}(r)\}
$$

be its terminal antichain. Both objects erase leaf colours. The frontier is
the boundary where future literal descent ceases: a proper prefix of one of
its elements is a branch, an element is an uncoloured terminal position, and
any other address is absent. Its prefix closure is exactly the support.

Use the already supplied $C(t)=\operatorname{sh}(\rho^2t)$ and its inverse $D$
on $\mathcal G::=A\mid B\mid\langle\mathcal G,\mathcal G\rangle$, where
$A=\langle\dot,\dot\rangle$ and $B=\langle A,\dot\rangle$. At $e\ge2$,

$$
\operatorname{sh}(\rho^eu)=C(\rho^{e-2}u),\qquad
D(\operatorname{sh}(\rho^eu))=\rho^{e-2}u.
\tag{NCR.3}
$$

Let $I$ denote the existing effective partial inverse of $\rho$ on its actual
image. Recognition fails off that image; no physical inverse source action is
introduced. The executed $e$ is not replaced by maximal intrinsic depth.

**Definition 5.2 (the four maps).** On $\mathscr H_{H,J}$ put

$$
\begin{aligned}
S(h)&=(\operatorname{Pos}(r_h),e_h,n_h),\\
T(h)&=\text{the complete ordered primitive event word from the entrance to }h,\\
B(h)&=(\operatorname{LeafPos}(r_h),e_h,n_h),\\
M(h)&=(\operatorname{code}(u),n_h;\mathcal I_{H,J}).
\end{aligned}
\tag{NCR.4}
$$

The fixed interpreter $\mathcal I_{H,J}$ has replay and finite indexed recall
routines. Its description and installation are charged. The code in $M$ is
the actually acquired seed block, not the private initial source packet.
$n,e$ denote the constructed receipt coordinates of Definition 2.3, with paid
numeral materialization when required. $M$ needs no independently supplied
epoch: replay derives it. An actual-image memory value supplies the seed and
prefix position, not a stored copy of $T$.

$T$ retains every tape/core occurrence, including installation and evaluator
work if present, and every actual Native Read/update with its literal
epoch/address/reply. It retains the declared full public operation, cell,
ownership/availability, commit/seal/copy and tick/fee labels. Halt is a
terminal annotation with its full output. A semantic row list or an update
count is not this temporal expression. Retaining only semantic events would
erase the distinction between different row-writing microcuts.

**Theorem 5.3 (acquired all-primitive-cut reconstruction).** Each of the four
expressions in NCR.4 determines the entire original joint state $x_h$ and the
entire actual prefix $h$, for every $h\in\mathscr H_{H,J}$. On each actual
expression image there is an effective finite prefix decoder $H_V$ and an
endpoint decoder $D_V=\operatorname{endpoint}\circ H_V$ satisfying

$$
H_V(V(h))=h,\qquad D_V(V(h))=x_h\quad(V=S,T,B,M).
\tag{NCR.5}
$$

These are decoding algorithms on acquired finite descriptions for named cuts;
their own paid execution, scratch and output are additional resources.

Proof. The node set with ordered addresses determines the unlabelled shape:
nodes with children are branches, and the remaining nodes are dots. The finite
leaf antichain determines the same shape by prefix closure. Since $e_h\ge2$
throughout this domain, NCR.1 and NCR.3 apply. Decode

$$
u=I^{e_h-2}\bigl(D(\operatorname{sh}(r_h))\bigr).
\tag{NCR.6}
$$

Every inverse application is in its actual domain by NCR.1. This uses the
existing two-step support decoder and actual-substitution inverse; it neither
reproves those suppliers nor assumes that a bare current source reveals its
own absolute epoch. Thus $S$ and $B$ both determine $(u,n_h)$.

The temporal word contains all the producer acquisition Reads before the
acquisition fence. Their projection is exactly the existing truthful preorder
and hence determines $u$ by the existing reconstruction. Counting all its
primitive occurrences gives $n_h$; counting actual update occurrences gives
$e_h$. The memory value supplies $(u,n_h)$ directly.

Now replay the explicitly installed program from its common entrance on a
local finite description of $u$, for exactly $n_h$ primitives. This is a
calculation with acquired data, not another physical source. On a Native Read,
compute its finite literal reply on the locally maintained current tree; on
an update, substitute that tree; on a tape occurrence, perform exactly the
same finite tape/latch/token/control rewrite and receipt append. Include all
retired cells and the native trace. Reproduce deterministic allocation,
framing, references, current and lagging counter versions, pending responses,
mailboxes and unavailable destinations. No hidden independent allocator or
control choice is allowed by Definition 2.2.

Induction on the replayed primitive number gives equality with the actual
state: the entrances agree; equal control selects the same next opcode; equal
actual-tree descriptions give the same literal reply or substituted tree;
equal constructed tapes give the same ordinary transition. The receipt
extension and all metadata changes are also the same. At $n_h$ the induction
therefore gives $x_h$, including a partially written row or an incompletely
copied destination. The replay records its full prefix along the way.
Termination follows because $n_h$ is finite and is a reached position of the
finite run. One may totalize off-image input with a typed decoding error, but
this is not an authentication theorem for such inputs. ∎

**Remark 5.4 (why the expressions have different content).** $S$ is a current
unlabelled incidence structure and $B$ its genuine terminal antichain; neither
stores acquisition rows, requests, replies or scratch. The two actual warm-up
updates encode erased colours into their present shape by an existing theorem.
$T$ is actual chronology. $M$ stores the acquired starting tree and a prefix
position, and regenerates past work. Only $T$ contains the full event word.
Their recoveries use injective source evolution and determinism, rather than
four fields made equal by definition.

## 6. One task and four individual exact kernels

**Definition 6.1 (continuation and audit task).** Starting at a cut of
$\mathscr H_{H,J}$, an experiment may request any finite number of `Advance`
actions. At an unfinished cut, `Advance` executes precisely the next
prescribed primitive of $P_{H,J}$. Its complete response includes that
primitive's label, released finite output, original joint successor, actual
writer/archive changes, reference and permission changes and successor type.
There is no choice of alternative source command at this interface. At halt,
`Advance` is illegal-unexecuted, and has no successor or failure row.

The root readout is $\mathsf{Running}$ before halt and
$\mathsf{Halt}(O(u))$ at halt. It is retained also for the empty experiment.
The complete response to a finite experiment retains ordered responses and
the terminal readout, with illegality at the first unavailable step. This is
the task of continuing and auditing the installed observer. In particular it
includes its actual complete consumer archive; replacing that output by only
a final numerical tree statistic would define a different task.

Write $K_{\mathcal V}$ for equality of all these complete experiment responses.
The task is specified from the observer's operation and output contract before
using the four views. It does not define equivalence to be equality of a view.

**Lemma 6.2 (a concrete separating subtask).** On this domain, equality of even
the weaker observations consisting only of running/halt status, availability
of each `Advance`, and full terminal $O(u)$ forces equal $(u,n)$.

Proof. The truthful acquisition subarchive in $O(u)$ reconstructs $u$.
Consequently $O(u)=O(v)$ implies $u=v$, even though neither output contains
its subsequent transmission events. Let the remaining primitive counts at
two cuts be $r=L(u)-n$ and $s=L(v)-m$. If $r<s$, after $r$ advances one cut
has root readout halt while the other has running; $r=0$ is the empty
experiment case. The case $s<r$ is symmetric. If $r=s$, that common finite
continuation reaches both terminal outputs. Equal observations force
$O(u)=O(v)$ and hence $u=v$. Determinism then gives the same total $L(u)$,
so $L(u)-n=L(u)-m$ implies $n=m$. ∎

**Theorem 6.3 (individual exact task kernels, including nonredundancy).** For
each individual $V\in\{S,T,B,M\}$, and all $h,h'\in\mathscr H_{H,J}$,

$$
V(h)=V(h')\quad\Longleftrightarrow\quad h\mathrel{K_{\mathcal V}}h'.
\tag{NCR.7}
$$

In fact their common kernel is equality of $(u,n)$ on this actual domain.

Proof. For $S$ and $B$, equal expressions give equal seeds by NCR.6 and equal
primitive positions from their clock coordinate. For $T$, equal words give
equal truthful acquisition and equal total primitive length. For $M$, this is
equality of its acquired seed and length. Thus each map separately determines
$(u,n)$, and by Theorem 5.3 equal values give equal original joint states.
Deterministic continuation therefore gives equal enabledness, labels,
success/rejection, complete outputs, original successors and all archive,
writer, reference and permission changes at every finite continuation. This
proves $\ker V\subseteq K_{\mathcal V}$ for each $V$.

Conversely, full task equivalence implies equality of the separating subtask
in Lemma 6.2, hence equal $u,n$. A common seed and position give the same
actual execution prefix, so $r,e$, support, frontier, event word and acquired
memory all agree. This proves $K_{\mathcal V}\subseteq\ker V$ separately
for all four views. The reverse direction uses an actual continuation
separation, not mutual recoverability. ∎

The theorem is exact sufficiency and nonredundancy for this task. It is not
minimum bit length, a claim that each tuple coordinate is indispensable, or
minimality for every conceivable observation task. For example $e$ is derived
from $(u,n)$, but it is required in the stated direct support decoder rather
than being unpriced advice. A task erasing the final archive or primitive
termination timing can have a coarser kernel.

## 7. Dynamic transports, selectors and actual callable memory

**Theorem 7.1 (lawful recovery and dynamic transport).** Put
$R_{VW}=W\circ H_V$ on the actual image of $V$. These maps are inverse in
pairs, preserve source identity, and satisfy triangle identities. The next
selector input, enabled action, complete response and original joint successor
factor through each $V$. Their induced transitions commute:

$$
R_{VW}\,\overline{\operatorname{Advance}}_V
=\overline{\operatorname{Advance}}_W\,R_{VW}
\tag{NCR.8}
$$

on their common enabled domain. Illegal-unexecuted and executed-reject cases
keep their distinct types.

Proof. Theorem 5.3 reconstructs the same actual $x_h$, so $R_{VW}(V(h))=W(h)$;
applying a reverse or a third transport proves both identities. The
controller's entire input is in its reconstructed control/tapes/latches.
Thus its selected primitive, admission token and reply-dependent continuation
are identical in every presentation. A busy cut admits only that primitive;
a halted cut admits no `Advance`. By Theorem 4.2 the actual successor is
$x_{h'}$ in the same joint image. Decoding before stepping or stepping after
decoding therefore gives that very same successor and all its response
fields, which proves NCR.8. A rejection commitment still has its actual
successor and pending row; it is `some(reject,successor)`. An illegal request
has no transition and is `none`. Neither is replaced by the other. ∎

There is also a direct tree meaning to the source part of transport. On local,
Fetch and literal Read occurrences, support and frontier are unchanged. On a
Native update, the supplied shape transport gives

$$
\operatorname{sh}(r_{h'})=\Theta(\operatorname{sh}(r_h)),\quad
e_{h'}=e_h+1,\quad n_{h'}=n_h+1.
\tag{NCR.9}
$$

The new boundary is the terminal antichain of this shape. Alternatively decode
the current labelled tree using NCR.6 and forward substitution, then replace
each $(p,\alpha)$ by $(p,\beta)$ and each $(p,\beta)$ by
$\{(pL,\beta),(pR,\alpha)\}$ before erasing colours. At a literal request,
the recovered current labelled frontier gives exactly a colour at a frontier
address, branch at a proper prefix and absent otherwise. These formulas keep
the original root and ordered occurrences; no reroot or free parent handle is
introduced.

**Proposition 7.2 (callability and selector closure).** At a named cut $h$,
$M(h)$ computes any finite indexed row of every sealed prefix then available,
or its exact out-of-range refusal. The observer itself actually services these
requests through Definition 3.1. Every $P_{H,J}$ choice and its complete
successor can be obtained from each other view without a new source Read.

Proof. Replay to $n_h$ reconstructs the exact prefix descriptor, actual rows,
tokens and bytes. A finite scan or direct selection of the regenerated finite
row list computes the requested row/refusal. If an actual owned copy is
required, use the corresponding reconstructed reference with the same paid
scan/mailbox/copy routine; no incomplete destination is read. The program's
scheduled calls demonstrate actual success, actual rejection and complete
copies, with NCR.2 preserving their records. Replay-based recall is a second
paid implementation of the same finite lookup function, not a promise that
the extant archive can be accessed for free. Reading the replayed selector
input and evaluating its finite routine produces its exact chosen next
action. Theorem 7.1 gives the original joint successor. ∎

The full atlas is asserted through every tape read/write/move/allocation,
counter increment, row append, copy and rejection cut of the declared hybrid
primitives. It is not extended to substeps of its atomic Native source calls,
arbitrary-entry histories, or freely interleaved consumers. A replay-only
logical payload does not remove the actual producer, mailbox, receiver,
retired versions, meter or interpreter from physical storage.

## 8. Independent command choices require an acquired order relation

**Definition 8.1 (a separate ingress interface).** After acquisition and the
two warm-up updates, grant an explicitly paid, source-independent command
ingress with alphabet
$\{U,R_1,\ldots,R_d\}$, where $U$ is actual Native $\rho$ and $R_i$ is actual
literal Read at the $i$th distinct address of a paid public dictionary. Every
finite command word is admitted at semantic sealed idle cuts; each chosen
command and its actual response is journalled before the next is admitted.
External choice is not an `Op` of `NativeSerialMachine` and is not presumed
determined by the source. Apart from this command word, the canonical finite
command encoding, ingress expansion, journal and allocation schedules are
fixed. There are no independently varying waiting ticks or input encodings.
This section's family consists of those sealed
semantic cuts and does not assert four-view microcut minimality for the
enlarged runtime.

For a histogram $\mathbf m=(b,m_1,\ldots,m_d)$, let $b$ be the number of $U$
commands, $m_i$ the number of $R_i$ commands, and $N=b+\sum_i m_i$. For a
fixed acquired seed $u$, all such words finish at $\rho^{b+2}u$. Define the
spatial base

$$
Z(h)=(\operatorname{Pos}(r_h),\mathbf m).
\tag{NCR.10}
$$

This base already includes the entire unlabelled current ordered support,
not a coarse numerical projection. A supplement is a causally acquired finite
label, rather than advice chosen using the future schedule.

**Theorem 8.2 (exact conditional chronology ambiguity).** Every nonempty
$Z$-fiber determines $u$ and has exactly

$$
F(\mathbf m)=\frac{N!}{b!\prod_{i=1}^d m_i!}
\tag{NCR.11}
$$

different complete executed command histories. If the task includes paid
indexed lookup of the ordered command rows, an exact supplement to $Z$ must
have at least $F(\mathbf m)$ values in that fiber. Conditional fixed-width
data length is therefore at least
$\lceil\log_2F(\mathbf m)\rceil$ bits, and this width is attainable.

Even after adding the complete unordered multiset of actual
$(\text{epoch},\text{address},\text{reply})$ Read rows, a fiber with $n_j$
distinct-address Reads at each epoch $2+j$, $0\le j\le b$, contains exactly
$\prod_{j=0}^{b}n_j!$ histories. Repeated indistinguishable reads within an
epoch instead give the corresponding multinomial factor.

Proof. The histogram fixes $b$. The shape in $Z$ is
$C(\rho^bu)$, so the already supplied inverse $D$, followed by $I^b$, recovers
$u$. Thus no missing source shape or predecessor accounts for this ambiguity.
Every ordering of the command multiset is executable: Native updates are
unconditional and each finite address has a defined four-valued reply.
At a Read in epoch $2+j$, the response is exactly
$\operatorname{Read}(p_i,\rho^{2+j}u)$. Different command words give different
ordered event words, since erasing replies and epochs recovers their command
tags and literal addresses. Position counting gives NCR.11, and every counted
word is realized on this same actual seed.

Two different words first differ at some row. A paid indexed Fetch at that
row returns different request tags or addresses, regardless of whether their
replies happen to agree. A supplement that identifies those two words cannot
answer that allowed task correctly on both. Pigeonhole counting proves the
alphabet and fixed-width lower bounds.

If all epoch-tagged unordered rows are fixed, each Read is already assigned
to a specific update interval. The $b$ updates have their one chronological
order, and the remaining freedom is to permute the $n_j$ distinct-address
rows within each interval independently. Their exact count is
$\prod_j n_j!$; equal rows divide by the respective multiplicity factorials.
Every such permutation again executes on the same source and has the
specified records. ∎

**Theorem 8.3 (causally acquired sharp complement).** A public enumerative rank
of the actually executed command word, conditional on its current histogram,
attains Theorem 8.2's supplement bound at each sealed semantic cut. The pair
$(Z,\operatorname{rank})$ has exactly the task kernel for arbitrary future
Native commands together with complete historical-row lookup on this
separate interface.

Proof. Fix a public alphabet order. For remaining counts $\mathbf c$ of total
$l>0$, the words beginning with an available symbol $a$ form a consecutive
lexicographic block of size

$$
F_a(\mathbf c)=
\frac{(l-1)!}{(c_a-1)!\prod_{q\ne a}c_q!}.
\tag{NCR.12}
$$

Rank adds the sizes of available preceding-symbol blocks and recurses after
decrementing $c_a$. Unranking chooses the unique block containing the given
integer, subtracts its preceding blocks and recurses. The blocks are disjoint
and their sum is $F(\mathbf c)$ because they partition by first symbol.
Induction on $l$, with the sole empty word at $l=0$, proves a bijection with
$\{0,\ldots,F(\mathbf m)-1\}$. This is Cover's credited enumerative method.

After an actual command has committed, unrank the old finite prefix, append
that acquired command, increment its histogram and rerank the resulting
finite word. The new version is sealed before admitting another command.
This algorithm needs no future histogram or command. Interim versions,
scratch, the pending command and its result remain actual charged work.
At the sealed cut the logical rank field uses the claimed conditional width;
this is not a bound on all simultaneous constructed storage.

Given $(Z,\operatorname{rank})$, recover $u$ by Theorem 8.2, unrank the actual
word, replay it on $\rho^2u$ and regenerate every epoch/address/reply row.
Equal $(u,w)$ therefore gives identical task behavior for equal future
commands. If $w$ differs, a historical-row lookup separates it; if one word
is a proper prefix, an in-range row versus an executed out-of-range refusal
separates them. If $w$ is equal but $u$ differs, their current trees differ by
substitution injectivity. Two different finite labelled ordered trees have a
different literal reply at an address: follow common branches to the first
differing constructor/colour. A Native Read there separates them. Hence task
equivalence is exactly equality of $(u,w)$, which the stated code captures.
All arithmetic, source-free replay, rank bits, ingress, row accesses and
copies are paid finite string routines. ∎

The same proof applies to distinct within-epoch row permutations with the
product-factorial alphabet. These are conditional source-recovered ordering
bounds, not lower bounds for the single fixed controller of Sections 3–7.
Neither a scalar update epoch nor a source code contains this independent
order. A primitive counter cannot be used as a covert command-word encoder.
The count here grants an equal *semantic command count*; no assertion is made
that different command orders have equal expanded tape runtimes. If a runtime
length is additionally supplied as side information, the relevant count is
its conditional fiber, not automatically NCR.11.

## 9. Source, operation and resource correspondence

**Proposition 9.1 (one-execution bill).** For an initial $m$-leaf tree,
Definitions 3.1–3.2 use exactly

$$
Q_{\mathrm{NativeRead}}=2m-1+J,\qquad
U_{\mathrm{NativeRho}}=2+J,\qquad
Q_{\mathrm{Fetch}}=J+2.
\tag{NCR.13}
$$

The supplier projection has exactly $2(m-1)$ acquisition branch-local actions,
in addition to the expanded tape work. Literal address-letter traffic is

$$
\sum_{p\in\operatorname{Pos}(u)}|p|+
\sum_{i=0}^{J-1}(i+1).
\tag{NCR.14}
$$

Proof. `native_source_producer` visits each actual node once; a full binary
$m$-leaf tree has $2m-1$ nodes and $m-1$ branches. Its displayed
`productionTrace` has two local actions per branch. Warm-up has two updates
and no Read. Each round has one Read, one update and one Fetch; completion
has two additional Fetches. The addresses are the supplier's actual preorder
node addresses and the declared $L^{i+1}$, respectively. ∎

The cited code contributes two bits per leaf and one per branch, hence
$2m+(m-1)=3m-1$ bits. Framing, identity and installation work are additional.

This is a raw-call count and an address-word count, not an acquisition optimum
or total runtime bound. In the following correspondence, every actual primitive
has one routine-purpose tag as in PR57.D9; no occurrence is billed twice.

| Resource | What is actually retained or paid |
| --- | --- |
| Source supply | The original installed tree/root occurrence, any private code, input bits, assembly and installation work. This is separate from observer acquisition and never source-specific free public advice. |
| Public control | Literal boot, $H,J,\xi$, finite routine/interpreter bits, dictionary if Section 8 is used, and their writes. No code selected after seeing $u$. |
| Native operations | NCR.13–14; actual source substitution work is separate from a tape opcode fee. In an explicit occurrence-tree implementation it must be charged on all touched/new tree cells. |
| Acquisition payload | Actual $2m-1$ replies with addresses, the producer frames and paid acquired seed serialization. The seed code has $3m-1$ payload bits in the cited prefix format, before framing/identity. |
| Clock | One actually constructed receipt per primitive; update/fence symbols have fixed finite size. Closed-fence scans, epoch counting, subtraction, numeral serialization and copies are additional work. |
| Callable archive | Complete request/response/epoch/reference rows, append, seals, Fetch scans and both success/rejection schedules. Rows do not appear merely by naming their index. |
| Copies and outputs | PR57's two-loop channel body costs $8k+4$ core occurrences for $k$ bits after positioning. Allocation/zeroing, `Home`/`Seek`, identities, framing and printing are additional. Sender, mailbox and receiver coexist. |
| Replay and transports | Finite local tree computation, tape/state simulation, inverse recognition, full successor serialization and decoder workspace. No new physical source Read is needed; this is not zero work. |
| Storage | All constructed source/work/archive/code/meter/mailbox/receiver cells, latches, tokens and retired versions simultaneously. Logical seed/counter or rank payload is not total storage. |
| Independent choices | Paid ingress and acquisition of the actual command, histogram, current rank, temporary unranked word, arithmetic and row writing. Theorem 8.2 prices conditional retained data, not this entire bill. |

If $u$ has at most $H$ leaves, every source during this finite observer has at
most $2^{J+2}H$ leaves, since one substitution at most doubles leaf count.
Thus a separately proved literal-port implementation with public capacity
$K\ge2^{J+2}H$ would avoid source-capacity rejection on these calls. This is
only a sufficient finite capacity bound. It does not establish the missing
implementation correspondence by itself. TM57 at capacity $H$ can reject
$\rho\beta$ when $H=1$, while Native cannot; their menus remain different.

## 10. Falsifiable boundaries and finite evidence

**Example 10.1 (the two-update fence has mathematical content).** Before
warm-up, $\alpha$ and $\beta$ have the same unlabelled support. At one update,
$\beta$ and $\langle\alpha,\alpha\rangle$ have the same substituted shape
$A$. The existing two-step theorem removes these shape collisions. An atlas
using the unlabelled views without the acquired warm-up fence is therefore
not established by Theorem 5.3.

**Example 10.2 (epoch and chronology are different acquired relations).**
$\alpha$ after four actual updates and $\rho^2\alpha$ after two have the same
current tree. The absolute executed epoch is not recoverable from that tree
alone. At two warm-up updates, the initial seed $\alpha$ gives a leaf reply
at $L$ in the first round, whereas $\langle\alpha,\beta\rangle$ gives branch
there; the programmed Fetch therefore chooses success versus executed
rejection. For every source, the final two Fetches supply both outcomes.
A literal Read below a leaf returns executed $\mathsf{absent}$ and is a
successful source observation, regardless of the archive index outcome.

**Example 10.3 (why a sealed-row counter does not index all cuts).** Consider
the cut after Native Read commitment and the next cut after writing one row
bit. The source, update epoch, sealed semantic row prefix and pending semantic
event can agree, but the writable tape cell, head/phase and remaining work
differ. A clock counting only sealed rows does not distinguish them. The
receipt count $n$ changes at every primitive, including that write. If a
primitive implementation removes the atomic receipt convention, it must add
its meter-update phase to the reconstruction index; a stale stored numeral
alone does not justify the all-cut theorem.

**Example 10.4 (exact order fibers).** Four distinct Reads and two updates
give $6!/2!=360$ command histories with one source-recovered spatial base,
requiring nine conditional fixed-width bits. If their complete epoch records
fix Read counts $(2,0,2)$, four within-epoch orders remain, requiring two bits.
Zero Reads gives one order, and a single Read with $b$ updates gives $b+1$
orders before epoch assignment is supplied.

**Finite evidence 10.5 (bounded mathematical checks).** Finite checks of tree
decoding, schedule ranking and separation test the displayed finite algebra
and command interface. The exact checked domains and results are:

| Finite domain | Result |
| --- | --- |
| All 102 labelled ordered trees with at most four leaves, each at actual epochs 2 through 6 | 510 support/frontier-to-seed inversions agreed with the initial tree; each boundary's prefix closure and terminal positions agreed with its actual support. |
| Those 510 current trees, all 63 literal addresses of length at most five | 32,130 labelled-frontier replies agreed with independent recursive tree Read, including absent. |
| The semantic calls of Definition 3.2 on all 102 seeds with $J=2$ | All terminal sources were $\rho^4u$; raw source/row counts agreed; 104 Fetch successes and 304 executed index rejections occurred, with both outcomes on every source. |
| Histograms $(2)$, $(2,1)$, $(1,1,1,1)$, $(2,1,1,1,1)$ and $(2,2,1)$, with first coordinate counting updates | All 418 multiset words had their exact lexicographic ranks and inverses; 2,835 prefix rank/unrank checks agreed using only each prefix's histogram. |
| Both one-leaf seeds and all four two-leaf seeds, four distinct-address Reads and two updates | All 2,160 actual command histories, 360 per seed, had a common terminal source within each seed and distinct full command traces. The fixed epoch partition $(2,0,2)$ had exactly four orders. |

These checks are not an execution of the expanded tape
interpreter, a model of electrical timing, a proof of source-call atomicity,
or a new Lean check. The complete proofs above, rather than enumeration,
carry the universal ordinary statements. No experiment program or command
transcript is part of this theory source.

## 11. Primary literature, reuse and the remaining bridges

**Literature statement 11.1 (conditions, not borrowed acquisition).**

| Primary source | Verified hypothesis and correspondence |
| --- | --- |
| J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce and A. Schmitt, *Combinators for Bi-Directional Tree Transformations: A Linguistic Approach to the View Update Problem*, TOPLAS 29(3), article 17; [author full version](https://www.cis.upenn.edu/~bcpierce/papers/lenses-toplas-final.pdf), Definitions 3.1–3.3, PDF pages 6–7 | `literature-attested`: get is partial, putback receives both the updated abstract view and the old concrete state; GetPut/PutGet are not totality. A lens law does not acquire the erased tree, clock or order complement. Here the actual-image inverses and dynamic successors are explicitly constructed instead. |
| N. Lynch and F. Vaandrager, *Forward and Backward Simulations, Part I: Untimed Systems*, Information and Computation 121(2), 214–233; [author copy](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf), Section 3.2, Lemma 3.8 and Theorem 3.10, PDF pages 11–12 | `literature-attested`: initial states must be related and each implementation step must have a finite matching abstract fragment from every related state; this implies trace inclusion. Theorem 4.2 supplies actual initialization/step witnesses for this model. Inclusion alone supplies neither exact reverse recovery, individual kernel equality nor equal costs. Our atlas does not erase visible tape steps as if they never occurred. |
| C. H. Bennett, *Logical Reversibility of Computation*, IBM Journal of Research and Development 17, 525–532; [complete paper text](https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html), introduction and discussion of history redundancy | `literature-attested`: a deterministic computation and its generated history have reusable redundancy; reversible simulation additionally preserves output before reversing computation. The present ordinary replay uses an acquired seed and a reached prefix position. It is not physical uncomputation, reversible archive erasure or a thermodynamic bound. |
| T. M. Cover, *Enumerative Source Encoding*, IEEE Transactions on Information Theory 19(1), 73–77; [author-hosted paper](https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf), Proposition 2, inverse algorithm and Example 4 | `literature-attested`: finite-alphabet lexicographic ranking uses counts of prefix blocks and has an inverse; permutation ranking is classical. NCR.12 specializes that tool. Same-source Native realizability, row-lookup separation, conditional fibers and causal paid retention are the additional application obligations proved here. |

**Statement 11.2 (result classification).** Theorems 4.2, 5.3, 6.3 and 7.1
and the actual-interface applications in Theorems 8.2–8.3 are `repo-derived`
ordinary constructions/proofs using the cited suppliers. Neither the
substitution/support decoders, the producer, generic simulation/kernel
principles nor enumerative ranking are new. The literature correspondence
does not give a global originality or priority certificate. No assertion is
made that all stronger exact suppliers are absent elsewhere in the repository.

**Open obligations 11.3 (what changes the next research action).**

1. A source-bound implementation must couple the literal Native port to the
   actual installed finite-cap source while retaining source-call busy cuts,
   code/workspace costs and success/rejection correspondence. TM57's paid
   archives already exist; the missing claim is this particular literal-port
   coupling, not archive or update existence. A separately declared paid
   literal instrument could supply it; Clifford Read cannot simply be renamed.
2. Arbitrary public requests, random input, interrupts or independent consumer
   schedules require an acquired exogenous relation. Section 8 gives an exact
   chronology complement for its semantic command family. Extending all four
   natural views and their individual kernels through the enlarged runtime's
   busy cuts remains open; its histogram/rank theorem alone does not do so.
3. The present histories begin at their actual declared source entrance and
   authenticate newly acquired rows by ownership and causal copying. An
   arbitrary-entry transcript-import/authentication service, and a method for
   recovering events before that entrance, are not supplied.
4. Grafts, rerooting or noninjective source changes need their own recoverable
   operation context and chronology. NCR.6 relies on pure actual $\rho$;
   a current numeric boundary or an independently possible coordinate tuple
   cannot replace that common-source certificate.
5. The public finite bounds give pointwise finite trees and computations.
   Uniform physical capacity, effective all-size implementation certificates
   and a realized coherent infinite thread require new proofs. Finite
   compatible views do not imply an actual infinite-source realization.
6. The original stationary task remains $F_D=\operatorname{pair}(\alpha,v)$,
   $\operatorname{height}(v)\le D$, with source-blind paid preparation before
   late $p$, source information only through charged original-root literal
   Reads, complete retained source-dependent control/buffers/timing, all
   $R$-starting $|p|\le D$, at most one late original-root Read and authentic
   $k$, followed by prediction for every $k\ge0$. No new stationary endpoint,
   $M_1(D)$ bound, sharp $\lambda$, original acquisition service or full
   four-expression completion follows from this acquired dynamic component.

The concrete bridge established here is an actually acquired seed, an
injectively evolved current support, and an honest primitive prefix position
for one deterministic flight. The next broader bridge is acquisition and
transport of genuinely independent choices, with the same complete-state and
individual-kernel requirements.

## 追加锚（本行以下为增补区）
