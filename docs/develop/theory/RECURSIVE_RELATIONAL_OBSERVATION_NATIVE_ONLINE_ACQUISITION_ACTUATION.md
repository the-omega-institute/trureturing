# Recursive relational observation: online acquisition and local actuation

> Mathematical reference input, with ordinary proofs and no new Lean
> certification. Published entries are immutable; subsequent additions use
> new numbered sections after an append anchor. This is a continuation of
> [Entry Reference and Graft Order][ER], abbreviated ER below.

## 1. One carrier, an unknown input and three streaming services

**Definition 1.1 (logical values and the new model).** Use ER Definition
1.1's finite free ordered trees
$\mathcal T=\{\alpha,\beta\}\cup\langle\mathcal T,\mathcal T\rangle$
and substitution $\rho\alpha=\beta$,
$\rho\beta=\langle\beta,\alpha\rangle$, distributing over pairing.
Put $E=\rho^2$, $A=\langle\beta,\alpha\rangle$,
$B=\langle A,\beta\rangle$, and $a_0=\langle\alpha,\alpha\rangle$.
Retain precisely ER Definitions 9.1 and 9.7's logical commands
$U=\rho$, $L(x)=\langle\alpha,x\rangle$,
$R(x)=\langle x,\alpha\rangle$, their left-to-right evaluation $F_w$,
and $j(u)=\langle a_0,u\rangle$. In particular

$$
E(\alpha)=A,\quad E(\beta)=B,\quad
E\langle s,t\rangle=\langle E(s),E(t)\rangle.
\tag{OA.1}
$$

The new model $\omega$ has every finite $u\in\mathcal T$ as an input
and every finite word over $\Lambda=\{\mathsf U,\mathsf L,\mathsf R\}$
as a command continuation. Its only varying inputs are the initially
installed actual tree and subsequently supplied command bits. The
receiver initially has no acquired tree, height, size, source-dependent
code or table. Its services have these mathematical input/output types;
the displayed $x$ is a proof parameter, not a runtime argument:

| Mode | Actual entrance source | Actual exit source | New receiver table |
| --- | --- | --- | --- |
| Boot | compound $x$ | $E(x)$ | $\mathsf A(x)$ |
| Scan | $E(x)$, compound $x$ | $E(x)$ | $\mathsf A(x)$ |
| Update | $E(x)$, compound $x$ | $E(\rho x)$ | $\mathsf A(\rho x)$ |

Here $\mathsf A(t)$ lists all $(p,r_t(p))$ at actual node addresses of
$t$ in preorder, omitting absent addresses. Boot is used once on the
actual $j(u)$; Update implements U; Scan follows a graft. These service
contracts will be proved in Theorem 3.2, rather than supplied as
whole-tree operations. The initialized return, not installation of the
unknown input, is the beginning of the returned-command recovery domain.

**Assumption 1.2 (owned occurrences, initialization and observations).**
Fix a root port $\pi$, owner $o$, left/right orientation and finite
program before choosing $u$ or any bits. Source nodes have three fields
$(\mathsf{tag},L,R)$. A terminal has tag $\alpha$ or $\beta$ and two
null children; a branch has tag $\mathsf b$ and two different nonnull
children. The active source is an occurrence tree reachable from
$\pi$. There is no sharing between its two subtrees. Detached nodes
remain allocated. There is no competing writer, interruption,
revocation, allocation choice or scheduling input.

The input installation supplies this actual unknown $u$, with canonical
source-node names allocated in preorder starting at zero, its actual
child fields and root attachment. It supplies no description to the
controller. Installing its $N(u)$ nodes, $N(u)-1$ child links and root
attachment is part of the backing account. The observer's chronology
starts after this installation. The observer can capture the reference
in $\pi$ but cannot inspect an allocation index, perform arithmetic on
a reference, or inspect installation material. Reference equality,
null tests and following an actually held field are allowed.

The owner has static read/write/allocation rights over this component,
fresh staging, local cells and retained material. This is a separate
operational premise, not a consequence of source recovery. Reads of one
field, child follows, assignment of one indicated field, allocation of
one bounded cell, finite-tag/reference tests, one-bit input, one-token
output and finite control edges are the operation basis. No source
primitive copies, compares, substitutes or decodes an unknown subtree.
Allocation returns the next name of its cell type; each type has a
fixed canonical order. Reference widths are charged separately.

After the fixed local installation of Definition 1.3, the observer
prepares three fresh known nodes for $a_0$, links
them, captures the old root and allocates one fresh branch above
$a_0,u$. It assigns that branch to $\pi$. This actually makes $j(u)$,
without reading any unknown tag. It then starts Boot. In particular
there is no complete raw acquisition followed by a global encoding
operation in this initialization.

**Definition 1.3 (local backing and deterministic row convention).**
Sender and receiver are control roles of this one owner, separated by
a one-token mailbox. Their work stacks are different. A sender frame
has $(\mathsf{node},\mathsf{next})$; a receiver frame has
$(\mathsf{word},\mathsf{next})$. Other cell types are packet cells
$(\mathsf{token},\mathsf{next})$, rows
$(\mathsf{word},\mathsf{label},\mathsf{next})$, snoc words
$(\mathsf{previous},\mathsf{letter})$, and forward words
$(\mathsf{letter},\mathsf{next})$. The empty word is a fixed null
sentinel. An operand row has the row payload but belongs to its own
retained list. An invocation has
$(\mathsf{operand},\mathsf{packet},\mathsf{focus},\mathsf{old},
\mathsf{new})$, with old/new initially null.
A completion has $(\mathsf{invocation},\mathsf{previous})$.
A service descriptor has
$(o,\pi,\mathsf{mode},\mathsf{entry},\mathsf{tableHead},
\mathsf{tableTail},\mathsf{previous},\mathsf{state})$.
Its entry is the actual chronological-tail reference at entry.

One fixed bank has a holder and sixty-four one-value slot cells,
created and attached in their slot order after input installation and
before known-source preparation, initially null. Of its slots,
the first thirty-two, in order, hold sender head, receiver head, focus,
current word, left source child, right source child, probe node, packet
head, packet tail, packet cursor, new table head, new table tail,
operand head, operand tail, active operand, invocation, completion head,
snoc cursor, forward head, forward cursor, path letter, path next,
source cursor, parent, attachment side, old root, descriptor, output
cursor, saved field, mailbox value, mailbox availability and command
prefix. The next nine hold staging nodes in preorder. The remaining
twenty-three are scratch or unused null slots, cleared in index order.
Finite latches hold mode, packet position, decoded constructor,
template position and instruction position. Addresses and stacks are
not unbounded values in a finite latch.

The operations in §§2–4 expand by the following convention. Named
reads, follows, tests, births, assignments and control edges execute
in their written order, one row each. Reading a cell's fields means
one row per field, in the displayed payload order. A stack pop reads
its fields and assigns its head to the read next reference. A push
birth initializes the displayed fields and assigns its stack head.
Appending a list cell initializes its fields, assigns a former tail's
next if nonnull, and assigns head/tail slots, in that order; the
nonnull test is a separate row. Bounded slot/latch assignments that
retain a returned value and select its next instruction are coeffects
of that row. There is no extra idle edge. Iteration always returns to
the named head/null test. Every exit clears the scratch slots in
increasing index order, retaining the designated list/descriptor roots.
The NodeDone block first clears slots 3–10, 15–16, 18–26, 29–31 and
33–64 in increasing order, leaving stack heads, table endpoints,
operand endpoints, completion head, descriptor, output cursor and
command prefix intact. Clear packet-position, constructor and template
latches, retain mode, then execute its single NodeDone edge to the
work test. A NodeDone checkpoint is the successor of that last edge.
Before a new packet, set packet endpoints and cursor null. At service
entry set the new-table endpoints, operand endpoints and output cursor
null, retaining the previous descriptor before replacing slot 27.
At Return clear all slots except 17 and 27; completion head and the
current descriptor are the only bank roots retained there. The current
table endpoints remain in that descriptor. At the next service's
entry the old descriptor is read only for linking its reference as
previous, never for table contents. Fresh temporary values not assigned
a named role use slots 42–64 in lexical order of their introduction,
reusing a slot after its last use in the displayed block. All displayed blocks have
fewer than twenty-three simultaneous such values. This fixes a finite
instruction scheme, including its conditional branches and clear masks;
a list traversal is never one row.

Each executed row appends one event with predecessor, opcode, actual
operand references, read value or emitted token and its bounded slot
coeffects. Events have a fixed arity bound, since the row alphabet and
payload arities are finite. Their initialization and tail operations
are charged. A false test has no executing successor, event or output;
an action disabled at that instruction likewise has no effect.
Invocations, completions, packets, words, rows, stack cells, old
descriptors and events are retained. Clearing a root does not release
their backing. Event contents, earlier tables and earlier outputs are
not operand-readable by this controller.

## 2. Receipt, node construction and the leaf publication boundary

**Definition 2.1 (source visit and actual packet).** Service entry
reads the actual chronological tail into saved scratch, marks any
current descriptor held, captures the actual $\pi$ reference, and
creates the new descriptor with that saved entry, the previous
descriptor reference, state building and null table endpoints. It
pushes one sender frame for that root and one receiver frame for
the empty word. Test the sender head. A nonnull head is popped to
focus; pop the receiver frame to the current word $q$. An empty sender
head requires an empty receiver head and empty mailbox and enters End.
Theorem 3.2 proves that these tests succeed.

In Boot, probe focus.tag and deliver exactly its one literal token
$\alpha,\beta$ or $\mathsf b$. In Scan and Update, probe focus.tag,
requiring branch, follow its left field, probe that child's tag, follow
its right field, and probe that child's tag. Erase terminal labels
before transmission, giving $\mathsf d$ for either terminal and
$\mathsf b$ for a branch. If the child statuses are $(\mathsf b,
\mathsf d)$, additionally follow the held left child's left field,
probe its tag, follow that same child's right field and probe its tag,
erasing these as well. All other continuations are determined by this
fixed finite status table. The only accepted complete packets are

$$
\begin{array}{c|c}
\text{packet in probe order}&\text{receiver constructor}\\ \hline
(\mathsf b,\mathsf d,\mathsf d)&\alpha\\
(\mathsf b,\mathsf b,\mathsf d,\mathsf d,\mathsf d)&\beta\\
(\mathsf b,\mathsf b,\mathsf b)&\mathsf b .
\end{array}
\tag{OA.2}
$$

After *each* probe, before another source probe/follow, Offer requires
empty mailbox, writes that token and marks it offered. Take reads the
offered token into the receiver latch. Arrival allocates a receiver
packet cell with that value and appends it. Acknowledge clears mailbox
availability. Only then can the next source operation occur. The
receiver's finite packet parser reads those cells in their arrival
order. At three encoded tokens it either accepts alpha/branch or
requires the two further beta tokens. Boot accepts at one token.
PackDone is a separate finite edge checking that both sender and
receiver packet controls finished and the mailbox is empty. Unexpected
packets have no accepting edge. Packet lists are distinct per visit,
with no old-table, event or whole-source-description input. Their
payload contains no source reference or supplied address.

The encoded probes use the existing erased-$E$ grammar of ER Definition
20.5 and [ABT Theorem 12.1][ABT]. The beta packet probes the right
child before the left grandchildren: its order is specified here,
not borrowed from an assumed preorder body. In the branch case the
child-root probes are branch for every possible encoded child; they
do not disclose that child's unknown logical constructor.

**Definition 2.2 (receiver-only rows and paired work).** After PackDone,
the next branch/leaf choice is the receiver parser's constructor.
For a branch, append the new table row $(q,\mathsf b)$, create snoc
words $qL,qR$, and push receiver frames for right then left. In Boot
follow the actual focus's left and right fields now. In encoded modes
use the two references actually followed in Definition 2.1. Push sender
frames for those right then left references. Execute NodeDone and
return to the head test. The order of all these operations is the
written order, so the stacks are paired again before NodeDone.

For a leaf with decoded label $\ell$, Scan merely appends $(q,\ell)$
and executes NodeDone. Boot and Update instead create and append an
operand row $(q,\ell)$, retaining its returned reference as active
operand and retaining the actual current packet head.
From this actual operand, read its word and label fields. Boot appends
$(q,\ell)$ to its new table. Update appends
$(q,\beta)$ for $\ell=\alpha$; for $\ell=\beta$ it appends
$(q,\mathsf b)$, creates $qL,qR$, and appends $(qL,\beta)$ followed
by $(qR,\alpha)$. They then enter Definition 2.3 with that actual
operand and its read word/label. These new rows are the literal
$\rho\ell$ expansion chosen by that received label. The new child
words are not pushed as source work. Leaves created by an edit are
not subsequently acquired as old logical input nodes in this service.

The old live descriptor, if any, is linked as previous and held aside
on entry. No row/word/leaf-list field reachable through it is read by
the service. Every new nonempty word originates in the receiver's
displayed snoc extensions; every new operand label originates in the
current receiver packet parser. The two stack heads and fixed empty
word supply no unknown tree value.

**Definition 2.3 (actuation from the fresh operand).** This is a
replacement fragment, not an atomic patch. The actual operand
row's word and label read in Definition 2.2 select $p,\ell$.
Create an invocation pointing
to that row, this packet and the actual sender focus. Reverse the snoc
word into a fresh forward list: test its cursor for empty; if nonempty
read last letter, read previous word, prepend a forward cell, and repeat.
Capture $\pi$ and walk that forward list, reading letter then next and
following the indicated source child; save the actual previous source
reference and side on each follow. At exhaustion require the reached
node equal the held focus, and store it as invocation.old. All service
inputs are compound, so every leaf word is nonempty.

The old/target template pair, selected by the receiver label, is

$$
\begin{array}{c|cc}
&\text{old tile}&\text{target tile}\\ \hline
\mathrm{Boot},\ell&\ell&E(\ell)\\
\mathrm{Update},\ell&E(\ell)&E(\rho\ell).
\end{array}
\tag{OA.3}
$$

These are fixed finite lists: $E(\alpha)=A$, $E(\beta)=B$,
$E(\rho\alpha)=B$, $E(\rho\beta)=\langle B,A\rangle$.
Use exactly their literal preorder positions and tags. For each old
position, in preorder, reset a probe cursor to the held old root,
follow that position's fixed letters, read its tag and require the
listed literal tag, then read its left and right fields and require
null at a terminal and nonnull at a branch. This is a bounded
field-by-field guard, not a whole-tree equality operation.

Allocate each target node in preorder, with its literal tag and null
children, retaining at most nine staging references. Record the first
returned reference as invocation.new. For each nonroot target position,
in preorder, test its parent's designated staging field for null and
assign its actual new reference to that field. Read the saved source
parent's saved side field and require equality to invocation.old.
Publish assigns invocation.new to that *one* field. This is the only
active-source assignment of the fragment. Append one completion cell
pointing to the invocation, execute NodeDone with its specified clear
mask, and resume the pending work test. The invocation
retains both old and new roots before scratch is cleared. There is
no whole old-leaf list, next-leaf oracle, refresh or second acquisition.

The source guards and staging discipline are the local mechanisms
credited to ER Definitions 16.4–16.5 and Theorem 17.1. Their initiating
complete leaf list and Next/Handoff/CellDone schedule are *not* imported.
Here the operand is born during this visit, and NodeDone resumes the
two unfinished acquisition stacks. Hence ER's exact fragment tariffs
do not apply to this fragment.

## 3. The remaining-observation relation and the online correspondence

**Definition 3.1 (partial observation and mixed source).** At a
NodeDone checkpoint let $H$ be the partial old logical tree obtained
by filling the next preorder hole with the constructor decoded at
each finished visit: a leaf closes that hole; a branch replaces it by
an ordered pair of holes. Let $\mathcal F(H)$ be its holes in left-first
pending order, and $D(H)$ its acquired leaf positions. Initially
$H=\square$. Hole fillings are proof parameters, not stack contents.

For a fixed service input $x$, let $P_H(x)$ replace each old leaf
$p\in D(H)$ by $\rho(x|_p)$, and no others. Define $\operatorname{enc}_H(x)$
by replacing those same old leaves by $E(x|_p)$. The mixed-source
relation at a checkpoint is

$$
r=\begin{cases}
\operatorname{enc}_H(x)&\mathrm{Boot},\\
E(x)&\mathrm{Scan},\\
E(P_H(x))&\mathrm{Update}.
\end{cases}
\qquad
r|_p=\begin{cases}x|_p&\mathrm{Boot},\\E(x|_p)&\mathrm{Scan,Update}
\end{cases}
\quad(p\in\mathcal F(H)).
\tag{OA.4}
$$

The sender stack contains exactly the actual roots of these latter
subtrees, in that order. The receiver stack's word values are exactly
their addresses, in the same order. Proper-prefix nodes on all these
paths are unchanged branch occurrences. The new table is the preorder
row prefix of $x$ in Boot/Scan, and of $\rho x$ in Update, ending after
the entire expansion of the last decoded old node. A branch contributes
one row; an Update beta leaf contributes its three-row expansion.

Between checkpoints the pending remainder excludes the currently
popped subtree. Its roots, their entire descendant fields and all
proper-prefix source paths are preserved by the operations on this
visit. Before Publish, the current observed leaf tile is preserved
as well. These equalities of actual rooted subtrees are the
remaining-observation relation; no set of promised replies is supplied
to the controller.

**Theorem 3.2 (actual receipt, framing, termination and table equality).**
For every finite compound $x$, each of the three services, entered
under Assumption 1.2 with its stated actual source and empty new work,
has one finite successful execution under the prescribed Advances.
Every finite prefix obeys the interior preservation clause of
Definition 3.1; every NodeDone obeys all of (OA.4), its paired stacks
and its new-table clause. Each visit's operand word/label, when used,
comes from its actual receiver arrivals and fresh word/row constructors.
All source walks, guards, staging tests and attachment tests succeed.
At End, the actual source and actual newly constructed table have
exactly the input/output correspondence of Definition 1.1. No complete
old acquired table, retained event payload or unknown subtree description
is used in this execution.

Proof. Initially the captured source root and empty word give the
single matching frontier $\{\varepsilon\}$, with no acquired leaves
and no new rows. This proves the initial relation, including (OA.4).
Suppose it holds before a visit. The popped roots and word denote
the same next old subtree at $q$. For Boot the actual root tag is
exactly its logical constructor. For encoded modes (OA.1) gives,
respectively, root/child statuses $(\mathsf b,\mathsf d,\mathsf d)$,
$(\mathsf b,\mathsf b,\mathsf d)$, and
$(\mathsf b,\mathsf b,\mathsf b)$. The middle case has two terminal
left grandchildren. Thus (OA.2) accepts exactly its actual constructor.
This is the credited ABT grammar, here realized by the listed probes.

After $i$ acknowledgements the receiver packet contains precisely the
first $i$ actual offered values and the mailbox is empty. Offer/Take/
Arrival/Acknowledge extends this assertion by one: the new cell's value
is the actual value read at Take, and no new probe or offer precedes
the acknowledgement. A parser read therefore obtains a received token,
not a proof parameter. The fixed one/three/five-token tests establish
the next decoded constructor before any construction uses it.

At a branch the source follows are real and both children exist.
The snoc extensions have the actual values $qL,qR$. Pushing right then
left on both stacks replaces one frontier subtree by its two children,
preserves their order and appends exactly the branch row. Neither
branch fields nor an unread child subtree is written. The new $H$,
the table prefix and (OA.4) follow. This is the ordinary preorder
frontier step; it is not an assumption of a finished traversal.

At a leaf, $q$ and $\ell$ in the new operand are exactly those just
obtained. Reversing its snoc chain gives a forward spelling of $q$:
after $i$ prepends, the snoc cursor is its length-$|q|-i$ prefix and
the forward list spells its removed suffix. The source walk then
follows its prefixes from the current $\pi$. Every proper prefix is
an unchanged branch of the old input skeleton. Previously processed
old leaves are prefix-incomparable with $q$ and with every pending
frontier hole. Therefore the reached root is the actually popped
focus, with its actual saved parent and side. Since $x$ is compound,
$q\ne\varepsilon$. Before publication its tile is precisely the old
tile in (OA.3). Every literal guard, including both null/non-null
child tests at every listed node, consequently succeeds.

Fresh target roots come only from actual allocations. Each nonroot
target has exactly one earlier parent in the fixed list; each designated
child field is used once. Null tests and individual writes therefore
build exactly the listed target, disjoint from active and pending
source material. The final attachment check still reads the saved
old root, by exclusivity. Publish changes just that attachment and
its descendants. Every pending hole is incomparable with the processed
leaf, so its rooted source subtree and its proper-prefix path remain
identical, including actual references. This proves the remainder
clause at every fragment cut and its extension across Publish.

For Boot the one changed tile is $\ell\mapsto E\ell$; for Update
it is $E\ell\mapsto E(\rho\ell)$. Distributivity in (OA.1) proves
the corresponding new mixed-source equation. The receiver's new rows
are respectively the original leaf or its $\rho\ell$ expansion, so
its table prefix extends by precisely the same logical contribution.
No new source work is pushed for that expansion. Scan has no source
write and extends its prefix by the original leaf. Completion and
NodeDone change no active-source field, and resume exactly the old
pending stacks. There is one completion per editing visit because
the control leaves its append and cannot revisit it without a new
operand. This completes the checkpoint induction and all interior
preservation cases.

There are exactly $N(x)$ visits: the work rule expands only original
logical branches and consumes each original logical node once.
Equivalently induct on $x$: a leaf contributes one visit, a branch
one visit followed by its finite left and right visits. Every packet
block has length at most five. Every word reversal/walk has finite
length $|q|$ and every template loop has a fixed finite bound. Thus
every visit ends, the stacks empty together, and End is attained
exactly once. At exhaustion all old leaves have been processed;
$\operatorname{enc}_H(x)=E(x)$ and $P_H(x)=\rho x$. The table prefix
is complete and is exactly $\mathsf A(x)$ or $\mathsf A(\rho x)$ as
asserted. This proves equality with the actual successor without a
post-edit scan.

The only variable constructor inputs in the row rules are the parsed
packet, the receiver work word and its own output cells. The only
variable editing inputs are that fresh operand, actual source fields
reached with its word, and newly allocated staging. Earlier descriptors
are retained but their data fields are never read. A sender frame
contains a reference, not a supplied subtree; its contents are observed
only by the displayed actual probes. This proves the stated provenance
and excludes the alternative operand suppliers. $\square$

**Theorem 3.3 (unknown local actuation while another component is unread).**
For every compound seed $u$, let $a$ be its leftmost leaf address and
$\ell=u|_a$. In Boot its first seed-leaf visit publishes
$\ell\mapsto E\ell$ at $Ra$ before any logical visit to the seed's
right child at $RR$. The actual subtree there is still the original
$u|_R$, protected by (OA.4).

For the first continuing Update, allow every finite completed command
prefix $v\in\{\mathsf L,\mathsf R\}^{<\omega}$ after Boot. Define
the inherited seed-root address by $q_\epsilon=R$,
$q_{v\mathsf L}=Rq_v$ and $q_{v\mathsf R}=Lq_v$, with juxtaposition
denoting concatenation of root-to-node address letters. The actual
Update entrance after this prefix is $E(F_v(j(u)))$, containing
$E u$ at $q_v$. Its first seed-leaf visit publishes
$E\ell\mapsto E(\rho\ell)$ at $q_v a$ before any logical visit
to the seed's right child at $q_vR$. That still-needed actual subtree
remains exactly the entrance occurrence of $E(u|_R)$, including its
references and fields. In both services the right seed component
ranges over all finite trees, with no bound on its size or height.

More explicitly, for every $\ell\in\{\alpha,\beta\}$ and
$z\in\mathcal T$, the seed $u=\langle\ell,z\rangle$ gives the
Boot operand $(RL,\ell)$ and target $E\ell$, while the still-needed
subtree at $RR$ is the original actual $z$. For every prefix $v$
above, the first Update gives operand $(q_vL,\ell)$ and replacement
$E\ell\mapsto E(\rho\ell)$, while the still-needed subtree at
$q_vR$ is $E z$. The immediate next Update from the initialized
return is the particular case $v=\epsilon$, with addresses $RL,RR$.
For the legal continuation $\mathsf L\mathsf U$, these addresses
are instead $RRL,RRR$: $RR$ is the seed root, visited before $RRL$.
No bound or description of $z$ is supplied as an input to either
service. For each fixed $v$, changing $\ell$ changes the actual leaf
packet, operand label, allocated target and resulting current source.
All these services complete by Theorem 3.2.

Proof. Boot enters on $j(u)$, with seed root at $R$. Its proved
return source is $E(j(u))$. Each subsequent L graft places the old
actual root in its right child and adds a fresh $A$ on the left; each
R graft places it in its left child and adds $A$ on the right.
Equation (OA.1) identifies these sources as $E(Lx)$ and $E(Rx)$
when the old source is $E x$. Scan writes no source field. Induction
on the completed prefix $v$ therefore gives the stated actual Update
entrance and the recurrence for $q_v$, preserving the occurrence
$E u$ and its descendant fields throughout these grafts and Scans.
This covers every possible completed command prefix before the first
Update under Definition 4.1; none of its L/R orders is excluded.

The leftmost leaf of a compound seed lies in its left child. In Boot,
left-first work reaches $Ra$ while $RR$ is still pending. In Update,
all visits before the seed is reached lie outside its occurrence;
their edited leaves are incomparable with $q_v$. Once the seed is
reached, left-first work reaches $q_v a$ while $q_vR$ is still
pending, regardless of the depth of $a$ or the surrounding grafts.
Theorem 3.2 publishes at this visit before resuming pending work.
Its (OA.4) and interior preservation clauses keep that pending root,
all its descendant fields and its proper-prefix paths unchanged.
Thus the protected subtrees are exactly the stated actual occurrences.
The addresses $q_v$ are proof notation for this correspondence; the
receiver constructs the operand words by Definition 2.2's fresh snoc
extensions, with no supplied seed-address input.

For $u=\langle\ell,z\rangle$, $a=L$. Boot has not even probed
the tag of $z$ at this publication. During this Update the physical
root of $E z$ was probed while classifying the seed root at $q_v$,
but is branch for every $z$; that probe discloses no logical
constructor or bound on $z$. For $v=\mathsf L$, the logical entrance
is $\langle\alpha,\langle a_0,\langle\ell,z\rangle\rangle\rangle$,
so preorder visits its branch $RR$ before publishing at $RRL$ and
leaves $RRR$ pending. For $v=\epsilon$ the seed root is $R$,
giving the displayed immediate-Update addresses. The receiver derives
alpha versus beta from the actual one-token or (OA.2) packet, and
the target pairs are $A/B$ in Boot and $B/\langle B,A\rangle$ in
Update. They differ as literal trees and as their actual allocation/
assignment events. Theorem 3.2 gives every finite completion. $\square$

**Definition 3.4 (extent of early actuation).** Theorem 3.3 asserts an
all-$z$ Boot family with a genuinely unknown untouched component and
an Update family uniform over all preceding completed L/R commands,
using the transported root-relative addresses. In Update, unread
means not yet logically visited in this service's new traversal.
Boot and any preceding Scans have already acquired full earlier
tables and retained records; their contents are not read as operands
by this service under Definitions 1.3 and 2.2. Its fresh receipt and
local publication precede completion of its own acquisition.
On every input Boot already edits the left wrapper before acquiring
the seed. A seed with only one leaf need not retain an unknown seed
component after that leaf's receipt; no stronger assertion of unknown
residual information on that degenerate input is made. Theorem 3.2's
all-finite service domain and Theorem 4.2's every-finite-command-word
domain, including later Updates, remain the domains used in §5.
Theorem 7.1 charges the actual entrance tree and its actual leaf-path
lengths, including the paths through any preceding grafts.

## 4. Attained returns and the full continuation task

**Definition 4.1 (commands, publication and return).** At End assign
the actual new table head and tail to the new descriptor's two table
fields, set its state live and retain it as current in slot 27. If
its previous reference is nonnull, assign that previous descriptor's
state retired without inspecting any of its data fields.
Output one Begin token; traverse the actual new row list, reading
word, label and next in payload order, and emit one constructor token
per row; at the null tail emit End. These $N(t)+2$ tokens encode the
current logical table $\mathsf A(t)$ by its full binary preorder.
No whole-table token is emitted. Clear service scratch in bank order,
mark the descriptor returned, and enter Ready on one final Return row.
No other row enters Ready. Boot uses the same publication/output/return
tail, with a distinct startup opcode.

At Ready, Supply(0) selects Update. Supply(1) enters Tail; there
Supply(0) selects L and Supply(1) selects R. These are the entire
command codes $0,10,11$. The latter two prepare a fresh literal $A$
and a fresh branch, link the old captured source root and $A$ in the
indicated order, and assign that branch to $\pi$. They then start Scan
on this actual source. Every intermediate control admits exactly the
next prescribed Advance, and no bit input; Ready and Tail admit both
Supply bits and no Advance. An unsupported action has the fixed
disabled response and no successor/event/output. A finite prefix may
stop at any such control; the model contains no waiting-event choice.

Let $J_\omega(u,w)$ be the complete joint state at the attained return
for the finite completed command word $w$, with $w=\epsilon$ denoting
the first Boot return. Complete means the source and root, every old
and fresh allocated node/cell, active/retired descriptors and tables,
all word/frame/packet/operand/invocation/completion backing, typed
allocators, bank/latches/control, input/output, full event chain and
the fixed rights. There are no independently chosen names or layouts.

Define $Q_\omega$ on these returns independently of the four views.
Its empty experiment exposes the actual extensional current table and
Ready. For every finite word of Supply(0), Supply(1), Advance and any
unsupported symbols it exposes all legal domains and actual partial
responses. An executing row's response is

$$
(a,\mathsf{legal},\mathsf{ok},\mathsf{opcode},
 \mathsf{actual\ read/emitted\ value},\Delta\Gamma,
 \Delta\mathsf{Out},J').
\tag{OA.5}
$$

The complete original successor $J'$ includes every component just
listed, including partial source changes, newly born packets and all
records/references. It is a mathematical response coordinate, not an
extra transmitted snapshot. Disabled trials execute nothing. This
task includes partially supplied commands, service interiors, guards,
publication and cleanup as continuation responses; it does not replace
them by a coarse emitted endpoint. The four-view theorem below has
returned cuts as its *starting* domain.

**Theorem 4.2 (actual ternary execution and unique returned position).**
For every finite $u$ and finite $w\in\Lambda^{<\omega}$ there is
exactly one attained return $J_\omega(u,w)$. Its actual source is
$E(x)$, $x=F_w(j(u))$, and its current receiver-built table is
$\mathsf A(x)$. Each next coded command and its finite Advances
terminates at the corresponding $J_\omega(u,wa)$. Every finite legal
action prefix has the complete actual row responses of Definition 4.1.

Proof. Initialization constructs the actual $j(u)$ by one known graft.
Theorem 3.2 for Boot constructs $E(j(u))$ and its table online, and
the finite output/cleanup tail reaches the first Return. Suppose the
claim holds for $w$. Update's proved correspondence gives
$E(\rho x)$ and $\mathsf A(\rho x)$, with no refresh acquisition.
For a graft, its actual $A=E\alpha$ and (OA.1) give
$\langle A,E x\rangle=E(Lx)$ or
$\langle E x,A\rangle=E(Rx)$. These inputs are compound and satisfy
Scan's premises. Its correspondence gives the authentic new table,
and the finite tail returns. In all cases the original sole owner and
port remain the binding, so source equality has not been substituted
for a current right.

All bit inputs and control paths are fixed by the given code and
actual probes. Only Return enters Ready; after that row its previous
control is no longer active. Another Return requires another completed
command. Thus the $|w|+1$-st Return exists uniquely. This does not infer
a return from a recurrent entry-test instruction. Canonical allocation
and the row convention determine all backing and events at every
finite prefix. The invariant in Theorem 3.2 proves enabledness of every
service test; the other finite initialization, graft and output rows
use held or fresh material. Hence their successors are the actual
complete $J'$ of (OA.5), including interiors, with the exact legality
rule in Definition 4.1. $\square$

## 5. Four independent returned observations

**Definition 5.1 (the selected expressions).** On the attained returned
history set $\mathcal H^{\rm ret}_\omega=
\mathcal T\times\Lambda^{<\omega}$ select:

| Expression | Selected actual content |
| --- | --- |
| $S_\omega$ | Ordered unlabelled node support of the active source at $\pi$. |
| $B_\omega$ | Its uncoloured terminal-address antichain. |
| $M_\omega$ | Current receiver table's addressed contents and its fixed live binding/right $(o,\pi)$. |
| $T_\omega$ | Ordered actual events from observer entrance through the current Return, including preparation, probes, offers/takes/arrivals, operand construction, source edits, command input, output and returns. |

Space and boundary contain no service cells or records. Selected memory
uses extensional word/row contents; it excludes allocation names,
descriptor entry/tail references, previous tables, mode counters,
packet archives and records. These remain in complete $J_\omega$.
Time retains the actual bounded events and their actual references;
no endpoint snapshot is attached to it. It observes order, not physical
duration. All four projections refer to the very same execution of
Theorem 4.2. They are not defined by prescribed inverse functions.

**Theorem 5.2 (space kernel and effective recovery).** For every two
attained returns $h,h'$, $S_\omega(h)=S_\omega(h')$ if and only if
$h=h'$, if and only if $h\sim_{Q_\omega}h'$. From an attained space
observation there is a finite algorithm recovering its complete
$J_\omega$, all continuation responses (OA.5) and the other views.

Proof. Theorem 4.2 gives the actual source $E(F_w(j(u)))$. Apply the
supplied ABT erased-image decoder and ER Theorems 9.3, 9.5 and 9.8
to this ordered support. They recover exactly $x$, then the unique
seed and ordered word $(u,w)$; no service/epoch count is an input.
This is exactly their stated ancestry-antichain domain, not a new
ancestry theorem. Reconstruct canonical installation and execute the
finite row scheme descriptively through its $|w|+1$-st Return.
Theorem 4.2 proves termination and identity with the complete actual
$J_\omega$. Equal spaces consequently give equal task profiles.
Conversely equal task profiles give equal empty-experiment tables,
hence the same $x$ and support by (OA.1) and Theorem 4.2. Equal $h$
gives equal actual execution and equal space. These are both kernel
inclusions. The recovered complete state determines every finite
partial action response, including disabled cases and full successors,
by its actual row rules. $\square$

**Theorem 5.3 (boundary kernel and effective recovery).** Separately,
$B_\omega(h)=B_\omega(h')$ if and only if $h=h'$, if and only if
$h\sim_{Q_\omega}h'$, with finite reconstruction to complete state
and every continuation response.

Proof. Finite prefix closure of this actual full binary tree's terminal
antichain is exactly its support. That elementary operation supplies
the decoder in Theorem 5.2. Thus equal boundaries give equal $h$ and
task profiles. In the converse task inclusion, equal present tables
give equal logical $x$, hence equal source $E x$ and its actual
terminal antichain. Equal $h$ gives the same boundary. These two
inclusions prove the boundary kernel individually. Subsequent finite
descriptive execution is the same complete reconstruction, not a
projection of a coarser boundary-only response. $\square$

**Theorem 5.4 (memory kernel and effective recovery).** Separately,
$M_\omega(h)=M_\omega(h')$ if and only if $h=h'$, if and only if
$h\sim_{Q_\omega}h'$, with finite reconstruction to complete state
and every continuation response.

Proof. The complete current rows reconstruct their labelled logical
$x$, by the full binary preorder parser with their backed addresses.
Form the finite $E x$ and use the space/ancestry decoder. Theorem 4.2
is indispensable here: the constructed table really is this current
source's $x$ after the online edits. Equal memory therefore gives equal
$h$ and profiles. Conversely equal profiles include equal current
tables, and their binding and right are the same fixed $(o,\pi)$,
which is precisely the selected memory equality. Equal $h$ gives the
same constructed contents. No allocation, archive or old-table field
has been silently added to memory to obtain either inclusion. $\square$

**Theorem 5.5 (time kernel and effective recovery).** Separately,
$T_\omega(h)=T_\omega(h')$ if and only if $h=h'$, if and only if
$h\sim_{Q_\omega}h'$, with finite reconstruction to complete state
and every continuation response.

Proof. Filter the actual Boot Arrival events before its Return. By
Theorem 3.2 they are precisely the one-token constructors of $j(u)$
in preorder, each actually received once. Parsing them and stripping
$a_0$ recovers $u$. The actual subsequent Supply events parse uniquely
into $0,10,11$; the last attained Return in the observation gives
exactly the completed word $w$ by Theorem 4.2. Thus equal time gives
equal $h$, complete execution and task profiles, including the
allocation/reference fields already present in those events.
Conversely equal profiles give equal current tables, whose $x$
recovers $h$ by the ancestry supplier. Canonical execution then gives
the same entire event word. Equal $h$ plainly gives equal time.
Neither implication erases raw replies or reference fields to make a
coarser transcript fit a memory fibre. $\square$

**Theorem 5.6 (all routes and actual continued dynamics).** For each
of the four separate decoders $d_V$ to $h$, put
$R_{VW}=W\circ d_V$ on attained images. For each command $a$ let
$A_a^V(V(u,w))=V(u,wa)$. Then

$$
R_{WV}R_{VW}=\mathrm{id},\qquad
R_{WZ}R_{VW}=R_{VZ},\qquad
R_{VW}A_a^V=A_a^W R_{VW}.
\tag{OA.6}
$$

Every route also gives exactly the same legality, output, actual
record append and complete original successors for every finite
continuation, including prefixes ending inside a command or service.

Proof. Each separate theorem proves $d_V(V(h))=h$ and recovers the
same complete $J_\omega(h)$. Compose these identities to obtain the
first two equations. Theorem 4.2 proves that the coded command actually
attains $h\mapsto(u,wa)$, which gives the third. For finer continuations
start from that same reconstructed complete $J_\omega$ and induct on
the supplied action word. Its first action has the same enabledness
test on every route. A disabled action has the same nonexecuting value;
an enabled action has the same actual opcode, field value, event and
output coeffects and complete successor by (OA.5). Repeat at that
successor. This establishes the stronger response correspondence
without claiming that S, B or selected M alone is injective at every
interior cut. The abstract route algebra is credited ER §22 machinery;
the online source/table/record correspondence proved here supplies
its different concrete process. $\square$

**Definition 5.7 (effective description versus installed access).**
The decoders just given are finite algorithms on finite serialized
attained observations: syntax parsing, terminating ancestry descent,
canonical finite descriptive execution and finite projection. They
do not depend on noncomputable choice from a singleton fibre. Their
input serialization, working material and execution have additional
costs. They construct descriptions of old states/events, and neither
reexecute an old physical event nor revive an old capability. The
actually installed controller supplies the receipt/actuation/return
service of §§1–4. There is no installed arbitrary S/B/M/T conversion
port or cross-owner invocation in its operation basis. An executable
description algorithm is therefore proved, while such a callable
conversion service is not assumed or asserted.

## 6. An exact acquired-prefix limit for selected memory

**Definition 6.1 (startup checkpoint domain).** Restrict this section
to the actual Boot NodeDone checkpoints after the known left $a_0$
has been completely processed, including the checkpoint just before
the first seed visit and the checkpoint after the last seed visit.
Let $H=\langle a_0,K\rangle$ be the old partial tree there.
The selected prefix memory $M^{\rm pre}$ is exactly the current new
receiver row prefix, with its extensional word/label contents and
fixed binding/right. No sender/receiver stack reference, allocator,
packet archive, event, invocation reference, descriptor entry, elapsed
time or initial-size field is included. The table prefix determines
$K$ effectively: parse its acquired seed constructors, leaving each
unfilled child slot a distinct ordered hole. The converse constructs
the same row prefix from $K$. Thus $K$ and this selected memory are
equivalent observations, without being complete retained local states.

Write $m(K)$ for the number of holes and

$$
\mathcal C(K)=\{K[t_1,\ldots,t_{m(K)}]:t_i\in\mathcal T\}.
\tag{OA.7}
$$

Every hole is a separate position; equal fillings are allowed. A
continuation at such a checkpoint uses the exact remaining Boot rows
and the full responses (OA.5), then the continuing command interface.
The completed-table output remains part of that task.

**Theorem 6.2 (exact prefix fibre and recovery boundary).** On the
domain of Definition 6.1, the seeds producing a specified selected
prefix memory are exactly $\mathcal C(K)$. Every member is a genuine
actual execution reaching that NodeDone checkpoint, with the same
selected prefix and pending word values, though not necessarily the
same references or full records. Consequently:

1. The full seed, full current active source, complete joint state
   and full continuation profile are recoverable from this selected
   memory if and only if $m(K)=0$. If $m(K)>0$ the fibre is infinite.
2. For a function $f:\mathcal T\to Y$, recovery of $f(u)$ on this
   fibre is possible exactly when $f$ is constant on $\mathcal C(K)$.
   If $f$ is effectively computable on finite trees, this constancy
   premise gives a finite recovery algorithm: fill all holes by
   $\alpha$ and compute $f$. Singletonhood is not used as an algorithm.
3. For a fixed original seed address $a$, its four-valued literal
   reply is determined exactly when descent along $a$ through $K$
   does not encounter a hole. Encountering a known leaf first also
   determines every deeper reply as absent. No unknown subtree's
   reply family is obtained by postprocessing this prefix.

Proof. At these checkpoints Boot has decoded a preorder prefix of
$j(u)$ and published exactly its acquired-leaf encodings, by Theorem
3.2. A preorder prefix is determined solely by the constructors already
read: replacing an unvisited hole subtree does not change any of those
tags, earlier source paths, receiver word values, leaf encodings or
the number of completed visits. The induction of Theorem 3.2 therefore
constructs an actual run for *every* filling in (OA.7) through the
same node checkpoint and selected rows. Initialization may give
different references; no reference value is an input to the selected
memory or a source-dependent control branch. Conversely a seed at
this checkpoint must agree with each acquired constructor. Unique
ordered-hole decomposition then puts it in (OA.7). No constraint on
unread size, height, shape or label has been imported from a record.

If there are no holes the seed is exactly the displayed finite $K$.
Its size and number of decoded nodes are known. Canonical descriptive
execution to this precise NodeDone reconstructs the complete joint
state, current mixed source and continuation profile, finitely by
Theorem 3.2. If there is a hole, freely varying its filling already
gives infinitely many seeds with the same memory. Their current
sources still contain that unchanged subtree at its corresponding
$R$-prefixed hole address, by (OA.4), so the full current sources
differ. Complete states differ as well. Finite Boot continuations
eventually output the distinct complete $\mathsf A(j(u))$, and
already a complete successor in (OA.5) retains the varying source.
Thus the declared full task cannot factor through this memory.
This proves both directions of clause 1, with actual common-memory
realizations rather than arbitrary hypothetical fillings.

Necessity in clause 2 is equality of the decoder's input on the fibre;
sufficiency is assigning its constant value. For the effective claim,
the all-alpha filling is a finite member of that *same* fibre and is
constructed from $K$. Computing $f$ there terminates and, under the
stated constancy premise, equals its actual value. This does not
decide constancy for an arbitrary supplied $f$.

For clause 3, a known branch chooses the indicated child, a known
leaf fixes its tag or all lower absence, and a known constructor at
the endpoint fixes its reply. If descent instead reaches a hole
with empty remaining suffix, alpha and beta fillings give different
replies. With a nonempty suffix, an alpha filling gives absent;
choose a finite full tree containing that suffix and put beta at its
endpoint to give beta. These are two actual fillings in (OA.7), so
the reply is undetermined. This proves the exact boundary. $\square$

**Theorem 6.3 (this memory fibre is not the time-record fibre).**
Equality of $M^{\rm pre}$ in Theorem 6.2 does not imply equality of
the full chronological records, nor of complete retained memory.
In particular at $K=\square$, the actual seeds $\alpha$ and
$\langle\alpha,\alpha\rangle$ give equal selected memory but
different actual records. No time-kernel statement on unfinished cuts
follows from Theorem 6.2.

Proof. At $K=\square$ both have acquired only the fixed wrapper's
root and left $a_0$, producing the same rows and word values.
Initial source-node allocation uses respectively one and three names.
The first subsequently allocated known $a_0$ node therefore has source
name one versus three. Its actual allocation event is part of both
chronological records and differs. These names are retained in complete
state and records, although not in selected row contents. No controller
can inspect their indices, and no comparison with one of these names
is a free branch on initial size: only held-reference equality/null
tests are enabled. Hence the pair genuinely follows the same selected
prefix construction. The displayed full records differ before any
seed tag is read. More generally (OA.7) characterizes the explicitly
selected extensional memory, not a transcript with raw references
silently erased. $\square$

## 7. Same-run operations, backing and mathematical dependence

**Theorem 7.1 (paid online resource vector).** For one actual service
on logical input $x$, write $n=N(x)$, $b$ for its branch count,
$a,c$ for its alpha/beta leaf counts, $d=\sum_{p\in\operatorname{LeafPos}(x)}|p|$,
and $n'=N(x)$ in Boot/Scan, $n'=N(\rho x)=n+2c$ in Update.
The following coordinates are exact for the boundaries defined here:

| Coordinate | Boot | Scan | Update |
| --- | --- | --- | --- |
| Classification tag probes, offered tokens, arrivals and packet-cell births, each | $n$ | $3n+2c$ | $3n+2c$ |
| Visit child-discovery follows | $2b$ | $2n+2c$ | $2n+2c$ |
| Sender-frame births, receiver-frame births, each | $n$ | $n$ | $n$ |
| New output rows | $n$ | $n$ | $n+2c$ |
| Receiver snoc-word births | $n-1$ | $n-1$ | $n-1+2c$ |
| Actual operand rows, invocations, completions, each | $a+c$ | $0$ | $a+c$ |
| Actuator forward-word births and root-walk follows, each | $d$ | $0$ | $d$ |
| Fresh target source nodes | $3a+5c$ | $0$ | $5a+9c$ |
| Active leaf-attachment publications | $a+c$ | $0$ | $a+c$ |
| Table-output tokens, including framing | $n+2$ | $n+2$ | $n+2c+2$ |

There is one new descriptor per service. With the fixed row expansion
of Definitions 1.3 and 2.1–2.3, there exist absolute finite constants
$C_r,C_f$ such that the service, output and return use at most
$C_r(n+d+1)$ rows/events and $C_f(n+d+1)$ bounded field operations.
In Scan the $d$ term can be omitted. These are bounds for the chosen
abstract operation basis, not physical unit-time or optimality claims.

Proof. One classification visits each old logical node. Boot probes
its root once and follows two children only at its $b$ branches.
Encoded classification probes root and both children at every visit,
plus two grandchildren at each beta, yielding the first two rows of
counts. Each probe has exactly one handshake and packet birth.
Paired stacks start with one frame each and create two per old branch;
$1+2b=n$. Each branch creates two receiver word extensions; Update
beta creates two additional words for its output expansion. The row
rules therefore give exactly $n'$ rows and $n'-1$ snoc cells.
Every editing leaf creates one operand, invocation and completion.
Its snoc reversal creates exactly $|p|$ forward cells and the walk
follows exactly $|p|$ child fields. The target lists (OA.3) have sizes
$3/5$ in Boot and $5/9$ in Update. Each leaf publishes one attachment,
and each target of size $k$ has $k-1$ separately tested/written
staging links. Output emits its two framing tokens and one per row.
These are counts of this same execution, without importing ER.90
or ER.91's different blocks.

For completeness, leaf guards add three field probes per old tile
position and the sum of its literal position lengths in follows.
Boot's old tile has one position and length sum zero; encoded
alpha/beta tiles have respectively three/five positions and length
sums two/six, exactly the literal ER Definition 16.1 lists. Each
fragment also makes its one attachment probe and reference tests,
its fixed completion and fixed-slot cleanup. Address reversal and
walking have fixed per-letter row lists. All other visit, packet,
push/pop, append and output blocks have finitely many bounded cases.
Take $C_r$ to exceed the sum of their maximum row-list lengths,
including loop-head/exit tests, all template iterations (at most nine
target nodes), entry and the sixty-four-slot cleanup. Multiplying by
the displayed bounds on block occurrences gives $C_r(n+d+1)$.
Let $F$ be the maximum field/read/write/initialization count of any
such bounded row, including event payload and tail coeffects;
$C_f=F C_r$ gives the second bound. Both constants are maxima/sums of
fixed finite lists, not costs assigned to an unbounded hidden routine.
$\square$

**Theorem 7.2 (initialization and retained backing on the same run).**
For a finite run through $k+1$ returns, its source/local-cell and event
backing is obtained by summing the actual coordinates in Theorem 7.1
over its one Boot and its $k$ subsequent services, together with:
the $N(u)$ installed input nodes and their links/root attachment;
the holder and sixty-four bank cells and their fixed installation;
four startup source births and five link/port assignments;
four source births and five link/port assignments per L/R graft;
the actual command-bit rows; and every declared initialization,
control, record and output coeffect. Nothing in these sums is
released when a descriptor or scratch root is retired.

Proof. The known $a_0$ preparation has three nodes and two internal
links. Its wrapper adds one node and two links, and the root-port
publication is the fifth assignment. A graft similarly has three
nodes/two links for $A$, then one node/two links and a port assignment.
Capture, tests, banks and descriptor setup have their own actual rows
and events. The row grammar lists every other cell type and every
operation producing it. Theorem 4.2 fixes exactly one Boot, one service
per completed command and the actual one/two input bits per command.
Disjoint birth events and canonical names partition all allocated
material, so adding their coordinates counts precisely this run's
backing; adding executed rows counts precisely its event births.
Earlier rows, packets, words, operand records and old source tiles
coexist with the current table. They are not removed from the account
because selected $M_\omega$ omits them.

This is a vector account. For a bit account, actual reference widths,
cell fields, code/rights, serialization and any later descriptive
recovery must additionally be priced. In particular finite control
does not bound $n,d$, typed allocator widths or accumulated records.
No total-cost optimum, constant-memory claim or comparison with a
different operation boundary follows. $\square$

**Definition 7.3 (supplied mathematics and the precise new conjunction).**
The contribution is the online joint invariant (OA.4) with actual
probe/arrival/operand/publication boundaries, its no-refresh successor
table in Theorems 3.2–4.2, and the resulting complete-response recovery
in this process, together with Theorem 6.2's specified prefix limit.
Generic traversal, framing, parsing, ancestry, replay and route algebra
are credited intermediate mechanisms. The following are correspondences
and boundaries of those suppliers, all at the source versions cited.

ER Theorems 9.3/9.5/9.8 supply the decidable ancestry antichain and
source-support inverse. ER §§10–12 supply marked inversion for their
own unfinished substitution relation; no such inverse is asserted for
every interior of $\omega$. ER §17 supplies directed old-tile framing
after complete acquisition. ER §§20–23 supplies actual received-body
operands and four returned kernels when the source stays stationary
through complete delivery, parse, materialization and Bind. Here no
complete input table or sealed whole-source body precedes the first
leaf publication, and Update has no postpublication refresh scan.
Those are new operational correspondences, not new versions of the
ER ancestry or generic kernel results.

[SLH Theorem 57.4][SLH] already acquires an entire left child, performs
actual certified global $\rho$ updates and checks the unknown right
child by a delayed acquired template. Its global-update contract,
certificate and equality task are retained. [VSC §2][VSC] changes
virtual replies while the actual source is stationary. [CWS §§1–2,
8.1–8.3][CWS] changes private candidates and permits an independent
global-$\rho$ writer, with the designated raw Read and protected
control fields stated there. [CNA §§14–18][CNA] gives protected-entry
acquisition budgets before its permitted global interference.
None of these is recast as a missing generic idea or an impossibility
claim. The new theorem is their distinct local same-source online
correspondence on the explicit owned basis above.

[NativeFullSourceProducer][PROD], including private `traverse`,
`production_reads`, `stationary` and its [owning Scribe][PRODB], supplies
source-blind preorder discovery with actual acquired constructions;
its source is stationary. [NativeBoundedPreorderRows][ROWS], including
private `pending_next`, `pending_left`, `cursor_frontier`,
`actual_cursor_residual` and its [owning Scribe][ROWSB], supplies the
exact reached frontier and path-selected prefix correspondence under
its certified epoch/trial premises. The present paired occurrence and
receiver stacks use that ordinary frontier law, with (OA.4) replacing
stationarity by protection of the remaining roots and paths.

[NativeDepthPatterns][DEPTH], including `fill`, `decompose`, private
`fill_decompose`, `decompose_fill`, `depthEquiv`, `frontier_geometry`
and its [owning Scribe][DEPTHB], supplies unrestricted actual frontier
fillings for fixed depths. Theorem 6.2 instead identifies an attained
adaptive-prefix fibre of this selected memory. [ActualTreeReadoutAcquisition][ACT],
`readout`, `acquisitionStep`, `restore`, `source_foundation`,
`acquisition_foundation` and its [owning Scribe][ACTB] supply actual
four-valued original reads and finite restoration; its `paid` counts
distinct addresses, whereas Theorem 7.1 counts every actual probe.

[NativeErasedSupportKernels][ERASE], including private
`root_reflection`, `erased_reflection`, `erased_support`,
`two_step_prefix_kernel`, `even_epoch_support_kernel` and its
[owning Scribe][ERASEB], supplies exact erased/support prefix kernels
at the stated even epochs. The finite child-status grammar in (OA.2)
is consistent with that supplier, but its theorem does not install
the mailbox, operand or source-write operations used here.
[IntrinsicSubstitutionCoordinates][ISC], including private
`substitution_injective` and its [owning Scribe][ISCB], supplies
substitution injectivity/ancestry mathematics, not a live inverse
operation. No absence of a named API is treated as a mathematical gap.

At the pinned mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`,
[StateTransition][ST]'s `Reaches`, `Respects`, `tr_reaches` and `tr_eval`
give ordinary deterministic finite-step/refinement language with their
matching-start and terminal premises. The new proof supplies its
actual source/receiver relation; those abstract definitions do not
already certify that relation. These source correspondences do not
confer new kernel certification.

Huet, [*The Zipper*, §§1.1–1.3][HUET], is literature-attested supply
for focus/context paths and local tree modification. Its location
already contains its focus and context; it does not supply unknown
source acquisition. Reynolds, [*Separation Logic*, Frame Rule][REYNOLDS],
is literature-attested supply for local reasoning with a disjoint
heap frame and the condition that the command modifies no variable
free in the framed assertion. Here exclusivity, incomparable old
leaf/frontier positions and unchanged saved references establish
those concrete preservation conditions; no unrestricted frame rule
is assumed for overlapping edits. Hassan, Mackie and Sato,
[*An Implementation Model for Interaction Nets*, §4 and Figure 4][NETS],
is literature-attested supply for allocation returning actual handles
and individual port assignments. It supplies no provenance or
four-expression theorem for this source. The synthesis proved above
is repo-derived, without a worldwide-priority claim.

**Definition 7.4 (scope of the recovery and continuing questions).**
The full-return kernels have exactly the attained domain
$\mathcal T\times\Lambda^{<\omega}$ and the complete continuing task
(OA.5). The prefix theorem has exactly Definition 6.1's startup
NodeDone domain and selected extensional memory. There is no assertion
that its memory fibres equal full time-record fibres, or that every
unreturned packet/guard/staging cut has four independent inverses.
The operation basis, exclusive owner, initialization and task of
$\omega$ are explicit additional model premises. An unowned source,
revoked right, competing writer, arbitrary layout/name choice,
independent service choice or arbitrary returning scheduler is outside
these theorems. Identical uncoloured bodies do not issue rights.

The two leaf symbols, ordered pairing, actual observation and local
owned replacement suffice for this finite construction. Separate
sender/receiver work, backed words, finite latches, packets and records
are paid resources for its specified task. None is declared universally
minimal; direct use of a held parent could change its word-walk cost
but would require a different operand-use proof. No unrestricted
history is attached to S, B or selected M. No physical spacetime
identification, native primitive realization, universal alpha/beta
reduction or infinite completion is concluded.

All earlier fixed-$G_{gc}$, original-$Q$, parked-consumer, unchanged-
initialization and authority obligations remain under their original
hypotheses. In particular ER's original prediction task (ER.3) and
its Open problem 8.1 are not settled by this changed model. A callable
arbitrary-view conversion service, a full interior four-view theorem
for this online controller and broader competing-writer models remain
additional mathematical/operational questions. The continuing
four-expression objective is not completed by these finite theorems.

[ER]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ENTRY_REFERENCE_AND_GRAFT_ORDER.md
[ABT]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[VSC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_VIRTUAL_SUBSTITUTION_COMPILER.md
[CWS]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_WORKSPACE.md
[CNA]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md
[PROD]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean
[PRODB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.scribe.cs
[ROWS]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.lean
[ROWSB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeBoundedPreorderRows.scribe.cs
[DEPTH]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.lean
[DEPTHB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns.scribe.cs
[ACT]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[ACTB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs
[ERASE]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.lean
[ERASEB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.scribe.cs
[ISC]: ../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean
[ISCB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.scribe.cs
[ST]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/StateTransition.lean
[HUET]: https://pauillac.inria.fr/~huet/PUBLIC/zip.pdf
[REYNOLDS]: https://www.cs.cmu.edu/~jcr/seplogic.pdf
[NETS]: https://arxiv.org/html/1505.07164v1

## 追加锚（本行以下为增补区）

## 8. Raw events and present support at every Boot row cut

**Definition 8.1 (starting cuts, observations and continuation task).**
Keep exactly the occurrence model, initial installation, operation basis,
row expansion and retention of §§1–4. Let $\mathcal D_0$ consist of
all attained row cuts from the entrance immediately after the unknown
input has been attached to $\pi$ through the first Return, inclusive,
for every finite seed. Thus even the bank installation and known-source
preparation may be unfinished. In particular this domain contains the
attachment of $j(u)$, Boot entry, every instruction inside every visit,
and every output/cleanup row. A cut is an actual finite execution
prefix, not an independently supplied instruction number. Disabled
trials insert neither rows nor extra cuts.

On this domain define $S_0(c)$ to be just the ordered unlabelled support
of the tree currently reachable from $\pi$. Detached old nodes,
detached staging, banks, words, stacks, descriptors and events are
excluded. Define $B_0(c)$ to be its terminal-address antichain.
Define $T_0(c)$ to be the complete ordered actual event word from
observer entrance to this cut, with the original literal references,
read values, predecessor references and bounded coeffects of Definition
1.3. It includes initialization and incomplete visits; it contains
neither the unobserved installation fields nor an endpoint snapshot.
These are the same source-support and raw chronological projections
as Definition 5.1 on their common domain. Put

$$
O_0(c)=(S_0(c),T_0(c)).
\tag{OA.8}
$$

The Boot continuation task $Q_0$ admits precisely the original Supply,
Advance and unsupported trials, with precisely the legality and complete
row responses (OA.5). Before Ready its empty readout is running and the
output prefix actually released so far; at Ready it is the current table
and Ready as in Definition 4.1. It may finish the remaining Boot rows
and then any finite coded-command continuation, with all its interior
responses. No request for $S_0$, $T_0$ or an unknown complete table is
added. The complete-successor coordinate remains a mathematical task
coordinate, rather than a controller read permission.

The symbol $M^{\rm pre}$ retains only Definition 6.1's meaning and
checkpoint domain. It is not a name for a full local state at other cuts.
No assertion below independently reconstructs all interiors from bare
$S_0$, bare $B_0$ or a newly enlarged memory view.

**Definition 8.2 (original leaves and executed classification).**
Write $\operatorname{sh}(u)$ for the ordered shape of the initial seed,
$\operatorname{Lf}(u)$ for its original leaf addresses, and $\ell_u(a)$
for the label there. Original addresses below the wrapper acquire the
prefix $R$. An original seed node always means its installed occurrence,
not a later node born in one of its encoding tiles.

Let $A(c)\subseteq\operatorname{Lf}(u)$ consist of the original seed
leaves whose Boot classification Probe has executed by $c$. This means
Definition 2.1's first tag probe of the popped focus, including its
coeffect that retains the read result. It does not mean Offer, Take,
Arrival, PackDone, operand construction or publication. Put

$$
U(c)=\operatorname{Lf}(u)\setminus A(c),\qquad r(c)=|U(c)|.
\tag{OA.9}
$$

These are mathematical sets associated to this run, not stored lists or
counters. The two known leaves of $a_0$ do not belong to either set.
A classification Probe is identifiable in $T_0$: follow the fixed
instruction scheme from its fixed entrance, using its actual recorded
outcomes and instruction coeffects. This distinguishes classification
from a later guard tag read even if their primitive field-read opcodes
coincide. No extra event kind or runtime marker is required.

**Lemma 8.3 (what an unfinished Boot can read and change).**
At every cut in $\mathcal D_0$ the following properties hold.

1. An original seed tag is first read by its classification Probe. It
   is never assigned. The subsequent leaf guard rereads only the
   already classified current leaf. All other source reads during
   that visit concern child references, paths through branch ancestors,
   or its own freshly constructed literal target.
2. The only assignments changing the active tree are the known startup
   root attachment and the single-field Publish at each original leaf
   of $j(u)$. At that Publish the new tile is already complete and the
   old tile is still exactly its original one-node terminal. Published
   positions are pairwise incomparable original leaf addresses.
3. At an unfinished editing visit all earlier publications remain
   complete, the current leaf remains attached until its Publish, and
   every unvisited original subtree and its ancestor path is preserved.
   During an unfinished branch visit some stack/word fields can be
   missing or unpaired; this does not modify those source subtrees.
4. Every non-source read value, reference equality test, allocation and
   slot/latch coeffect is determined by the fixed row, the actual
   previously acquired results and the indicated held/fresh fields.
   There is no read of an original unknown tag through a descriptor,
   event archive, staging cell or receiver word.

Proof. Before the startup attachment the original source is unchanged;
all source births and link writes concern the four known fresh nodes.
The attachment puts the original root under their fresh wrapper without
reading an unknown tag. At Boot entry the paired stacks contain the
actual wrapper root and the empty word. At a visit, popping and reading
frames reads only their displayed fields. The next original tag read
is exactly the focus Probe. The handshake uses its one literal token;
all parser and receiver rows use the arrived packet and constructed
words. A branch's child-discovery follows read references, never their
tags. Receiver pushes and sender pushes can be partially completed in
the specified order without a source write.

At a leaf, the invocation is initiated only after this same leaf's
classification and actual receiver operand. The reverse-word loop
reads only its snoc chain. The forward walk follows only proper-prefix
branch paths, by Theorem 3.2. Its equality test concerns the reached
reference and the held focus. Boot's old guard has exactly one template
position, its original leaf root; its tag has already been classified,
and both child fields are null. The target lists are literal $A$ or
$B$. Each allocation and staging link is detached. The saved-parent
check reads a child reference. The single Publish occurs only after
these links and tests; its replacement is therefore a full valid tile.
Theorem 3.2's incomparable-leaf and pending-path invariant applies
before and after that assignment. Completion, clear-mask rows and
NodeDone make no source changes. End, descriptor publication, output
and Return read local rows or change local control only. This exhausts
the displayed source-reading and source-writing instructions. The
remaining instructions have exactly the payloads and dependencies
listed in Definitions 1.3 and 2.1–2.3, proving clause 4. $\square$

**Lemma 8.4 (a two-run relation including all named coeffects).**
Fix $c\in\mathcal D_0$, with seed $u$. Choose arbitrary labels
$\sigma:U(c)\to\{\alpha,\beta\}$ and let $u_\sigma$ have precisely
$\operatorname{sh}(u)$, the original labels on $A(c)$, and $\sigma$
on $U(c)$. There is an actual execution on $u_\sigma$ through exactly
the event word $T_0(c)$. Its endpoint $c_\sigma$ has the same support,
control, typed allocator positions and all actual named non-source
state. More strongly, the entire allocated joint states agree field
by field except possibly for the original tag fields at $U(c)$.
This includes the named source attachment fields, detached old tiles,
unfinished staging and every partial local object.

Proof. Equal initial shapes have equal node counts and identical
preorder occurrence names. Initially the only differing fields are
exactly the indicated original leaf tags; their child fields are null
in both installations. Root attachment, rights and all allocator starts
agree. Induct over the actual rows of the original prefix, maintaining
that same fieldwise relation and equal event words. At the next row,
all held references, instruction latches and named operands agree.
The possible source cases and their local consequences are as follows.

| Row family | Equality preserved at the actual successor |
| --- | --- |
| Bank birth/initialization, known-source preparation, root capture and startup attachment | Equal initial node counts give equal fresh names; all payloads and coeffects agree. The original seed remains equal outside its allowed tags. |
| Entry, descriptor fields, head/null tests and individual stack-pop fields | All operands are equal local references or their equal fields. A pop partway through its fields needs no paired-stack assumption. |
| Boot classification Probe | If it is a seed leaf in this prefix, that leaf is in $A(c)$ and has the same tag. Branch tags and known-wrapper tags agree as well. The returned value and its latch/control coeffects agree. |
| Offer, Take, individual Arrival allocation/append fields, acknowledgement, parser and PackDone | The token is equal from the Probe onward. The offered latch, partially appended packet, receiver latch and parser can be at different stages of one receipt, but are equal between the two runs at each such stage. |
| Table/operand allocation and append, snoc birth, receiver/sender pushes and branch child follows | Labels already acquired are equal. Original child fields agree. Each partial list, stack and word birth, former-tail assignment and head/tail coeffect therefore agrees literally. |
| Invocation fields, snoc reversal and every forward-word walk row | The actual operand, packet and focus are equal named objects. Each individual letter/next read, prepend, source-child follow, saved parent/side and final focus test agrees. |
| Old-leaf guard, every detached target birth, every null test and staging link | The old tag was already classified. Target choice and literal field values agree; typed allocations and all partial staging fields agree. No residual tag is read or changed. |
| Saved-parent check and Publish | The old and new references agree. The completed target and its attachment field agree; only that field is assigned in both runs. |
| Completion append, each cleanup assignment and NodeDone | The payloads and cleared slots/latches agree even before the clear block has finished. Retired and unrooted backing is retained equally. |
| Work exhaustion, End, descriptor/table publication, every output-list read and token, final cleanup and Return | Local lists, tests, values, emitted tokens and finite control agree. There is no remaining unknown-source access in this tail. |

These families cover each primitive row of the written expansion,
including loop-head tests and its finite control edges. In every case
the event predecessor, actual operand references, returned value and
all bounded coeffects agree. Their own initialization and tail work
also agree. Lemma 8.3 excludes reading one of the differing tags: if
such a classification had occurred in this prefix, that tag would not
be in $U(c)$. Thus every row that succeeds in the original run succeeds
in the second with the same event, without waiting or a new choice.
Fresh names stay equal because births occur in the same typed order.
Unprobed original leaves remain attached original terminals, so their
tag differences affect neither support nor terminal boundary. This
proves the asserted fieldwise relation at the desired cut. $\square$

**Lemma 8.5 (undoing exactly the publications already executed).**
From an attained pair $(s,t)=O_0(c)$ one can recover precisely the
initial seed shape, the set $A(c)$ with its acquired labels, and the
positions whose encodings have actually been published. This is a
finite descriptive procedure. It uses no supplied seed or stored
history ordinal.

Proof. Read the finite actual event word in its original order.
Receiver snoc words start at the known empty sentinel. Their birth
fields give their previous word and last letter, so construct their
finite word values in birth order. Operand birth/field reads identify
the actual word and received label. Each invocation names that operand,
its actual packet and focus. Its subsequent source walk and saved-side
operations have their recorded outcomes. Consequently each executed
Publish identifies its actual leaf address $p$ and received label
$\ell$, using existing word backing described by the events. A
partially created operand or invocation is not counted as a Publish.
Nor is invocation.new, a target birth, a completed detached target or
an attachment check a publication.

Before the known startup root attachment, $s$ is the original seed
shape. After that attachment, contract the entire subtree of $s$ at
each published $p$ to one terminal. Lemma 8.3 proves that these positions
are pairwise incomparable and their active subtrees are exactly the
completed encoding tiles, irrespective of later work. Thus contraction
recovers exactly the shape of $j(u)$. Its left known component and root
can now be removed, giving exactly $\operatorname{sh}(u)$. No contraction
is performed at the currently staged but unpublished leaf: its active
subtree is still the original terminal. Nothing in $s$ is attributed
to an unattached staging occurrence.

This shape fixes the canonical preorder naming of every original seed
occurrence. Match the classification Probe operand references in $t$
to these original occurrences. Their recorded terminal results give
exactly $A(c)$ and its labels. A branch cannot be mistaken for a leaf,
and a fresh code-tile node cannot be mistaken for an original seed
node: their canonical names and initialization/birth roles are distinct.
Equivalently one may compare the finite canonical-name lists generated
from the recovered shape, without a live reference-to-integer operation.
Known-wrapper probes contribute no unknown seed labels. Each construction
uses a finite list or a finite tree already in the observation, proving
effectiveness on the attained image. $\square$

**Theorem 8.6 (the exact joint fibre at every Boot row cut).**
For every $c\in\mathcal D_0$, the seeds of all and only cuts $d$ with
$O_0(d)=O_0(c)$ are

$$
\mathcal F_{ST}(c)=
\left\{v:\operatorname{sh}(v)=\operatorname{sh}(u),\quad
       \ell_v(a)=\ell_u(a)\text{ for all }a\in A(c)\right\}.
\tag{OA.10}
$$

Each member has exactly one such actual cut. Its state is related to
$c$ exactly as in Lemma 8.4: every named field outside the remaining
original terminal tags is identical. In particular all actual named
non-source state and the complete raw events are identical, even when
receipt, word construction, guard, staging, publication or cleanup is
unfinished. Replacing $S_0$ by $B_0$ gives the same assertion.

Proof. Equal raw words have the same actual finite sequence of executed
rows, including initialization, control and partial clear blocks.
Lemma 8.5 applied to the equal pair recovers the same original shape,
same classified leaf positions and same labels. Hence any such seed
belongs to (OA.10). This direction does not infer initial shape from
a partially constructed receiver table or a pending-stack abstraction.

Conversely, every seed in (OA.10) is one of Lemma 8.4's arbitrary
independent choices of the remaining tags. That lemma constructs the
actual successful prefix with exactly the same raw word and support,
not merely a compatible abstract state. The row scheme is deterministic
and has no idle edges. Its unchanged chronology fixes the exact cut;
there cannot be two different prefixes with this same event word on
one seed. This proves existence, uniqueness and the stronger fieldwise
statement. At every cut the active source is a finite full tree:
initial attachment and each Publish preserve this property, and all
other writes are local or detached. Its support is the prefix closure
of its terminal antichain. Thus the two source projections determine
one another throughout this domain, proving the boundary version.
$\square$

## 9. The exact residual, finite experiments and first temporal recovery

**Corollary 9.1 (residual size and every row transition).**
On the entire domain of Theorem 8.6,

$$
|\mathcal F_{ST}(c)|=2^{r(c)}.
\tag{OA.11}
$$

At an original seed-leaf classification Probe the residual drops by
one and the two possible recorded labels split the incoming joint
fibre into two equally large successor fibres. At every other executed
row it is unchanged. This includes original branch classification,
known-wrapper classification, Offer, Take, Arrival, parser steps,
operand birth and reads, all word walks and guards, every staging
birth/link, Publish, completion, individual clear rows, output and
Return. A disabled trial changes neither observation nor residual.

Proof. Fixed shape makes the remaining leaf positions a fixed set;
each has exactly two independent labels, and every choice is realized
by Theorem 8.6. This gives (OA.11), with value one when the set is empty.
A seed-leaf classification reads that original tag once for the first
time. Its two choices are both actual by Lemma 8.4 applied before that
Probe, and exactly one of the remaining coordinates becomes fixed.
Any later guard reread concerns a coordinate already fixed.
Lemma 8.3 shows that no other row first reads a residual tag or destroys
its original occurrence. It therefore changes no coordinate in (OA.9).

This also describes fibres in the full attained image, not just a
chosen family that happens to remain synchronized. The successor raw
word determines its predecessor word. For a source-changing row the
predecessor support is recovered by replacing the published tile by its
old terminal, or by removing the known startup wrapper. For any other
row the support is unchanged. Thus an ordinary row cannot merge in a
new predecessor fibre unnoticed. $\square$

**Theorem 9.2 (full-task separation and the sufficient reconstruction
condition).** For a fixed attained $O_0(c)$, the following conclusions
hold on its full fibre.

1. Two different seeds have different $Q_0$ profiles. There is an
   actual common finite continuation of Advances exposing a different
   classification read value. Even without private successors, the
   completed Boot output tables eventually distinguish them.
2. The initial seed, labelled current source, complete joint state
   and entire finite-continuation response map are each reconstructible
   from $O_0$ on this fibre if and only if $r(c)=0$.
3. For any specified function $f$ of these attained cuts, an exact
   descriptive recovery from this observation is possible precisely
   when $f$ is constant on the fibre. For an effectively computable
   $f$, constancy gives a finite algorithm by the all-alpha choice
   for the still-unprobed labels and canonical descriptive execution.

Proof. Different members of (OA.10) differ first at some still-unprobed
original leaf in the remaining preorder. Up to its classification the
same row induction as Lemma 8.4 applies, since every tag read earlier
has the same value in both seeds. By Theorem 3.2 the leaf is reached
in finitely many rows, even if the present cut lies inside a packet,
walk, guard, detached target, completion or clear block. The common
Advance word ending at that Probe therefore has different actual
read values. These are actual (OA.5) response coordinates; no new
query address or source inspection is supplied. Full logical tables
$\mathsf A(j(v))$ for different $v$ are distinct, and Boot eventually
emits their literal preorder words with the existing framing. Hence
the emitted completed outputs distinguish as well, although their
subsequent row counts can differ after the first distinct label.

If $r(c)>0$, flip just one of its remaining tags. It is an attached
original leaf by Lemma 8.3, so the labelled current source and complete
state differ. Clause 1 separates their complete task profiles. Equal
observation cannot determine any of these four targets.

If $r(c)=0$, Lemma 8.5 supplies the full shape and every original leaf
label, hence the exact seed. Construct its canonical installation and
run the exact row scheme while consuming the supplied finite $T_0$
word. Stop at its end, checking each row against its actual recorded
values and coeffects. Theorem 8.6 and determinism identify precisely
the given cut and all its named backing. There is no supplied replay
counter: the finite input event list itself gives the stopping boundary.
For any finite experimental action word, simulate its original legal
or disabled rows from this reconstructed state to obtain all actual
responses. Each row is a finite operation. Complete services terminate
as in Theorems 3.2 and 4.2; all subsequent finite commands, including
arbitrary Updates and Scans, keep those original domains. This proves
sufficiency for the full continuing task, rather than just its Boot
endpoint.

For clause 3 necessity is equality of the recovery input. For
sufficiency choose the member with alpha at every remaining leaf.
It is an actual member by Theorem 8.6. Reconstruct its finite state
as above; for a computable $f$, evaluate $f$ there. Under the stated
constancy condition its value is the actual one. This does not decide
constancy for an arbitrary $f$. $\square$

**Theorem 9.3 (the sharp first raw-time-only recovery cut).**
For each actual seed run let $c_*$ be the successor of the classification
Probe of the last original seed leaf in preorder. It exists and is
strictly before that leaf's Offer, Take, Arrival, operand construction,
Publish and the first Return. At every attained cut from $c_*$ through
the first Return, raw $T_0$ alone has a unique seed and actual prefix,
and a finite decoder reconstructs the complete joint state and all
finite-continuation responses. At every earlier attained cut, $T_0$
alone fails to determine the seed, complete state and $Q_0$ profile.
Thus $c_*$ is exactly the first temporal recovery cut on each run.

Proof. The final visited original node of a finite nonempty full tree
is its final preorder leaf. All branches precede a descendant leaf.
Consequently at $c_*$ the recorded Boot classification results, in
visit order, are exactly the complete literal preorder constructors
of $j(u)$, including the last token in its Probe event. Filter these
classification events by the fixed row scheme as in Definition 8.2.
The full binary parser recovers $j(u)$ and hence $u$. It does not wait
for a packet cell or a receiver table row. Later chronological prefixes
retain these events, so recover the same $u$. Finite canonical execution
consuming their raw event word then gives their exact full endpoints
as in Theorem 9.2. Their arbitrary finite responses follow from the
same reconstructed state.

Before $c_*$ at least one original seed leaf has not been classified.
Change just its label, leaving the entire original shape fixed.
Lemma 8.4 gives exactly the same raw word and, even, the same support
and all named non-source state. Its original unprobed tag remains
present and differs. The common finite experiment of Theorem 9.2
eventually reads that tag and separates the full task profiles.
Therefore no earlier raw-time decoder can have any of the asserted
exact targets on its full attained fibre. This argument also covers
all initialization cuts and the immediate predecessor of the last
Probe. The row convention places Offer and every later receipt/use
operation in distinct later rows, proving the stated strict order.
$\square$

This threshold concerns descriptive temporal information. At $c_*$
the final result has been acquired by the sender's Probe, with its
actual bounded coeffect, but has not yet arrived in the receiver
packet. Arrival, parser completion, the operand and its read fields
remain necessary steps of this controller's actual actuation. A complete
Boot table does not become the returned current entry until the original
End/publication/output/cleanup/Return tail. Temporal singletonhood
neither executes those rows nor adds a receiver conversion port.

**Proposition 9.4 (a supplement on exactly the fixed joint fibre).**
Fix one actual observation $O_0(c)$, and a supplement convention giving
each of its seeds an exactly $b$-bit word, with no free variable length,
external label or other source-dependent side channel. Exact recovery
of the seed or its complete $Q_0$ profile on this fibre requires
$b\ge r(c)$. A descriptive $r(c)$-bit supplement suffices: list the
remaining labels in original leaf order, alpha as 0 and beta as 1.

Proof. Theorem 9.2 makes all $2^{r(c)}$ profiles distinct. The decoder's
first input is fixed on this fibre, and its second has at most $2^b$
values, giving the inequality. The ordered leaf positions and acquired
labels are already determined by Lemma 8.5. Inserting the supplement's
labels reconstructs the unique seed and its actual cut. This proves
sufficiency in the stated coding convention. It neither supplies those
bits to the live receiver nor prices their acquisition, serialization,
working storage, authentication or invocation rights. $\square$

## 10. The raw-time refinement at the original startup checkpoints

**Definition 10.1 (literal names and ordered pending sizes).**
Restrict this section to exactly Definition 6.1's Boot NodeDone domain:
the known left $a_0$ has completed, and $H=\langle a_0,K\rangle$.
Write $k$ for the number of actual acquired constructors of $K$,
$m=m(K)$ for its ordered holes, and $n=N(u)$ for the initial seed
node count. Number original seed nodes in their canonical preorder
$0,\ldots,n-1$. Write $\nu(q)$ for the actual source reference with
canonical name $q$; $\nu$ is notation for the fixed naming convention,
not an operation that the controller can execute or invert.

All these checkpoints contain the first known-source birth event,
whose returned source reference is $\nu(n)$. They also retain in their
raw events the actual sender stack, recovered from frame birth fields
and head coeffects. Let its pending seed roots in next-work order be
$\nu(s_1),\ldots,\nu(s_m)$. If $m>0$ put $s_{m+1}=n$ and

$$
d_i=s_{i+1}-s_i\quad(1\le i\le m).
\tag{OA.12}
$$

These mathematical coordinates can be extracted from a finite serialized
raw observation by comparison with the fixed enumeration of canonical
names, terminating on its attained image. Literal name equality is
essential. Nothing extracts a stored numeral from a live opaque
reference or installs reference arithmetic. At $m=0$ the size list is
empty. The reached preorder law gives

$$
s_1=k\quad(m>0),\qquad
n=k+\sum_{i=1}^m d_i,
\qquad d_i\text{ positive and odd}.
\tag{OA.13}
$$

**Lemma 10.2 (the raw word exposes exactly the ordered size constraints).**
For two checkpoints in this domain, equal raw chronological words imply
equal $K$, equal $n$ and equal ordered pending-root names. Their hole
fillings therefore have the same sizes $d_i$ individually. Conversely,
for a fixed actual checkpoint every filling of its $K$ by finite trees
of those individual sizes reaches a NodeDone with exactly the same
raw event word. Its actual named non-source state is the same, without
erasing any references or coeffects.

Proof. At a NodeDone every visit represented in the prefix has finished
its packet and receiver work. The Boot classification tags, or equally
its completed Arrivals, give exactly the acquired constructors. Parse
the seed portion with the ordered-hole rule of Definition 6.1 to recover
$K$. The first source birth names $\nu(n)$, so equality of this actual
name gives equal $n$. Bank initialization is fixed and recorded.
Every stack-frame birth contains its node and next, and every head
assignment is a recorded coeffect. Thus the chronological word gives
the pending sender-root list, even when older frame roots have been
cleared. This uses events describing existing cells, not an assumption
that the live controller can traverse its archive.

In canonical seed preorder the acquired constructors form exactly the
first $k$ original nodes. What remains is, in order, the complete
preorder interval of hole 1, then hole 2, and so on. This follows by
induction on a prefix step: acquiring a leaf removes its one node;
acquiring a branch removes its root and places its two child intervals
before the remaining intervals. Therefore the first pending interval
starts at $k$, each next pending root is the next interval boundary,
and their final boundary is $n$. This proves (OA.12)–(OA.13) and the
necessary size constraints. It uses the existing preorder frontier law;
it does not assume a complete traversal of a hole.

For the converse fix arbitrary fillings $t_i$ with $N(t_i)=d_i$.
Unique hole decomposition supplies an actual finite seed
$v=K[t_1,\ldots,t_m]$. It has exactly $n$ original nodes. Its acquired
prefix consists of exactly the same $k$ constructors with the same
canonical names $0,\ldots,k-1$. Its pending roots have the same
$s_i$, by (OA.13). In the initial installation, each child of an acquired
branch is either another acquired constructor or one of these pending
roots. Consequently all these original child references agree. The
fields of an unvisited hole can differ, but none has been read: all
such subtrees are still pending and unmodified.

Initialization now has the identical source allocator start $n$ and
identical fresh known-node names. Replay the fixed prefix by the row
families of Lemma 8.4, with the following field relation in place of
its fixed-shape relation: all tag and child fields of nodes in the
still-unvisited hole intervals may vary; their root references and
interval lengths are fixed, and every field outside those intervals
agrees. At every classification in this prefix the node is an acquired constructor,
with the same label. Child-discovery follows only the acquired branch
fields just identified. Every edited leaf is an acquired leaf outside
all those intervals. Word walks stay on acquired ancestor paths;
its guard and literal target depend only on its acquired label.
No instruction enters a pending hole. Thus each primitive field read,
allocation, control branch, event and coeffect agrees. This includes
the partial blocks preceding each completed NodeDone, not just the
checkpoint equation (OA.4). The exact same clear mask and final
NodeDone edge are reached. Every frame, word, packet, descriptor,
operand, invocation, completion, staging node and event has the same
actual name and payload. This establishes the converse on actual
runs for all the proposed fillings. $\square$

**Theorem 10.3 (exact raw-time fibre and its cardinality).**
At a checkpoint $c$ in Definition 6.1, its raw chronological fibre,
with literal canonical names and no renaming quotient, has exactly
the following seeds and one actual checkpoint for each seed:

$$
\mathcal F_T(c)=
\left\{K[t_1,\ldots,t_m]:
          t_i\in\mathcal T,\ N(t_i)=d_i\ (1\le i\le m)\right\}.
\tag{OA.14}
$$

If $d_i=2h_i-1$, its cardinality is

$$
|\mathcal F_T(c)|=
\prod_{i=1}^m 2^{h_i}C_{h_i-1},
\qquad C_j=\frac{1}{j+1}\binom{2j}{j}.
\tag{OA.15}
$$

The empty product is one. If there is a hole the cardinality is at
least two. The seed, full current source, complete state and $Q_0$
profile are recoverable from raw time at these checkpoints if and
only if $m=0$.

Proof. Necessity and actual realization of every member are Lemma
10.2. Determinism and equality of the whole event word give uniqueness
of its checkpoint, as in Theorem 8.6. A full binary tree with $h_i$
leaves has $h_i-1$ branches and $2h_i-1$ nodes. The standard ordered
full-binary shape count is $C_{h_i-1}$; each shape has $2^{h_i}$
independent terminal labelings. These are the credited Catalan and
shape/label ingredients, with no quotient by equal labels at distinct
positions. Distinct hole valuations give distinct whole trees by
unique ordered-hole decomposition, so their counts multiply to
(OA.15). The case $m=0$ is the single finite seed $K$; every nonempty
factor has $h_i\ge1$ and contributes at least two.

With no holes, canonical finite descriptive execution reconstructs the
actual checkpoint and every finite response. With a hole, change one
of an actual filling's leaf labels without changing its size or shape.
Both members of (OA.14) have identical raw time by Lemma 10.2, and
Theorem 9.2 separates their task profiles. Their unchanged pending
source leaves have different labels. Hence all the indicated targets
fail to factor through raw time on that fibre. This also gives the
necessary direction for complete-state recovery, with actual equal-word
witnesses. $\square$

**Corollary 10.4 (three distinct fibres and their coding boundaries).**
At this same checkpoint the three observations have the following
exact seed fibres:

| Observation held fixed | Exact free choices |
| --- | --- |
| Selected $M^{\rm pre}$ | All finite independent hole fillings, as in (OA.7). |
| Raw $T_0$ | All hole fillings of the respective sizes $d_i$, as in (OA.14). |
| Joint $(S_0,T_0)$ | Each hole's actual ordered shape fixed, with all its leaf tags free, as in (OA.10). |

In the last row $r(c)=\sum_i\lambda(t_i)$, where $\lambda$ is leaf
count, and the cardinality is $2^{r(c)}$. In the middle row $r$ has
the same value $\sum_i h_i$ for every filling but its fibre also varies
hole shapes. For an exactly $b$-bit conditional supplement with no other
side channel, raw-time recovery on this fixed middle fibre requires
and descriptively admits

$$
b\ \ge\ \left\lceil\log_2
       \prod_i 2^{h_i}C_{h_i-1}\right\rceil.
\tag{OA.16}
$$

Proof. The first row is Theorem 6.2 without adding a reference field
to its memory. The second is Theorem 10.3. At these checkpoints all
probed seed leaves have been published and all holes are unvisited.
Contract those published tiles as in Lemma 8.5. Fixing current support
then fixes exactly each remaining hole shape; its unobserved tags are
free by Theorem 8.6. This proves the third row and its count.
For (OA.16), distinct fillings give distinct current labelled sources:
the acquired-leaf encodings lie outside their unchanged pending holes.
The next work-head test is a successful Advance and preserves this
source, so its complete original successor separates any two such
fillings, including ones with different shapes. Thus the fixed fibre
needs that many supplement values. Enumerate the finitely many
size-constrained labelled trees in each ordered hole and use its fixed-width rank; this gives
the converse. Enumeration is on finite descriptions and has no claimed
installed cost. $\square$

For example, at $K=\square$ with $n=5$, raw time leaves
$2^3C_2=16$ seeds. Fixing one of its two shapes leaves eight joint-view
seeds. Selected prefix memory at this very same $K$ instead permits
all finite trees. The one-node pending case has $d_1=1$ and two raw
and joint seeds, so size knowledge never removes an unread terminal
label.

Ordered sizes cannot be replaced by a total-size constraint. At
$K=\langle\square,\square\rangle$, both
$\langle\alpha,\langle\alpha,\beta\rangle\rangle$ and
$\langle\langle\alpha,\beta\rangle,\alpha\rangle$ have $n=5$,
but their pending-root names are respectively $(\nu(1),\nu(2))$
and $(\nu(1),\nu(4))$. The actual right-child follow after the seed
branch reads those different references. Their selected memories agree
and their raw times differ. Thus (OA.14) retains each individual interval
constraint, not just $\sum_i d_i$.

Literal raw-name equality is also distinct from equality modulo a
renaming of references. Theorem 6.3's one-node versus three-node
seed pair already has different first known-source names while the
same selected prefix was acquired. Here (OA.12) uses those names exactly
as supplied by canonical installation. Erasing them, quotienting them,
or allowing an arbitrary different initial layout changes the observation
or model. No formula here asserts a fibre count for that changed domain.

## 11. Resource interpretation, supplied methods and remaining scope

**Proposition 11.1 (same-run account for the new boundaries).**
Theorems 8.6–10.3 require no new maintained field, sidecar, frame,
service, source probe or replay counter. Their same-run information
boundary is exactly the original classification occurrence. If $a_c$
and $b_c$ count the alpha and beta old leaves of $j(u)$ whose Publish
has executed, then after startup attachment

$$
N(\text{active source at }c)
   =N(u)+4+2a_c+4b_c.
\tag{OA.17}
$$

The source backing at any cut is instead $N(u)$ installed nodes plus
the startup nodes actually born so far plus every target node actually
born so far, including an unfinished target and all detached old/new
material. At completed Boot this is

$$
N(u)+4+3(a+2)+5b,
\tag{OA.18}
$$

where $a,b$ are the original seed's alpha and beta leaf counts.
All other cell/event and operation coordinates are precisely those
of Theorems 7.1–7.2, restricted to the actual prefix or summed over
its later completed services.

Proof. Each original seed leaf is classified exactly once in Boot;
the wrapper's two leaves are known. Thus $r(c)=\lambda(u)-|A(c)|$
decreases only at those seed-leaf classification rows. Offer, Take
and Arrival each follow their own already counted Probe; operand
creation follows the actual receipt/parser and is not an additional
unknown-source observation. Root attachment creates $j(u)$ with
$N(u)+4$ active nodes. Replacing an alpha leaf by $A$ adds two active
nodes; replacing a beta leaf by $B$ adds four. Lemma 8.3 leaves no other
active change, proving (OA.17) also during every partial staging block.
The targets remain detached until Publish and so do not enter that
active count early.

All source births, however, remain in backing. The fixed startup
contributes four. Each of the $a+2$ alpha and $b$ beta old leaves of
$j(u)$ contributes three or five target births respectively; no old
leaf is freed. This proves (OA.18) and its partial-birth version.
Sender and receiver frames already born, snoc/forward words, packets,
operands, invocations, completions, current/old descriptors and their
rows remain retained even when roots are cleared. Each actual row
has its actual event initialization and append coeffects. The holder,
sixty-four bank cells, initial input nodes/links/root attachment,
known-source preparation, later command bits, grafts, output framing
and cleanup retain exactly Theorem 7.2's account. None is paid for
by the conditional supplement's bit length. $\square$

A reconstruction in §§8–10 takes a finite serialized observation as
mathematical input. Reading or delivering that serialization, comparing
literal canonical names, representing and manipulating large ranks,
retaining simulated states and outputting a recovered description all
require their own backing and operations if implemented. The event
archive is not operand-readable by the installed controller. Counting
an existing raw word is not a free acquired numeral in a live slot.
No cost optimum, constant-space realization, physical latency gain,
capability revival or paid-conversion implementation follows from
(OA.11), (OA.15) or (OA.16).

**Definition 11.2 (mathematical suppliers and the precise correspondence).**
The generic methods used here retain their existing ownership and domains.

| Supplier | Reused fact and the additional correspondence proved here |
| --- | --- |
| [ActualTreeReadoutAcquisition][ACT], `flip`, `source_foundation`, and its [owning Scribe][ACTB]; [Discovery and Retained Context, §2][NDR8] | Existing one-leaf locality and leaf-label rigidity supply the elementary competitors. Lemmas 8.3–8.4 verify that those competitors preserve this controller's literal names, every row, every non-source field and every coeffect even through partial publication. Leaf flips themselves are not new. |
| [NativeFullSourceProducer][PROD], private `traverse`, `production_reads`, `stationary`, and its [owning Scribe][PRODB] | Existing source-blind preorder reconstruction supplies the traversal method. The source here changes online, so protection of pending original paths and the no-unprobed-tag-read property must be supplied by §§3 and 8; stationarity is not imported. |
| [NativeBoundedPreorderRows][ROWS], private `pending_next`, `pending_left`, `cursor_frontier`, `actual_cursor_residual`, and its [owning Scribe][ROWSB] | Existing exact pending-preorder correspondence supplies the ordered intervals behind (OA.13). The equality of actual raw pending-root names with those interval boundaries, and the converse preserving all Boot event fields, are Lemma 10.2's source-specific content. |
| [NativeDepthPatterns][DEPTH], `fill`, `decompose`, private `fill_decompose`, `decompose_fill`, `depthEquiv`, `frontier_geometry`, and its [owning Scribe][DEPTHB] | Independent actual hole fillings and unique decomposition are supplied mathematics. The attained adaptive $K$, individual raw-name size restrictions and all-row publication converse are different concrete conditions established here. |
| ER §§10–12, 16–19 and 20–23 | Marked source inverses, local old-tile framing, fine fragments and actual received operands retain their stated acquisition and phase premises. The published-address contractions in Lemma 8.5 concern Boot's original one-node leaves, without importing ER's complete-acquisition initialization, leaf-list schedule or different tariffs. |
| [AIF Theorems 4.2, 4.4–4.5][AIF8] and [CSA Lemma 5.4/Theorem 6.3][CSA8] | All-microcut acquired-input replay and actual-history kernels already exist in their stated runtimes, with their actual seed/ingress/activation and position evidence. Here neither a previously acquired seed nor a new retained position is assumed; Theorems 8.6 and 10.3 first identify exactly the missing seed information. Finite replay is used only after that information is supplied or determined. |
| [NativeSerialMachine][SER8], `replay_deterministic`, `reached_prefix_replay`, `actual_register_execution`, and its [owning Scribe][SER8B]; pinned mathlib [StateTransition][ST] | Deterministic finite-prefix induction and matching-start refinement are generic suppliers. The fieldwise two-run relation and its exact converse are proved for the separate row basis of this volume, without claiming a lowering to NativeSerialMachine. |
| [TypedFiniteViewKernel][KERN8], `response`, `typed_finite_view_kernel`, and its [owning Scribe][KERN8B]; [PredictiveMemoryMinimalQuotient][QUOT8] and its [owning Scribe][QUOT8B] | Complete finite-path response kernels and factorization requirements are supplied abstractions. The actual common Advance experiment in Theorem 9.2 supplies the needed separation; equal descriptions alone do not assert readout/update factorization for a deficient view. |
| [Dynamic Acquisition Frontiers, §6 and literature map][DAF8]; Flajolet and Sedgewick, [*Analytic Combinatorics*, printed pp.6–7][CAT8] | The ordered binary-tree generating equation $C(z)=1+zC(z)^2$, Catalan formula and independent leaf-label multiplication supply (OA.15)'s counting ingredients. The new issue is which actual named Boot executions belong to that finite product, proved before counting. |
| Huet, [*The Zipper*, §§1.1–1.3][HUET]; Reynolds, [*Separation Logic*, Frame Rule][REYNOLDS] | Focus/context modification and disjoint-footprint preservation are generic methods. In this model the actual word walk, incomparable original leaves, exclusive writer and detached target establish their concrete preconditions. No focus/context description is treated as acquisition. |
| [Paid View Conversion, §§5–7][PVC8] | Finite conversion algorithms, genuine acquired serialized inputs, completed-object registries, owned import, publication, acknowledgement and token return are already positive suppliers in their enlarged installed runtime. Those operations are not installed in $\omega$, and the present descriptive inverse does not acquire them. |

The contribution is the exact two-run raw-reference/coeffect relation
and converse for the unchanged online Boot at every reached row,
including partial publication, together with the ordered pending-size
refinement of its original NodeDone raw-time fibre and the sharp
classification-Probe temporal threshold. Generic framing, traversal,
replay, leaf flips and counting are credited tools. These are ordinary
proofs and a repo-derived correspondence; they carry no new Lean
certification or worldwide-priority assertion.

**Definition 11.3 (full domains retained and continuing obligations).**
The all-row joint theorem includes the source attachment/start, all
finite initial seeds, incomplete Probe/Offer/Take/Arrival and parser
work, partly constructed operands and words/stacks, each guard and
staging field, before and after the one Publish assignment, completion,
individual cleanup rows, every output token and the first Return.
The raw-time product theorem uses exactly Definition 6.1's original
checkpoints. In particular it does not silently restrict Theorem 8.6
to NodeDone, or extend selected $M^{\rm pre}$ to an interior full-memory
projection. The first raw-time recovery cut can precede the final
NodeDone, while that receiver is still waiting for the last token.

Reconstructed full states support all the old finite-command response
continuations by the unchanged row semantics. This is distinct from
independently recovering an arbitrary later Update/Scan starting cut
from each of its four views. No such later-cut inverse, callable
arbitrary-view service, acquired converter input, cross-owner return
or new operation is claimed. The exclusive owner, canonical literal
names, no-sharing occurrence tree and absence of competing writers,
revocation, interrupts and arbitrary scheduling remain essential model
premises. Their broader variants require separate proofs.

All earlier fixed-$G_{gc}$, original-$Q$, parked-consumer, unchanged-
initialization and authority obligations retain their exact original
statements. Independent four-view recovery at arbitrary continuing
Update/Scan and other interiors, actual acquired/callable cross-view
conversion with full return and resource accounting, and broader
interference/rights models remain unresolved. The full sustained
four-expression objective remains active beyond these finite Boot
and startup-checkpoint theorems.

[NDR8]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DISCOVERY_AND_RETAINED_CONTEXT.md
[DAF8]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DYNAMIC_ACQUISITION_FRONTIERS.md
[AIF8]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md
[CSA8]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CALLABLE_STORAGE_ATLAS.md
[PVC8]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_VIEW_CONVERSION.md
[SER8]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean
[SER8B]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs
[KERN8]: ../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean
[KERN8B]: ../../../Blueprint/D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.scribe.cs
[QUOT8]: ../../../D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.lean
[QUOT8B]: ../../../Blueprint/D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.scribe.cs
[CAT8]: https://algo.inria.fr/flajolet/Publications/book.pdf

## 追加锚（本行以下为增补区）
