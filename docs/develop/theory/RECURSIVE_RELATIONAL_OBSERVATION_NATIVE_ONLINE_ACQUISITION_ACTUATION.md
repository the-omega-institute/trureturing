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

## 12. An incoming-field runtime for the same logical services

**Definition 12.1 (the distinct runtime $\iota$).** Retain the finite
tree algebra, $\rho,E,a_0,j,F_w$, unknown-input occurrence installation,
source fields, fixed owner $o$ and root port $\pi$ of Definitions
1.1–1.2. Retain their exclusive, static read/write/allocation rights,
no sharing, no competing writer, no revocation and canonical typed
allocation. References have no inspectable indices or arithmetic.
There is one actual installed finite seed $u$, not a description of
it. Every $u\in\mathcal T$ and every finite word over $\Lambda$ is
admitted. The instruction description, cell types, owner, orientation
and slot layout are fixed independently of both inputs.

The runtime $\iota$ uses the bounded field-operation basis of
Assumption 1.2. It retains the sender/receiver token handshake and
constructor parser of Definition 2.1, the fresh receiver words and
table construction of Definition 2.2, and the literal old/target
templates (OA.3). It changes the retained source work and the
attachment acquisition/use rules to Definitions 12.2–12.5. In
particular, it performs neither snoc reversal nor a root-to-leaf
actuation walk. Its Boot, Scan and Update have exactly the logical
entrance/source-successor/new-table contracts of Definition 1.1;
these are conclusions of Theorem 13.2, not added whole-tree
operations. The row events and complete successors belong to this
new runtime.

**Definition 12.2 (material incoming fields).** A source-work cell has
four fields in the displayed order

$$
f=(\mathsf{node},\mathsf{holder},\mathsf{side},\mathsf{next}).
\tag{OA.19}
$$

Its node, holder and side are initialized from actually held values
at its birth and are never assigned again. Side is one of
$\mathsf{root},L,R$. For side root the holder is the actual fixed
port $\pi$; otherwise it is an actually held source node. Write
$\operatorname{at}(v,s)$ for reading the one field $\pi$ when
$(v,s)=(\pi,\mathsf{root})$, and the indicated child field $v.s$
for $s=L,R$. This notation abbreviates a finite three-case field
instruction, not a search for an incoming edge or a first-class
unbounded address. It has no executing edge outside these typed cases.

Receiver frames, snoc cells, packets, table rows, completions and
descriptors keep Definition 1.3's payloads. A fresh editing operand
instead has $(\mathsf{word},\mathsf{label},\mathsf{site},\mathsf{next})$;
its site is a source-work-cell reference. An invocation has
$(\mathsf{operand},\mathsf{packet},\mathsf{site},\mathsf{focus},
\mathsf{old},\mathsf{new})$. All their fields are individually
initialized and charged. An operand's first three fields are never
assigned after birth. There is no new source-node parent field.
The complete source-work-cell backing is retained after its pop.
Consequently a site remains readable without being a live stack head.
Retention is not reclamation or bounded memory.

In addition to the holder and sixty-four slots of Definition 1.3,
install a second holder and sixteen one-value slots, in this order:
current site, holder, side, expected node, attachment value, operand
site, left word, right word, descriptor owner, descriptor port, and
six scratch slots. These seventeen cells are created and attached
in their fixed order with null values, before known-source
preparation. The new slots are accessed by fixed literal positions.
The old reversal/walk routines and their live cursor roles are
absent. All sixteen new slots are cleared, one at a time in index
order, after each old NodeDone clear mask, before its NodeDone
edge; they are likewise cleared
before Return. At service entry they are null. Stack heads, output
roots and the current descriptor keep their old retention rules.
The finite mode/parser/template latches contain no source-dependent
integer, reference list or address.

**Definition 12.3 (row expansion, initialization and action domains).**
Use Definition 1.3's ordered expansion of each named field read,
follow, test, birth, assignment, input, output and control edge.
Pop reads the four fields of (OA.19) in order before changing the
head; push initializes all four and changes the head. List append
uses the old null test, field initializations, tail link and endpoint
assignments. Slot/latch coeffects retain the bounded returned values.
The sixteen-slot additions in Definition 12.2 are included in every
specified clear sequence. Finite template loops can equivalently be
unrolled in literal preorder; the selected fixed template determines
that finite instruction sequence. Iteration over work, packet cells
and output rows always executes the indicated head test. No linked
list traversal is one row.

Each executed row appends one bounded-arity event with predecessor,
opcode, actual operand references, read/emitted value and bounded
slot coeffects, including its actual birth/initialization and tail
assignments. Event recording is the instrumentation of that row;
it does not initiate a second instrumented row. Finite cell arities
and the fixed slot/coeffect lists give a fixed event arity bound.
An ordinary conditional test selects its specified true or false
branch. A failed requirement has no executing successor. Prescribed
Advance is the only action during installation, preparation, graft,
service, output and cleanup. The input controls and disabled response
are precisely Definition 4.1's Ready/Tail codes $0,10,11$; neither
admits Advance. Any other action executes nothing and emits nothing.
Stopping an action prefix adds no event.

Observer chronology begins after the unknown input installation,
as in Assumption 1.2. Install both local holders/banks, then prepare
the actual three-node $a_0$ and its wrapper with the captured old
root, publish $j(u)$ at $\pi$, and enter Boot. No unknown tag is
read in this preparation. Grafts after command input prepare the
actual $A$ and wrapper and publish exactly as in Definition 4.1,
then enter Scan. All these births, initializations, captures, links,
events and clears are part of this execution. They are not an
unobserved attachment constructor.

**Definition 12.4 (acquiring sites during actual descent).** At service
entry read the actual chronological tail into saved scratch, mark
any current descriptor held and retain it as previous, capture
the actual reference $r$ in $\pi$, and create the new descriptor
with that saved entry, previous, fixed owner/port, mode, state
building and null table endpoints. Clear the new-table/operand
endpoints and output cursor as in Definition 1.3. Push the source-work
cell $(r,\pi,\mathsf{root},\mathsf{null})$, and push the receiver
frame for the empty word. On a nonempty work head, retain its actual
cell reference in current site, pop its payload, retain node as
focus and holder/side in the new bank, and pop the receiver word
$q$. Read $\operatorname{at}(\mathsf{holder},\mathsf{side})$
and require its value equal to focus. This is a new paid read and
reference test at every visit, including the root.

Classify this focus by precisely Definition 2.1's actual probes,
Offer, Take, Arrival, Acknowledge, receiver parser and PackDone.
Packets still contain only the literal constructor tokens of Boot
or the three/five-token encoded statuses (OA.2). They contain no
source reference, supplied word or right. In the branch case,
append the receiver branch row, construct the backed snoc words
$qL,qR$, retain their actual references in left word/right word,
and push the receiver frames right then left. Obtain the actual
source children by the Boot follows or the already performed encoded
classification follows, exactly as in Definition 2.2. Push the source
cells

$$
(r_R,\mathsf{focus},R,\mathsf{oldHead}),\qquad
(r_L,\mathsf{focus},L,\mathsf{newHead})
\tag{OA.20}
$$

in that order, using the actual returned head after the first push.
Execute the expanded NodeDone and resume work. Thus the stored
holder is the source parent *from which the child was actually
followed*. It is not recovered from the child's name, receiver word
or a supplied parent map. At empty source work, require empty
receiver work and mailbox, then enter End.

For a Scan leaf, append $(q,\ell)$ and execute NodeDone, as before.
For a Boot/Update leaf, after PackDone read the current-site slot
and append the fresh operand $(q,\ell,f,\mathsf{null})$, with $f$
that actually read reference. Read its word, label and site fields
in order. The first two determine exactly the table rows of
Definition 2.2, including the Update beta expansion; no new source
work is scheduled for that expansion. Retain the operand's read site
in operand site and enter Definition 12.5. This is a paid local
connection of a receiver-built operand to the current sender work,
under their common owner. It does not transmit a reference in the
constructor packet or assume that its constructor describes a
location. Earlier tables, events and completed operands remain
unread as operand suppliers.

**Definition 12.5 (actual local use).** Create an invocation with this
fresh operand, this packet, its read site and held focus, with old/new
null. Read the site's node, holder and side fields in that order.
Require its node equal to focus and its side belong to $\{L,R\}$.
Read the current descriptor's owner and port fields and require the
fixed values $o,\pi$. These checks identify the current binding;
the static right in Definition 12.1, not the check or a tree shape,
authorizes operations. Read the indicated holder child field,
require equality to the site's node, and assign that actual value
to invocation.old. The operand word is retained as the receiver's
actual addressed content but is neither expanded nor walked.

Select the old/target template by mode and the operand's received
label. Execute Definition 2.3's bounded fieldwise literal old-tile
guard from invocation.old, its preorder target births, null tests
and individual staging-link writes. Save the first target birth in
invocation.new. At the final attachment check reread just the site's
indicated holder child field and require equality to invocation.old.
Publish writes invocation.new to that same field. Append the one
completion and execute the expanded NodeDone. Apart from this
Publish, no active-source field is assigned during the visit.
Source-work-site fields and operand fields are not retargeted to
the replacement. They record the acquired old occurrence and its
one actual invocation.

The use of an incoming arc/location is the known method of Huet,
[*The Zipper*, §§1.1–1.3 and binary specialization §2.2][HUET].
Here an immutable four-field work cell stores an actual acquired
parent field, rather than Huet's reconstructed applicative context.
It supplies no free focus or parent acquisition. The source-specific
joint relation needed to justify these operations is defined next.

## 13. Joint acquisition, protected fields and every finite prefix

**Definition 13.1 (the joint live-site relation).** Fix a service's
finite compound logical entrance $x$, and its mode. At a NodeDone
checkpoint use exactly the partial old logical tree $H$, hole order,
processed-leaf set and mixed source in Definition 3.1. For each
pending hole $q$, let $r_q$ be its actual source root. The matching
source/receiver stack pair consists of (OA.19) and a receiver frame
whose backed word has value $q$, with

$$
\begin{aligned}
 f_q.\mathsf{node}&=r_q, &
 \operatorname{at}(f_q.\mathsf{holder},f_q.\mathsf{side})&=r_q,\\
 \text{actual subtree at }r_q&=
 \begin{cases}x|_q&\mathrm{Boot},\\ E(x|_q)&\mathrm{Scan,Update}.
 \end{cases}
\end{aligned}
\tag{OA.21}
$$

At the initial singleton frontier, $q=\varepsilon$ and the site is
the actual port capture. Every later nonroot site has the actual
parent occurrence at $q^-$ and side the last letter of $q$, acquired
by the two follows and pushes in (OA.20). At strict prefixes of
each pending $q$, source-node identities and branch tags are those
of the original logical branch occurrences. The child fields on
those particular paths are unchanged.
The receiver table has precisely Definition 3.1's row-prefix value.
The static right remains the same actual owner's right over the
source component, local backing and fresh staging.

During a visit, remove its head pair from the pending set and retain
it as the current pair. The remaining sites' designated incoming
fields, path fields and descendant subtrees are protected. The
current site's incoming field and old subtree are protected until
Publish; after Publish that field contains exactly the new target.
During a branch's partial pushes there is a finite intermediate
pairing: newly born receiver words/frames and source cells occupy
their specified slots/stack positions, with each already initialized
payload equal to its originating actual read or constructor. Paired
stacks are required again at NodeDone, not between the two pushes.
During packet/operand/guard/staging/cleanup phases, acquired values
are precisely those already obtained in the specified rows; no
future read is included in a latch or payload. This phase assertion
includes partial lists and partly linked fresh target trees.

Protection is fieldwise. If two pending/current sites have the same
holder but different sides, the side not being published stays
unchanged, while the other child field may change. Neither (OA.21)
nor this relation asserts immutability of the whole holder node or
of every descendant of an original branch.

**Theorem 13.2 (acquired content, acquired location and current lawful
use).** For every finite compound $x$, a service entered with its
Definition 1.1 entrance source and the empty work of $\iota$ has
one finite successful execution. Its NodeDone checkpoints satisfy
Definition 13.1 and (OA.4); every finite row prefix satisfies that
definition's phase assertion. In every editing invocation, all of
the following refer to this *same actual execution*:

1. The operand word is the receiver-built word of the visited old
   logical occurrence, and its label is decoded from that visit's
   actually arrived tokens.
2. The operand's site is the actual acquired work cell for this
   occurrence; its indicated holder child field still contains the
   invocation's old root until this invocation publishes.
3. That old root has exactly the guarded literal old template, the
   new root consists of this invocation's actual fresh births and
   links, and the owner's unchanged right authorizes their reads,
   staging and publication.
4. Publish changes only that designated incoming field. All
   remaining-observation subtrees and their necessary fields stay
   available for subsequent receipt and use.

At End the source and new table are respectively $E(x),\mathsf A(x)$
in Boot, $E(x),\mathsf A(x)$ in Scan, and
$E(\rho x),\mathsf A(\rho x)$ in Update. Root and partial-operation
phases are included; no root-leaf edit is used on this domain.

Proof. Service entry captures the actual port and creates the root
site from that capture. The first read of the port therefore verifies
the singleton instance of (OA.21). The receiver's empty word and
empty table give precisely (OA.4). The root is a logical branch
because $x$ is compound, also in encoded modes by (OA.1). Its
classification can thus enter the branch construction but never
the nonroot-only editing block. The root port is not written during
a service; graft publication lies strictly before its entry.

Suppose the checkpoint relation holds before a visit. Pop obtains
the actual immutable payload and its matching backed receiver word.
The new incoming-field read succeeds by (OA.21). The ordinary
preorder frontier step is the one already used in Theorem 3.2 and
in [NativeBoundedPreorderRows, `cursor_frontier` and
`actual_cursor_residual`][ROWS]. It identifies this pair as the next
old logical node, with no old table or descendant description in
the controller. Previously processed leaves and pending holes are
prefix-incomparable. In particular no earlier publication has
detached this node or changed its indicated incoming field.

During classification there is no source assignment. Boot reads
the actual constructor; in encoded modes (OA.1) and the supplied
erased-$E$ grammar give exactly (OA.2). After each probe, Offer,
Take, Arrival and Acknowledge preserve the following prefix fact:
each packet cell already born has the actual token taken from this
visit's offer, in order, and no later probe precedes the preceding
acknowledgement. This remains true before Arrival and during parser
reads, because it asserts only values already received. The accepted
constructor is therefore the actual old logical constructor at $q$.
This reuses the handshake proof of Theorem 3.2 on unchanged source
reads and packets; the added field checks do not generate tokens.

At a branch, the fresh receiver word constructors give exactly
$qL,qR$. Their row/frame writes expose no unknown contents. The
source children in (OA.20) are the references returned by actual
follows of this focus. They are distinct nonnull children, and the
focus is the actual original branch at $q$. Hence both newly
created sites satisfy (OA.21) for their respective sides, and their
matching receiver words have the required values. The finite
partial-push assertion records each of these facts as soon as its
payload is initialized; it does not assume both stacks have already
been updated. At NodeDone both pushes have occurred, so the full
paired frontier is restored. No active field has changed.

At a Scan leaf, the authentic packet and word append exactly the
required row and consume this hole. At an editing leaf, the
current-site slot still contains the popped source-cell reference:
no intervening row assigns that slot. The operand's word and label
are initialized from the current receiver word and parser result,
and its site from the actual slot read. Reading those fields back
thus joins the acquired constructor, backed address and acquired
incoming field of the same visit. The site was not selected by a
leaf-label lookup, equality of two views, or a separate existence
witness. The invocation and its packet have these actual origins.

All logical leaf addresses of a compound $x$ are nonempty. This
proves the side check $L$ or $R$, while equality of site.node to
focus follows from its unchanged payload. Its holder is the
original branch immediately above this leaf and remains reachable.
Indeed every active-source write in this service is at an old
logical leaf's incoming field. No such leaf can be a strict prefix
of the current leaf, and none can replace one of its branch
ancestors. At a shared parent an earlier sibling publication may
have changed the *other* child field. It has not changed the
current side. Thus the initial attachment read in Definition 12.5
returns this actual focus, even in that shared-parent case.

The current old tile is the unchanged raw leaf in Boot, or its
unchanged $E$ tile in Update. Its literal guard therefore succeeds
at every read, follow and null/non-null test. All staging references
come from this invocation's fresh allocations; no source or pending
node is reused. Literal parent-before-child order and one link per
nonroot position prove each vacancy test and each target field
value, even at a partial staging cut. Descriptor owner and port
remain the current fixed binding, and the premise grants that owner
the read/write/allocation rights used here. No row transfers or
revokes them. Authentication of the operand and equality of a
template consequently do not stand in for authorization.

Between the two attachment reads there are only reads and writes
to fresh staging or local/record material. The indicated source
field still contains invocation.old at the final check. Publish
changes that one field to invocation.new. Every other pending
hole is incomparable with this old leaf. Its entire actual
descendant subtree is disjoint from the detached old tile, new
target and edited field. Its proper-prefix path does not use that
field. Even if its incoming holder is the same node, its selected
side is different. This proves the protected-field assertion
through the one assignment and at its immediate successor.
This is the concrete field-level framing needed for Reynolds's
[Frame Rule, §4][REYNOLDS]: the framed storage is disjoint from
the write footprint, and its reference parameters are immutable
payloads or fixed proof parameters. A mutable scratch cursor is
not used as a supposedly stable free variable in that assertion.

The source change is the old-leaf replacement (OA.3), so
distributivity of $E$ gives the new mixed-source equation (OA.4).
The receiver's rows give the same logical leaf contribution, with
the beta Update expansion included before NodeDone. The completion
is born once on this control path. Cleanup changes only its named
slots/latches, not the pending work payloads, source fields or new
row contents. This proves the next checkpoint and all intermediate
phase cases by induction. In particular no whole shared-parent
immutability was needed.

There are exactly $N(x)$ visits by structural induction on the old
logical tree: one branch visit followed by its two old subtrees,
or one leaf visit without scheduling its replacement. Each packet
has at most five tokens. All other per-visit loops are bounded
literal templates or finite stack/list operations; there is no
address-length loop in actuation. Thus each visit finishes and the
stacks empty together after precisely those visits. Exhaustion
processes every old leaf. The mixed-source equations and row-prefix
equalities give the three asserted complete contracts. This proof
both establishes successful requirements and fixes the actual
operations; it does not assume a response sequence at pending holes.
$\square$

**Theorem 13.3 (initialization, all finite commands and partial actions).**
For every finite $u$ and every finite $w\in\Lambda^{<\omega}$,
the prescribed initialization and commands of $\iota$ attain a unique
returned state $J_\iota(u,w)$, with source
$E(F_w(j(u)))$ and current table $\mathsf A(F_w(j(u)))$.
Every legal finite action prefix from observer entrance, including
partial installation/preparation, a single first command bit,
partial graft, root entry, any service row, output or cleanup,
has its actual complete deterministic successor and retained events.
Every such prefix can be extended to a return after completing any
partly supplied command. No claim concerns an infinite command word.

Proof. The bank installations are fixed finite births/attachments.
At every partial cut their already created fields have their stated
values; uncreated cells are not read. Known-source preparation
initializes fresh nodes and links from held values. Until its final
port assignment the active source is the installed $u$; afterwards
it is the actual $j(u)$. Partial staging is detached throughout.
All its accesses have the fixed owner's right. These statements
give every preparation prefix without assuming the service
invariant before a service exists. Theorem 13.2 applies to the
compound $j(u)$ for every seed, including either single terminal.

End uses Definition 4.1's table publication, retirement, constructor
output and Return, with the additional sixteen clears. Its finite
row traversal prints exactly the table's $N(j(u))+2$ framed tokens
and attains Ready only on the final Return. This gives the first
returned state. Suppose a return has logical value $x=F_w(j(u))$.
Code $0$ starts Update, whose contract gives $E(\rho x)$ and
$\mathsf A(\rho x)$. Codes $10,11$ prepare a detached $A$ and
new branch using the held old root. Until the port write, the old
active source remains $E x$; after it the source is
$\langle A,E x\rangle=E(Lx)$ or
$\langle E x,A\rangle=E(Rx)$. This gives every graft cut and
the compound entrance needed by Scan. Its contract and the same
finite output/cleanup tail give the next return.

Ready and Tail have exactly the stated two bit choices. All other
next executing rows are fixed by finite control and actual reads;
Theorem 13.2 proves every service requirement on these inputs.
Only Return enters Ready. Another such occurrence requires a new
command and its complete finite service. Canonical typed births,
the prescribed field order, event append and clear order determine
every allocated object and complete state at each prefix. Induct
on the finite action sequence for uniqueness and the disabled cases.
For extendibility, complete a pending two-bit code if necessary;
every remaining initialization/graft block is finite, and Theorem
13.2 plus the output tail finishes the current service. This proves
the full finite-prefix domain, rather than only a checkpoint domain.
$\square$

## 14. Logical refinement and the separate complete-response task

**Definition 14.1 (the common logical service interface).** A logical
service state exposes its mode, entrance $x$, current extensional
active source tree, new addressed row prefix, and constructor-output
prefix. At entry, within visits, and at End, interpret the first
three by Definition 3.1: one old constructor is acquired in preorder,
a branch exposes its children as pending work, an editing old leaf
is replaced by (OA.3), and its new table contribution is precisely
Definition 2.2's contribution. Finite local work may stutter without
an active-source change. Table publication and each actual output
token have their stated effects. A completed service must have the
entire Definition 1.1 contract and the framed $n'+2$ constructor
tokens. At returned commands the logical task exposes the current
table and every finite subsequent completed coded command with
its new table/source and constructor stream. Input is still actual
$0,10,11$, and no next command is admitted while a service is busy.

Neither allocation identities, per-row opcodes, retained local
backing nor the number of Advances is identified in this common
interface. In particular it is not the complete-response task
$Q_\omega$. Its input/source/table/output obligations precede the
choice between $\omega$ and $\iota$; its logical $x$ is a proof
parameter, not a service argument delivered to either controller.

**Theorem 14.2 (paid online refinement on the common contract).**
On every allowed seed and finite command word, both $\omega$ and
$\iota$ implement Definition 14.1 with the same logical source
and table at matched node completions, the same ordered old-leaf
publication effects, and the same constructor-output tokens.
For $\iota$ the implementing locations, received labels and continued
rights are actually acquired/retained as in Theorem 13.2. There is
no complete-table acquisition or refresh before its first leaf
publication or between Update's publications and its new table.

Proof. Relate the two executions at entry and their $i$-th completed
old-node visit by the same $x$, the same partial $H$, the mixed-source
tree (OA.4) and the same extensional receiver row prefix. Theorems
3.2 and 13.2 establish these statements independently for both
executions. The next old constructor is the same and its packet
values are the same, since each actual pending subtree has the
stated raw or encoded value. Receiver branch/leaf constructions
therefore make the same words and row contents. At an editing leaf
the old root reached by $\omega$'s word walk is at $q$; the actual
field in $\iota$'s site is at the same $q$ by (OA.21).
Their selected templates and one-field publication effects agree.
Extra attachment reads, word-walk work, local births and staging
can be matched by finite stuttering in this interface; they do not
alter the active source before Publish. Both append the table
contribution in the same order. This extends the relation to the
next node completion and through each ordered source publication.

At End the full contracts give the same table. Output traverses
its actual rows and emits the identical constructor word, including
Begin and End. At returned cuts, induction using the same command
codes and the actual graft equalities proves every finite logical
continuation. Theorem 13.2 supplies the additional actual location/
content/right correspondence, not equality of extensional tables
alone. Inspection of its operand rules gives the final no-refresh
claim. This is a refinement of the declared logical interface, not
a matching of old and new full row responses. $\square$

**Definition 14.3 (the new complete task $Q_\iota$).** Complete
$J_\iota$ includes the active and detached source, port and fixed
rights, both holders/banks, every old/new descriptor and table,
all sender sites, receiver frames, words, packets, operands,
invocations, completions, events, allocators, latches/control,
input and output. At returned starting cuts, the empty experiment
exposes the extensional current table and Ready. A finite action
word has all actual legal domains, disabled responses and, at each
executing row, the response

$$
(a,\mathsf{legal},\mathsf{ok},\mathsf{opcode},
  \mathsf{actual\ value},\Delta\Gamma_\iota,
  \Delta\mathsf{Out},J'_{\iota}).
\tag{OA.22}
$$

The event chain begins after the actual input installation and
includes both bank installations, known-source preparation, every
classification handshake, site/operand access, guard, staging,
publication, command bit, graft, output, clear and Return. The
complete successor is a mathematical response coordinate, not a
transmitted snapshot. It includes prefixes ending before a receiver
Arrival or inside a field guard. It has the new cell payloads and
new chronology, so there is no asserted equality with $Q_\omega$
or with an original fixed-$G_{gc}$ task.

## 15. Complete service costs and actual continuing sums

**Theorem 15.1 (uniform linear complete-service account).** On one
actual $\iota$ service let $n=N(x)$, and let $b,a,c,d,n'$ have
exactly Theorem 7.1's meanings for that entrance. Let $s$ be the
number of source nodes actually reachable at service entry:
$s=n$ in Boot and $s=N(E x)$ in Scan/Update. Then
$n\le s\le5n$ and $n'\le3n$. The following counts are exact:

| Coordinate | Boot | Scan | Update |
| --- | --- | --- | --- |
| Classification probes, offers, arrivals and packet births, each | $n$ | $3n+2c$ | $3n+2c$ |
| Classification/child-discovery source follows | $2b$ | $2n+2c$ | $2n+2c$ |
| Source-site births, receiver-frame births, each | $n$ | $n$ | $n$ |
| Visit incoming-field reads and their equality requirements, each | $n$ | $n$ | $n$ |
| New table rows | $n$ | $n$ | $n+2c$ |
| New snoc-word cells | $n-1$ | $n-1$ | $n-1+2c$ |
| Fresh operands, invocations, completions, each | $a+c$ | $0$ | $a+c$ |
| Actuation word-reversal cells and root-to-leaf walk follows, each | $0$ | $0$ | $0$ |
| Fresh target source nodes | $3a+5c$ | $0$ | $5a+9c$ |
| Active leaf-attachment publications | $a+c$ | $0$ | $a+c$ |
| Constructor-output tokens including framing | $n+2$ | $n+2$ | $n+2c+2$ |

There is one descriptor birth per service. There are absolute finite
constants $C_R,C_F,C_V$, independent of $u,w,x$ and all depths,
such that the *complete* service from entry through Return satisfies

$$
\begin{aligned}
\mathsf{rows}_\iota=\mathsf{events}_\iota&\le C_R(s+1),\\
\mathsf{fieldops}_\iota&\le C_F(s+1),\\
\mathsf{newcells}_\iota&\le C_V(s+1).
\end{aligned}
\tag{OA.23}
$$

Field operations include reads, follows, assignments and every field
initialization/coeffect of cells and events. New cells include
source, local and event cells, all retained. Each finite prefix of
this service has the corresponding upper bounds, with the same
actual entrance $s$. These are bounded-reference/field-operation
coordinates; they are not bit, physical-time or bounded-memory
bounds.

Proof. Theorem 13.2 gives precisely the same old logical visits,
classification packets, receiver word/table contributions and
templates as Theorem 7.1. Its first, second, fifth, sixth, seventh,
ninth, tenth and eleventh counts therefore follow from those
specific unchanged operations. Site births are one initial root
and two per old branch, hence $1+2b=n$; each is wider than its
old two-field sender frame, and those extra initializations and
reads must still be charged. There is one new incoming-field read
and comparison at each pop, including the root. No row reverses
the snoc word or walks it from the root. This proves the two zero
coordinates without omitting the bounded literal-guard follows.

For each editing leaf, there is also the actual current-site-slot
read and initialization of operand.site, its subsequent site read,
three site payload reads, node/side checks, two descriptor-binding
reads/checks, two attachment reads/checks and one Publish. Invocation
site and all other fields are initialized and retained. The old
literal guard reads tag and both children at each old tile position
and performs its fixed path follows and finite-tag/reference tests.
Its old tile has at most five nodes and fixed path lengths. The
target has at most nine nodes, each with all three source fields
initialized; its at most eight links each have a vacancy test and
one field assignment. Its invocation.new assignment, completion
birth, list endpoint operations and all scratch clears also occur.
These are bounded leaf work, not a unit-cost hidden edit.

For a fully specified constant bound, take the finite collection
$\mathcal B$ of the following bounded row lists in Definitions
12.2–12.5 and the retained rules: entry/exit setup; one work test;
one source pop, receiver pop or push; one visit attachment check;
one classification case's source reads/follows; one token
Offer/Take/Arrival/Acknowledge; one parser-cell iteration or finite
acceptance edge; one snoc birth; one row/operand/completion append
or invocation birth; one of the four *unrolled* literal guard/stage/publication
cases; one expanded NodeDone clear/edge; descriptor publication/
retirement; one output-row iteration; framing and Return cleanup.
Split a list at its calls to another member, so no called operation
is counted twice. Include each loop's head, exit and branch tests
in its member list. For $B\in\mathcal B$, let $r_B,f_B,v_B$ be
its row, full field-operation and cell-birth counts, including
its events and their tail/slot coeffects. They are finite syntactic
counts of fixed lists; event recording introduces no recursion.

The number of calls to each member is at most $20(n+1)$: visits
are $n$, token/parser iterations at most $5n$, each stack has $n$
pushes and pops, row/snocs at most $3n$, editing blocks at most
$a+c\le n$, NodeDone blocks $n$, output iterations $n'\le3n$,
and entry/exit/framing blocks a constant number. Template work is
already unrolled, so its size is in $r_B,f_B,v_B$ and not hidden
in a call frequency. Set, for example,

$$
C_R=20\left(1+\sum_{B\in\mathcal B}r_B\right),\quad
C_F=20\left(1+\sum_{B\in\mathcal B}f_B\right),\quad
C_V=20\left(1+\sum_{B\in\mathcal B}v_B\right).
\tag{OA.24}
$$

This includes sender and receiver storage, the wider site/operand/
invocation fields, both bank clear sequences, all guard and target
work, event births and appends, retirement, every output token and
the final Return. It gives (OA.23) first with $n+1$; $n\le s$
gives the stated actual-entrance bound. Directly, the non-event
birth counts in the table plus its descriptor are at most $25n+1$,
and adding one event birth per executed row gives another such
bound for all new cells. Since costs are nonnegative, a prefix
cannot exceed its proved finite completion. Finally, $E$ replaces
each leaf by a three- or five-node tile and keeps logical branches,
so $n\le N(E x)\le5n$. Update adds exactly $2c$ logical nodes,
giving $n'\le3n$. $\square$

**Theorem 15.2 (installation, input, grafts and the actual finite run).**
For a finite run through returns for $\epsilon,w_1,\ldots,w_k$,
let $s_0,\ldots,s_k$ be its *actual* Boot and subsequent service
entrance sizes, $g$ its number of L/R commands, and
$\ell=\#\mathsf U+2\#\{\mathsf L,\mathsf R\}$ its number of
command-bit rows. All retained backing and field operations are
the disjoint sums of the service counts just proved, together with:

1. The actual $N(u)$ installed source nodes, their initialized
   fields, $N(u)-1$ child attachments and root attachment, including
   their initialization/installation account even though installation
   precedes observer chronology.
2. The original sixty-five local cells, the additional seventeen
   holder/slot cells, their fixed attachments/initializations, fixed
   control/rights installation and its finite account.
3. Four source births and five source link/port assignments in
   known-source preparation, and the same counts for each of the
   $g$ later grafts, with their actual captures/tests/control and
   event coeffects.
4. The $\ell$ actual input rows and their events/coeffects.

In particular, for the three coordinates of (OA.23) there are
absolute constants $D_0,D_1$ with the vector bound, interpreted
coordinatewise,

$$
\mathsf{cost}_{\iota}(u,w)
 \le D_0(N(u)+1)+D_1(\ell+g)
       +(C_R,C_F,C_V)\sum_{i=0}^{k}(s_i+1).
\tag{OA.25}
$$

Here the scalar fixed terms abbreviate a common upper bound in
each coordinate, not a scalar optimization objective. For a run
stopping inside a service include that service's actual entrance
size once; for an incomplete input/graft/preparation retain just
its executed rows and births, or bound them by its fixed complete
block. No service or later graft is charged against initial size
alone, and no cleared backing is subtracted.

Proof. Installation and preparation use precisely the fixed
constructors of Definition 12.3. The original bank has one holder
and sixty-four slots and the new bank one holder and sixteen slots.
Known $a_0$ and $A$ each have three nodes and two internal links;
each wrapper adds one birth, two links and the one port assignment.
All other captures, permission-preserving accesses, tests and
control operations in these blocks have bounded fixed row lists.
The command codes give exactly the displayed $\ell$. Theorem
13.3 gives one Boot and one service per completed command. Every
birth has one type, one chronological occurrence and a unique
canonical name; every field operation belongs to its actual row.
This partitions the complete finite run into the indicated sums.
Theorem 15.1 bounds the service summands, and a fixed constant
times $N(u)+1$ bounds the actual input installation fields/links.
Fixed installation and per-graft/input blocks supply $D_0,D_1$.
Nonnegativity gives the partial-run version, using Theorem 13.3
for its finite completion. Records, sites, packets, old tables,
detached tiles and both banks remain in the account. $\square$

**Definition 15.3 (additional resource coordinates).** A reference in
these bounds is an opaque actual reference, not a fixed-width bit
word. A bit account must additionally sum the actual widths of
each initialized, read, written, retained or emitted reference
occurrence, including event copies and allocator state, together
with finite tags/control/rights and code. These widths grow with
the actual finite allocation history. Likewise the specified
constructor output is $n'+2$ tokens, not an output of every address
spelling or of $J'_\iota$. If full addresses, a decoded state or
another view are separately serialized/delivered, their actual
input, working and output operations are additional coordinates.
In particular separately spelling every receiver word can involve
$\sum_p|p|$ letters although building the shared snoc backing and
emitting the constructor stream obey (OA.23). Nothing here prices
such an additional service as free or proves a linear bit cost.

## 16. A strict comparison with the published word-walk execution

**Theorem 16.1 (complete-service depth separation on common inputs).**
Define the finite all-alpha right combs
$c_0=\alpha$, $c_{m+1}=\langle\alpha,c_m\rangle$ and take the
actual seed $u=c_m$, with no restriction on $m\ge0$. Compare the
complete Boot services of $\omega$ and $\iota$ on their actual
common logical entrance $x_m=j(c_m)$. They implement exactly
Definition 14.1's Boot contract. Its actual entrance size and
old-leaf depth sum are

$$
n_m=2m+5,\qquad
d_m=\frac{m^2+5m+10}{2}.
\tag{OA.26}
$$

For each of rows/events, bounded field operations and total newly
allocated bounded-arity cells, the published $\omega$ execution
has order $\Theta(n_m+d_m)=\Theta(m^2+1)$, whereas the entire
$\iota$ service has order $\Theta(n_m)=\Theta(m+1)$.
Consequently the old/new ratio in each of these three coordinates
tends to infinity. In particular the new complete service has
strictly smaller cost in each of these coordinates for all
sufficiently deep members of this same input family.

The same separation holds for their immediate first Update after
these Boot returns, measured per Update service: the logical
entrance is again $x_m$, the actual source is $E(x_m)$ and its
actual entrance size is $N(E(x_m))=4m+11$. Every finite $m$ and
both services remain within the admitted domain. The finite run
from input installation through that Update still has the same
linear versus quadratic orders in the stated coordinates.

Proof. The comb has $m$ branches and $m+1$ leaves. The familiar
comb-depth identity, also used in [SLHC §13][SLHC12], is a counting
ingredient, not the lower-bound interface here. Its depth sum
$e_m$ satisfies $e_0=0$ and
$e_{m+1}=e_m+(m+1)+1$, since all old leaves move down once and
the new left leaf has depth one. Thus $e_m=m(m+3)/2$.
In $j(c_m)$ the two $a_0$ leaves have depth two, and all $m+1$
seed leaves gain one edge. Therefore
$d_m=e_m+4+(m+1)$, and the node count gives (OA.26), including
the terminal case $m=0$.

For this exact published $\omega$ execution, Theorem 7.1 counts
exactly $d_m$ actuator forward-word births and exactly $d_m$
root-walk source follows in Boot, besides every other service
operation. Each follow is a row with its event and a field read.
Hence rows, events, field operations and total cells each have
the lower bound $d_m$. The complete upper bounds in Theorem 7.1,
including guard/output/cleanup and event coeffects, give
$O(n_m+d_m)$ in all three coordinates. For cells, add the
displayed linear births, the $d_m$ forward cells and one event
cell per row. These facts prove the asserted quadratic orders;
no lower bound from a different literal-query interface is used.

Theorem 15.1 bounds all three new coordinates by an absolute
constant times $n_m+1$, since Boot's $s=n_m$. The $n_m$
classification probes/packet births already give their linear
lower bounds. In particular for any one of the three coordinate
constants $K$, its old/new ratio is at least
$d_m/(K(n_m+1))$, which tends to infinity by (OA.26).
Taking the maximum of the three finite thresholds proves the
simultaneous eventual strict inequality. This includes the wider
new sites, fresh operand associations and all their added work;
it does not compare only the removed walk.

Immediately after Boot both logical tables are $\mathsf A(x_m)$
and both actual source values are $E(x_m)$. Here $x_m$ has
$m+3$ alpha leaves and $m+2$ branches, so its encoded source
size is $3(m+3)+(m+2)=4m+11$.
Thus the actual Update entrance size is $4m+11$.
The leaf addresses processed by Update are still those of the
old logical $x_m$, hence their sum is the same $d_m$. Theorem
7.1 again gives the exact $d_m$ walk/birth coordinates for
$\omega$ and its complete quadratic upper bound. Theorem 15.1
gives linear bounds for $\iota$ in this actual entrance size,
with the linear probe/birth lower bounds as before. Installation,
known preparation, the one command bit and both services add
only the terms in Theorems 7.2 and 15.2, establishing the final
finite-run assertion. $\square$

**Definition 16.2 (comparison boundary).** The comparison concerns
the specified $\omega$ word-walk implementation and $\iota$'s
specified same logical service, with their common primitive field
basis and separately retained complete records. Scan was already
linear and has no asserted asymptotic strict gain here. The new
site cells are wider, there are new field checks and more bank
material, so no every-coordinate dominance is asserted. There is
no lower bound for every implementation of Definition 14.1:
the incoming-location method is known, and Definition 7.4 expressly
identified held-parent use as a different operand-use problem.
Nor is there a bit/physical-cost separation, a total-cost optimum,
an initial-size-only continuing bound or a bounded-memory claim.

## 17. Returned expressions, correspondence and the remaining scope

**Definition 17.1 (independent meanings in $\iota$).** On the actual
returned domain $h=(u,w)\in\mathcal T\times\Lambda^{<\omega}$,
select the following projections of $J_\iota(h)$ independently:

| Expression | Actual selected content |
| --- | --- |
| $S_\iota$ | Ordered unlabelled support of the active source reachable from $\pi$, with no service backing. |
| $B_\iota$ | Uncoloured terminal-address antichain of that source, with no records. |
| $M_\iota$ | Extensional addressed contents of the current receiver table and fixed live binding/right $(o,\pi)$, excluding sites, names, archives and entry/event references. |
| $T_\iota$ | Ordered actual bounded events from observer entrance through this Return, including actual operands, acquired values and references, both installations and all subsequent operations. |

Thus space describes occurrence geometry, boundary its exposed
terminals, memory the presently acquired logical table with its
actual current binding, and time the order of actual operations.
They are not defined as inverse encodings or as four copies of
history. The full retained backing is larger than selected memory.

**Theorem 17.2 (credited returned recovery for the new execution).**
For each separate $V\in\{S_\iota,B_\iota,M_\iota,T_\iota\}$,
and all attained returned histories $h,h'$, one has

$$
V(h)=V(h')\quad\Longleftrightarrow\quad h=h'
 \quad\Longleftrightarrow\quad h\sim_{Q_\iota}h'.
\tag{OA.27}
$$

Each has a finite descriptive decoder to the same complete
$J_\iota(h)$ and every finite response (OA.22). The twelve induced
view maps on attained images have inverse opposite routes, agree
under composition and commute with every completed command action.
Every route gives the same legality, records, output and full new
successors for all finite continuations from those returned cuts.
These recovery/route facts reuse the ancestry, parsing and replay
methods of §5 and ER §§9, 22; their required new-runtime source,
receipt, return and deterministic-execution premises are Theorems
13.2–13.3, rather than an identification of the two row runtimes.

Proof. Write $x=F_w(j(u))$. Theorem 13.3 proves that the actual
source is $E x$ and the actual table is $\mathsf A(x)$ in this
execution. For space, the existing erased-$E$ support decoder
and ER Theorems 9.3/9.5/9.8 recover $x$ and then the unique
$(u,w)$ on their stated ancestry-antichain domain. For boundary,
finite prefix closure is precisely the ordered support, since
the active source is a full finite binary occurrence tree.
Applying that same decoder gives $(u,w)$ from this separate
observation. Neither projection has received a site or record.

For memory, its actual addressed rows reconstruct their labelled
logical $x$. The same ancestry supplier gives $(u,w)$; the binding
and current right are the fixed actual $(o,\pi)$. Theorem 13.2's
fresh online correspondence is needed to equate this table with
the present source, including Update's no-refresh successor.
For time, filter actual Boot Arrival events through its first
Return. Their one-token constructors are exactly the preorder of
$j(u)$ by Theorem 13.2; parse and strip the known wrapper to
obtain $u$. Parse subsequent actual Supply events by $0,10,11$.
At an attained Return they specify precisely $w$, since Theorem
13.3 proves that only one completed service per command returns.
Extra site/binding reads, installations and clears are genuine
events, but supply neither an extra input nor an ambiguity in
these two filters. Thus every individual observation determines
the same history.

Given that finite history, construct the canonical installed
source and execute the new row scheme descriptively to its
$|w|+1$-st Return. Theorem 13.3 proves finiteness and equality
with the actual *new* complete state, including both banks,
site payloads and all actual event/coeffect references. Conversely
equal histories give equal canonical executions and views. Equal
$Q_\iota$ profiles give equal empty-experiment current tables;
ancestry then gives equal histories. Equal histories give equal
complete states and all finite profiles by deterministic action
induction. This proves both kernel inclusions for each view in
(OA.27), not just one implication from a common latent parameter.

For clarity let $d_V(V(h))=h$ be the separate decoder just proved
and $R_{VW}=W\circ d_V$ on attained images. Each identity
$d_V\circ V=\mathrm{id}$ gives the two route identities in
(OA.6). Theorem 13.3 gives the actual completed command
$h=(u,w)\mapsto(u,wa)$, so those identities also give the
dynamics equation in (OA.6), now entirely within $\iota$.
For a finer finite continuation, all routes reconstruct the same
complete $J_\iota$; induct on its actions, using the precise row
legality and complete successor of Definition 14.3. Unsupported
actions execute nothing and supported actions produce the same
new response on every route. This is the credited deterministic
replay argument with its matching-start premise established here.
The algorithms consume finite descriptions and do not install a
converter port or revive a historical capability. $\square$

**Definition 17.3 (suppliers, new conjunction and exact boundary).**
The new mathematical content is Theorems 13.2, 14.2, 15.1–15.2
and 16.1's source-specific conjunction: actual online acquisition
of the incoming-field/receiver-content association, continued
authorized use under fieldwise protection, all-finite service and
prefix correctness, complete paid bounds, and a strict comparison
to the published OA execution on a common logical task. It is a
repo-derived synthesis with ordinary proofs. The following
components retain their existing ownership and conditions:

| Supplier | Reused component and correspondence boundary |
| --- | --- |
| Huet, [*The Zipper*, §§1.1–1.3, 2.2][HUET] | A location as an incoming arc, local modification and binary focus/context operations are literature-attested. The variadic upward operation need not be constant-time; the binary specialization is local. Neither form acquires this unknown mutable source or establishes the new operand/site/right relation. |
| Reynolds, [*Separation Logic*, §4, Frame Rule][REYNOLDS] | Field-level local reasoning requires disjoint storage and no modification of variables free in the frame. Here different child fields of one shared parent are distinct locations, and immutable site payloads fix the frame parameters; the whole parent need not be stable. |
| ER Definitions 20.2–20.5 and Theorem 21.1 | Actual received-shape pending parent/side slots and actual body-derived operands are positive supply. They fill receiver shape fields after stationary delivery/materialization and use their separately priced Bind/Edit schedule. They are not this online source incoming-field acquisition or its complete bill. |
| OA §§1–5, 7.1–7.4 | Unknown installation, one actual owner, fresh token/operand/table contracts, framed literal edits and the held-parent lead are prior supply. The new site-use theorem discharges the different operand-use proof required by OA7.4; it does not count the lead or online actuation itself as new. |
| [NativeFullSourceProducer][PROD], private `traverse`, `production_reads`, `stationary`, and [owning Scribe][PRODB] | Source-blind actual preorder acquisition and receipt-built constructions are reused traversal methods. Its source stays stationary; Theorem 13.2 instead supplies protection through online writes. |
| [NativeBoundedPreorderRows][ROWS], private `pending_next`, `pending_left`, `cursor_frontier`, `actual_cursor_residual`, and [owning Scribe][ROWSB] | Exact path/frontier and attained-prefix laws supply the ordinary traversal organization under their own certified epoch/trial premises. They do not replace the new correspondence of actual parent fields, receiver words and edited source. |
| [NativeSerialMachine][SER8], `replay_deterministic`, `reached_prefix_replay`, `actual_register_execution`, and [owning Scribe][SER8B] | Matching-start finite execution/replay is reused mathematics. Its literal-query/global-update operations differ; no lowering of $\iota$ to that machine is asserted. |
| ER Theorems 9.3/9.5/9.8 and OA §5 | Ancestry antichains, erased-source decoding, full-preorder parsing and returned route/dynamics algebra remain credited reuse. Theorem 17.2 checks their new execution premises, without promoting them to new ancestry or kernel results. |
| [TMC §24][TMC12] and [Structural Storage Atlas §5][SSA12] | Semantic fixed-epoch navigation and actual parent-endpoint storage give other scoped positive location results. TMC's semantic cursor does not issue references/rights; the Atlas explicitly has actual reciprocal parent slots and atomic patch premises. Neither is treated as absent supply or as the present downward-only occurrence/online service. |
| [SLHC §13][SLHC12] | Comb depth sums and its literal-query theorems remain supplied. The lower counts in Theorem 16.1 come from OA7.1's exact executed walks, not from transferring SLHC's different interface lower bound. |
| [Paid View Conversion §§5–7][PVC8] | Acquired serialized view inputs and actual paid callable conversion already exist in its enlarged runtime with its own installation/authority/return premises. The descriptive returned decoders here do not subsume or invalidate that positive service. |

The two source leaves and pairing, finite observation/control and
local owned replacement remain the content generators of this
model. A word describes where the receiver's row belongs; its
site retains the actual incoming field obtained during descent;
the received label selects what local template to construct; the
owner's static authority determines whether it may act. These
are different roles. Equal constructor contents cannot select
between different actual occurrences, and an incoming field alone
does not supply an unread label or an ownership grant. The
retained association joins the roles without a second root walk.
This explains its task-relative use, not universal minimality of
these cell types or of alpha/beta generation.

Every finite seed, every finite U/L/R word and all their finite
installation/service/return prefixes are in the proved operational
domain. The independent four-view inverse domain is only attained
returns. No arbitrary-interior inverse, arbitrary-view callable
conversion, old-full-$Q$ equivalence or transfer of OA §§8–11's
exact raw-time/joint microcut fibres is claimed. Different row
opcodes, bank installation and site/reference records require new
fibre analysis for those latter questions. Broader interference,
revocation, sharing, arbitrary allocation/layout and ownership
domains require separate hypotheses and proofs. All earlier
fixed-$G_{gc}$, original-$Q$, parked-consumer and initialization
obligations keep their exact statements. The sustained common-
relation/four-expression objective and its remaining operational
and interior-recovery obligations are not completed by this
finite-service resource refinement.

[TMC12]: RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md
[SSA12]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md
[SLHC12]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT_CONTINUATION.md

## 追加锚（本行以下为增补区）

## 18. A bounded late-attachment model and an independently named old cut

**Definition 18.1 (original target and entry interval).** Fix the
original runtime $\iota$ of §§12–17, including its precise row expansion,
lexical scratch convention, canonical typed allocators, orientation,
exclusive static owner $o$ and source port $\pi$. Quantify over every
finite $u\in\mathcal T$, every nonempty completed command word
$w\in\Lambda^{<\omega}$, and every row cut in the following interval.
Start immediately after the canonical unknown-source installation of
Assumption 1.2. The source-node names are its preorder names starting
at zero, all its tag/child fields and the root attachment are initialized,
the original event/input/output words are empty, the chronological tail
is null. All other original typed allocators, including events, start
at zero; the not-yet-constructed bank/work roots are null, and control
is at the first original local-installation instruction with its
prescribed empty finite latches. The source-node allocator starts at
$N(u)$. Execute the two original banks, known-source
preparation, Boot, and then precisely the commands $w$, under
Definitions 12.2–12.5 and 4.1. Write $C_k=C_k(u,w)$ for the complete
original state after $k$ executing original rows of this finite run.
An original Supply row counts as a row. Disabled attempts are omitted.

Let $a_w$ be the index immediately after the last bit of the last command
code, $b_w$ immediately after that command's Begin, $e_w$ immediately
after its End, and $r_w$ immediately after its Return. The entry domain is

$$
\mathcal D=\{(u,w,n):u\in\mathcal T,\quad
 w\ne\epsilon,\quad a_w\le n<b_w\}.
\tag{OA.28}
$$

The target is the already specified $C_n$, including the original source
and detached material, all allocations and partially linked backing,
all banks/latches, saved references, inputs, outputs, events, allocators
and original rights. It is defined by this original execution, before
introducing a recovery program. $J_\iota(u,v)$ keeps its returned-only
meaning; $C_n$ is not a new use of that notation.

The interval includes every attained Update/Scan row cut after its
complete code and before Begin. For $10$ and $11$ it also includes the
prescribed detached-$A$/wrapper preparation, partial links and port
publication preceding Scan entry. At such a cut the command has selected
the prospective Scan, even if no new service descriptor exists yet.
The incomplete two-bit command at Tail, Boot, an already emitted Begin,
and cuts inside an indivisible row are outside $\mathcal D$.
Membership in $\mathcal D$ is a mathematical premise. No membership,
mode, old-command, old-ordinal or old-state recognition port is supplied.

**Definition 18.2 (the distinct model $\chi\iota$).** Before choosing
$u,w,n$, fix the same owner and source port, one auxiliary request port,
one auxiliary output port, auxiliary cell types and a finite program
specified below. Auxiliary types have separate canonical allocators,
initially empty. Original non-event allocators keep their original
namespaces. There is **one shared chronological event type and tail**.
Its fixed finite tagged union contains the original event format
literally, an original-row format with the bounded observer coeffects,
and an auxiliary-row format. Pre-Attach events keep their original
payload and initialized fields; no field is retroactively added or
backfilled. Every executing original or auxiliary row appends one
event, using the next name of that shared type. Its bounded record includes its opcode,
predecessor, actual operands/values and bounded field/slot coeffects;
recording does not initiate another instrumented row.

The following are declared interface additions, not old $\iota$ actions.

1. At an original row boundary, the fixed owner may execute Attach once.
   It changes a dormant finite attachment flag to bootstrap, initializes
   a bounded tick latch to empty, a bounded optional-token latch to empty,
   a finite receiver phase to AwaitBegin and a finite bootstrap PC.
   No source field, original bank, saved scratch, descriptor, original
   non-event allocator or original control is assigned. The Attach event
   has the actual old global tail as predecessor. Attach returns only
   its fixed acknowledgement. It neither reads old events nor supplies
   their number, and performs no unbounded installation.
2. After installation, an executing original action, whether Advance or
   Supply, has the additional synchronous coeffect setting the tick latch
   to pending and copying its **one newly emitted token**, if any, into
   the optional-token latch. The original row emits at most one token.
   Old outputs are not copied. These latches must both be empty before
   another original action. Auxiliary rows do not trigger this coeffect.
   Its event includes these bounded assignments. A disabled original
   action has no row, tick, token, event or successor.
3. Auxiliary operations are individual owned field reads, null/finite-tag/
   reference tests, assignments, one bounded-cell birth, one-bit input,
   one-token output and finite control edges. Their expansion is the
   one-row-per-operation convention of Definition 12.3. A returned value
   and the bounded successor PC may be retained as coeffects. There is
   no subtree, string, numeric, copy, historical-read or Call operation.
   Fixed owner authority covers these fresh arenas and ports. Original
   source authority remains with this same owner throughout.

The successful-original-row latch can equivalently be implemented by the
finite continuation of the owner's invoking instruction: it records one
completed invocation, not a source-state answer. The new output coeffect
is a bounded future receiver, not (OA.22)'s mathematical complete-successor
coordinate. The observer never receives that coordinate. The source's
ordinary constructor stream and the auxiliary DATA stream have distinct
finite channel tags; publishing DATA does not feed it back as source
output. Only the single serial controller invokes source actions.
Arbitrary external interference, revocation and concurrent invocations
are excluded, as in Definition 12.1.

**Definition 18.3 (actual finite installation and local word routines).**
The irreducible addition is the finite Attach/bootstrap mechanism just
declared. It installs the one fixed controller $P$ of §§18–21. Expand
sequence, finite alternatives and while tests into individual rows;
replace recursive tree traversals by allocated stacks. Assign instruction
labels in textual routine order and then textual row order. Inline
fixed subroutines with fresh temporary register roles; calls form the
finite acyclic macro hierarchy below. Let $m$ be the number of distinct
register roles in this expansion. Install one auxiliary holder and its
$m$ one-reference slots in that order, all null. Finite tags and latch
bits are installed separately, one bit per row. Encode the expanded
finite instruction table as a list of tuples of unary instruction
labels, finite opcode/field identifiers and successor labels, with
$U(j)=1^j0$. Its bit length $K$ is the length of this specified expansion,
not a source-dependent input.

The bootstrap walks the fixed literal table in its finite control:
for each bit, birth a code cell $(\mathsf{bit},\mathsf{next}=\mathsf{null})$,
test the former code tail for null, assign either code head or its next
field, and assign code tail. A final seal edge enables the installed
table. Every field initialization, slot link, branch test and seal is
charged. The finite dispatcher selects its installed rule; this is the
finite control mechanism, not dynamic unbounded code fetch. During this
installation the original control is paused. At every prefix the code
list and slot list consist exactly of the items already constructed,
with their actual null or linked fields; the uninstalled suffix is not
read. The fixed table contains no unknown seed or target data.

In addition to code, holder and slot cells, auxiliary storage uses
bit cells $(\mathsf{bit},\mathsf{next})$, mark cells
$(1,\mathsf{next})$, and work cells
$(\mathsf{tag},\mathsf{first},\mathsf{second},\mathsf{next})$.
These are different typed namespaces, starting at zero at Attach.
All are retained after popping or clearing. A word is a linked finite
bit list with null terminator; a natural in computation is a mark list.
A tuple/list is encoded by the finite grammar
$0$ for nil and $1\,U(|x|)\,x\,s$ for an item $x$ followed by list $s$.
Finite tags have fixed-width binary codes. Data copying never aliases a
mutable construction frontier with a sealed input.

The local macros have the following literal bounded-operation expansions.
Cons births a bit cell and assigns the destination slot. Pop tests null,
reads bit and next separately, and assigns its cursor. Copy consumes a
cursor, conses each read bit to a reverse word, then reverses that word
by the same pop/cons loop. Cat reverses a copied first word and conses
its bits onto a copy of the second. Length consumes a copied word and
conses one mark per bit. CopyMarks follows a mark cursor by individual
next reads and conses fresh mark cells, obtaining a distinct list of the
same length; cancelling marks uses separate next reads and cursor
assignments. Encoding such a natural emits one 1 per followed mark
and then one 0. Equal consumes two copied cursors, comparing
each pair of read bits, and tests simultaneous exhaustion. ReadUnary
consumes leading ones into marks and requires the terminating zero.
Take consumes one input bit and one mark per iteration, then reverses
its accumulated bits. ReadFrame is ReadUnary followed by Take. A list
scan reads its tag and ReadFrame, consumes that item, and continues at
its retained suffix until the nil tag. Nth counts down acquired marks
while scanning; Replace and AppendItem rebuild a new list, copying
unselected items. EmitWord tests its cursor, reads bit and next, emits
that bit, assigns the cursor and repeats, with explicit outer Begin/End
and acknowledgement edges. Each mentioned read/test/assignment/edge is
a row; no macro name is a primitive.

Tuples, lookup tables, stacks, predecessor references and simulated
heaps are consequently finite words operated on by these macros.
All counters and variable addresses are backed lists, not latches.
The number $m$ and the table length $K$ are fixed finite syntactic
quantities; workspace, retained versions and runtime are not bounded
by them. This uses RCA §12.1's already supplied word-program methods,
with linked cells in place of RCA's tape banks. It does not import
RCA's 32–40 port layout or its Ready-only installation permission.

## 19. The source-specific shared chronology

**Definition 19.1 (the correspondence, including entry-reference phases).**
Compare the original continuation of $C_n$ with the one live source after
Attach. Match rows by their **original** action order, ignoring intervening
auxiliary rows for this matching only. Keep equality of original control,
finite mode/parser/command latches, source/port fields, all original
non-event cells, their identities and allocator positions, banks and
input/output, with the following explicitly tracked chronology components.

The actual global event chain is the old prefix followed by *all* new
original and auxiliary events in their executed order. Each new event
has its actual predecessor and actual fields, including the coeffects
of Definition 18.2. Its allocator is the length of that global chain.
The original comparison chain has only original rows. Neither chain
is asserted equal to the other after Attach.

A source entry capture reads the then current global tail. During the
lexical lifetime from that read until the descriptor's entry initialization,
the actual saved-entry scratch contains precisely this captured reference,
even when more events have since been appended. The new descriptor.entry
is initialized to that saved value and never retargeted to the later tail.
After its lexical last use the ordinary clear/reuse rule applies to the
scratch. This is a role/lifetime assertion, not a fixed numbered scratch
slot. If the capture occurred before Attach, its original saved value
survives Attach and the installation unchanged. If the descriptor was
already born, its original entry stays unchanged. If neither occurred,
the later capture may name an auxiliary event. Every shared event remains allocated and immutable, including an
auxiliary event subsequently captured by source entry. Thus these
saved copies have live retained targets for their whole lexical or
descriptor lifetime. Old descriptors keep their
own actual entry values; descriptor.previous, table endpoints and sites
keep their ordinary non-event references. Every source event stores the
actual values of these fields when its row reads or writes them.

The comparison allows these specified saved-entry and descriptor.entry
values to differ between runs, and allows the specified event/tail/
event-allocator components to differ. No other original field is erased.
In particular partial operand/invocation fields, staging null links,
actual sites, completion references, descriptor states and all original
bank contents outside a live saved-entry role must agree. A global
tail, a list/table tail and the command-control state Tail are three
different objects.

**Lemma 19.2 (exhaustive operational noninterference).** In $\mathcal D$,
after installation and after every finite interleaving prescribed below,
the correspondence of Definition 19.1 holds. Every next original
requirement has the same result, the same original row executes, and
the same original token is emitted as in the original continuation.
The original non-event source and backing agree at every matched
partial cut. All chronology components have the actual values of
Definition 19.1. This remains true through Return and any later finite
commands supplied through the installed controller.

Proof. Before Attach the original components are exactly $C_n$.
Attach/installation/local rows write only auxiliary fields and the
shared event system. Their record appends determine a new real tail,
not a source write. They leave any existing saved-entry reference
untouched. This proves the local-row case, including partial installation.

For the original-row case it is necessary to inspect the operands in
the owning rules, rather than infer the conclusion from disjoint heaps.
Here is their complete partition.

* The command rules test Ready/Tail and supplied bits. Known preparation
  and grafts read the held port/root and their fresh staging fields,
  initialize literal source nodes, test null links and write the specified
  port. None tests an event reference or an entry field.
* Entry reads the chronological tail once, into the saved-entry role.
  The subsequent holding/linking of the previous descriptor, port capture,
  endpoint clears, new descriptor birth and root-stack pushes use the
  operands of Definition 12.4. Only descriptor.entry receives that saved
  reference. Descriptor.previous receives a descriptor reference, not the
  tail. The old descriptor's table contents are not read.
* Work-head tests, four-field site pops, receiver pops, incoming-field
  reads/equalities and source follows use exactly the sites, source nodes,
  words and frames of Definitions 12.2/12.4. Packet Offer/Take/Arrival/
  Acknowledge and the finite parser use only their mailbox, packet cells
  and finite tags. Receiver row/word construction and paired pushes use
  their actual newly obtained payloads. Table/list tails here are
  non-event endpoints. None is the global chronological tail.
* At an editing leaf, Definition 12.5 reads the operand, immutable site,
  actual focus, descriptor.owner/port and the indicated holder field.
  It tests the static binding, node/side and attachment equalities.
  Its guard follows the fixed literal tile paths and tests their actual
  tags/children. Target births, vacancy checks, links, invocation.old/new,
  the one attachment Publish and completion append use those same
  non-event operands. No field of an event or descriptor.entry is an
  operand of a guard, a site, a label selection or a publication.
* NodeDone and service/Return cleanup assign the listed slots/latches
  and clear masks. A scratch role ceases to carry an entry reference
  precisely at its stated last use/clear; later scratch users get their
  ordinary newly assigned values. End assigns actual table endpoints,
  descriptor states and the old descriptor's retirement state.
  Output reads only current row word/label/next fields, prints the
  prescribed tokens and finishes its fixed cleanup/Return. The source
  never rereads an old output archive or event payload.

This covers installation/preparation, every service instruction and
its finite tests, every output/cleanup row, and both Supply controls
in Definitions 1.3, 2.1–2.3, 4.1 and 12.2–12.5. In particular a saved
entry is not used as a source pointer, and fixed owner/port checks do
not inspect it. Equality of the other operands proves equal branch
results, read values, allocations and non-event updates row by row.
At an entry-tail read, instead apply the explicit live-tail rule:
both reads succeed, and each saves its own actual tail. At descriptor
birth each copies its own still-live saved value. This proves the
entry-reference phases even if Attach occurred between the two rows.

Finally append the actual event, with the actual pre-append predecessor,
actual values, initialization and bounded coeffects, and assign the
actual global tail. The next global name is the next event allocation;
source non-event allocations are unaffected by auxiliary types. This
establishes the complete event clause without identifying the two
event chains. Instrumentation cannot recurse. The extra tick/token
coeffect reads only the newly emitted finite token, and no original
guard reads its auxiliary destination. Induction over the interleaving
proves the assertion at every partial cut. The same operand partition
applies to later commands, so the proof does not stop at the first Return.
This is source-specific operational correspondence, not full-state
equality obtained by deleting a disjoint heap. $\square$

**Corollary 19.3 (the first frame belongs to the same source).** From
$(u,w,n)\in\mathcal D$, pause for finite installation, then repeatedly
invoke the next original Advance with finite receiver work between
invocations. The first source Begin after Attach is the Begin at matched
original index $b_w$, its constructor body is precisely the preorder
of $t=F_w(j(u))$, its End is at $e_w$, and the fixed subsequent cleanup
reaches the matched Return $r_w$ and actual Ready. There is no Supply
between Attach and that Return.

Proof. Theorem 13.3 supplies this original finite continuation, including
graft preparation when selected. Lemma 19.2 preserves each of its row
choices and outputs. By (OA.28) no earlier Begin remains between $n$
and $b_w$. Definition 4.1 prints exactly that service's current table.
After End, its ordinary row-list tail is exhausted; the remaining
bank-order clears, descriptor-state assignment and Return constitute
one fixed finite non-Boot row list. Its length $c=r_w-e_w$ is the
syntactic length of that expanded cleanup, not a received old ordinal.
Following those $c$ Advances is lawful and ends at Ready.
The sixteen additional clears are included. $\square$

## 20. Actual first-frame acquisition and exact old-state construction

**Definition 20.1 (driver, received partial states and the stopping
distance).** When no tick/token is pending, installation is complete,
and the source is in the initial running phase, invoke its next Advance.
Its synchronous coeffect precedes any further invocation. To discharge
one pending tick, test pending, birth a mark pointing to tally head,
assign tally head to that mark, then clear pending. The three-row
birth/assign/clear body has its separate head test and control edges.
This immutable tally counts *all executing original actions since
Attach*, not auxiliary rows. A partly completed increment has its old
head, fresh initialized mark and finite subphase; it is never used as
a completed tally. No next original action is admitted in that subphase.

Next test optional-token availability. If present, read its finite
value and run the following finite dispatch, then clear availability.
A token being appended has an initialized new cell, its old list
endpoints and its explicit link/head/tail subphase. Advance is barred
until that append and acknowledgement finish.

In AwaitBegin, the first received Begin saves the completed tally head
as $D$, initializes the constructor list empty and changes to Body.
In Body each received $\alpha,\beta,\mathsf b$ is actually appended
to that list; End changes to Closed. No other token is accepted on
these phases. After Closed the first-frame list and $D$ are immutable.
All later source tokens are read and acknowledged in Drain and do not
reset either object. Absent tokens require no fabricated Arrival.
The source's own Offer/Take/Arrival/Acknowledge mailbox of Definition 2.1
is a different internal channel; auxiliary reception observes only the
source's public Begin/body/End emissions.

For clarity the entire partial-receipt invariant is: (i) a pending
tick names exactly the last unmatched executing source invocation;
(ii) outside increment, the completed tally has one mark per discharged
invocation, and inside increment its fresh mark has exactly that old
head as next; (iii) the optional-token latch is the one still unacknowledged
emission of that invocation or empty; (iv) the committed first-frame
list is exactly the already appended constructor prefix following the
first Begin, with at most its one read-but-not-yet-linked token; (v) $D$
is absent before that Begin and afterwards is the immutable completed
tally of its invocation; (vi) no parsing, historical record availability
or source-ready claim is made from an unfinished list.

At Closed, discharge/acknowledge completely, set Drain, and execute
the $c$ cleanup Advances of Corollary 19.3, with these same per-invocation
discharges. The resulting source is actually Ready; the global event
tail has continued to change during receiver work. Keep it paused
while constructing and publishing the record.

**Definition 20.2 (finite parsing, ancestry and original-row simulation).**
Parse the *received* closed constructor list by a work stack of destination
sockets in fresh word/tree data, initially its root socket. For each
token, pop a socket, create the indicated tag with null children, fill
that socket, and for a branch push its right then left child sockets.
Require a nonempty stack before each token and an empty stack at
exhaustion. Each push/pop/read/birth/link is expanded separately.
This is the usual full binary preorder parser, now on received cells.

On the resulting finite $t$, use ER's actual ancestry algorithm, with
this explicit syntax implementation. The image grammar for $\rho$ is:
$\beta$ decodes to $\alpha$; $\langle\beta,\alpha\rangle$ decodes to
$\beta$; a pair whose children both decode decodes to the pair of their
decodings; $\alpha$ fails. The exceptional pair is disjoint from the
pair-of-images case since $\alpha$ is not an image. Evaluate this
bottom-up with a traversal stack. To take a compound $U$ predecessor
require both children in that grammar. To take $L$ require left child
$\alpha$ and compound right child, and symmetrically for $R$.
Before each predecessor test, test membership in $j[\mathcal T]$ by
its fixed left child $a_0$; if true, retain the right child as $u$.
Otherwise take the unique available predecessor and prepend its label
to a word register. No predecessor yields Invalid. These are finite
tree traversals, Equal, list construction and finite dispatch. ER
Theorems 9.3/9.5 prove uniqueness, the attained stopping point and
termination by the strictly decreasing positive measure
$\nu(x)=2A(x)+3B(x)$. Thus this is credited ancestry, not a new inverse
or an ancestry oracle.

The original simulator represents a complete original state by:
finite control/latch fields; one list per original cell type in canonical
allocation order; every cell's full field tuple and initialized status;
root/bank/input/output roots; next-allocation counters; event list and
tail; and the original static binding/rights. A null reference, an
uninitialized field, a finite value and a typed ordinal reference have
different tags. An ordinal is DATA encoded by $U(j)$, not an actual
reference. Initial construction uses the recovered tree $u$: allocate
its represented nodes in preorder with the actual canonical initial
tag/child/root fields, empty original chronology and the original initial
typed counters. Do not insert any auxiliary cell, Attach event or
observer code into this represented original state.

For one simulated original row, keep its sealed pre-row word in a
separate slot and build a fresh working version. Fetch old operands
from that saved word before assigning their replacements; retain new
values in separate finite register roles. The completed state/input
cursor and row tally are committed only after the working word and
its event are complete. Select the finite original PC rule.
Read its indicated represented field by typed-list Nth and tuple Nth.
Perform its finite null/tag/reference test. Replace the indicated field
or initialize the next canonical bounded cell and increment that type's
mark counter. Keep every other item. For input use the next bit of the
recovered $0,10,11$ encoding of $w$, only at its represented Ready/Tail.
For output append only the finite emitted token to represented Out.
Apply exactly the stated bounded bank/latch coeffects and then append
the original event with its pre-row tail, operands, values, initialization
and tail coeffects. Advance represented PC. Event self-references use
the next represented event ordinal; they do not embed the event value
recursively. The finite rule cases are the field/read/follow, birth,
assignment, finite test, input/output and control rules of Definition
12.3, including the lexical temporary allocation/clear convention.
This specifies a finite Step program using Nth/Replace/AppendItem,
not an atomic virtual instruction or a full-state response from the
live source.

Run that simulator from initialization with a mark tally until it executes
the last command's Begin: all bits of $w$ have then been consumed, and the
next Begin following their exhaustion is the selected one. Earlier Boot
or command Begins do not pass this test. Let its computed tally be $B$.
Cancel copied marks of $D$ against copied marks of $B$; the remaining
marks are $N$. Restart the original simulator and execute exactly $N$
Step iterations, consuming one copied mark per iteration. Serialize
this complete resulting state with the tuple/list codec, retaining also
the computed binding $(o,\pi,u,w,N)$. Loops never scan their own growing
destination; loop stacks and countdowns are ordinary retained cells.

**Theorem 20.3 (acquisition of the independently specified $C_n$).**
For every $(u,w,n)\in\mathcal D$, the installed program has a finite
actual execution constructing a sealed finite record $R$ such that

$$
\operatorname{decode}(R).\mathsf{state}=C_n(u,w),
\qquad |D|=b_w-n,\quad |B|=b_w,\quad |N|=n.
\tag{OA.29}
$$

It starts with no source-dependent observer data and reads neither
old archives, old event payloads, old references as ordinals, nor an
old complete-state response. All received data are the actual first
future public frame and actual successful invocations.

Proof. Installation is finite and source-independent. At each source
invocation the tick is set once, the mark block executes once, and
original dispatch is barred until it finishes. Local events do not
set that tick. Induction proves the tally and all partial-state clauses
of Definition 20.1, including a cut between birth and head assignment.
For token receipt the synchronous copy is exactly the newly emitted
token. Acknowledgement precedes the next source action. Induction on
append subphases proves that the committed list is the received prefix;
it supplies no not-yet-arrived constructor.

By Corollary 19.3 the first Begin has matched index $b_w$, and the
executing original actions from $n$ through its successor number
$b_w-n$. The Begin invocation's tick is discharged before $D$ is saved.
Hence $|D|=b_w-n$, including the cases immediately before Begin,
inside a guard, between site/operand operations, and during graft
preparation. Installation and receiver rows add no marks to $D$.
The first closed frame is precisely the full preorder of
$t=F_w(j(u))$. The parser's stack is its usual ordered unfilled-socket
frontier; a branch replaces its socket by left/right sockets and a
leaf closes it. Induction on the received prefix gives every partial
parser state and the actual final $t$. This is an actual finite
acquisition, not inversion conditional on an arbitrary transcript.

Apply the supplied ancestry theorem with entry antichain
$j[\mathcal T]$, constants $\alpha$ in the two grafts, and forward
left-to-right word convention $F_w$. It returns precisely this $u,w$.
No hypothesis identifies an unknown historical entry by fiat.

For simulation, prove by original-row induction that each represented
field, allocated identity, initialized/null distinction, control,
input/output and event equals the corresponding original one. A read
uses the same typed ordinal and field. A test therefore has the same
branch. A birth uses the same type's next name; its actual initialized
fields and later links are separately represented. An assignment changes
only that field. Supply consumes exactly the next recovered command bit;
the deterministic busy rows consume none. Output and clear masks are
the original ones. Finally the event uses the same pre-row predecessor
and actual represented coeffects, so its new tail and allocator agree.
This includes entry-tail capture *in the original chronology*, its
saved scratch lifetime, descriptor.entry and descriptor.previous.
It also covers a stopped partial packet, incomplete target template,
invocation.old/new and detached old tiles; no equality of extensional
source trees replaces these fields. This row induction is the specific
finite heap analogue of the credited replay method.

The original run is finite by Theorem 13.3, so the first simulation
stops exactly at $b_w$. Its own original-row tally is $B$ of length
$b_w$, regardless of the later real time spent simulating. Cancellation
therefore succeeds and gives $n$. The second finite countdown replay
stops at precisely the independently defined $C_n$. Serialization
copies that represented complete state; it neither uses the altered
live chronology as an old one nor restores its old pointers. All
macro loops consume finite words/lists or a decreasing structural
work measure. Ancestry decreases $\nu$, and both simulator outer
loops have the finite witnessed bounds just proved. Thus construction
and sealing finish in finite actual local rows. $\square$

**Lemma 20.4 (all reconstruction prefixes).** At every local row cut
of the acquisition/reconstruction, the installation and receipt clauses
of Definitions 18.3/20.1 hold. During tree parsing, completed tokens
fill exactly the corresponding left-first sockets, with the current
token's birth/link/push subphase separate from the committed frontier.
During an ancestry traversal, its work stack contains exactly the
unprocessed structural tasks and its already constructed results;
the outer command list is the reverse-removal list already prepended
into forward order. During either original simulation, if $j$ Steps
have committed, its sealed current word is exactly original $C_j$;
a pending Step has that unchanged pre-word and precisely the work
prefix prescribed by its current macro/row. A pending tally increment
is not a completed $j+1$. If $i$ pairs of marks have been cancelled,
the copied cursors have lengths $b_w-i$ and $b_w-n-i$. The second
simulation's completed-step countdown is $n-j$. During serialization
the committed record prefix is exactly the encoded prefix of its
sealed completed input, with one possible pending field/bit append;
availability remains false. All allocated intermediate cells retain
their initialized payload and actual canonical identity.

Proof. A pop consumes its recorded head and a cons points to the
pre-cons destination; the Copy/Reverse invariant is that the accumulator
is the reverse of the consumed source prefix. Cat and the framed-list
macros inherit this statement, with unconsumed suffixes saved before
new appends. Every partial list append has only its initialized new
cell, old endpoints, and named pending link/head/tail assignments.
The explicit finite subphase determines which have occurred.

The socket parser invariant follows by consuming one task per leaf
and replacing a branch task by its two ordered child tasks. Bottom-up
image parsing similarly replaces only a finished task by its computed
result. The ancestry outer step prepends precisely the last removed
label, so the removed suffix is in its original forward order.
Theorem 20.3's row induction identifies a committed Step. Before
commit, immutability of its saved pre-word and the finite macro cursor
give exactly its unfinished transformation, including an event whose
fields have not all been appended. No later Step can use that work.
The two tally/countdown loops advance only after their pending mark
operation has completed. Paired cancellation consumes one mark from
each copied cursor, giving the displayed lengths; since
$b_w-n\le b_w$, it never requires a missing $B$ mark. The serialized
input is sealed before its first output bit, so the same copy invariant
proves its partial-prefix assertion. None of these routines frees a
cell. This proves the stated clauses by induction on individual local
rows, including cuts before input retention, in a tuple replacement
and in an unsealed result. Together with Lemma 19.2 they describe
the simultaneous source and observer partial state, not just completed
abstract macro values. $\square$

## 21. Completed DATA, genuine requests and actual current use

**Definition 21.1 (retained-record and request phases).** Historical fields
have the disjoint wire type HistoricalData. In particular a historical
reference is its original type and canonical ordinal *as bits*; an old
owner/right field is a finite description. No decoding instruction
casts those bits to a live reference, changes a live allocator or executes
a permission transfer. The current source right is the original fixed
right of $o$ on $\pi$.

After Theorem 20.3's serialization, retain its actual bit-list head and
a Complete seal in a finite latch. There is exactly one target record
per Attach, so its installed request port names this completed object;
no unknown package number is required. Execute the following initial
publication: emit DATA-Begin, traverse the sealed record by actual
null tests, bit/next reads, one bit emission and cursor assignments,
emit DATA-End, execute a local acknowledgement edge, then set
RecordAvailable and RequestIdle. This publication reads the whole
completed retained record. It is not a declaration that a symbolic
value has been delivered. Owner-local read authority on that sealed
list was installed in the model. No cross-owner channel or restored
historical token is invoked.

Record-construction phases are Empty, Building, CompleteUnprinted,
Printing, AwaitAcknowledgement and Available. A partial serialization
has only its initialized prefix and its explicit link/endpoint subphase;
it is neither sealed nor available. During Printing the cursor is a
suffix of the sealed list, and emitted DATA bits are exactly its read
prefix. Before acknowledgement no request is admitted. These flags
concern the new record, not the source's descriptor state.

The driver sets its own finite SourceReady flag only after the fixed
cleanup and complete tick/token discharge. It does not read or recognize
an unknown source PC. With that flag and RequestIdle, the genuine
bounded auxiliary input is In$(b)$ for one bit $b$. Its row sets a one-bit latch and enters
InputPending; separate local read/birth/link/clear rows retain that
supplied bit before another In is possible. After processing a first
one it enters RequestUnary; each subsequent one returns to RequestUnary
after its paid mark update, and only the terminating zero enters the
answer handler. In is enabled at RequestIdle or RequestUnary, never
during InputPending or an answer. The request grammar is

$$
0\quad(\mathsf{GetRecord}),\qquad
1\,1^k0\quad(\mathsf{GetBit}(k)),\qquad k\ge0.
\tag{OA.30}
$$

The first one selects the second grammar arm; subsequent ones cons marks
onto its backed index; its terminating zero completes it. The request
bit list, possibly pending input bit, tag, unary prefix and parser phase
are all retained. No reply is produced for a proper unfinished prefix.
A user may stop there; supplying its finite remaining bits completes the
request. An original source input is disabled throughout RequestUnary
as well as the pending-input and answer phases.

For GetRecord, Copy the sealed record into a fresh answer word. For
GetBit, read the retained record head into a cursor and copy the received
index; while its mark head is nonnull, test the record cursor. A null
cursor immediately selects OutOfRange without a field read; otherwise
read its next, assign the cursor and consume one mark. At index
exhaustion test the cursor and read the indexed bit if present,
otherwise select OutOfRange. The finite tagged answer is respectively
Record with its copied word, Bit with its read bit, or OutOfRange.
Construct and seal that answer by the same tuple/word routines. Read and
print it with DATA framing, then acknowledge and restore RequestIdle.
Only then is the request counted completed. Partial answer construction,
printing and acknowledgement keep their own actual backing and cursors;
RecordAvailable and the immutable old target never change.

At RequestIdle the owner may instead supply an original source bit.
A successful Supply is a genuine original source row with the tick
coeffect and subsequent discharge of Definition 20.1. The known
Ready/Tail code state is maintained from these *actually supplied* bits:
after a first 1 it clears SourceReady, enters its known SourceTail
phase and waits for its second bit. After a complete $0,10,11$ it clears
SourceReady and drives genuine Advances. Drain has the finite subphases
WaitingBegin, InBody and Cleanup, selected by the actually received
Begin and End; constructor tokens are read/acknowledged in InBody.
Cleanup has the fixed $c$-row sequence in finite control, not an unknown
numeric argument. After its last tick/token discharge it sets SourceReady
again. No original PC read or Return-notification primitive is used.
During that source service requests are disabled. The receiver is permanently in
Drain after the original acquisition; future Begin/body/End tokens
never replace $R$ or $D$. There is no second Attach or reacquisition.

**Theorem 21.2 (installed historical use and a next real Update).**
For every member of $\mathcal D$, the procedure reaches actual source
Ready, reads and publishes a completed retained record equal to $C_n$,
and enables the request service of Definition 21.1. Every actually
supplied finite complete request has a finite completed answer and
return on that retained object. Every request prefix has the partial
state just specified and, on supplying a finite completion, terminates.
After initial publication, or after any finite number of completed
requests, the owner can actually Supply$(0)$ and complete a next Update
on the **same live source**, with current logical value $\rho t$ and
actual source $E(\rho t)$, and can then make another completed request
for the unchanged historical $C_n$.

Proof. Corollary 19.3 and the cleanup part of Definition 20.1 reach the
actual original Return control, not merely a table-equivalent state.
Every cleanup source invocation, including Return itself, has its tick
discharged and optional token acknowledged before source-ready dispatch
is enabled. The original service's own packet mailbox and work stacks
are empty by Theorem 13.2. Thus neither an original receipt nor an
auxiliary tick/arrival remains pending.

Theorem 20.3 gives the complete serialized old state. Word construction
does not write it after sealing. Induct over the actual read/output loop:
at each cursor the public bits are precisely the consumed prefix and the
unread suffix is still sealed and reachable. At exhaustion the output
is exactly $R$; the acknowledgement and availability assignment occur
after DATA-End. This proves completed publication and retained readability.

For a request prefix, induction on In, pending-latch and append subphases
gives exactly the supplied bits and marks. The grammar is prefix-free,
so completion selects exactly one handler with a genuinely acquired
finite $k$, rather than an unbounded argument supplied in one action.
Copy terminates on the finite sealed word. In the bit handler, after
$i$ successful iterations the cursor is its $i$-th suffix and the index
is $k-i$; exhaustion returns precisely the specified bit or OutOfRange.
The answer-copy/seal/print/ack induction is the publication induction
again, with actual fresh backing. A partial request waits for supplied
bits and does not assume their future arrival. This proves exactly the
stated completion-conditional prefix assertion.

All these local rows satisfy Lemma 19.2 and leave source control at
Ready and source authority with $o$. Hence Supply$(0)$ really executes
its original Update selection. Discharge its tick before the first
busy Advance. The same lemma and Theorem 13.2 give the actual Update
from $E t$ to $E(\rho t)$ and its authentic new output. Drain reads
and acknowledges every token, without changing the closed first-frame
data. The finite prescribed cleanup again returns the actual source
to Ready with no pending tick/token. The installed request port is
available again and still reads the original $R$. Induction gives
the same result for any later finite supplied command/request sequence
obeying these admission phases. Historical data equality has never been
used as a current capability. $\square$

## 22. One-run rows, fields, backing and finite bounds

**Definition 22.1 (distinct horizons and exact additive account).** Fix
one actual run in Theorem 21.2. Its first-source-return horizon $H_0$
is the cut after the first matched Return and discharge, before the
historical computation. Its first-record-return horizon $H_1$ is the
initial DATA publication acknowledgement/availability cut. A later-use
horizon $H$ follows only the source commands and requests actually
supplied, and may stop inside any of their partial phases.

Let $s(H)$ be executing original rows after Attach and $L(H)$ all
auxiliary rows, including Attach. Since no earlier auxiliary row
exists, the shared chronology length and row count are exactly

$$
\mathsf{Rows}(H)=\mathsf{Events}(H)=n+s(H)+L(H).
\tag{OA.31}
$$

At $H_0$, $s=r_w-n$; at $H_1$ it is still $r_w-n$.
For a later completed original continuation $v$ it increases by the
actual complete services and graft rows **and** the actual supplied-bit
rows $\#\mathsf U(v)+2\#\{\mathsf L,\mathsf R\}(v)$.
A partially supplied code contributes only its executed Supply rows.
Virtual original rows in either replay are auxiliary computation,
not additional real source actions.

Partition $L$ into installation, invocation accounting, source-token
receipt, parsing/ancestry, the two simulated runs, mark cancellation,
historical encoding/seal, publication, request ingress/handling/output,
and auxiliary dispatch/return work. These are disjoint actual row
occurrences, with tests and phase edges assigned to their invoking
routine. In particular, for each executing original invocation there
are the pending test, the three-row mark body, token-availability test,
any read/append/link/ack work, and dispatch/phase edges. The three-row
body alone is **not** the bookkeeping tariff. A synchronous tick/token
assignment is counted as a bounded coeffect of the source row and in
its full field-operation account, not as an unexecuted local row.
No marks are created by a disabled attempt.

Let $\mathcal R_H$ be the actual rows through $H$, and $f(r)$ their
complete field-operation counts: core reads/tests/writes, all birth
initializations, event fields and links/tail assignments, bounded bank/
latch/tick/token coeffects and all actual outputs. With $I_F(u)$ the
canonical input-installation field/link account of Assumption 1.2,

$$
\mathsf{FieldOps}(H)=I_F(u)+\sum_{r\in\mathcal R_H}f(r).
\tag{OA.32}
$$

Let $v_{\rm core}(r)$ count its actual non-event births, including code,
words, marks, record/answer backing and simulated-state **data** cells.
Then retained cell backing is exactly

$$
\mathsf{Cells}(H)=N(u)+
 \sum_{r\in\mathcal R_H}v_{\rm core}(r)+|\mathcal R_H|,
\tag{OA.33}
$$

with the fixed primitive control/right representation charged separately.
The last term is all shared events. Original bank births, packets,
sites, operands, staging, detached tiles and all old cleared cells are
in the sum. Auxiliary popped/cancelled marks, intermediate word versions,
code, simulated event encodings and printed answers are retained too.
No erasure subtracts allocated backing. Unknown-input installation
precedes chronology and is included once, not as fictitious event rows.

**Proposition 22.2 (effective instancewise finite recurrence).** The
above routine specifications give a finite cost vector at every admitted
finite prefix and a finite instancewise completion bound whenever the
remaining requested bits are supplied. They give neither uniform memory
nor a cost-optimal primitive basis.

Proof. For a bounded expanded primitive use its actual vector of one row,
one event, field operations, core births and output tokens. For sequence,
add at the actual successive states. For a test, add its own vector and
the chosen branch's vector. For a loop consuming a finite word/list or
countdown $x$, use

$$
\mathcal C_{\rm loop}(z,x)=
 \mathcal C_{\rm test}(z,x)+
 \begin{cases}
 0,&\text{exit},\\
 \mathcal C_{\rm body}(z,x)+
 \mathcal C_{\rm loop}(z',x'),&\text{continue}.
 \end{cases}
\tag{OA.34}
$$

Here $z'$ includes the actually allocated retained versions and the
actual current event tail; $x'$ is the unconsumed suffix, tail countdown,
or next structural work configuration. Pop/link subphases use their
individual bounded rules, so the recurrence applies inside an append
or partially built tuple as well. For ancestry the outer well-founded
index is decreasing $\nu$; for the socket/tree traversals it is the
finite unvisited input with its stack, not the growing output. An
original simulated Step has only the finite scans of Definition 20.2.
For its $j$-row Prefix loop the recurrence is, more explicitly,

$$
\mathcal C_{\rm prefix}(j+1,X)=
 \mathcal C_{\rm test}(j+1,X)+\mathcal C_{\rm Step}(X)
 +\mathcal C_{\rm consume}(j)+
 \mathcal C_{\rm prefix}(j,\operatorname{Step}(X)),
\tag{OA.35}
$$

with a separately tested zero exit. Every value in these formulae is an
acquired word, a constructed virtual tuple, or a mathematical parameter
for the bill. No recurrence value is a new runtime oracle.

For an explicit finiteness envelope, put $h=N(u)$ and $b=b_w$.
The fixed original row scheme creates at most a fixed number of bounded
cells per row, uses fixed cell arities, and has at most $h+O(b+1)$
allocated objects through original row $b$. With unary typed-reference
DATA and list framing, there is a fixed $A$ such that every complete
original state word through $b$ has length at most

$$
q=A(h+b+1)^2.
\tag{OA.36}
$$

The initial nodes contribute $h$ bounded tuples. Every original
non-event/event birth adds boundedly many fields whose reference
ordinals are at most $h+O(b+1)$; allocator words have the same bound.
Fixed roots/latches and the input/output words contribute no more.
Length framing increases this by a fixed factor. This proves (OA.36)
for the complete represented state, not just its current tree.

Define $M(q)$ as one plus the maximum expanded row cost of the finite
non-outer routines in §§18–21, on all finite bit-word arguments of
total length at most $q$, using typed failure on invalid encodings.
The routines are Copy/Cat, list/tuple operations, one bottom-up grammar
or parser traversal, one original Step, one state encoding, cancellation
and one closed-word output/copy. All terminate on finite arguments:
invalid syntax returns failure rather than following a fabricated
reference, and scans have their finite end/countdown. There are finitely
many words of bounded length, so $M$ is a finite computable bound.
This maximum defines a mathematical envelope; the installed controller
does not evaluate it. Enlarge its argument by a fixed polynomial when
a routine constructs framing/countdown operands.

Let $p=N(t)$ and $d=b-n$. Parsing costs one bounded local append per
actually received constructor plus its structural parse; ancestry has
at most $\nu(t)$ predecessor iterations, each a finite grammar traversal;
the two simulations have $b+n$ Steps and their real tests/countdowns.
Thus, with a fixed polynomial $Q$ large enough for their tuple/word
operands, one sufficient local envelope through $H_1$ is

$$
L(H_1)\le I(K,m)+A_1(r_w-n+p+1)
 +\bigl(b+n+\nu(t)+A_1\bigr)
       M\!\left(Q(h+b+p+d+1)\right).
\tag{OA.37}
$$

Here $I(K,m)$ is the actual finite bootstrap/slot/latch/seal recurrence,
and $A_1$ bounds the fixed per-invocation/token/dispatch blocks.
This envelope includes the full record encoding, reads, bit emissions
and acknowledgement: their input lengths are bounded by (OA.36) and
the binding length, so they are among the stated $M$ terms. The value
$r_w-n$ is finite by Theorem 13.3; its same-run source bill is the actual
suffix of Theorems 15.1–15.2, not an assumed elapsed-time input.
For $H_0$ only installation, invocations/receipts, the first-frame
appends and cleanup are needed. For each later actually supplied
request, add its actual bit-ingress recurrence and the finite
copy/index/answer/output recurrence at that state. For each later
source command, add its actual input/graft/service/cleanup rows and
their invocation/token work. Do not charge requests that were not
supplied. This gives the requested bound on the same execution,
including partially received requests and source-busy cuts. $\square$

**Definition 22.3 (reference occurrences, bits and continuation resources).**
Row/event counts do not fix detailed bit costs. For each actual reference
type $\tau$ and allocated name $j$, let $w_\tau(j)$ be its actual
representation width in this model; an opaque canonical binary encoding
is permitted, but its ordinal is not inspectable by the source program.
Charge each initialized/read/written/retained/emitted reference occurrence
its actual $w_\tau(j)$, including copies in events, slots, code/record
descriptors and allocators. Add the actual finite-tag/latch/control/right
bits and the actual bit-list payload and links. Equivalently, the
read/write traffic coordinate is the sum of these widths over the
field occurrences in (OA.32); the retained coordinate is the width
sum over every initialized retained field in (OA.33), not the traffic
sum counted as storage. Use the actual *shared* event names after Attach,
whose widths can exceed the comparison run's event widths.

Historical reference ordinals in $R$ use their declared unary DATA
codec; those payload bits and the actual references linking the payload
cells are separate charges. Initial source installation includes all
original tag/child fields, $N(u)-1$ child links and the root attachment.
Initial and query DATA publication charges all read/next/cursor/output
operations and the full actual number of bits emitted. Source constructor
output still has its original finite-token count; it is not a free
full-state or full-address output.

At $H_0$ source Return is complete but the historical record is not yet
available. At $H_1$ the record and request service are complete, while
the current source retains $E t$. Later-use costs include the next real
Supply and Update and any subsequent output draining. The finite bounds
grow with actual source history, target record, supplied indices, queries
and shared references. No uniform workspace, minimal generator claim,
physical runtime price or optimality follows.

## 23. Supplier correspondence and the exact increment

**Definition 23.1 (credited methods and source-specific synthesis).**
The statements above are ordinary conditional mathematics. Their
supplier correspondence is as follows.

| Supplier | Parameters, exact reuse and boundary |
| --- | --- |
| OA §§12–15, especially Definitions 12.3–12.5/4.1 and Theorems 13.2–13.3 | The original source, owner/port, initialization, sites, literal templates, actual constructor output, cleanup and canonical row scheme. New auxiliary types are disjoint from original non-event types; the chronological event type is deliberately shared. Lemma 19.2 proves its metadata correspondence instead of assuming it. |
| ER Theorems 9.3/9.5/9.8 and OA17.2 | Set the entry antichain to $j[\mathcal T]$, graft constants to $\alpha$, and endpoint to the actually received $t=F_w(j(u))$. Reuse attained ancestry and canonical original replay. This does not extend OA17.2's separate four-view theorem to arbitrary interiors. The new acquired distance $D$ locates the old row cut. |
| [AA12.5–12.6][AA18] and [Joint Moment Fibers §§36,42,65][JM18] | AA already supplies prepared full-address simulation and conditional same-source installation on its $Q_v$ family. JM separates generator signatures, genuine origins and acquired records. Here no AA prepared tree, INITIAL field, unknown entry choice or JM origin-acquisition premise is treated as an old $\iota$ operand. |
| [Paid Current Return §§31–35][PAID18] | Finite future-event acquisition and current use already exist with its acquired depth, residual label and continuing right. Its event/depth interface is not $\iota$'s. Here the future frame supplies the ancestry endpoint, the completed-invocation marks supply distance, and the original static right supplies current use. |
| [Paid View Conversion §§5–7][PVC8] | Finite conversion algorithms, actual acquired bodies, registry, publication/ACK and returned invocation rights are supplied methods. The present owner-local one-record/bit-query service uses actual bounded ingress and read/output/seal phases; it asserts none of PVC's twelve installed view converters for busy $\iota$. |
| [RCA §§11–16][RCA18], [NCR Definition 2.3][NCR18], [Callable Storage Atlas §§5–7][CSA8] | Reuse finite word expansion, complete-row replay, paid ordinal construction and the separation of an immutable historical image from its later service. RCA's original activation is Ready-only and has its own copy authorities; NCR's fence route requires an authorized fence and its atomic-source premises; CSA's all-cut replay has acquired seed/activation/input/ordinal fields. Attach and the first-frame/distance acquisition here supply a different entry, without importing those premises into an old busy PC. |
| [PR57.D1–D3,D7,L4][TMC12] | Bounded primitive effects, explicit unary/scanning costs, immutable completed publication and authentic-copy methods are credited. This Annex uses linked owned fields, one shared event chain and owner-local reads, not PR57's tape ports, private Clifford source or eight-bit receipt tariff. No PR57 numerical fee is silently transferred. |
| NativeFullSourceProducer.lean, including private traverse, production_reads, stationary, and its owning Scribe | Actual acquired preorder and source-blind finite traversal are already supplied in the stationary native model. Its whole-register/control types and epoch-zero proof do not implement Attach or give a busy $\iota$ state. The socket parser and source correspondence here have their own received-source premises. |
| NativeBoundedPreorderRows.lean, including private pending_next, cursor_frontier, actual_cursor_residual, trial_geometry, guard_value_progress, virtual_next, and its owning Scribe | Existing preorder frontier, actual-prefix and virtual-continuation arguments are credited. Their parameters $P,h,\tau,N$ and licensed virtual-source/guard replies are not unknown inputs supplied to this observer. OA13 already checks their preorder use in the owning source. |
| NativeSerialMachine.lean, Replay, replay_deterministic, operational_replay, reached_prefix_replay, and its owning Scribe; pinned mathlib Computability.StateTransition | Finite reached-path replay and generic transition/refinement language. Actual source acquisition is an additional obligation, discharged by (OA.29); it is not a consequence of generic refinement or a free transcript. |

Huet's [*The Zipper*][HUET] supplies the focus/context method already
credited by OA12.5; no new zipper algorithm is claimed. Lamport's
[*Refinement in State-Based Formalisms*][LAM18] distinguishes refinement
and stuttering under a stated observation relation. Here auxiliary
rows stutter only on the non-chronological source workload, while the
full event/tail state changes; Lemma 19.2 gives the actual relation
and initial-state argument. Reynolds's [*Separation Logic*][REYNOLDS],
§4, requires a framed assertion's free variables to avoid the command's
modified variables. A global tail or live saved-entry variable cannot
be framed as unchanged. The explicit saved-reference phases and
operand enumeration above carry that extra obligation. These primary
methods are used within those hypotheses, not as a proof of unknown
source acquisition.

The substantive increment is the conjunction of actual late acquisition
of the independently marked original pre-Begin $C_n$, a source-specific
shared-chronology proof with actual entry-reference lifetimes, completed
owner-local DATA publication/query, and a next actual Update. Ancestry,
generic replay, word compilers, completed publication and callable
archives remain supplied methods. This is a repository-derived
construction, with no world-novelty or exhaustive literature-absence
claim.

**Definition 23.2 (preserved domains and remaining objectives).**
The model explicitly adds bounded late Attach, fixed paid installation,
a bounded future-token coeffect and genuine owner request ingress.
It assumes the original canonical initialization, occurrence/no-sharing
source, static exclusive authority and no unrecorded autonomous source
actions. It does not solve an unchanged-initialization entrance problem
in a machine whose old menu lacks Attach. It proves neither recognition
of $\mathcal D$, acquisition after a missed Begin, arbitrary-interior
four-view equality, twelve installed converters, arbitrary allocation
or ownership, nor a physical implementation of the new permission.
Its source chronology is the actual enlarged chronology; only the
retained old DATA is the exact original $C_n$.

All previous fixed-$G_{\rm gc}$, original-$Q$, parked-consumer and
unchanged-initialization statements keep their published scope.
The broader independent space/time/boundary/memory recovery programme
and any universal alpha/beta reduction remain separate obligations.
No new Lean, Blueprint, kernel or machine-admission certification is
asserted for §§18–23.

[AA18]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md
[JM18]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_MOMENT_FIBERS.md
[PAID18]: RECURSIVE_RELATIONAL_OBSERVATION_PAID_ZECKENDORF_CURRENT_RETURN.md
[RCA18]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md
[NCR18]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CLOCKED_RECOVERY_AND_ORDER.md
[LAM18]: https://lamport.azurewebsites.net/pubs/refinement.pdf

## 追加锚（本行以下为增补区）
