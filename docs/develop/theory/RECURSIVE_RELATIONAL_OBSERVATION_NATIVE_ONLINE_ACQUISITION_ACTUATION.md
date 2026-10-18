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
