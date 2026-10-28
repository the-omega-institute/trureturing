# Native single-vertex construction on the original relational source

> **Reading contract.** This is an ordinary mathematical theory volume,
> using the generic-v1 numbering convention. Lean code is the repository's
> mathematical truth source; this volume has no Lean kernel certification.
> Published text is append-only. Further results and corrections begin
> after the final append anchor and end with another append anchor.
> Repository source correspondences below refer to the fixed revision
> 07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942.

## 1. The constructor interface and its exact scope

**Convention 1.1 (suppliers and status).** Write
[UAS](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GROWING_UNARY_STORAGE_ATLAS.md)
for growing unary storage,
[SSA](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md)
for structural storage,
[ARC](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACTOR_LOCAL_RESERVE_RECOVERY.md)
for actor-local Reserve recovery,
[CAP](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md)
for the original capacity source, and
[PR57](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md)
for the constructed-tape primitive specification in its §57.
All new statements here are repo-derived ordinary deductions. Standard
tree inversion, deterministic native replay and allocation conservation
are reused ingredients, without a worldwide novelty claim.

**Definition 1.2 (unchanged original instance).** Fix one actual finite
preparation $\xi$, original source $u$, initial $H_0$, actual prior and
initialized original controller as in UAS §1 and ARC §§1–4. Retain the
same source 16, its creation chain and capacity embedding $\phi_K$.
Retain the original ownership map, all 74 actual ports, original
verifier on 32–39, original INITIAL consumer on 40–47, original
experiments $Q$, and original global halt. A later capacity $J$ is
runtime input to this same apparatus.

In particular ARC Definition 9.1 provides one fixed instance with
$u=\beta$, $H_0=h=K=1$ and the truthful INITIAL-Stop client. Its code
and preparation contain no future capacity maximum or list of Reserve
values. The present local construction does not replace that instance
by a new source for each $J$.

**Definition 1.3 (coverage and missing obligation).** UAS Assumption 1.2
admits bounded atomic patches. UAS Definition 2.2(3) creates a complete
unary tape-cell extension in one such patch; Theorem 2.4 matches whole
native rows, including control and receipts, under that premise.
UAS Definition 8.3 expressly leaves a new phase-sensitive proof below
the patch basis. SSA §13 supplies a restricted five-occurrence setter,
with continuing authorization, control, constructors and receipts still
outside its conclusion.

The interface supplied here replaces precisely the cell-extension
data suboperation by 24 one-vertex attachments and gives its partial
states, guards, inverse and full local bill. Its immediate actual
consumer is the new unmarked right-marker cell in source-16 EX during
strict Reserve's Zero loop. It does not perform the rest of EX.
The same template can serve a new meter right-marker cell, but the
source-specific history argument below cannot be transferred to that
meter construction without a new pending-receipt proof.

**Convention 1.4 (syntax, mechanism, encoding and execution).** FIB §2.1
defines free ordered binary trees with distinct leaves $\alpha,\beta$;
pairing is a separate constructor. FIB §10 adds reduction semantics.
The seven-slot graph mechanism below is another explicitly assumed
execution semantics. A finite encoding of its graphs or rule table by
alpha/beta trees is mathematical data, not an installed interpreter.
Neither two irreducible physical operations, a constructor, nor
universal computation is deduced from $\rho$. AtomicPrefixParser
supplies serialization; NativeSerialEffective assumes
OriginalCodeRealization; the virtual substitution compiler supplies its
specified acquired-entrance Read lowering. None is used as an allocator.

## 2. Actual entrance, current authority and the remaining atoms

**Definition 2.1 (eligible source occurrence).** Let $h$ be a history in
UAS's canonical acquired domain $\mathcal C$. Require $h$ to end just
before an actually enabled source-16 EX at the installed strict-Reserve
Zero site in ARC Definition 8.3. Write

$$
d=4(J-K)>0,\qquad
|h|=n_0+5r+1,\qquad 0\le r<d.
$$

Here $r$ counts completed positive Zero iterations, not a graph address.
Denote this fixed installed row site by $\kappa$. The preceding bound
RD has executed. Its actual branch, code version
and PC select this EX, with the original producer's current source
writer/availability condition and original receipt eligibility.
Let $a$ be the actual marked old source-16 right-marker cell root.
From the actual source origin follow its existing $\mathsf O_0$ link
to $a$, then $\mathsf P\mathsf R$ to the existing trailing terminal
$z$. This is the original reached construction site.

No numerical pointer, future historical image or actor-held descriptor
is substituted for this route. The source head and all original
access links remain fixed throughout the component. The initially
empty child slots of $z$ will acquire the new cell and trailing terminal.
Every old occurrence, including $z$, remains the same occurrence.

**Definition 2.2 (target literal).** In PR57's actual symbol and track
order let

$$
c_R=\operatorname{enc}_{\rm sym}(R)\,00000
       =(b_1,\ldots,b_8).
$$

The final five zero tracks are the three head/append/read marks, seal
mark and reserved bit. Thus this is the new unmarked right marker,
not the old marked cell's byte. These eight constants depend only on
the supplier encoding. They contain no private source value, $J$,
capacity-dependent advice or acquired runtime operand.

**Assumption 2.3 (endowed finite local evaluation).** Keep the distinguished
root and seven reciprocal endpoint types
$\mathsf P,\mathsf L,\mathsf R,\mathsf O_0,\mathsf O_1,
\mathsf H_0,\mathsf H_1$ of SSA/UAS. An empty endpoint has no partner.
The L/R child layer is a finite rooted ordered tree. Local unary
intermediate vertices are allowed. A known reached endpoint admits a
partner/vacancy probe; no incoming-edge search is available.

Endow a finite private mechanism which, in a single fine transition,
performs the explicitly bounded guard and matching probe lists of
Definition 4.1, evaluates the finite prefix table, and performs at most
one attachment of Definition 2.4. Its temporary evaluation space is
bounded by those fixed lists and the at-most-25-vertex local pattern.
It is discarded between transitions. There is no retained cursor,
phase register, unbounded work tape, graph scanner or free allocator
beside the actual carrier.

Bounded matching, finite evaluation and this temporary space remain
ideal mechanism assumptions. Their internal probe/evaluation instants
are not additional operational cuts of this model. Every probe is
nevertheless charged. A model exposing those instants, or individual
initialization assignments, requires further states and a further
refinement theorem. The construction does not claim that last descent.

**Definition 2.4 (one-vertex attachment).** At a currently reached parent
$p$ and side $s\in\{0,1\}$, with vacant $p.s$ and the current guard of
Definition 4.1, attach one fresh occurrence $v$. Its complete effect is:

$$
v.\mathsf P:=(p,s),\qquad
v.\mathsf L=v.\mathsf R=v.\mathsf O_0=v.\mathsf O_1
              =v.\mathsf H_0=v.\mathsf H_1:=\varnothing,
\qquad p.s:=v.
$$

This means seven designated new-slot initializations and one assignment
at the reached parent, coherently reciprocal inside the attachment.
It has exactly one birth and one fine commitment. It changes no other
old endpoint, source symbol, head link, native PC, latch, token, input,
output or receipt. Freshness is the actual birth occurrence, not an
integer supplied to a global allocator. New material inherits this
source-16 region's original ownership and creation binding.

The seven initializations and reciprocal attachment remain atomic;
unilateral endpoint writing is not implemented here. The atom is
strictly smaller in constructed material than a 24-vertex extension,
and has no whole-row or receipt coeffect.

**Assumption 2.5 (current component evaluation and permission).** During
this isolated component, only its specified transitions execute. Each
one rechecks the presently installed call-site control, actual source
writer/availability fields, actual old source head/right marker and
unchanged original meter eligibility. The original active version and
immutable code binding remain those of the eligible entrance.
The original core executor may inspect exactly this bounded original
guard/meter footprint and the pending source construction, under the
producer's current construction authority. Its ability to continue
through the partial shapes below is a stated scoped interface premise.

No historical permission byte confers this right. Loss of a current
required token, the wrong PC or version, a wrong original head, or a
failed shape test enables no constructor transition. The sequential
component is not a protocol implementing admission, token retention,
concurrent exclusion, dispatch to a parent continuation or return.
It grants no source read to actor $A$. Its mathematical observations
across owners are not actor-accessible inputs.

## 3. The finite literal template and every construction state

**Definition 3.1 (target positions).** Identify $0,1$ with L,R. In UAS
Definition 2.1 the eight-track unary cell $C_U(c_R)$ is an $F_8$
scaffold with eight terminal bit children. Relative to the old $z$,
the desired support is

$$
P_{24}=\{\varepsilon,1\}
 \ \cup\ \{0w:|w|\le3\}
 \ \cup\ \{0w b_{i(w)}:|w|=3\},
$$

where $i(w)=1,\ldots,8$ is lexicographic track order. Its root is the
old $z$; the left subtree is $C_U(c_R)$ and path 1 is the new trailing
terminal. The 24 nonroot positions, in parent-before-child left-first
preorder, are the following fixed list:

$$
\begin{aligned}
(w_1,\ldots,w_{24})=(&0,00,000,0000,0000b_1,0001,0001b_2,\\
 &001,0010,0010b_3,0011,0011b_4,\\
 &01,010,0100,0100b_5,0101,0101b_6,\\
 &011,0110,0110b_7,0111,0111b_8,1).
\end{aligned}
$$

There is no runtime recursion in this list. It is a fixed finite
description. Each $b_i$ is substituted by its literal side before
the mechanism is endowed.

**Definition 3.2 (partial carrier).** For $0\le j\le24$ set
$P_j=\{\varepsilon,w_1,\ldots,w_j\}$. Let $C_j(h)$ be the actual
original graph at $h$, replacing the subtree rooted at $z$ by this
partial tree. Every child and parent endpoint agrees, all four O/H
slots in this local component are empty, and the external attachment
of $z$ is unchanged. Every other incidence, owner binding, native
field, head, meter cell and input reservoir is exactly the old one.

The $j$ new occurrences are the first $j$ actual attachment births,
named by their template roles. Absolute execution names come from the
actual occurrence relation. Arbitrary fresh-name renaming does not
alter the relative theorem and does not change an original origin.
These are 25 real partial construction states. They are not all
complete UAS byte/tape records, and need not be valid source trees.

**Lemma 3.3 (available next parent).** For $0\le j<24$, the parent of
$w_{j+1}$ belongs to $P_j$, and $w_{j+1}\notin P_j$. Every $P_j$ is
prefix-closed.

Proof. The displayed list is a preorder of the target tree. Every
scaffold parent precedes its children, each bit terminal follows its
own socket, and the final path 1 has parent $\varepsilon$. All listed
paths are distinct: scaffold paths have length at most four; a bit
terminal has length five at its distinct track socket; and path 1 is
outside the left subtree. Taking any initial segment therefore includes
all proper prefixes of its members and no later listed position. ∎

**Theorem 3.4 (literal append path and frame).** Under Assumptions
2.3 and 2.5, from every eligible $h$ the relation in §4 has the unique
path, up to consistent fresh-name renaming,

$$
C_0(h)\longrightarrow C_1(h)\longrightarrow\cdots
                  \longrightarrow C_{24}(h).
$$

Every cut is a connected reciprocal rooted child tree. Exactly one
vertex is born at each edge. All exterior incidences, all old material,
the original source binding, original source head, native control,
tokens and original meter remain unchanged. At the last cut the data
effect is precisely UAS Definition 2.2(3) for $c_R$.

Proof. At stage $j$, Lemma 3.3 supplies the existing parent and vacant
destination. Definition 2.4 attaches a fresh terminal there. It cannot
create a cycle or a second parent; it makes exactly the two reciprocal
endpoints agree and initializes the other slots empty. Hence it gives
exactly $P_{j+1}$. Induction gives every stated cut and preserves the
frame, since no other old endpoint is designated.

The guard's original finite fields, old marked R cell, original head
links and original meter do not change. Its tests therefore continue
to hold under the stated current authority. At each stage the distinct
cardinality $j+1$ and exact pattern select one prefix-table entry;
Lemma 3.3 supplies one next side and parent. There is no alternative
birth in the defined relation. At stage 24 no birth entry is present.
The final left subtree has the 15 scaffold/socket vertices and eight
bit terminals of $C_U(c_R)$, and the right child is one terminal.
This is exactly $\langle C_U(c_R),z'\rangle$ at the retained $z$. ∎

## 4. Matching, labels, legality and the parent-operation boundary

**Definition 4.1 (literal current guard and evaluation strategy).** The
following ordered probe recipe is part of the mechanism, repeated
from scratch on every executing fine transition.

1. Let $\mathcal F_\kappa$ be the finite ordered set of required
   present native bit locations for the active-version/row-decoder,
   mode/PC, source writer/availability and original receipt guard of
   this installed EX site. Enumerate them in UAS's physical catalog
   order, counting each physical bit once. Follow each fixed root
   route $\pi_f$ and inspect its unary bit by the two child probes at
   each of its two vertices and its one parent return. An absent
   required bit or failed literal finite guard disables the rule.
   These are original core guard locations, not all-owner tape data.
2. Follow $\pi_{16}$ to the actual source origin, probe $\mathsf O_0$
   to $a$, check $a.\mathsf H_0$ back to that origin, inspect the
   complete old 23-vertex cell by both child probes and parent returns,
   and follow $a.\mathsf P\mathsf R$ to $z$. Probe $z.\mathsf P$
   to check this same external attachment. Test the old marked R byte.
   Its byte is unchanged, even when the pending subtree is partial.
3. Let $\mathfrak m$ be the supplier's fixed meter port, retaining its
   actual numeric assignment in 56–63; it is not directory port 0.
   Let $j_{\rm app}\in\{0,1\}$ name its actual fixed append lane;
   the other lane is its read lane. Follow $\pi_{\mathfrak m}$ and
   $\mathsf O_{j_{\rm app}}$, check the reached old append cell's
   $\mathsf H_{j_{\rm app}}$ backlink, inspect
   its full 23-vertex byte, and follow $\mathsf P\mathsf R$ to its
   unchanged trailing terminal. Probe that terminal's $\mathsf P$,
   L and R. Test its original append-marker/receipt eligibility.
   Read-head marks and both original lane links retain their actual
   values; this inspection neither moves nor merges them.
4. Start another distinguished-root walk
   $\pi_{16}\mathsf O_0\mathsf P\mathsf R$ to $z$. Inspect its whole
   at-most-25-vertex component in left-first depth-first order.
   Probe L/R at every vertex, P on each nonroot return, and all four
   O/H slots at every vertex. Require exact agreement with one $P_j$,
   $j<24$, including empty O/H slots and reciprocal parent returns.
   This is bounded pattern inspection: stop and reject on an
   unexpected extension, depth beyond five or a twenty-sixth vertex;
   never inspect an arbitrarily large component to find a match.
5. Evaluate the fixed finite table once. For the uniquely matched $j$,
   follow the proper-parent path of $w_{j+1}$ from $z$, and reprobe
   the final destination child slot. Require vacancy and perform
   Definition 2.4. There is no native control or receipt update.

The required finite fields are obtained by expanding the actual
decoder and guards of this fixed original row; there is no branch on
an encoded future capacity or on arbitrary source payload. This
dependency description and UAS's fixed physical ordering specify the
finite field/route list even if some fields share a parent component.
Each listed route is still walked separately. Current original
enabledness at the eligible entrance is a premise, not supplied by
matching a historical certificate.

Inspection and table evaluation are the bounded internal matching
of Assumption 2.3. They are not an unpriced scan or individually
observable microsteps. The O/H probes in step 4 are deliberate:
matching only the child tree would not check the specified local
access-slot emptiness. No endpoint is retained across fine cuts.
As for the supplier's partial primitive relation, a failed guard has
no executing transition or receipt. The executing-transition tariff
below does not claim a physical zero-cost implementation of rejected
matching attempts.

**Definition 4.2 (fine operation and mathematical readout).** A fine
label records the actual EX site, its attachment occurrence and
template role $w_{j+1}$. Its local mathematical readout is the real
incidence successor and enabled next constructor action. The terminal
constructor readout is the append postcondition at $C_{24}(h)$.
There is no constructor edge there. This is component completion,
not original global halt or an executed return.

The actual operation order is these fine occurrences after the old
native history. Temporary private probe values and endpoint choices
are not additional released outputs. If fine progress/charge labels
are made public, they are an explicitly finer observation interface,
not automatically an original $Q$ experiment. A mathematical view of
the graph does not install a graph-output service.

**Proposition 4.3 (what the path does and does not complete).** The
path closes the multi-vertex construction data obligation at this
EX site. It does not yield the original EX successor.

Proof. Its endpoint has exactly the required new unmarked R cell.
However the old marked R cell still has symbol R, whereas original
EX must make it blank and leave the ordinary head on that same old
cell. The original PC has not advanced, and neither the old meter R
overwrite, new meter cell, append-mark/link transfer nor original
ordinary/F receipt has occurred. These are concrete differing
coordinates of the proposed endpoint and the original successor.
They cannot be supplied by naming the last birth a commit.

In particular $C_{24}(h)$ must not be fed to UAS's complete-native-row
decoder as if the pending EX had committed. A parent adapter must
implement these effects, its phase dispatch and actual return.
No row-sized atomic patch is an operation of the relation in this
volume. ∎

## 5. Independent observations and their exact recovery domains

**Definition 5.1 (four observations).** Define
$\mathcal H_C=\{(h,j):h\text{ is eligible},\ 0\le j\le24\}$.
This is a one-fragment family over original canonical acquired entries,
not an already composed all-row fine runtime. On its actual executions
define the following observations independently.

| View | Actual object observed |
| --- | --- |
| $S_C$ | Root-relative L/R child-path reachability in the whole current carrier, including the partial append. Access links are not child edges. |
| $B_C$ | Paths ending at actual vertices with both child slots empty. This geometric terminal boundary is unrelated to the machine's halt output. |
| $T_C$ | The chronological word of actual UAS patch occurrences through $h$, followed by the $j$ typed attachment occurrences, with actual operands, values and creation roles. This is actual process order, not a retained log. |
| $M_C$ | UAS Definition 3.3's actual joint retained selection $M_J$, together with the actual bounded source-16 subtree reached by its original head and P,R, including its current attachment and ownership relations. |

The last view selects material, not a serialized history key. It is a
joint mathematical observation across owners, including private
material. It does not make $M_J$ or source 16 an A-owned input.
The source append leaves every selected family in $M_J$ unchanged:
source 16 is outside that selection, and code, ingress, frontier
words, native PC, latches, tokens and meter are fixed here.

**Theorem 5.2 (all-cut local inverse, with both directions).** With the
actual exterior attachment and owner/guard interface held fixed,
either the local support below $z$ or its independently defined local
terminal boundary determines the complete local incidence at every
$C_j(h)$, the exact phase $j$, and the specified next constructor
operation/readout. Encoding after decoding and decoding after observing
are identities on each respective actual image.

Proof. Apply the supplied finite-tree inversion of UAS Theorem 3.2
and SSA Proposition 13.3, which permits unary vertices:

$$
S_{\rm loc}=\operatorname{Pref}(B_{\rm loc}),\qquad
B_{\rm loc}=\operatorname{Max}_{\preceq}(S_{\rm loc}).
$$

Place a vertex at each support path; join each nonempty path to its
immediate prefix by the corresponding child endpoint and reciprocal
P endpoint. Give all local O/H slots their stipulated empty values,
and keep the supplied exterior attachment of the root. This
reconstructs precisely the local graph. Its cardinality gives
$j=|S_{\rm loc}|-1$. The fixed literal table selects $w_{j+1}$ when
$j<24$, or the append-complete readout when $j=24$.

Thus this decoder applied to an actual observation returns the
observed state. Conversely an actual-image support is exactly its
set of reconstructed paths, so observing that reconstruction gives
the same support. For a boundary, first take prefix closure and use
the same decoder; taking maximal paths again returns the same
actual-image boundary. These prove both identities separately.
Current exterior permission is a fixed boundary parameter of this
local statement; it is not inferred from the local tree. ∎

**Theorem 5.3 (source-specific one-fragment history recovery).** For
each $V\in\{S_C,B_C,T_C,M_C\}$ separately and
$(h,j),(k,t)\in\mathcal H_C$,

$$
V(h,j)=V(k,t)\quad\Longleftrightarrow\quad (h,j)=(k,t).
$$

Each view therefore recovers the actual partial raw graph, old native
history and this fragment's fine history. On its actual image its
decoder $D_V$ and encoder $E_V$ satisfy

$$
D_VE_V=\operatorname{id}_{\mathcal H_C},\qquad
E_VD_V=\operatorname{id}_{\operatorname{im}E_V}.
$$

Proof. First decode a whole support. The fixed outer sockets locate
source 16 and the original finite fields. Along its actual tape
spine, the old complete marked R cell remains unchanged. All newly
constructed portions have only prefixes of the unmarked $c_R$
template; none adds another occupied true head-mark track. The
original complete marked cell therefore remains uniquely identifiable
from child geometry. Its P,R route identifies the original $z$,
even when the last new trailing child is still absent. Count the
strict descendants below $z$ to obtain $j$.

Prune these descendants mathematically, retaining $z$. This gives
exactly the original child tree at $h$. This pruning is a decoder,
not an executable deletion or source reset. UAS Theorem 3.2 decodes
its whole raw record $W(h)$, with its original cursor-track-determined
access links. The new O/H slots are empty and every old access link
has been unchanged, so they also reconstruct the fine graph.
Selecting $M_J(h)$ and applying the supplied UAS Theorem 3.4 on
$\mathcal C$ recovers $h$. Equal whole supports consequently give
equal $h,j$. Conversely equal $h,j$ give the same graph and support
by Theorem 3.4. This proves both support implications.

For the independently observed boundary, finite-tree prefix closure
gives the same whole support, including the unfinished component.
The preceding decoder therefore gives $h,j$. Equal $h,j$ give the
same terminal paths. This proves both boundary implications.

For retained memory, its $M_J$ part is exactly the unchanged
$M_J(h)$, not a later completed reservoir. UAS Theorem 3.4 gives
$h$ from it. Its extra bounded append component has $j$ strict
descendants and hence supplies $j$. Conversely $h$ fixes the actual
selected backing and rights, and its deterministic $j$ births fix
the selected append. This proves both memory implications.

For process, the two occurrence types distinguish the old UAS
prefix from the new attachment suffix. Native erasure of that old
prefix is $h$, and the actual suffix has length $j$. Conversely
$h$ fixes its original initialized occurrence word, and the fixed
list fixes the $j$ actual birth roles. This proves both process
implications. No separately installed process transcript is used.

The same arguments construct all four decoders. Their observation
direction returns the same actual graph/material/process; their
reconstruction direction returns the same pair. Original absolute
creation identities are those of the recovered native history;
fresh ones are its actual appended template roles. No arbitrary
external birth names are guessed from an unnamed tree. ∎

**Corollary 5.4 (phase-sensitive transition correspondence).** On
$\mathcal H_C$, the four actual-image encodings carry the same
constructor partial edges, fine labels and mathematical readouts.
Every comparison is with the current guard. Both forward transition
and inverse observation directions commute.

Proof. Each decoder recovers the identical $h,j$ and fine graph,
including original finite guards, source and meter links, and local
vacancy. For $j<24$ under the stated continuing permission it
selects the same unique attachment and successor $(h,j+1)$.
For $j=24$ no attachment is enabled and the append postcondition is
the same. Re-observing either successor gives its own actual image
by Theorem 5.3. Thus for a view $V$,

$$
\operatorname{next}_V(E_V(h,j))
 =(\operatorname{label}_{j+1},E_V(h,j+1))
$$

on exactly its executing domain; decoding the right side recovers
the actual successor. At completion each image has the same
component readout. Composing any two decoders/encoders gives inverse
and triangle equations on their actual images. This is a concrete
instance proof, not an invocation of an abstract commuting-square
criterion as an implementation. ∎

**Definition 5.5 (limits of the inverse).** On a fixed exterior, local
geometry recovers only the construction phase and local data. It
does not recover that exterior's source, original inputs or current
permission. The stronger history statement needs the whole-support
or specified joint-memory observation and the canonical acquired
domain in Theorem 5.3. It is not asserted before acquisition, for
noncanonical preparation/code, or for a previous history already
containing unspecified serially refined rows.

Fine-history equality is distinct from raw-state equality in general,
and from original $Q$ equality. The new fine cuts are not original
ARC ordinals $n_0+5r+s$, not already installed HistoricalImage
selectors, and not a paid source read or decoder input for $A$.
No original terminal-history collision is removed.

## 6. Exact work, foundation and retained material on this fragment

**Definition 6.1 (tariff and fixed guard bill).** Keep separate coordinates
for fine commitments $N$, endpoint probes $P$, designated assignments
$W$, births $A$ and bounded table evaluations $E$. Charge unit prices
to the first four and a declared price $\theta\ge0$ per bounded
evaluation. Its fixed mechanism/description price $\rho_C$ is additional.
This is a structural tariff, not a physical duration/energy theorem.
Finite evaluation is an explicit priced ideal operation, with no
unrepresented runtime interpreter.

Let $d_{16}=|\pi_{16}|$, $d_{\mathfrak m}=|\pi_{\mathfrak m}|$, and
$d_z=d_{16}+3$. On an eligible entry all required finite guard bits
are present. Definition 4.1's steps 1–3 cost exactly

$$
G_h=\sum_{f\in\mathcal F_\kappa}(|\pi_f|+5)
                         +(d_{16}+73)+(d_{\mathfrak m}+75).
$$

For step 2 the additional counts after the origin route are one
O-link, one H-backlink, 68 byte-inspection probes and three P,R,P
probes. Step 3 has those same 73 probes plus two trailing vacancy
probes. A 23-vertex cell inspection has $2\cdot23+22=68$ probes.
An independently routed unary finite-bit inspection has five.
Repeated routes, including aliases of their scaffolds, are not
deduplicated. The guard and all its route lengths are unchanged at
every $C_j(h)$; no old-graph whole-tape scan occurs.

**Theorem 6.2 (same-fragment work at every cut).** Define
$L_j=\sum_{s=1}^j|w_s|$. At $C_j(h)$ the cumulative executing work
after the eligible entry is

$$
\begin{aligned}
N_j&=j,&W_j&=8j,&A_j&=j,&E_j&=j,\\
P_j^{\rm work}
 &=j(G_h+d_z)+\frac{7j(j-1)}2+6j+L_j,\\
g_C(j)&=10j+P_j^{\rm work}+\theta j.
\end{aligned}
$$

At completion $L_{24}=90$, and hence

$$
\begin{aligned}
(N,P,W,A,E)_{24}
  &=(24,\ 2166+24(G_h+d_z),\ 192,\ 24,\ 24),\\
g_C(24)&=2406+24(G_h+d_z)+24\theta .
\end{aligned}
$$

Proof. Before birth $i+1$, the local pattern has $i+1$ vertices.
Step 4 probes its two child slots and four O/H slots at each vertex,
and P on each of $i$ nonroot returns: $7i+6$ probes. Its new
root-to-$z$ walk costs $d_z$ even though the guard already reached
that site. Step 5 costs $|w_{i+1}|$: its proper-parent path followed
by the destination vacancy reprobe. Thus this event has exactly
$G_h+d_z+7i+6+|w_{i+1}|$ probes, eight assignments, one birth,
one commitment and one evaluation. All seven fresh-slot initializations,
including empty ones, are in those eight assignments.

Summing over $i=0,\ldots,j-1$ gives the displayed prefix formula.
The target nonroot depths have multiplicities $2,2,4,8,8$ at depths
$1,2,3,4,5$, respectively. Thus
$L_{24}=2+4+12+32+40=90$ and
$\sum_{i=0}^{23}(7i+6)=2076$. Their probe sum is 2166.
Adding 24 commitments, 192 assignments and 24 births gives 240
nonprobe units and the stated scalar. These are successive states
of one fragment, without adding an old atomic subtotal. ∎

**Theorem 6.3 (all-cut material account).** Let $V_h,L_h,\ell_h$ be
the actual original carrier's vertex, geometric-terminal and access-link
counts at $h$. Let $\eta_j$ count the births among the first $j$
whose parent already had its other child. Then the exact graph counts
at $C_j(h)$ are

$$
\begin{aligned}
V_j&=V_h+j,&L_j^{\rm term}&=L_h+\eta_j,\\
E_{\rm tree,j}&=V_h+j-1,&E_{\rm access,j}&=\ell_h,\\
\operatorname{occupied}_j&=2(V_h+j-1+\ell_h),&
\operatorname{capacity}_j&=7(V_h+j).
\end{aligned}
$$

Here $\eta_{24}=8$, so the completed append adds 24 vertices and
eight terminals. There is no discarded allocation or record.

Proof. Every birth adds one connected vertex and one child edge;
all old access edges stay fixed. A fresh child at a terminal replaces
that terminal by one new terminal and leaves the terminal count
unchanged. At a parent with its other child already present, it adds
one terminal and removes none. These are the only cases, proving
the formula for $\eta_j$. The completed subtree has nine terminals
instead of $z$ alone, proving $\eta_{24}=8$. Each reciprocal child
or access edge occupies two of the seven slots per vertex. ∎

**Definition 6.4 (foundation and installation boundary).** UAS's actual
original foundation is retained once:
$V_{U,0}=195+2q+c_0$ graph vertices, its original slot initialization
and birth bill $1+8V_{U,0}$, and its separately charged apparatus
$\rho_U$. Its actual original preparation, boot, code ingress,
source construction, acquisition and activation execute as in the
supplier before an eligible $h$. They are not preloaded by this
constructor.

The added mechanism has the 24 literal prefix cases, fixed guard
routes, bounded matcher/temporary space and coherent attachment atom.
Encode the finite guard, patterns, ordered walks, endpoint effects
and literal table by SSA Definition 3.2's unary/list encoding; let
$d_C$ be its resulting finite description length. Its endowed
foundation is the explicit extra apparatus coordinate $\rho_C$,
with description $d_C$ and bounded private evaluation storage.
There are zero added mutable graph vertices at constructor entry.
The table, routes and description size depend only on the fixed
original finite controller, routing foundation and symbol encoding;
they contain no source payload, future $J$, capacity maximum or
elapsed-history advice. They are not silently included among native
installed code bits or set to zero.

A materially installed native implementation must instead give its
actual installation vector $I_{\rm mat}$: every description ingress
bit, allocated backing, initialization/write, move/read, control bit,
descriptor, token transfer and original receipt, with all partial
installation cuts. It must prove that its actual code executes this
table and reaches its authorized entry/return. That vector and
proof are not supplied here. The finite endowed ideal theorem has
foundation $\rho_C$; it cannot be renamed a material native-code
installation theorem by substituting $d_C$ for $I_{\rm mat}$.

**Proposition 6.5 (component comparison and scoped optimality).** The
24-birth path attains the least number of executing steps among
components that start with this same carrier, end with this same
24-vertex increase and create at most one vertex per executing step,
with no external prebuilt material ingress. This is not a minimal
complete primitive basis or total-price theorem.

Proof. A path of $m$ such steps can increase the retained vertex
count by at most $m$; deletion only lowers that increase. Hence
$m\ge24$. Theorem 3.4 attains 24 in the stated endowed matching
basis. It says nothing about subdividing that basis's internal
probes/evaluation/initializations, or about an actual material
implementation.

For a narrower data-only comparison, the old atomic append has
one commitment, $7\cdot24+2=170$ assignments and 24 births, subtotal
195. The present path has 24 commitments, 192 assignments and 24
births, subtotal 240, before probes and evaluation. The 22 additional
assignments arise because new parents' child slots are first
initialized empty and later assigned by subsequent births; the
old $z$ supplies the other two parent assignments. The 23 additional
commitments give the remaining difference, for a subtotal increase
of 45. This comparison holds only for those same data coordinates.
It does not subtract or reuse an original whole-row bill. ∎

**Definition 6.6 (original events, physical receipts and output costs).**
Throughout the fragment the old original completed-row count is
$n=|h|$, its existing physical receipts remain exactly those at $h$,
and its original logical tick/fee coordinates remain $n,2n$.
The $j$ fine commitments have the separate positive structural bill
above. They are neither $j$ original rows nor $j$ implicit physical
receipt cells. There is no separate permanent fine-event log, new
input consumption, OUT, copy, ACK, historical package or native return
in this component.

All original input/setup costs for the particular Reserve, the
original code and occupied source material remain at their real
preceding states. The parent EX's old-R-to-blank assignments, native
finite effects, original receipt construction, both meter-head
effects, PC/authority commitment and return are additional unresolved
work, not zero-cost effects of the last birth. A full-run price is
undefined until that join is specified. For a future full compiler,
one must sum its actual fragment vectors at their actual updated
states, including input, all constructors and original receipts.

## 7. Conditional retained-receipt production boundary

**Definition 7.1 (one finite entrance and counted production).** Fix one
actually reached finite entrance $P$ of a proposed lower apparatus on
the same original source. Let $R_0$ be its finite initial vertex stock,
generously including all initial code, foundation, spare material and
already constructed buffers. Let its next $m$ actual executing fine
events have birth counts $\beta_1,\ldots,\beta_m$, and set
$A(m)=\sum_{i=1}^m\beta_i$. Every current vertex must have come from
this initial stock or these counted births. All stock, event and birth
counts in this section are natural numbers. Any physical material
influx is counted here; a hidden external allocator is excluded.

Count all executing events, including fine metering, receipt catch-up,
probes made separate events by that model, helper construction,
installation after $P$, and cleanup. Deletion may occur in this
general bound, but creates no new vertex. The constructor in §§2–6
itself deletes none.

**Definition 7.2 (optional fine receipts, disjointness and lag).** Impose
the following extra policy on the proposed class, not on the original
goal. Of its first $m$ fine events, let $r(m)$ have completed actual
retained fine receipts. Each such receipt requires at least $a\ge1$
distinct vertices, with $a$ a positive natural number; receipt blocks
are pairwise disjoint, and their
vertices are disjoint from $D(m)$ distinct currently required nonreceipt
vertices. Every counted completed receipt remains retained at the cut
in question. Finite initial receipt stock is allowed and credited in
$R_0$.

If bounded backlog is claimed, require one fixed $L\in\mathbb N$, independent
of the future Reserve input, with
$r(m)\ge\max(0,m-L)$ at the cuts to which the bound is applied.
No lag assumption is needed for the first inequality below. A fully
settled cut has $r(m)=m$. The counts are mathematical quantities of
this actual execution, not readable registers or A-owned inputs.

**Theorem 7.3 (retained-record birth budget).** Under Definitions
7.1–7.2, at every declared cut,

$$
a\,r(m)+D(m)\le R_0+A(m).
$$

With the bounded-backlog premise,

$$
D(m)\le R_0+aL+\sum_{i=1}^m(\beta_i-a).
$$

If also $\beta_i\le B$ for every executing event, this implies

$$
D(m)\le R_0+aL+(B-a)m.
$$

For $B<a$ necessarily
$m\le\lfloor(R_0+aL)/(a-B)\rfloor$; for $B=a$ necessarily
$D(m)\le R_0+aL$. For $B>a$ a demanded size $D$ requires at least

$$
m\ge
\left\lceil\frac{\max(0,D-R_0-aL)}{B-a}\right\rceil ,
$$

as a necessary production condition only.

Proof. The retained completed receipt blocks and the $D(m)$
nonreceipt occurrences form disjoint subsets of the current carrier.
The current carrier has at most $R_0+A(m)$ vertices, because every
current occurrence is initial or born at a counted event. Deleting
or retiring an occurrence cannot increase that bound. This proves
the first inequality. Since $r(m)\ge m-L$, even when $m<L$,
substitution and rearrangement give the prefix-sum inequality.
Summing $\beta_i\le B$ gives the uniform bound. Nonnegativity of
$D(m)$ proves the $B<a$ event limit; the zero-slope and positive-slope
cases follow by the indicated rearrangements and integrality. ∎

**Corollary 7.4 (same-source finite Reserve consequence).** Fix once
the beta initialization of ARC Definition 9.1 and any actually
reached outer entry $P$ with current reserve $K_P$. Fix the finite
$R_0,L$ of a proposed realization. Suppose it preserves the original
uncompressed UAS source backing and realizes every canonical finite
strict Reserve from this same entry through its original source
Zero return. If its extra fine-receipt policy satisfies Theorem 7.3
with $B\le a$, it cannot realize all these finite inputs.

Proof. Actually supply 01 and the canonical strict Reserve$(J)$
frame, $J>K_P$. ARC Proposition 10.4 gives $d=4(J-K_P)$ and
$d+1$ newly appended source cells at that return, including the
delimiter. UAS's source tape gains exactly 24 retained vertices per
append, so the newly retained source material alone gives

$$
D_J=24(d+1)=96(J-K_P)+24.
$$

It is disjoint from the stipulated fine receipts. Original receipts,
old source, later directory/journal/copy work and control material
are additional demands that can be omitted from this lower bound.
Choose the finite actual runtime input

$$
J=K_P+R_0+aL+1.
$$

Then $D_J>R_0+aL$, whereas Theorem 7.3 with $B\le a$ requires
$D_J\le R_0+aL$ at that return, irrespective of elapsed fine time.
The contradiction uses the same $\xi,u,H_0$, code and initial stock.
It does not select a new source per size, assume infinite supply,
or impose a uniform deadline on completing any one finite input. ∎

**Proposition 7.5 (native receipt instance and settled variants).**
For uncompressed UAS fine receipts the marginal requirement is
$a=24$. A literal one-birth engine with that policy has
$m\le\lfloor(R_0+24L)/23\rfloor$. Even $B=24$ gives no unbounded
source-growth surplus. A one-vertex retained fine stamp with
$a=B=1$ also bounds nonreceipt material by $R_0+L$.

Proof. A $k$-cell UAS tape has $24k+1$ vertices. The marginal
source/receipt increment is therefore 24, not merely the 23 vertices
of the byte subtree. For a receipt chain, allocate to each completed
receipt its byte subtree and spine occurrence; these blocks are
distinct. Boundary/initial stock constants are already generously
credited in $R_0$. Apply Theorem 7.3. For the last assertion substitute
$a=B=1$.

If receipts are only promised eventually, without any fixed lag,
the first inequality still applies. At a genuinely fully settled
checkpoint $r(m)=m$, it yields
$D(m)\le R_0+\sum_i(\beta_i-a)$, hence $D(m)\le R_0$ for $B\le a$.
Thus a claimed finite returning or halting realization with all its
fine receipts settled there has the same unbounded-growth obstruction.
Unbounded unsettled debt at every relevant checkpoint is outside
that settled premise; eventuality alone supplies no uniform $L$. ∎

**Definition 7.6 (escapes and the actual original receipt contract).**
The user goal and PR57 require one original physical receipt per
original completed row. They do not require a disjoint new physical
receipt for every inserted lower event. The present constructor
uses mathematical fine prices and no such extra fine records.
It consequently violates the extra fine-receipt policy, not the
production inequality. Its parent's one original receipt remains
an actual integration obligation.

The bound also has these exact escape conditions. A larger actual
birth surplus may pay for records and data, but still needs an
operational construction. A different shared/compressed representation
may fail the disjoint-block or $a$ premise and needs its own decoder,
current ownership, original-meter projection and cost proof.
Discarding records fails retention. An unbounded backlog fails a
fixed-$L$ claim and needs an explicit account of its pending phases
and task readout. External material is permitted only when counted
as actual production; an uncounted supplier fails Definition 7.1.
A future-input-dependent initial reserve fails the same-initialization
premise. These are changes of hypotheses, not counterexamples.
In particular a supposed one-birth primitive with a free 24-birth
receipt coeffect has total birth allowance at least 25, not one.

Appending extra fine receipts to the original meter also changes
its original ordinals, fence counts and paid readout. Even if enough
vertices existed, an original-meter consumer correspondence would
still be necessary. A separate fine meter does not by itself solve
the production inequality.

## 8. Boundary examples and failed extensions

**Proposition 8.1 (a partial cell is not a byte).** At $C_1(h)$ only $z.0$
has been created. That single child is not a complete $F_8$ cell.
The old source head, native PC and original meter still have their
entry values. The partial-tree decoder in §5 applies; the old
complete-byte decoder applied directly to this new component does
not. At $C_{24}(h)$ the new byte is complete, but Proposition 4.3
still separates append completion from an EX successor.

Proof. Definitions 3.1–3.2 give $w_1=0$ and
$P_1=\{\varepsilon,0\}$. Thus the new cell-root occurrence at $z.0$
is still a terminal; it has neither the complete $F_8$ scaffold nor
its eight bit children. It cannot satisfy the complete-byte decoder's
shape premise. The frame in Theorem 3.4 leaves the old head, PC and
meter fixed. Theorem 5.2 decodes this actual partial tree, including
its phase. At cut 24, Theorem 3.4 gives the complete $C_U(c_R)$
subtree, while Proposition 4.3 identifies the remaining old-symbol,
control and meter effects of EX. ∎

**Proposition 8.2 (uninstalled target information cannot be guessed).**
Replacing $c_R$ by an arbitrary runtime byte without supplying its
actual remaining target information does not yield a self-dispatching
variable-byte constructor from the partial tree alone.

Proof. Consider the displayed preorder with two intended bytes that
agree before track $i$ and disagree on $b_i$. Just before the
terminal child at that track is born, their local partial trees are
identical: all earlier bit choices and all scaffold vertices so far
are the same. Their required next child sides differ. A selector
factoring only through that identical local tree must choose the
same side for both and fails at least one target. A rule immediate
for the fixed $c_R$ avoids this missing input. A variable target
needs actual acquired or retained operand material and its priced
reads, not a proof-side target parameter. ∎

**Proposition 8.3 (permission is outside a local shape).** For
$0\le j<24$, two identical local $P_j$ components can be placed in
exterior contexts with source writer availability respectively 1 and
0, or with the required active PC and a different PC. Their local
supports and terminal boundaries agree. With the remaining guard
premises satisfied, only the appropriate current context enables the
next birth. Thus local shape alone does not determine permission.

Proof. Keep the local component, its exterior attachment and its
ownership fixed. Choose the first exterior's finite guard fields to
satisfy Definition 4.1 and Assumption 2.5; in the second change only
the exterior availability field to its disabling value, or the PC
to a value failing the installed-site test. Neither change alters
any local child path or local terminal. In the first context the
prefix test selects $j$ and Lemma 3.3 supplies the vacant next
destination. In the second the current guard fails, so Definition
4.1 enables no attachment. The disabled context is not an eligible
point of $\mathcal H_C$. This is precisely why
Theorem 5.2 holds exterior permission fixed, whereas Theorem 5.3
uses the specified whole observations on $\mathcal H_C$. No step
restores a historical permission. ∎

**Proposition 8.4 (meter construction is a different join).** The
$M_J$ part of $M_C$ is unchanged because this construction modifies
only source 16. Constructing a meter cell modifies the very chain
from which UAS extracts the completed-row ordinal. A full-looking
but uncommitted receipt, or only its unfinished byte, must not be
counted as a completed original row. The source-specific pruning
argument does not by itself settle the pending/completed receipt
distinction for a meter-cell construction.
The parent join needs actual phase material and both meter heads.

Proof. Definition 2.4 changes only the pending source subtree, which
Definition 5.1 excludes from $M_J$; hence that selected memory is
fixed throughout this fragment. A meter-cell construction instead
changes the retained receipt chain used to recover the old history
in Theorem 5.3. Its proof's unchanged-$M_J$ premise therefore no
longer holds. Moreover, Definitions 4.2 and 6.6 distinguish the
birth or completion of a data component from an original completed
row: the latter also requires the parent control and receipt effects
listed in Proposition 4.3. An unfinished or merely full-looking
receipt does not establish those effects. The parent join must
therefore identify its pending/completed phase in actual retained
material and preserve the distinct read and append lanes specified
in Definition 4.1. This does not preclude a different inverse for
a separately specified meter protocol. ∎

**Proposition 8.5 (finite stock and helpers).** With $B=a=1$, the
production and retention conditions admit event-count sequences of
arbitrary finite length with exactly one birth per event, used as
that event's distinct retained stamp, and no additional required
nonreceipt data. Their surplus is zero
and $D$ stays bounded. Further stamp-producing helper events consume
their own one-vertex production allowances. A finite initial arena
is already credited in $R_0$ and does not change the zero slope.

Proof. Fix an initial stock of $R_0$ vertices containing the required
nonreceipt material, of size $D_0\le R_0$. For any finite $m$, take
$m$ distinct fresh vertices, disjoint from that stock, one per event,
and use each as that event's retained singleton receipt. At every
prefix $k\le m$, the production and retention counts are
$A(k)=r(k)=k$ and $D(k)=D_0$. The receipt blocks are disjoint and
$r(k)+D_0=k+D_0\le R_0+k$, so all these resource conditions hold,
even with $L=0$. This supplies a witness for the counting conditions
at every finite length; it supplies no operational controller or
original-task realization. Each added helper with one birth and its
own retained one-vertex stamp has increment $\beta_i-a=0$, so it
adds no surplus in Theorem 7.3. Substituting $B=a=1$ there gives
$D(k)\le R_0+L$ regardless of the number of helpers; enlarging the
fixed initial arena changes only $R_0$, not that zero slope. ∎

**Convention 8.6 (assignment and time boundaries).** The old five-vertex
setter is not silently imported onto UAS's two-occurrence unary bits.
Existing Boolean periodicity, SSA's continuation-information examples,
and its unchanged-write accounting remain supplied boundaries.
This volume supplies no new relocation-only assignment algorithm.
Nor does geometry retain all general elapsed time: navigation-only
events or a returned no-op cycle can leave a child tree unchanged.
The phase recovery here works because every declared fine event is
one new vertex in this fixed literal schedule. A finer model exposing
the inspection instants would need its own cursor/evaluation phases.

## 9. The next actual join and the unchanged full goal

**Definition 9.1 (required parent constructor/assignment/control join).**
The next supplier must construct one initialized finite row protocol
on this same source and actual code lineage. It must admit the
original row under its actual current guard, bind its actual operands,
and retain every occupied IN value until its real write. It must
combine existing-bit assignments, this literal append component and
all other required constructors with the actual control fields and
continuing maintenance authority. It must handle mark/head phases
whose noncanonical marks no longer determine access links by the
old complete-state decoder.

For this EX specifically it must assign the old R symbol to blank,
preserve that ordinary head and its original occurrence, construct
exactly one original meter receipt and new marker, preserve the
meter read head while changing the separate append head, and perform
the real PC/token/receipt completion and parent return. Coincident
meter targets must retain both typed lanes. A staged full-looking
receipt is not a completed original event merely because its byte
has been built. Every proposed snapshot, phase marker or rollback
map must be represented or justified from actual retained material,
with current access and full price. A final unexplained row-sized
commit is not this join.

**Definition 9.2 (full domains and original consumer remain obligations).**
A complete lowering must additionally cover the original raw domain
$\mathcal R$: private preparation and acquisition, original and added
boundary boot, wrong IN values, partial or malformed installed code,
raw source-invalid overwrite phases, unchanged writes, descriptor/
archive construction, loans and unavailable copies, both publication
copies, selectors and ACKs, rejects, all Reserve phases including
delimiter/return work, genuine guarded Raise/Rho, and final halt.
These domains are not excluded from the original task by restricting
Theorem 5.3 to $\mathcal H_C$.

The next proof must join all those rows and repeated constructor
calls, with actual initialization and finite code independent of
future capacity maxima. Only then may it claim the one-boot arbitrary
finite Reserve continuation and original verifier/INITIAL consumer
route preserved by the lower runtime. ARC's existing Step74,
Prefix74, ClientImage and acquired Issue/Call are consumers of
original native cuts. They do not already accept new fine cuts or
supply a current actor's private-source input.

**Definition 9.3 (remaining common-instance recovery).** The original
space/process/boundary/memory programme still requires the intended
original-task experiment and successor-coordinate correspondence on
every claimed domain, independently defined views, current paid
acquisition where needed, and natural-view serialization/return
services with real code, copies and prices. Full-history recovery,
raw-state recovery, original $Q$ equivalence, added $Q_G$ behavior
and current actor access remain separate.

Original same-output absorbing-terminal fibres and the final
no-Ready horizon remain unchanged. Adding a full-state terminal
audit, a new historical selector or an all-owner source probe would
change that task. Generic original-client success retains its actual
proposal/prior/local-termination premises. Infinite progression
retains actual continuing supply requirements. Neither global
minimality, complete-runtime price dominance, physical spacetime
ontology nor completion of this full goal follows from the constructor.

## 10. Sources, correspondences and verification boundary

**Definition 10.1 (fixed repository source map).** The following source
URLs fix every repository attribution to the stated snapshot; local
links above are reading conveniences.

| Fixed source | Supplied statement and exact limit |
| --- | --- |
| [UAS](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_GROWING_UNARY_STORAGE_ATLAS.md) | Assumption 1.2, Definitions 2.1–2.3, Theorems 2.4, 3.2–3.5, 4.2 and Definition 8.3 supply unary storage, actual raw-row guards, canonical joint-memory replay, 24-vertex increments and the explicitly unmet below-patch interface. They do not provide this fine constructor or a full fine-row join. |
| [SSA](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md) | Assumption 3.1, Definition 3.2 and §§10,13 give priced reciprocal ports, finite apparatus/naming, existing phase limitations and the five-occurrence setter. Prefix inversion and those obstructions are reused. |
| [ARC](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACTOR_LOCAL_RESERVE_RECOVERY.md) | Definitions 8.1–8.3, Proposition 8.4, Theorem 9.2 and Proposition 10.4 give the actual Zero site/ordinals, one fixed beta boot, original consumer/halt and $d+1$ source cells. These are original atomic-basis results, not a completed lower runtime. |
| [CAP](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md) | Definitions 2.1–2.2, 3.3 and §5 fix source16 ownership, actual Zero/Reserve/Raise and the same-source capacity semantics. A descriptor grants no private source token. |
| [PR57](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md) | PR57.D1, D3, D6 and D9 specify EX, one original receipt per original row, two-head metering, original observation and paid readout. Fine-event receipts are not imposed by those statements. |
| [FIB](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md) | §§2,9,10 distinguish free-tree syntax, serialization and additional execution semantics. The later appendices are not presumed absent. No two-operation physical claim is imported. |
| [NativeSerialEffective](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.lean) and [Scribe](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.scribe.cs) | OriginalCodeRealization and original_code_service_simulation, including private evaluator/prefix helpers, concern a supplied effective selector's Local/Read/ApplyRho/Stop simulation. No graph allocator or receipt price is supplied. |
| [NativeSerialMachine](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean) and [NativeFullSourceProducer](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.lean) | Actual replay and stationary acquisition, including private traverse/production_reads/stationary, retain their actual input assumptions. Proof-side subtree parameters are not installed source advice. |
| [AtomicPrefixParser](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/D5/S3/Arith/FibonacciAtomic/AtomicPrefixParser.lean) and [NativeConstructorArrays](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeConstructorArrays.lean) | Parsing and legal complete-array realization, including private inverse helpers, do not execute partial native cell construction. |
| [Virtual substitution compiler](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/docs/develop/theory/RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_VIRTUAL_SUBSTITUTION_COMPILER.md) | Its acquired-entrance Read lowering preserves its specified response task; it is not a storage-patch implementation. |
| [TypedFiniteViewKernel](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean) and [PredictiveMemoryMinimalQuotient](https://github.com/the-omega-institute/trureturing/blob/07a301c6d4fbb7c6bf19d8d9820b4f5e9d21c942/D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.lean) | Abstract edge/readout and update-factorization hypotheses must be supplied. They do not implement this constructor, provide ownership or equate fine observations with original $Q$. |

**Definition 10.2 (primary literature and library boundaries).** These
are supporting constructions and failure boundaries, rather than
substitutes for the explicit proof above.

| Source | Literature-attested correspondence and limit |
| --- | --- |
| Hassan, Mackie and Sato, [An Implementation Model for Interaction Nets, v1](https://arxiv.org/html/1505.07164v1), §§2,4 | Principal-port active pairs preserve free ports. Its LL0 explicitly has heap allocation by mkAgent/mkName, assignments, an equation stack and freeing. These are operational resources of that implementation model; they do not supply our current source/owner guard, coherent attachment, installed native code or price. |
| Plump, [Term Graph Rewriting, author manuscript](https://eprints.whiterose.ac.uk/id/eprint/243318/1/author_manuscript.pdf), §§1.3–1.4, DOI 10.1142/9789812815149_0001 | Term graphs represent sharing, and rewriting has construction/redirection and garbage treatment. Those graph-level operations do not constitute a paid serial reciprocal-endpoint implementation with retained original occurrences. A changed sharing or garbage representation requires a new observation/consumer correspondence. |
| Arrighi, Costes, Dowek and Maignan, [Space-time deterministic graph rewriting, v2](https://arxiv.org/html/2404.05838v2), local operators and Remark 7 | A local replacement and unchanged exterior must agree on their common frontier; border vertices/edges cannot simply be changed. This motivates the frame obligation proved in Theorem 3.4, but their atomic local operators do not expose this construction's internal slots or provide original authority. |
| Bennett, [Logical Reversibility of Computation](https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html), history/copy/reverse construction | History and copying use real tape/work; history recording is explicitly suspended during the described copy stage. Logical reversible simulation supplies neither a recursively self-paying fine receipt mechanism nor current historical rights. Our bound is allocation conservation, not a thermodynamic theorem. |
| Leroy, [Formal verification of a realistic compiler, author manuscript](https://xavierleroy.org/publi/compcert-backend.pdf), §3.7, Definitions 10–12 | Initialized state relations, matching observable traces and final-state agreement are explicit simulation premises. A naive finite-star match can lose divergence through infinite stuttering; the stated star simulation uses a well-founded decreasing measure. Such compiler correctness does not supply our current permissions, inverse fine cuts or material/work bill. No whole-runtime simulation theorem is inferred from this isolated constructor. |
| [Pinned mathlib StateTransition](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Computability/StateTransition.lean), Respects, tr_reaches, tr_eval | Respects demands positive matching fragments and termination agreement on related starts. Reachability/evaluation transport assumes that relation. It does not manufacture intermediate-state inverses, vertex production, native permission or a cost theorem. |

**Convention 10.3 (verification and attained statement).** The results
are the explicit 25-cut literal constructor, its current-guard/frame
and phase-sensitive actual-image inverse, same-fragment work/material
formulas, and the conditional retained-receipt bound with a same-source
finite Reserve consequence. Their proofs are ordinary mathematics.
They do not certify a Lean application, material native execution,
installed controller, complete EX/full-row lowering or completion of
the full original programme. All unresolved joins are the substantive
obligations in §9, rather than effects hidden in a constructor-completion label.

## 追加锚（本行以下为增补区）
