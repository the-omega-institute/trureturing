# Recursive relational observation: monotone LAB indexed execution

## 1. Two distinct owned objects and finite execution domains

**Definition 1.1 (sources and mathematical supply).** Write AA for
[Atomic Generation Acquisition](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GENERATION_ACQUISITION.md),
UJB for [Unified Joint Law Bridge](RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md),
and PG for [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
The logical work syntax is the ordered free binary tree on
$\alpha,\beta$, with exactly AA17.1's guarded changes

$$
P_p:\alpha\longmapsto\beta,\qquad
S_p:\beta\longmapsto\langle\beta,\alpha\rangle.
\tag{ML.1}
$$

A work root is not the observation root. The latter, denoted $o$, is one
fixed stationary member $F_1(z)$ of UJB5.1's entire promise
$\mathcal C_N$, $N\ge4$. Its sole source-dependent port is precisely
UJB5.2's original-root Read, with replies
$\alpha,\beta,\mathsf b,\bot$. Work changes never change $o$. A work
read is an authorized field inspection of owned work material; it is not
an additional observation-source port. In probabilistic statements $o$
has the original once-shared full-injection law, with prior
$\theta=a/b\in[0,1]\cap\mathbb Q$, $0\le a\le b$, $b>0$.

The literature supply is Neary–Woods–Murphy–Glaschick,
[*Wang's B machines are efficiently universal*, arXiv:1304.0053v2,
Definitions 3–6, Lemma 5, Theorems 1 and 7, §§2–3.1.3](https://arxiv.org/pdf/1304.0053v2),
abbreviated NWMG; its exact scope is in
[the bibliography note](../../../Library/Computability/nearywoodsmurphyglaschick2014wang.md).
Only its effective tape simulation is used as an intermediate result.
The work representation, guarded instruction correspondence, paid framing
and original-source UJB consumer below are `repo-derived` ordinary
mathematics. They assert neither a new universality theorem nor a new
proof of UJB16–17.

**Assumption 1.2 (paid installation ML-I).** Use AA20.1's actual
allocation, current exclusive work rights, source parent/left/right
fields, separate null header slots, actual header/tape objects and
charged finite bit buffers. An allocated work root is a known actual
$\alpha$, not an arbitrary integer interpreted as a pointer. The
installation supplies reference equality, null/arity tests, individual
field access, reference-register assignment, a finite transition graph,
bit input/output, End and local acknowledgement. Actual references and
their rights are returned by allocation; their storage and transport
widths are charged. The finite driver depends on the program and public
syntax alone. It contains no table indexed by the hidden source, hidden
injections, unobserved input or future replies.

Every successful work growth uses the material template and ancestor
maintenance of AA20.2. Thus a split has its real routing header, and
each event appends one real side cell at every proper logical ancestor.
No routing record is suppressed on the ground that it is unnecessary
for a tape instruction. Fresh evaluator jobs receive separately paid
known roots; earlier roots, source vertices, headers and routing cells
are retained. No deletion, graft, reset or reinterpretation of an old
root as fresh occurs. Clearing an auxiliary buffer clears its live
fields or marks it reusable; it does not erase work growth or an
authentic receipt.

The bound original port $o$, its continuing Read authority and its
return connection are supplied separately. A successful call accepts
the actual finite operand, produces that root's actual reply and
returns it in an occupied latch. No numeral-to-source cast is provided.
The observer has no authority to grow $o$, inspect preparer fields,
reroot, copy it or request fresh samples. Grants, refusal and timing
have exactly UJB5.2's source-blind scope. No concurrency, crash,
revocation, visible exhaustion or missing acknowledgement is included.
For every finite prefix claimed to complete, the finitely many required
objects and primitive completions are supplied. A missing input suffix
or actual reply leaves a waiting state, with no invented completion.

**Definition 1.3 (bilateral B configurations).** A finite B program is
$W=(I_0,\ldots,I_{q-1})$, $q\ge0$, with instructions $L,R,M,J(j)$,
$0\le j<q$. Its configuration is $(\tau,h,c)$, where
$\tau:\mathbb Z\to\{0,1\}$ has finite support, $h\in\mathbb Z$,
$0\le c\le q$. At $c=q$ it is halted. L/R move the head by $-1/+1$;
M replaces $\tau(h)$ by one, including an unchanged repeated mark;
these instructions advance $c$ by one. J(j) sets $c=j$ on one and
$c=c+1$ on zero. A supplied finite input $x=x_0\cdots x_{m-1}$ has
$h=c=0$, $\tau(j)=x_j$ for $0\le j<m$, and zero elsewhere. The
empty program halts at once. The assertions quantify every such finite
program, every finite input, every finite initial segment of its unique
run and every internal initial segment of its realization. Termination
of the infinite abstract computation is never a premise for a finite
prefix assertion.

## 2. A birth-legal bilateral comb and actual loading

**Definition 2.1 (encoding ML-C).** Put $B_0=\alpha$, $B_1=\beta$ and,
for a finite bit word $u$, define

$$
K(\varepsilon)=\beta,\qquad K(bu)=\langle K(u),B_b\rangle,
\qquad T(u_-,u_+)=\langle K(u_-),K(u_+)\rangle.
\tag{ML.2}
$$

The right cells at $RL^j$ represent positions $j\ge0$, and the left
cells at $LL^j$ represent positions $-j-1$. A cell is a branch, its
right logical leaf is its bit, and its left child is the next cell or
the still unexpanded $\beta$ frontier. A physical unary marker inside
a logical $\beta$ is not a tape cell. Write $n_\pm=|u_\pm|$,
$C=n_-+n_+$ and require $n_+\ge1$. The represented interval is
$[-n_-,n_+-1]$; unrepresented positions have bit zero. The head is
an actual branch reference in that interval, with a retained arm bit.
The coordinate $h$ is decoded from the path; it need not be stored as
an unbounded control label. A B program counter is a vertex of the
finite installed program graph, not an uncharged arbitrary integer.

**Definition 2.2 (loader ML-L).** At a new actual root execute
$P_\varepsilon,S_\varepsilon,P_R$. Both arms are now $\beta$
frontiers. Let $d=\max(1,m)$. In increasing $j<d$, split $RL^j$.
Its new right leaf $RL^jR$ is zero; if $j<m$ and the actually received
$x_j=1$, promote that leaf. Each split is fully maintained before the
next event. Keep the actual root and the first right-cell reference;
return the head there, arm plus, counter zero. All of $x$, its framing,
and any compiler input transformation have actual readable backing
before a bit is used. Zero bits are represented by allocated leaves,
not by unbacked promises of future storage.

**Theorem 2.3 (guarded initialization and finite input).** For every
finite $x$, ML-L is a finite legal LAB history, constructs
$T(\varepsilon,x0^{d-m})$, and decodes the initial B configuration.
Every successful growth prefix is legal. With $b_x$ the number of ones
in $x$, it has exactly $2+b_x$ promotions and $1+d$ splits. All present
$\alpha$ leaves have right-ending logical addresses.

Proof. The first promotion enables the root split, and that split gives
the right $\alpha$ enabling $P_R$. Initially $RL^0$ is therefore a
$\beta$ frontier. At each iteration its split makes the next frontier
born $\beta$ at L and the bit born $\alpha$ at R. The optional
promotion sees that very fresh right leaf. Induction over $j$ gives
(ML.2), the stated guards and counts. No other logical position is
altered. The root and all next-frontiers are $\beta$ or branches;
zeros occur only at cell right children. The AA17.2 reachability
condition is satisfied at each complete event prefix. AA20.2 supplies
the legal material subphases and maintenance between these events.
The blank extension and the retained first right cell give exactly
Definition 1.3's initial tape and head. $\square$

## 3. Guarded instructions, busy cuts and the converse

**Definition 3.1 (finite instruction graph ML-B).** At an instruction
boundary ReadyB the head, root, arm and program counter are valid,
all routing appends are complete, and no pending bit or growth is
uncommitted. For a nonhalted instruction the phases are Fetch,
Inspect, Plan, optionally Grow, Maintain, ReturnHead, Commit and
ReadyB. The finite graph has a copy of these phases for each program
location and a finite number of pending subphases. All unbounded
backing belongs to material fields or finite bit lists.

Inspect for M or J reads the head's actual right bit's logical arity.
For M on zero call $P$ at that right leaf; on one make no growth.
For J take its installed one/zero successor. For L or R, retain the
old head and arm and choose the following actual path:

$$
\begin{array}{c|c|c}
\text{head arm}&L&R\\\hline
+&\text{parent, or root.L at position }0&\text{head.L}\\
-&\text{head.L}&\text{parent, or root.R at position }-1
\end{array}
\tag{ML.3}
$$

The parent-equals-root test detects the two exceptional crossings.
At a crossing switch the retained arm. A parent destination is already
a cell. A next-frontier or root-arm destination is tested: if a branch,
use it; if a $\beta$ frontier, execute S there and use that new cell.
Its bit remains zero. No movement can have an $\alpha$ destination.
All decisions use actual links and equality with the bound root.

Grow is exactly AA20.2's reserve and edit protocol. Pending retains
event kind, actual target, old head, proposed head, old/new arm,
next counter and maintenance cursor. Maintain appends at each proper
ancestor and retains incomplete append subphases. ReturnHead restores
the proposed actual head from its saved reference after maintenance.
Commit installs the selected head, arm and next counter and releases
the instruction's scratch. No next instruction or external query is
enabled during these phases. There is no P attempt on a marked bit and
no S attempt on a cell branch. Counter $q$ enables the halt return
handler, with no further B instruction.

**Definition 3.2 (busy interpretation).** A busy state decodes the last
committed $(\tau,h,c)$, the instruction it is completing, any one
pending logical edit, the intended successor and the material subphase.
Before an edit it has the old comb; after an edit it has the new comb
with incomplete routing maintenance permitted. While a split's physical
attachments are being initialized its finite template phase and actual
fresh references are retained; the old comb with this pending template
is the interpretation, rather than a claim that an unfinished attachment
is a complete logical tree. No unrelated field change is admitted.
The source's completed logical event occurs at template completion;
the instruction commits only after all its routing work. Thus busy
interpretation records exactly which state is old, which is intended,
and which material writes have really happened. It never discards the
pending phase as a zero-time B instruction.

**Theorem 3.3 (every finite B prefix has a legal realization).** Under
ML-I, for every $W,x$ and every $s\ge0$ not exceeding the number of
instructions in the abstract run, ML-L followed by $s$ ML-B macros
finishes in finite time and decodes its $s$th B configuration. The
work source remains an ML-C comb at instruction boundaries. All its
logical event prefixes satisfy the actual guards (ML.1), all internal
prefixes have Definition 3.2's interpretation, and every newly visited
position is backed by a real blank cell. These assertions apply to all
finite prefixes of a nonhalting computation.

Proof. Theorem 2.3 is the base case. Assume the boundary invariant.
Inspect terminates on an actual bit leaf. A successful mark is P at
the right-born zero, changing exactly $\tau(h)$; a repeated mark
does nothing and still advances control. A jump leaves tape and head
unchanged and takes exactly the successor selected by $\tau(h)$.
For a move away from zero within an arm, the left chain increments
the arm's depth and hence the absolute coordinate by one. Toward zero,
the parent chain decrements it. The two root crossings give
$0\mapsto-1$ and $-1\mapsto0$ with the stated arm change. This proves
each entry of (ML.3) realizes the right bilateral neighbor. A tested
frontier is born $\beta$, so S is enabled and creates a real zero bit;
an existing cell is used unchanged. No tape value outside the old or
new head changes.

The target has finitely many actual proper ancestors. Reserved
material and the AA20 protocol complete the finite edit, append once
at each ancestor and return to the saved head. Each microphase either
executes a specified primitive, shortens a finite parent traversal or
advances a bounded template; none invokes an unsupplied evaluator.
Maintained routing words have exactly AA19.1's actual side meaning.
The pending fields describe each incomplete case before Commit,
and Commit restores the invariant. Induction gives the assertion for
every finite $s$, without assuming an eventual halt. $\square$

**Theorem 3.4 (completed-macro converse and halted output domain).**
Any finite ML-L/ML-B execution beginning with the same actual input,
obeying these phases and reaching $s$ instruction commits, decodes
exactly $s$ successive instructions of $W$ on $x$. Its next boundary
is halted exactly when the decoded counter is $q$. It cannot create
an extra B step by repeating a mark, a test, maintenance or an
unfinished instruction. A run stuck on a missing primitive completion
has no claimed next committed configuration.

Proof. The guarded shape fixes which cell and bit each saved reference
denotes. The only template-changing choices are the Inspect/Plan
cases already exhausted in Theorem 3.3. Each has that one B successor,
and Commit is reachable exactly once after its prescribed finite
maintenance. Finite deterministic control fixes all other subphases.
Induction on commits identifies the entire decoded prefix. Repeated
M has one commit and zero promotions, whereas a paused Maintain
has zero additional commits. The counter and halt convention now give
the halt assertion, including $q=0$. $\square$

## 4. Finite words, exact arithmetic and the compiled consumer

**Definition 4.1 (finite framing ML-F).** For $n\in\mathbb N$ let
$\operatorname{bin}(n)$ be its usual binary word, with
$\operatorname{bin}(0)=0$, and set

$$
\begin{aligned}
V(u)&=1^{|u|}0u,& U(n)&=V(\operatorname{bin}(n)),\\
\operatorname{List}(u_1,\ldots,u_t)&=U(t)V(u_1)\cdots V(u_t).
\end{aligned}
\tag{ML.4}
$$

Integers use a sign bit and U of the absolute value, with zero sign
zero. Rationals use sign, U of the numerator magnitude and U of a
strictly positive denominator; reduced output uses coprime numerator
and denominator, with zero represented by $0/1$. An address is V of
its L/R bits. Replies are $00,01,10,11$ for
$\alpha,\beta,\mathsf b,\bot$. Masks use exactly $15N$ indicator
bits in original sample/coordinate order, followed by the acquired
values of the selected coordinates in that same order. A cylinder
uses the same form; an explicit conflict flag denotes an empty event.
A cylinder starts with one conflict bit: one is the empty event with
no following mask, while zero is followed by the entire mask/value word.
This permits every within-slot mask, an empty mask, and null proposed
conjunctions. Lists have their stated lengths; no omitted trailing
zeros are inferred.

A service reply is a two-bit kind followed by V of its finite payload:
00 is BadFrame with empty payload, 01 is Arithmetic, 10 is an original
Read reply with its two-bit value, and 11 is Closed with empty payload.
An Arithmetic payload is List of its $3+3t$ rational words in (ML.5),
then a positivity bit, then List of the $t$ conditional rational words
if that bit is one. A zero positivity bit denotes NullEvidence and
has no following ratio list. A response-distribution request uses a
fixed list of its four candidate response cylinders, in reply-code
order. Every payload is therefore finite and unambiguously delimited.

Receive latches one real bit, appends it to a charged linked bit buffer,
then clears that latch. Unary length marks and remaining counters are
backed finite bit lists. A proper frame prefix waits; invalid completed
syntax returns BadFrame. A completed reply is constructed in a finite
buffer, sealed, traversed bit by bit to the actual output, followed by
End and the local acknowledgement. Return clears reusable request,
traversal and output scratch, preserving work roots and permanent
receipts, then enables the same installed entry. An unfinished Print
retains its cursor and unsent suffix. Acknowledgement has no hidden
source-dependent value.

**Definition 4.2 (finite output observation).** For an arbitrary B
program, a caller may supply finite $l\le r$ and request the halted
counter, signed head and bits in $[l,r]$. At halt, descend each arm
up to its actual frontier, copying its finite bits with their order;
positions outside the backed interval are zero by the encoding. Use
backed signed counters to select $[l,r]$, form (ML.4), Print and
Return. This is an explicit finite encoded output, not an assertion
that an arbitrary B computation's intended numerical answer is known.
It adds neither tape overwrites nor a decision whether a nonhalting
program will halt.

**Definition 4.3 (bit algorithm ML-A for UJB).** The arithmetic input
word contains U($N$), the rational $\theta$, an indexed cache $D$
and a finite list $E_1,\ldots,E_t$ of cylinders. Require $N\ge4$;
all other integers and all selected values are represented as in
ML-F. The output is

$$
Z_0^*(D),\ Z_1^*(D),\ Z^*(D),\
\bigl(Z_0^*(D\wedge E_v),Z_1^*(D\wedge E_v),
 Z^*(D\wedge E_v)\bigr)_{v=1}^t,
\tag{ML.5}
$$

together with NullEvidence if $Z^*(D)=0$, or all reduced ratios
$Z^*(D\wedge E_v)/Z^*(D)$ otherwise. The algorithm below is fixed
independently of $N$, $D$, $\theta$ and the original source.

For each required normalizer, enumerate restricted-growth words
$(a_1,\ldots,a_N)$ with $a_1=0$ and
$0\le a_j\le1+\max_{h<j}a_h$, in lexicographic order. They are
exactly the partitions of $[N]$, ordered by their first members.
Enumerate the left and right partitions in nested loops, discarding
left block counts above 72 and right counts above 243. Scan every
original $j$ to obtain its block incidence and the intersection of
all restrictions at that block. For each of the 128 left or 256 right
labels test each required coordinate and form the allowed-label table.

For $t'$ distinguished blocks use two arrays indexed by subsets of
$[t']$. Initialize $f_0(\varnothing)=1$ and all other entries zero.
For each successive label compute into the other array, reading only
the old array,

$$
f_v(S)=f_{v-1}(S)+
 \sum_{b\in S:\ell_v\text{ allowed at }b}f_{v-1}(S\setminus\{b\}).
\tag{ML.6}
$$

The final full-subset entries give $L_p(D),R_q(D)$. If either is
zero, skip that partition pair before the type-map loops, paying
this exact zero test. Its entire contribution is zero. Enumerate all
type maps in the orders of UJB15.2: the 36 affine lines and 27 points
for source zero, and the nine field values on each side for source
one. Points and field coordinates are lexicographic ternary words;
lines are ordered first by the four displayed directions of UJB15.2,
then by the least point on the line. Incidence is tested by the
displayed finite-field equations. For each map initialize occupancy
counters to zero; scan all distinguished vertices, multiply the
remaining literal capacity and increment that type's occupancy. An
exhausted capacity or failed required incidence contributes zero.
Sum these products to compute exactly $J_i(H_{p,q})$. Use capacities
$(2,9)$ for source zero and $(8,27)$ for source one. Repeated
incidences are tested without removing their original sample indices
from the denominator. Accumulate

$$
\frac{J_i(H_{p,q})L_p(D)R_q(D)}
 {1944^N(128)_{|p|}(256)_{|q|}}
\tag{ML.7}
$$

for each $i$. Finally mix with $(1-\theta,\theta)$, test the exact
numerator for zero and form only the permitted ratios. Conflicting
restrictions give zero, including those in a cylinder conjunction;
zero terms are never divided by zero. No full hidden injection or
unread realized bit is an input to any loop.

**Definition 4.4 (finite bit realization ML-T).** Use finite-alphabet
tape records separated by delimiters for the input, nested-loop
counters, current partitions, occupancy vectors, allowed tables, the
two subset arrays, integer work and the output. All indices and
integers are little-endian binary records with an end delimiter.
To look up a record, scan from its delimiter roster and increment a
backed counter until the desired index; to extend a record, shift its
finite suffix right one square. Boolean words and fixed ternary
coordinates are manipulated one symbol at a time. Successor with
carry and comparison from the highest nonzero bit implement counters
and loop tests. The partition-loop test checks the displayed maximum
condition by a scan of the finite prefix. Binary subset successor and
bit tests enumerate all subsets; testing a membership never invokes
a set-valued oracle.

Nonnegative integer addition scans the two bit records with carry;
subtraction on a proved larger operand uses borrow. Multiplication
adds the shifted first operand at each one of the second. Division
with remainder scans the dividend from its highest bit, doubles the
current remainder, adds the next bit and subtracts the divisor when
possible. Its remainder stays below the positive divisor. Euclid's
repeated remainder algorithm reduces fractions; a nonzero remainder
strictly decreases its positive divisor. Rational addition and
multiplication use cross-products, signs and this reduction. Comparing
to zero tests numerator bits. Constants 2, 9, 8, 27, 128, 256, 1944
and the finite-field tables are public finite code.

These scans give a deterministic finite-alphabet single-tape Turing
machine for ML-A: every cursor is a head position or a marked field,
every loop variable is a finite record, and each individual scan has
finitely many symbol/carry states. Replace this finite alphabet by
equal-length binary blocks and perform each symbol access by a
bounded block scan; blanks and head alignment are part of that
encoding. At final output place the framed answer between two distinct
encoded delimiters, with the simulated head at its first delimiter,
and enter halt. This fixes an effective binary TM family without
assuming an arithmetic/evaluator primitive.

**Theorem 4.5 (actual acquired-input evaluator).** For all finite
$N\ge4$, represented rational $\theta\in[0,1]$, every indexed
mask/value assignment $D$, every finite cylinder list, including
inconsistent conjunctions, ML-A terminates with (ML.5). ML-T, the
NWMG effective compiler and ML-L/ML-B therefore give a finite legal
owned-LAB computation of these answers from the actually received
finite input. Its encoded output is really printed and returned under
ML-I. No exact decision on an unrepresented real is used.

Proof. Each partition, type-map, label and subset loop has an explicit
finite domain, even as $N$ varies without a common upper bound.
Occupancy products are the falling factorials in UJB15.3, and (ML.6)
is exactly UJB16.1's old-array recurrence. Consequently (ML.7) is
UJB16.2's actual-source normalizer on every assignment, including zero
ones. UJB17.1 identifies the positive ratios with the original indexed
conditional cylinders. This reuses those probability theorems; the
new step is their realization on the specified owned substrate.

Every operation described in ML-T is a finite bit scan or a loop on
a decreasing finite positive integer. In particular Euclid cannot
diverge and no denominator in (ML.7) vanishes, since the partition
caps were tested. This proves termination of the tape computation.
Use NWMG's supplied simulation with the explicit monotone metadata
convention of Definition 4.6. At a simulated instruction boundary the
selected record has one head triple and precisely the old finite window.
The rule is selected by that triple and the finite simulated state.
Marking its neighbor, or the corresponding new guard, selects exactly
the next head. A consumed flag changes only the copying cursor, never
the old head/value triple. Hence, when a triple is copied, its value
is the old value except at the unique old head, where the rule's write
value is used. The new-head flag supplies exactly the selected new head.
The two blank guards extend the window by one on each side. Induction
over its consumed prefix proves that every copied triple has the
required successor value and head flag. After the right guard and end
are complete, the active/retired handoff establishes the same invariant
for the next simulated instruction. During the handoff the finite phase
identifies which record is old and which is intended; there is no
assertion of a unique active record at an unfinished cut.

Each shuttle is a scan over the two finite adjacent records. Each
iteration consumes one old triple, so it terminates; every written bit
is zero-to-one or an unchanged one. The block operations expand to
ordinary binary non-erasing transitions as specified below. NWMG's
thirteen-instruction state blocks then give the B program without
changing their transition correspondence. These facts prove forward
simulation and the completed-copy converse, rather than merely an
existence of unspecified output delimiters. At halt the selected record
is the actual returned header. Decode the B 10/11 symbol pairs, then
its data head/value triples, and finally ML-T's output delimiters.
The only value of each output bit is the value in this actual copied
tape; a table of arithmetic answers supplies none of it. Both input
conversion and these decoding scans have finite readable backing and
are charged independently of the arithmetic tape steps.
Theorems 2.3 and 3.3–3.4 realize the resulting B run and
its actual finite tape. ML-F then gives Print, acknowledgement and
Return. At zero evidence the only conditional answer is the explicit
NullEvidence tag. $\square$

**Definition 4.6 (selected lowering ML-N).** First fix the finite
binary erasing machine of ML-T, with states $0,\ldots,k$, start zero
and sole halt $k$. Its transition row for each nonhalted state has
the two ordinary read-zero/read-one rules. A finite window initially
contains the supplied word, or one zero square for the empty word;
its first square represents coordinate zero. The block copier below
retains NWMG's head/value triple and supplies explicit monotone
navigation metadata. This metadata is part of the chosen owned
construction, not an additional theorem or transition table quoted
from the paper.

Partition the binary non-erasing tape into eight-bit blocks. Number
bits zero through seven. Bits 0, 1 and 2 are respectively the header,
data and end type bits; a completed block has exactly one type bit.
An unused block has all bits zero. The remaining used fields are:

| Block | Used fields |
| --- | --- |
| Header | bit 3 active, bit 4 retired, bit 5 the next left-guard head |
| Data | bit 3 old head, bits 4–5 value zero/one as 10/01, bit 6 consumed, bit 7 next head |
| End | bit 3 the next right-guard head |

The initial word is one active, unretired header, one data block per
initial square, and one end block. Exactly the first data head flag
is one. All consumed, next-head and guard flags are zero. The
non-erasing head starts at the header. Its finite state contains the
simulated state. At a completed simulated step, the head again rests
at the selected active header, with that step's next simulated state.

For a nonhalted state use the following fixed finite block protocol.
Scan right to the unique data head and inspect its value pair to
select the transition rule. The rule's write bit, direction and next
state are retained in finite control. Move one block in its direction.
At a data neighbor set next-head bit 7; at the header or end neighbor
set its designated new-guard head bit. Return left to the old header,
read its guard flag, find its end, and begin the fresh record immediately
after that end. Write the new header with active and retired both zero,
then a zero-valued left guard with the head flag just obtained.

From the fresh frontier shuttle left to the old active, unretired
header, passing the new inactive header. Scan right past the consumed
prefix. If the next block is data, read its next-head flag and its
value, substituting the rule's write value exactly when its old-head
flag is one. Set its consumed bit and carry these two bits in finite
control. Scan right to the first unused block, passing both old and
new blocks. Append the corresponding data block there and repeat.
If the scan reaches the old end, copy its guard flag to a fresh
zero-valued right guard, append a new end, and finish copying.

For handoff, scan left to the new header and set its active bit;
scan left to the old header and set its retired bit; return right
to the new header and enter the next simulated state. No next simulated
step is enabled until this handoff completes. Old head/value triples,
records and metadata are retained. A halt state performs no copying.
The protocol uses no reference arithmetic, record-length oracle,
mutable unbounded finite-control label or tape erasure.

Each block operation has an explicit binary expansion. To inspect bit
$j$, move $j$ squares right, branch on the bit while preserving it,
move one square right, and return $j+1$ squares left with the branch
in finite control. To set bit $j$, use the same route and write one.
To move one block, take eight ordinary moves. Tests of the three type
bits and the active/retired flags form the finite scans above. Thus
this is a finite transition-graph construction from the erasing table,
with only the six permitted non-erasing rule forms. All state names
are finite tuples of the simulated state/rule, block phase and bounded
bit offset. Their enumeration fixes an ordinary finite binary table.

After $s$ completed copies, an initial window of $m\ge1$ squares
has active coordinates $[-s,m+s-1]$. There are $s+1$ records, with
$(s+1)(m+s)$ data blocks and $2(s+1)$ header/end blocks in total,
hence $8(s+1)(m+s+2)$ retained binary squares in these records.
Counting retired headers before the returned active header determines
$s$ and hence the coordinate offset. Reading its data through its
own end determines the represented tape and unique head, without
choosing a record by an external answer or unrepresented length.
These are mathematical decoding scans; their actual buffers, counters,
cursors and intermediate storage remain charged by ML-Cost. Each copy
uses $O((m+s+1)^2)$ binary moves, so $s$ simulated instructions use
$O(s(m+s+1)^2)$ moves, retaining the initial input length. This is
consistent with, and does not strengthen, the supplied cubic quotation.

Apply NWMG's unchanged thirteen-instruction construction and 10/11
symbol encoding to this non-erasing table, with its terminal M. The
result is $W_U$. The B head initially stands at the first encoded
header bit, at coordinate zero. The source halt returns at a header
whose first bit is already one; the terminal M therefore changes no
encoded value. ML-L loads the actual finite encoded input and ML-B
executes the result. The finite code depends only on ML-T, including
its input/output grammar; it is not reselected for $N$, masks, the
original source or acquired replies. No arbitrary adaptive/oracle
controller compiler is included or needed by the session handlers.

## 5. Authentic continuation at the unchanged original port

**Definition 5.1 (online state ML-R).** An online session retains the
same actually bound $o$, its grant, public $N,\theta$, an ordered
receipt chain $\Gamma$, an indexed cache $D$ and finite service control.
Initially $\Gamma$ and $D$ are empty. An already attained prefix can
instead be supplied by its actual retained receipt objects bound to
this very port, with their readable backing and current rights; this
is an input-provenance premise, not a numerical reference conversion.
Import copies every actual record in order and pays its entire input
and storage cost. Prior acquisition and prior retained material remain
part of the account. A bare mathematical cache can always be submitted
to the offline arithmetic handler, but is not certified as this
session's attained history merely by having positive normalizer.

Each receipt has payload

$$
\operatorname{Rec}(w,v)=V(w)\operatorname{code}(v)
\tag{ML.8}
$$

and a next link. Choose one receipt object with three reference fields:
payload head, payload tail and next receipt. Its payload uses ML-Cost's
linked bit cells. The chain header has three reference fields: actual
$o$ binding, first receipt and last receipt. The binding is retained
once; it is not a public source identity numeral. Every
occurrence has its own record, including repeated operands and replies.
The indexed cache is one linked buffer of exactly $30N$ bit cells:
first the $15N$ mask bits, then the $15N$ value bits, with unselected
values ignored. Its head/tail header has two reference fields.
Merging a repeated consistent bit changes no
mask but never deletes its receipt. Under the stationary contract a
contrary repeat cannot be an actual successful return. Such a proposed
arithmetic input is an empty event, with normalizer zero.

**Definition 5.2 (real call and receipt phases ML-Q).** The session
entry accepts one of three two-bit command tags: 00 is offline
Evaluate with V of the complete ML-A input word, 01 is actual Read
with V($w$), and 10 is Predict. Predict has one variant bit: zero
followed by V($w$) requests the four response probabilities, and one
followed by List of cylinder words requests their probabilities at
the current cache. Malformed sealed payloads return BadFrame.
For a response request the classifier constructs four cylinder words:
a constant reply has the universal event at its own code and the
empty-event flag at the other three; an informative reply table has
its corresponding one-bit restriction at each of its two possible
codes and the empty-event flag at the remaining codes. Thus the
response calculation uses only ML-A's explicit cylinder input format.
The remaining tag closes the entry after printing its finite closing
reply. Public initialization is U($N$) followed by the rational prior;
the actual $o$ connection is installed physically, never encoded in
these public bits. Return reopens the same entry and binding except
after Close. The arithmetic handlers allocate fresh paid work roots,
load actual ML-T/NWMG input and use Theorem 4.5. They read no port
reply on behalf of Predict and do not modify the original source.

For actual Read the finite phases are Receive, SealOperand,
CallOriginal, WaitReply, Capture, AppendReceipt, UpdateCache,
BuildReply, Print, Ack and Return. Receive and SealOperand obtain the
entire actual $w$ and retain its backing. CallOriginal transmits this
very word on the retained port, with its current grant. Pending
contains the bound handle and operand. WaitReply has no transition
manufacturing a value. Capture copies the actually returned two-bit
reply to occupied pending backing before releasing the return latch.
AppendReceipt allocates and initializes the payload and links, links
it at the true chain tail and only then advances the tail. Its
unlinked/linking/tail-advanced phases and references are retained.
UpdateCache classifies this actual $(w,v)$ by UJB5.3's complete
spine/slot/marker table. A constant adds no bit. An informative slot
suffix adds the uniquely decoded bit at

$$
j=1+\lfloor(b'-1)/15\rfloor,\qquad
h=1+((b'-1)\bmod15),\qquad 1\le b'\le15N.
\tag{ML.9}
$$

The classifier scans the finite operand, counts the initial R's,
checks its remaining finite suffix against UJB.7705, and checks the
fixed terminal marker if needed. Long extensions of leaves are still
classified; the menu is not cut off at canonical probe lengths.
Original indices are never replaced by equality classes of observed
values. The reply backing is then sealed and printed. Return restores
the original input and output entry, clears only scratch and retains
$o$, its grant, $\Gamma$ and $D$. No new input or work-source growth
interleaves with a pending original call. A completely received word
whose actual call has not returned has no acquired reply or committed
cache update.

**Theorem 5.3 (same-source receipt and cache correspondence).** For
every $N\ge4$, every $z\in\{0,1\}^{15N}$ and every supplied finite
sequence of actual Read operands, including arbitrary long operands,
repeats, off-path addresses and partial slots, each completed ML-Q
handler returns the original-root reply of $F_1(z)$. Its receipt chain
is exactly the ordered actual address/reply occurrences, and its cache
is exactly their consistent indexed restriction. All prior receipts
persist. The original root and the once-shared injections are unchanged.
Every internal prefix retains the actual unconsumed input, reply,
record-linking and return obligations.

Proof. Receive cannot use an unreceived bit by ML-F. CallOriginal
uses the retained original handle and the sealed word; ML-I supplies
exactly that port's value and no other writer. Capture cannot clear
the only copy before a backed copy exists. The append order makes
the new record reachable before it can become the chain's advertised
tail; no subsequent call is enabled in an intermediate subphase.
This proves the authentic chain invariant at Return, occurrence by
occurrence, including repeats.

UJB5.3 classifies every finite word. Each informative two-valued table
entry is injective in its one designated $z_{b'}$, even when one
reply is absence. All other entries are constant. The finite scan
therefore inserts exactly that actual bit at (ML.9), or no bit.
Repeated consistent information leaves the same intersection and
keeps its new chain occurrence. No source operation appears in any
handler phase. Induction on completed handlers proves the assertions,
and the explicitly retained phase fields give the prefix assertion.
Nothing in this argument requires positive prior mass; the entire
promised family retains its literal Read semantics. $\square$

**Theorem 5.4 (real evaluation and predictive continuation agree).**
Fix the original UJB5.1 probability law, including each entire
injection sampled once, and rational $\theta$. At every attained
session prefix with $Z^*(D)>0$, Predict computes the exact response
distribution of every next original operand and the exact conditional
mass of every finite indexed cylinder. An actual subsequent Read
handler obtains its value from $o$, rather than from this distribution.
After its real return the newly evaluated cache law is UJB17.1's
same-source continuation. The claim includes old-slot rereads,
partial-to-complete transitions, equal observations at different
indices, constants, informative absences and null proposed replies.

Proof. Theorem 5.3 identifies the earned restriction at each original
index, without a new label map, sample or source. Theorem 4.5 computes
the exact UJB16.2 normalizers of that restriction and each proposed
extension. UJB17.1 gives their ratio on positive evidence. For a
constant reply its probability is one or zero; for an informative
suffix its two probabilities are precisely the two indexed bit
conjunction ratios. They sum to one. A recorded bit yields the
actual old value with probability one, while a contrary proposed
repeat has numerator zero.

Upon an actual new bit return, Theorem 5.3 conjoins that one restriction
once. The partly acquired slot's likelihood is replaced by the full
new conjunction, rather than multiplied by its old partial likelihood
again. UJB17.1 then identifies the updated whole indexed law. For any
finite successive address selection using only the actual returned
records, induction conditions on each real finite prefix; the
normalizer ratios telescope on positive branches. This proves
agreement for those realized conditional cylinders without compiling
an arbitrary oracle controller. At a zero-evidence cache the arithmetic
handler returns the zero normalizer and NullEvidence; ML-Q still
has its literal port semantics, but no conditional probability is
assigned there. The original prior and shared full maps have not been
replaced by independent coordinate or completion draws. $\square$

**Proposition 5.5 (all finite masks remain in scope).** Every consistent
indexed mask assignment has a finite ML-A input frame, regardless of
its probability under the prior. If it is the restriction of an actual
$F_1(z)$, it can be earned at the original port with at most its
number of selected coordinates additional calls, using
$R^{b'-1}LL$ for bit $b'$. Each such call's full operand, reply and
receipt is paid. Completion of all slots and later replay are allowed;
no wholly unread sample is needed for this direct evaluator.

Proof. The fixed-order mask encoding represents all $2^{15N}$ masks
and all their assignments. At $R^{b'-1}LL$, UJB.7705 returns
$\beta$ for zero and $\mathsf b$ for one, so each selected bit is
actually acquired with one call. Theorem 5.3 inserts it at its original
index. This statement acquires only the specified actual restriction;
it does not certify an arbitrary submitted assignment as attained.
The unread-slot condition belongs to UJB17.2's support-closure inverse,
which is not used to replace $D$. $\square$

## 6. One simultaneous account for this installation

**Definition 6.1 (charged finite prefixes ML-Cost).** A resource vector
has separate coordinates for work promotions/splits, source vertices,
routing headers/cells, buffer cells, object allocations, initializations
and field writes, field reads, navigation links, null/equality/arity/bit
tests, reference-register writes, individual bit operations, input and
output bits, original-port calls and operand/reply bits, grant operations,
acknowledgements and cleanup field/bit operations. A finite control
description and its actual bit length are an installation coordinate.
Retained and peak live storage are separate coordinates, not cumulative
allocations. Charge all components of a primitive: for example, an
allocation is an allocation, its grant delivery, the reference's actual
transport bits, and its initialized fields. A branch inspection entails
the field reads and null tests, rather than a free mathematical arity.

Fix an actual finite primitive prefix $\xi$. Its cumulative resource
vector is the sum of the declared charges of its actual primitive
occurrences. Its live-storage vector is the census of its reachable
objects, live buffer bits, reference slots, pending latches, code and
current grant backing. Peak storage is the coordinatewise maximum of
these censuses over prefixes of $\xi$. This convention charges waiting
storage without asserting an elapsed waiting-time bound. It adds no
resource or timing readout to the observer's source menu.

For determinacy of bit-buffer charges choose the following installation:
every buffer has a two-reference head/tail header; each bit cell has
one bit and one next reference. Receive or answer construction appends
one cell per bit; a cell is initialized before linking and its tail is
advanced after linking, exactly as for a routing append. Clearing scans
the retained allocated backing, clears occupied bits and reference
fields, and places reusable cells on a paid free list. Every traversal,
test, free-list write and reused-cell initialization is still a
primitive occurrence. There is no ideal uncharged array access. For
the finitely many indexed records and masks, record selection is by
the paid linear scans described in ML-T. Mutable cache mask/value bits
are authorized auxiliary record writes; computation of (ML.7) occurs
on the monotone B work tape, not through a hidden arithmetic instruction
on these records.

**Theorem 6.2 (exact persistent work and routing counts).** In one job,
at any completed instruction boundary after loading, let $C=n_-+n_+$
be the number of cells ever instantiated and $b_1$ their number of
marked bits, including loaded ones. Then the actual work counts are

$$
\begin{aligned}
P&=2+b_1,& S&=1+C,& E&=3+C+b_1,\\
V&=5+2C+b_1,& H&=1+C,\\
D_{\rm route}
 &=1+\frac{n_+(n_++1)}2+\frac{n_-(n_-+1)}2
    +\sum_{j\text{ marked}}(2+\operatorname{depthcell}(j)).
\end{aligned}
\tag{ML.10}
$$

Here $\operatorname{depthcell}(j)=j$ on the plus arm and $-j-1$
on the minus arm. Exactly $D_{\rm route}$ routing cells and side-bit
appends are retained. In particular

$$
D_{\rm route}\le1+\frac{C(C+1)}2+b_1(C+1).
\tag{ML.11}
$$

The located source/header/routing assignments are exactly

$$
A_{\rm fields}=3+4P+11S+V+4D_{\rm route}.
\tag{ML.12}
$$

These persistent objects have exactly $4V+2H+D_{\rm route}$
reference slots and $D_{\rm route}$ routing side bits, in addition
to controller, cache, input/output and other auxiliary backing.

Proof. The root setup has two promotions and one split. Every cell
is created by exactly one frontier split, and every marked bit by
exactly one P, irrespective of the number of repeated M instructions.
AA22.1 therefore gives $V=1+P+2S$ and one header per split.
The setup's $P_R$ contributes depth one; its root events depth zero.
The split depths on each arm are $1,\ldots,n_\pm$. The marked
bit at arm depth $d$ has address depth $2+d$. Every one of these
events appends once at each proper ancestor, giving exactly (ML.10).
The sum of the two triangular terms is at most $C(C+1)/2$ and
$d\le C-1$, giving (ML.11). AA22.1's two assignment counts are
$3+4P+8S$ and $V+3S+4D_{\rm route}$; adding gives (ML.12).
Four reference fields per source vertex, two per header and one next
field per routing cell give the slot count. These are counts of the
chosen physical construction, without conflating fields and bits.
$\square$

**Definition 6.3 (navigation and bit-width convention).** The driver
has a finite control graph containing the $q$ installed program
locations, their encoded jump destinations, finite phase states and
finite latches. Its description length is $K_W$ bits; at least the
actual instruction/destination encoding is included. A fixed finite
number $r_0$ of live reference registers suffices for root, head,
target, old/proposed head, ancestor, child, header, tail and pending
allocation. Unbounded input lengths, loop counters, cache indices,
print cursors and the number of jobs use paid backing, not extra
finite-control states. A linked-list cursor is one reference register;
its list still occupies all its actual cells.

Let $A(u)$ count all distinct non-null object bindings retained at
cut $u$, including original-port/connection objects and buffer backing.
Distinct references require at least
$\lceil\log_2(A(u)+1)\rceil$ bits in a simultaneous injective naming
scheme. Actual width $w(u)$ is the width of the supplied binding
representation, not automatically this lower bound. Every live
reference slot and every transported/read/written reference carries
that actual width. One permissible bounded-prefix installation
reserves a finite arena with capacity $A_{\max}$ and uses width
$\lceil\log_2(A_{\max}+1)\rceil$ throughout that prefix. All arena
material and its grant directory are then an initial charge. An
unbounded continuation may instead widen actual records; copying and
rewriting those slots is charged and its old/new overlap enters peak
storage. No single fixed-width finite device is asserted to realize
all finite prefixes at no new charge.

**Theorem 6.4 (same-run full vector).** For every finite completed job
with $s$ B instructions and loaded B input of length $m$, let
$d=\max(1,m)$. Then

$$
C\le d+s,\qquad b_1\le b_x+s.
\tag{ML.13}
$$

All resource coordinates in Definition 6.1 are finite simultaneously.
They are computed by the single ML-L/ML-B/ML-F phase execution, with
(ML.10)–(ML.12) as exact persistent coordinates. The instruction
driver makes at most $2s$ head-navigation link traversals outside
growth maintenance and loading. Maintenance makes exactly
$D_{\rm route}$ proper-ancestor visits; any separate root return or
address reconstruction is additional paid navigation. At most a fixed
constant number of field/test/register primitives per instruction,
per reserve/edit, per ancestor visit, and per loaded bit is needed
outside buffer scans. Thus for a construction constant $c_W$ these
non-buffer work primitives are bounded by

$$
c_W(1+m+s+C+b_1+D_{\rm route}).
\tag{ML.14}
$$

For multiple jobs sum these exact persistent coordinates over their
retained distinct roots, retaining all their routing storage. Each
root census includes only its own source vertices and routing objects;
each job's instruction/maintenance counts refer to that job, even when
other jobs are subsequently installed in the same arena. An arena-wide
cumulative counter is not a root-specific census. Add the
actual buffer/record/counter scans, code installation and conversion,
I/O, grants, acknowledgements and cleanup of those same runs.
Neither $s$ nor the rational-arithmetic count $\mathcal W(N)$ is
their total resource price.

Proof. A move crosses at most one new cell frontier; no instruction
removes a cell. A mark creates at most one new marked bit. This
gives (ML.13). The two-arm path (ML.3) uses at most two edges, even
at a crossing, so the head-navigation bound follows. Marks/jumps
inspect a constant number of fields; each edit has AA20.2's fixed
finite template. Each maintenance visit inspects the actual parent,
its two children and its header/tail, appends one cell and proceeds
to its parent. All these use fixed finite primitive lists, proving
(ML.14). Loading makes the stated finite bit/edge scans. At halt,
both finite arms and each requested finite output interval have
finite traversal bounds. The input transformation, ML-T, compiler
and output decoder have their own finite bit scans, proved in
Theorem 4.5; each occupies real buffers and contributes its actual
operation counts. Definition 6.1 charges them rather than assigning
them zero because they are not source Reads.

More explicitly, let $B_i(u)$ count the actually allocated bit cells
in buffer $i$ at cut $u$, including cleared reusable cells still in
that buffer's pool. A shared free pool is a further buffer in this
census. Their bit fields and next-reference slots each number
$\sum_i B_i(u)$; retained buffer headers add $2t$ reference slots.
Occupied payload bits can be fewer, but do not reduce the retained
material count. Receipt storage with
completed operands $w_1,\ldots,w_a$ has the exact payload size

$$
L_\Gamma=\sum_{v=1}^a(2|w_v|+3),
\tag{ML.15}
$$

since (ML.8) has $2|w|+1$ framing bits and two reply bits. At a
completed boundary the chosen chain therefore has exactly
$1+a+L_\Gamma$ objects, $3+3a+L_\Gamma$ reference slots and
$L_\Gamma$ bit fields. Its initialized payload and append writes
are $3+5a+4L_\Gamma$: three for the initial chain header, three
per initialized record, two per chain link/tail commit and four per
payload bit append. The cache has exactly $1+30N$ objects,
$2+30N$ reference slots and $30N$ bit fields, even if some values
are unselected. Its initialization and every selected/repeated-bit
test or write are charged separately. A pending
operand, returned reply and unlinked receipt count at their simultaneous
cuts, before any scratch is cleared. Multiply all live reference
slots, including the work slots of Theorem 6.2 and the $r_0$ register
slots, by their actual widths to obtain their bit storage. Add code,
control, latch, grant-directory and connection backing. Taking the
maximum over these same cuts gives peak storage; it cannot be replaced
by the final retained count. Sum of primitive charges gives cumulative
work, including each cleared field. Every set just enumerated is
finite for a finite completed prefix. For disjoint job roots,
additivity holds for cumulative and retained quantities, while peak
uses the simultaneous census, not a sum of mutually incompatible
instantaneous optima. $\square$

**Definition 6.5 (unchanged source port tariff).** Retain the actual
original source and its inherited preparation/storage account
$\mathcal R_o$. UJB5.3 gives $75N+4$ logical preparation events
and, for the AA17.3 source material, $120N+8$ vertices. Any actual
preparer extras and their storage belong to $\mathcal R_o$; neither
their absence nor their acquisition by the observer is inferred.
These costs are inherited once, not erased when an online session
starts. For each original invocation charge its entire transmitted
operand length, its two reply bits, the invocation, return, latch and
grant traffic and the provider's actual navigation/testing work.

A concrete compatible port provider has private access to the actual
AA17.3 source links and starts each call at its original root. It
inspects the two child fields of each visited logical position to
decode terminal/unary/binary arity. While a word bit remains, a binary
node follows the indicated actual child; at a logical leaf a strict
extension returns absent. After all bits it returns the current tag.
The unary material marker is never followed as a logical child. If
$e(w,o)$ vertices are examined and $\ell(w,o)$ logical edges followed,
then $e\le |w|+1$, $\ell\le |w|$, with exactly $2e$ child-field
reads for this provider and its actual null tests, cursor writes and
word-bit scans charged. It exposes only the original four replies;
its internal counts and timing are not observations. Using this
provider changes neither the source port nor its reply function and
adds no observer field-inspection authority.
If the physical call connection serializes its operand, use V($w$):
it transmits $2|w|+1$ framing/payload bits, while the logical
original-operand coordinate remains $|w|$. The provider receives and
backs that entire frame before traversing it. Its two returned bits,
occupied latch, End, acknowledgement and root return remain separate
charges. A reference passed across an installation boundary is an
actual authorized binding with its actual transport width; this call
uses the previously installed bound port, not a new numerical address.

**Theorem 6.6 (continuation resources are additive on actual receipts).**
A finite online execution has resource vector

$$
\mathcal R_o+\mathcal R_{\rm install}
 +\sum_{\text{actual evaluator jobs}}\mathcal R_{\rm job}
 +\sum_{\text{actual original calls}}\mathcal R_{\rm call}
 +\mathcal R_{\rm session},
\tag{ML.16}
$$

where the session term includes every cache update, receipt append,
command/answer bit, import, grant, pending phase, acknowledgement and
cleanup. Each term is evaluated on this one execution. The same
execution's live objects determine its retained and peak storage.
Constants, repeats and null-law calls are still actual calls and have
full receipt occurrences. No observation source is allocated per
arithmetic evaluation.

Proof. The handlers partition the actual primitive occurrences by
their owning installation, job, original call or session phase; shared
code and inherited objects are counted once. An evaluator's input is
the retained indexed data and public parameters, not a new observation
source. The port's private traversal implements the same original Read
by structural induction on the word; at a leaf every strict extension
is absent. Its actual operations and the session's real traffic are
therefore finite and distinct from the B instruction count. The
receipt and cache invariants of Theorem 5.3 ensure the sums range
over actual occurrences, not just unique bits. Definition 6.1's live
census gives the simultaneous storage assertion. $\square$

**Definition 6.7 (three different scales).** For ML-A let
$T_{\rm bit}(N,D,\theta,E)$ be the actual single-tape bit computation
length of ML-T, including its actual finite-input length. Let $s$ be
the actual compiled B instruction length. NWMG supplies the effective
tape-time simulation; its cubic quotation assumes the initial tape
window is included in the time/length convention. With an arbitrary
initial window retain that length in the copying bound, rather than
claiming it is at most a smaller running time. UJB16.3's
$\mathcal W(N)$ bounds rational arithmetic operations per normalizer,
not $T_{\rm bit}$, $s$, integer bit length, navigation or storage.
Equations (ML.10)–(ML.16) charge the actual chosen B/LAB execution,
including input conversion, growing integer encodings and routing.
No polynomial LAB price or simultaneous global optimum follows from
either of the two literature/arithmetic scales.

## 7. Spatial recovery with the information needed to continue

**Definition 7.1 (annotated actual views ML-V).** At an instruction
boundary, each work root has the AA17.3 oriented support and terminal
antichain. Supplement either with the location of its active head,
arm, installed program/counter, actual routing records, current rights
and bound driver. At an online service boundary also retain the same
original port, public $N,\theta$, actual receipt chain, original-indexed
cache and any retained job roots. A memory view consists of their
readable backing and current callable bindings. A causal view contains
AA17.2's endpoint-labelled work generation order, with these same
control and source annotations; if actual generation order is wanted,
include the actual acquired routing words as in AA19.2. Busy views
add all pending fields of Definitions 3.2 and 5.2. Finite descriptions
are compared on these actual bound objects, up to consistent fresh
reference renaming. Descriptions do not manufacture rights.

**Theorem 7.2 (sufficient dynamic correspondence on its stated domain).**
Fix the installed program and the same actual original source $o$;
there is no comparison between different hidden source realizations
with a handle erased. On these annotated actual images, the work support, terminal
boundary and retained-memory descriptions recover the same logical
comb, head and installed continuation state. The endpoint-labelled
causal view recovers the same work tree; with routing words it also
recovers the actual successful work P/S order. With the declared
source and pending annotations each view is sufficient for legality,
the complete next action/reply/record effects and the actual annotated
successor, for the specified ML-B/ML-Q task. All source-respecting
conversions agree and commute with the completed lawful macros.
This is a sufficiency assertion, without a minimality or actual full
serial-history assertion.

Proof. AA17.3 parses arity and interconverts support and terminal
antichain, explicitly retaining the unary marker. Formula (ML.2)
then identifies the two arms, cells, bits and the annotated actual
head. AA17.2 interconverts the work tree and its labelled generation
partial order. AA19.2 supplies precisely the optional successful
P/S serial supplement. Memory traverses these same actual fields,
and each reverse conversion reconstructs their contents on the
actual image. Since every route uses the same rooted tree and
annotations, it has the same result. No reconstructed fresh copy
is substituted for the original binding.

For a work instruction, the recovered head, program and counter give
exactly Inspect/Plan and its legal template, and the routing records
and pending fields give each maintenance/return obligation. For an
online call, the recovered command, actual original handle and grant
give the same operand and enabledness. Its real reply is a function
of that same source; with that reply the handler appends the same
receipt and updates the same index. The full joint action and actual
successor, not merely their marginals, are preserved. Induction gives
commutation for every completed finite continuation and for pending
microphases when these are included. This is PG43.1's kernel-inclusion
direction: retained irrelevant roots or extra receipts may distinguish
states having the same selected future behavior, so no reverse kernel
inclusion or memory minimum is asserted. $\square$

**Proposition 7.3 (reachable bare geometry does not determine the next
action).** For $W=(R,M)$ on $x=00$, the initial ReadyB state and
the state after its first commit have the same work tree, work
support, terminal boundary and work routing words. The next installed
action is respectively R at cell 0 and M at cell 1. These are two
reachable states in one actual installation.

Proof. Loading allocates both zero cells. R follows the already
present left child of the right arm, with no growth or routing
append. Its head changes from $R$ to $RL$ and counter from zero
to one. Thus all bare tree data are equal but the actual next
instruction and target differ. Erasing head/control fails even in
this two-cell finite domain. Similarly, after a logical growth but
before its last routing append, a pending state and its later
completed state have the same logical tree but different next
maintenance/commit obligations. $\square$

**Definition 7.4 (boundaries of the relation).** The stationary
observation source still has UJB9.3/17.2's conditional-law transport
between its ordered endpoint, support, boundary and labelled causal
order. Applying ML-A evaluates that existing law from earned data;
it does not recover the actual unread endpoint, the hidden full
injections or a chosen preparer serial extension. Source-port handles
and present authority are necessary inputs to real continuation,
irrespective of whether a mathematical law has been computed.

The complete-quantum-record and directed-window statements of
[C117 §§4, 9, 14](https://github.com/the-omega-institute/trureturing/blob/15070fa5f71c4237050acc7ebe058958cbc04e6e/docs/develop/theory/AURIC_COMMON_SOURCE_SELF_REFERENCE_AND_OBSERVER_SEQUENCES_C117.md)
retain their finite complex systems, full comparison, internal records,
consistent positive window and coverage assumptions. ML-C provides
neither their spherical positive cone nor quantum amplitudes,
isometries or actual refinement ports. Their native frontend of
C117 §14.3 remains a separate mathematical obligation. The annotated
classical dynamic correspondence here cannot be substituted for those
premises.

## 8. Prospective finite witnesses and exact falsifiers

**Definition 8.1 (finite realization contract ML-X).** A finite
realization instance is the tuple $(W,x,s,l,r)$, with zero-based
program and head conventions of Definition 1.3. Its expected objects
are the unique B configuration after at most $s$ legal instructions,
the ML-C term with frontier lengths and bits, the complete ordered
successful P/S events, the actual primitive prefix with phase fields,
the routing word at every split and the resource coordinates of §6.
Halt stops before any extra instruction. Primitive guard failures
are represented as refusals without work growth; they are never
successful templates. Equality compares trees, decoded states,
ordered events, routing words, printed frames and primitive-count
vectors separately. An event at address $p$ adds its actual first
side to each proper ancestor's routing word, in event order.

A purported realization is falsified by any changed marked bit,
wrong head/control, unexplained edit, accepted wrong guard, premature
commit/output, unbacked input/reference/length, missing routing append,
unpaid navigation or omitted live pending object. Finite arithmetic
instances are $(N,a,b,D,(E_v))$ with exact rational answers (ML.5).
Finite port instances include an actual prepared $F_1(z)$, a sequence
of operands, the actual returned replies and the receipt/cache states
after each Return. A predicted probability cannot stand in for a
returned value. These finite mathematical objects define comparisons
without relying on floating-point tolerances or random seeds.

**Proposition 8.2 (bilateral, branching and nonhalting witnesses).**
The following exact instances have the indicated results; input is
empty unless specified.

| Identifier | B program or input | Expected finite result |
| --- | --- | --- |
| MLX-cross | $(L,M,R,M,L,L,M,R,R,M)$ | Halt after 10 instructions at $h=0$; positions $-2,-1,0$ marked; $(n_-,n_+)=(2,1)$; $(P,S,V,H,D_{\rm route})=(5,4,14,4,12)$. |
| MLX-branch | $(J(3),M,J(4),R,M)$ | The first jump falls through; the second jumps to 4; the executed locations are $0,1,2,4$, hence exactly 4 commits before halt at $h=0$, with bit one and one successful mark. |
| MLX-frontier | $(R,R,L,L,L,L,R)$ | Halt after 7 commits at $h=-1$; $(n_-,n_+)=(2,3)$; all bits zero; $(P,S,V,H,D_{\rm route})=(2,6,15,6,10)$. |
| MLX-loop | $(M,J(1))$ | For every supplied finite bound $s$, the first instruction marks and every later instruction stays at location 1; no halt, head 0, and no further growth. |
| MLX-bare | $(R,M)$, input 00 | The two boundaries of Proposition 7.3 have equal bare tree and different next actions. |
| MLX-input | Empty program, input 0101 | Loader has $P=4,S=5$ and the finite output interval $[-1,4]$ is 001010. |

Proof. Apply Definition 1.3 instruction by instruction. For MLX-cross
the head list is $0,-1,-1,0,0,-1,-2,-2,-1,0,0$; its last M is
repeated. There are three newly marked bits at arm depths $0,0,1$.
Equation (ML.10) gives $D_{\rm route}=1+1+3+2+2+3=12$ and the
remaining counts follow. For MLX-branch, zero at location 0 sends
control to 1; M sets one, so location 2 jumps to 4, whose M is
repeated and falls off the five-instruction program. Its four
commits, not its program length, count the abstract instructions.
For MLX-frontier the visited extremes are $-2$ and 2 with no marks;
the two triangular sums are 3 and 6. In MLX-loop the mark makes
the self-jump permanently enabled, proving every finite bound and
nontermination by induction. The bare witness was proved above.
The input witness has two ones and four allocated right cells;
one zero is added at each requested outside end, giving the displayed
six-bit word. $\square$

**Proposition 8.3 (positive, null and capacity-sensitive law witnesses).**
For either source branch, all $N\ge4$ and either value of the
mixture prior at an endpoint, the following exact arithmetic cases
hold.

1. An empty cache has $Z_i^*=1$. Specifying one bit gives $1/2$;
   specifying one left full word at a fixed original index gives
   $1/128$. A contrary conjunction on its same coordinate is zero.
   Under the positive one-bit cache, repeating its known value has
   conditional probability one and its opposite has zero.
   If every original sample has the same specified complete pair of
   left/right words, the evidence is
   $1/(1944^{N-1}\cdot128\cdot256)>0$. For this input the allowed-label
   recurrence makes all partition pairs except the one-block pair
   zero, so ML-A's explicit pruning leaves only its finite single-edge
   type enumeration. In particular this is a direct finite $N=4$
   positive instance of the chosen evaluator.
2. Two distinct original indices both having the same fixed complete
   left word have evidence $1/(72\cdot128)$. Two distinct specified
   complete left words at those indices have evidence
   $71/(72\cdot128\cdot127)$; equality of words and inequality of
   words are different indexed events.
3. For $N=30$ assign the full array indexed by $(a,b)$,
   $0\le a<3$, $0\le b<10$, in lexicographic order. Its left
   word is the seven-bit binary encoding of $a$, its right word the
   eight-bit encoding of $b$. Then

$$
Z_0^*=0,\qquad
Z_1^*=\frac{9(8)_3(27)_{10}}
 {1944^{30}(128)_3(256)_{10}}>0.
\tag{ML.17}
$$

   Thus at $\theta=0$ this submitted evidence is null; at
   $\theta=1$ it is positive. For every represented
   $0<\theta\le1$ its mixture normalizer is
   $\theta Z_1^*$. With $N\ge73$, 73 different specified complete
   left words at distinct indices give zero under both sources.

Proof. One uniformly assigned full-injection label at a fixed literal
left endpoint is uniform among 128 words, so the first assertions
follow, independently of its distribution among literal endpoints.
Two iid sampled edges have the same left endpoint with probability
$1/72$, since every literal left endpoint has the same degree 27.
The common label is then the specified word with probability $1/128$.
If the labels are specified and distinct, the endpoints must be
distinct, with probability $71/72$, and their ordered labels have
probability $1/(128\cdot127)$. This proves the two different values.
For the complete repeated pair in part 1, full-injection equality
forces every sample to be the same literal edge. The first edge is
arbitrary, the other $N-1$ equal it with probability $1944^{-(N-1)}$,
and its two labels have the specified values with probability
$1/(128\cdot256)$. An injective assignment of two different endpoint
blocks to this same label is impossible, proving the pruning assertion.

The full array in part 3 forces exactly the left and right equality
partitions of $K_{3,10}$, with compatible label counts one. In source
zero, ten distinct literal right endpoints cannot all have one point
type because that capacity is nine. At least two distinct affine
points must therefore lie on every one of the three left line types.
Two distinct points determine at most one affine line, and its literal
left capacity is two. An injective three-left lift is impossible,
so $J_0(K_{3,10})=0$. In source one a connected required relation
must lie in one of nine complete components; its lift count is exactly
$9(8)_3(27)_{10}$. UJB16.2 gives (ML.17), with all thirty sample
denominators retained. The last zero case follows from only 72
literal left endpoints and injectivity of their labels. These are
closed-form checks of the exact existing evaluator, not a new source
separation or reduced acquisition-cost claim. $\square$

**Proposition 8.4 (authentic finite return witnesses).** For any
$N\ge4$, both constant bit arrays $z=0^{15N}$ and $z=1^{15N}$
are attainable with positive probability under either original branch.
On the zero array the operand sequence

$$
\varepsilon,\ LL,\ LRR,\ LLR,\ LL,\ LR,\ LLL,\ LRL,
\quad R^{b'-1}LL\ (b'=2,\ldots,15),\quad LL
\tag{ML.18}
$$

has initial replies $\mathsf b,\beta,\alpha,\bot,\beta$.
Its final cache has exactly sample 1 complete and every other sample
unread. Every LL occurrence is separately receipted at that same
original bit index. On the one array, LL, LR, LLL, LLR, LRL, LRR
return $\mathsf b,\beta,\beta,\alpha,\bot,\bot$ respectively, with the appropriate
informative-absence restrictions. The pair of arrays tests both
entries of each informative local suffix table, and no law computation
can substitute for any one of these actual returns.

Proof. Choose any one literal edge, repeat it in all $N$ independent
draws, and assign its two endpoints the all-zero, or all-one, labels.
There are full injections extending each such assignment; the event
has positive mass for both sources. UJB.7705 at the first slot gives
all displayed replies. Every operand $R^{b'-1}LL$ earns precisely
bit $b'$, so the sequence completes only the first sample. The
source is stationary; the three LL occurrences keep their old value
and each appends a distinct actual record. On the one array the same
table gives the stated replies, including absence at LRL and LRR.
Theorem 5.3 preserves the exact occurrences and indices. $\square$

**Definition 8.5 (prefix and resource discriminators).** The finite
objects of ML-X also include a cut immediately after a successful
logical edit but before its last proper-ancestor append, a cut after
receiving a proper frame prefix, a cut after a real reply but before
the receipt tail update, and a cut during Print before End/Ack.
Their expected pending fields are those of Definitions 3.2, 4.1 and
5.2. For MLX-cross the persistent work/routing reference-slot count
is $4\cdot14+2\cdot4+12=76$, its persistent object count is
$14+4+12=30$, and its routing bits are 12. Ignoring the routing cells would
give 18 objects, which fails this construction's exact census.
For a Read on an operand of length $d$, its receipt payload alone
has $2d+3$ bits even when the reply was already known. Live request,
return latch, unlinked receipt and answer backing must be counted at
their common cut. Wrong P on a marked bit, S on a branch, premature
Read completion and premature acknowledgement each violate a named
guard or phase and have no successful successor in this contract.

## 9. Source correspondence and exact limits of the assertions

**Definition 9.1 (supplier correspondence).** The mathematical
dependencies used above have the following domains.

| Supplier | Used correspondence and retained boundary |
| --- | --- |
| AA17.1–17.3, AA19.1–20.3, AA22.1 | Actual guarded growth, birth types, oriented unary material, routing acquisition, finite reserve/maintain/return and located material counts. ML-C is a different consumer of these operations; it keeps their routing overhead. |
| UJB3.2, 5.1–5.3, 9.1–9.3, 15.2–17.1 | The literal $72/243$ endpoints, $1944$ edges, complete shared injections, entire $N\ge4$ promise, every-word Read classification, indexed normalizers and old-slot continuation. ML-A computes these exact formulas from actual data without recovering hidden realizations. |
| UJB17.2 and the delivered intrinsic-recovery interface | The fixed-prior, fixed-partial-cache support inverse needs an unread slot; acquired partners and bindings have their original scopes. ML-R retains full indexed data, so it does not weaken those inverse premises or repeat the affine/label-fibre recovery. |
| `ActualTreeReadoutAcquisition.readout` | L/R are false/true, $\alpha/\beta$ are `of true/of false`, branch and absent retain the original four replies. Private source-link traversal in §6 is a realization of this same readout, not a new observer menu. |
| `NativeSerialEffective.original_code_service_simulation` | Its supplied effective selector and terminating OriginalRun preserve external Reads/observations after erasing local evaluator steps. It neither lowers P/S nor pays all local work; no such implication is borrowed here. |
| `NativeControlConjugacy.native_control_conjugacy` | Reindexing an already supplied controller preserves its specified action/trace coordinates. It does not charge arithmetic erased as localStep; ML-Cost separately counts it. |
| PG43.1 and AA21.2 | Source-respecting annotated recovery with legality and actual successor factorization gives task sufficiency. No converse kernel equality without no-redundancy is inferred. |
| NWMG, primary pp. 4–9 | Effective finite TM-to-non-erasing-to-B simulation, repeat M, bilateral motion and fixed instruction jumps. Definition 4.6 supplies the explicit monotone metadata/handoff and finite decoder; these details are not a transition table supplied by the paper. Its abstract tape-time bound is not a LAB resource vector or an original-source port implementation. |
| C118 §§140–149 at `86172888e706177b6c1d135cb12aec3b6d2cdce8` | Its fixed finite octahedral menu and calibration/positive-floor hypotheses do not supply ML-I or the C117 native frontend. Its control-factor count is not a total material or runtime tariff. |
| C117 at the fixed published object, §§4, 9, 14 | Conditional complete-record and directed-window reconstruction remains within its quantum/algebraic assumptions. No C117 quantum frontend follows from the classical execution construction. |

**Definition 9.2 (proof and physical domains).** The mathematical
assertions are ordinary conditional definitions, theorems and proofs
under ML-I. They quantify every finite B program/input/prefix, and
the UJB application quantifies every $N\ge4$, every represented
rational prior, all original-indexed masks and finite cylinder lists,
with conditional ratios restricted exactly to positive evidence.
The finite witnesses specify exact potential comparisons; they do
not assert that those comparisons have been executed or replace the
universal proofs. No new Lean-kernel result or independent acceptance
is part of these assertions.

The installation hypothesis includes real allocation, navigation,
finite control, current grants, auxiliary records, original port and
I/O. Bare two-atom syntax alone does not supply those operations.
Observable capacity/failure, interrupts, concurrent writers or
reference revocation require their own state and phase semantics.
An infinite actual computation, arbitrary effective integration over
a general seed space, unrepresented-real equality, the physical
quantum frontend, optimal total encoding and the original full serial
history remain outside the proved correspondence. The finite
prefix results preserve their full domains without asserting any of
these additional conclusions.

## 追加锚（本行以下为增补区）

## 25. Integrated B composition and one chronological source-observer account

**Definition 25.1 (the common service configuration).** Let $I$ denote the
actual native installation of Sections 18--21, $G$ the received-command
graph of Sections 22--24, $O$ its observer-side connection arena, and $S$
the unchanged source arena rooted at the supplied $F_1(z)$ object.  A
configuration cut is the tuple

$$
 C_t=(I_t,S_t,O_t,Gamma_t,D_t,ho_t,pi_t,chi_t,omega_t),
$$

where $I_t$ contains the installed code, image pages, native control and
reserve; $S_t$ contains the original root, its provider fields and all
retained preparation; $O_t$ contains the service connection, input and
reply latches, receipts, cache, output buffers and free pool; $Gamma_t$ is
the ordered receipt chain; $D_t$ is the paired indexed cache; $ho_t$ is
the native reference/control location; $pi_t$ is the service phase and
its literal continuation; $chi_t$ is the pending operand/reply state; and
$omega_t$ is the owner-indexed reference-width vector.  Every cursor,
counter, selector, pending latch and result in this tuple is an actual
field or finite-control bit of its owner.  Audit counters and independent
inspection views are not members of $ho_t$ or $pi_t$.

**Assumption 25.2 (the integrated ML-I boundary).** The supplied native
primitive graph, current grants and finite reserve are valid at the initial
cut.  The complete fixed A image and its routing directory are the same
objects used by the production decoder and driver.  The original port is
the same bound source/root throughout.  Allocation returns a fresh object
with its actual grant and fields; a grant may be pending, refused or
returned, but it is never represented by an integer.  Source calls are
made only by the installed connection successor and return only the
reply produced by that port.  No source reset, reroot, resampling,
hidden-generator answer, law-to-Read substitution or unrepresented real
decision is available.  A finite reserve is a parameter for the finite
prefix under consideration; it is not a bound on $N$, a prior, an operand,
or a run.

**Definition 25.3 (literal driver boundary relation).** A production
request has the chronological phases

$$
 \mathsf{Receive}\to\mathsf{Seal}\to\mathsf{Convert}\to
 \mathsf{Load}\to\mathsf{Driver}\to\mathsf{Decode}\to
 \mathsf{Print}\to\mathsf{End}\to\mathsf{Ack}\to\mathsf{Return}.
$$

At `Receive` and `Seal` the complete framed input is held in its linked
buffer.  `Convert` reads that buffer and writes the owned binary input
record.  `Load` initializes the actual B root, header, data and end fields.
At a `Driver` cut the old head, new head, arm, program reference and the
current image fetch continuation are all backed locations.  A move, mark,
jump or halt is enabled only after its guard and destination fields have
been read.  `Decode` follows the returned active header and data-head flag;
it does not choose a coordinate by a host integer.  `Print`, `End`, `Ack`
and `Return` consume the returned linked output and preserve their pending
latches until the guarded successor.  An actual `Read` takes the parallel
source path in Definition 5.2; its reply is captured before the return
latch is released, then its receipt is linked before its tail is advanced.

**Lemma 25.4 (boundary preservation).** Every valid intermediate cut of
Definition 25.3 has one of the displayed phases, a finite literal
continuation, and the fields needed to resume that phase.  A transition
that advances a phase either preserves the old material or adds the
freshly granted object and records it in the owner directory.  A transition
that would read a missing field, use a wrong arity, consume an unoccupied
latch, or use an unavailable grant is refused before its effect.  During a
source call, the pending handle and operand remain present; during reply
capture the occupied reply remains present until its backed copy exists.
During receipt linking the new record is reachable before the advertised
tail is changed.  During output, `End`, `Ack` and `Return` are enabled in
that order.  Thus every valid cut has a unique next actual successor and
every completed transition has the stated predecessor cut.

*Proof.*  Induct on the finite transition graph.  Native dispatch reads
the five opcode bits and the sixteen literal selector bits from the
installed code vertex, then reads the selected reference fields.  The
four-reference and eight-bit shape tests reject all other locations.
The input and reply transitions have occupied bits as guards, while the
source successor calls the retained `OriginalPort.call`.  The receipt and
cache successors are the explicit field writes in Definition 23.2, so an
old record, repeated occurrence, and indexed cell remain reachable at
every later cut.  The same argument applies to the output cursor and its
End/Ack/Return chain.  No inspection value is in any successor field.
The converse follows by reading the phase, guard and continuation fields
at a completed transition.  The production graph therefore has exactly
the displayed cut relation. $\square$

**Theorem 25.5 (integrated LAB-driver correspondence).** Fix a valid
initialized A image, an actual received finite input, and a sufficient
finite reserve.  For every finite bilateral non-erasing B program, every
supplied finite binary input, and every finite internal prefix, including
the immediate-halt prefix and prefixes of a nonhalting run, the production
driver realizes the corresponding B prefix on the actual LAB root.  Its
old/new head, arm, program counter, mark, frontier and pending growth are
the fields in $C_t$; no host selector supplies any of them.  A completed
driver macro decodes to exactly the B transition of Sections 2--3, and a
completed B transition has the same driver macro as its converse.  The
returned active header and data-head flags are then consumed by the actual
output decoder and framing path.  The source operation is never used to
choose a driver instruction.

*Proof.* The initial input and image bindings are the actual outputs of
`Receive`, `Convert`, and the fixed image decoder.  Apply Lemma 25.4 to
the initial load and then induct on the B prefix.  The guard tests select
the literal transition row, the move or mark successor changes only the
new head/mark fields, and a frontier extension allocates and links the
required LAB cells before the new head is committed.  The ancestor routing
updates are the guarded P/S operations of Definition 1.1.  The old head
and program reference remain in their saved locations until the commit
field, so a busy cut is a valid prefix rather than a second transition.
The induction is the forward simulation of Theorem 3.3 with the actual
field graph inserted at every boundary.  Reading the committed fields
gives the completed-macro converse of Theorem 3.4.  At halt the decoder
starts at the returned active header and follows its data-head flag, after
which the framed Print/End/Ack/Return path is Lemma 25.4.  The argument
uses only finite control and the given reserve, so it is uniform in the
program, input and prefix. $\square$

**Definition 25.6 (one chronological ownership ledger).** For the actual
source and observer session, let an event be

$$
 e=(t,owner,phase,operation,object,\Delta_{ref},\Delta_{bit},
     grant,pending,free,width).
$$

The owner is one of `installation`, `source`, or `connection`.  The ledger
keeps all earlier jobs and roots, source routing material, code pages,
directory links, grants, receipts, cache cells, request/reply buffers,
pending objects, and returned objects.  A cleanup operation clears the
fields and moves the cell to the owner free pool; it does not delete the
object or silently release its grant.  A width migration records the old
and new widths and the simultaneous copy of every live reference slot.
The source, observer and installation rows at one timestamp form one
configuration cut; their peaks are never added when they belong to
different timestamps.

For a cut $t$, let $A_t$ be the set of all retained owner-tagged objects,
including a pending object and free-pool cells.  A direct census counts
$A_t$, its actual reference fields and bit fields, the owner width vector,
and grant bits.  The incremental census starts at the initial retained
set and applies the event deltas in order.  Its width-migration charge is
the actual number of copied reference slots times the new width, with the
old and new images simultaneously retained during the copy.

**Theorem 25.7 (common-cut census and resource correspondence).** On every
valid event prefix of Definition 25.6, the incremental census equals the
direct census of $A_t$.  The equality includes retained old jobs and roots,
source/provider/connection charges, all grants and returned objects,
receipt and cache material, free-pool cells, pending End/Ack/Return cuts,
failed or busy/refused phases, and post-return retained material.  Every
component uses the same timestamped cut and keeps its actual width; the
unified total is the sum of component fields at that cut, not a sum of
independent fixture peaks.  The installation, source and connection
operation counts therefore charge the same actual session.

*Proof.* Allocation adds one fresh granted object and its literal fields to
both ledgers.  Linking changes ownership reachability but not membership
of $A_t$; a pending object is already included before the link.  A field
write either adds the one field counted by the direct census or changes an
existing field, and a read changes no membership.  Cleanup moves a cell
to the free pool while retaining the object, so the object, grant and
width remain in both counts.  At a widening, the old reference image and
the new image coexist; the copied-slot event adds exactly the direct
overlap charge and then changes the owner width.  Refusal and busy events
advance no prohibited field and hence add no object or receipt.  Induction
over the event order proves equality at every cut.  Summing the three owner
rows only after the cut is fixed gives the displayed unified total and
avoids combining unrelated peaks. $\square$

**Proposition 25.8 (operational falsifiers and cleanup boundaries).** The
integrated path rejects premature End, Ack, Return or Close, a second
request while busy, an absent grant, an occupied input/reply latch, a
wrong field selector, and an exhausted finite reserve.  Omitting an
operand-bit transfer leaves the actual connection latch unoccupied and
prevents the original call.  Omitting an indexed cache write leaves the
receipt but changes the returned cache state.  Removing a source-field
read, a grant delivery, or a free-pool cleanup event makes the incremental
census disagree with the direct one.  These are state and census
failures, not merely result-file comparisons.

*Proof.* Each refusal is the negative branch of the corresponding guard in
Lemma 25.4.  The two omission cases remove the only actual write that can
occupy the latch or set the indexed mask/value pair, so the subsequent
source call or cache invariant fails.  The census claims follow from the
allocation, field and cleanup cases in the proof of Theorem 25.7. $\square$

**Theorem 25.9 (whole-family composition).** Under Assumptions 1.2 and
25.2, the preceding correspondences compose for every finite bilateral
non-erasing B program, every supplied finite input and every finite legal
internal prefix, including halt and nonhalt prefixes.  They retain every
source-permitted finite $N\ge4$, every represented rational
$\theta=a/b\in[0,1]$ with $b>0$ (including endpoints and unreduced forms),
all $15N$ original-indexed mask/value assignments and finite cylinders,
all finite operands and histories, repeats, partial slots, old-index
rereads, distinct indices with equal observations, both once-shared full
injections, and source arrays outside prior support.  The finite reserve is
chosen per finite prefix.  The fixed-image 64-bit restriction concerns
only image addresses and their proved arithmetic.

For every completed `Read`, the exact original invocation tariff is paid,
including constants, repeats and absences; receipt occurrences retain
their order and indexed cache identity.  `Predict` performs no source call
and fabricates no reply.  Null evidence is retained, and a conditional
ratio is formed only when its normalizer is positive.  The original source,
control, reference and permission failures remain the same.  The
composition asserts neither a full evaluator execution nor a completed
ML.16 full-session account.

*Proof.* The domain clauses are those of Theorems 3.3--3.4, 4.5, 5.3--5.4
and Proposition 5.5.  Theorem 25.5 supplies their actual LAB driver and
returned-head boundary.  Theorem 25.7 supplies one resource cut for the
same source and observer session.  The receipt/cache induction of
Theorem 5.3 gives occurrence order, original indices and repeated calls;
The Predict branch has no source successor by Definition 5.2.  The
arithmetic evaluator of Section 4 is called only on its finite received
frame, and its zero-normalizer branch emits null evidence rather than a
ratio.  Thus each clause is preserved by composition.  The final sentence
is a scope boundary: the two strict executions require the subsequent
full positive/null evaluator runs and complete same-run census. $\square$

**Definition 25.10 (author evidence and remaining boundary).** The private
author result `rro-lab-execution/integration-results.json` records the
actual installed service run: $69$ original calls, $57$ distinct
operands, $29{,}266{,}611$ native steps, $185{,}513$ field actions and
$44{,}916{,}792$ installation steps.  Its common cut has installation,
connection and original-source widths $(21,12,14)$ and direct/incremental
census equality at all $69$ source-call boundaries.  The same result
re-runs the finite whole-family author checks: $1{,}722$ B
program/input instances, $490$ bounded nonhalting boundaries, $511$ V
words, all $32{,}768$ within-slot masks, and $8{,}248$ original-port
calls.  Source binding and compatibility checks retain the two operational
mutant falsifiers `actual_port_transfer_occupied` and `actual_cache_write`.

These results close B-LAB-driver, B-allocation-width-and-common-timeline,
and B-whole-family-correspondence for the stated conditional ML-I
construction.  The strict objects `ML-N-evaluator-execution` and
`ML-Cost-full-evaluator-session` remain not executed.  Therefore this unit
is B-complete for its assigned outcomes, while C is not released, D is not
complete, independent acceptance has not occurred, and the long research
goal remains open.  No Lean declaration, digestion settlement, judge
change, minimality claim, hardware claim, quantum frontend, or actual
serial-history recovery is made.

## 追加锚（本行以下为增补区）


## 10. A fixed word-stack evaluator and its scalar representation

**Definition 10.1 (the finite evaluator network ML-S).** A register is a
finite Boolean word with its first element at the top. The instruction
algebra is precisely halt with a Boolean decision, goto, push of one
constant bit, pop with empty/zero/one successors, and peek with those
same successors. Pop of the empty word leaves it empty. Control labels
and the register set are fixed finite sets. No instruction applies an
arbitrary function to a word. ML-S is the network obtained by the
following finite routine compositions; names in this definition identify
entries of that network, rather than new atomic instructions.

The scalar representation is the canonical little-endian word
$\nu(0)=\varepsilon$, with no high zero in $\nu(n)$ for $n>0$.
An arbitrary finite Boolean word $w=b_1\cdots b_k$ has the internal
record

$$
\langle w\rangle=1b_1\cdots1b_k0.
\tag{ML.17}
$$

A finite vector is the concatenation of these records, with no extra
sentinel; its known length is retained separately when random access
is needed. Thus an empty vector and a vector containing a zero are
respectively $\varepsilon$ and $0$. Natural-number vectors use records
of $\nu(n)$. Internal record lengths impose no bound on $N$, a scalar,
a cylinder count or a subset-array size.

There is one private argument/result bank for each routine. A call copies
the actual argument words into that bank, pushes its fixed eight-bit
return identifier onto that routine's initially empty return stack, and
jumps to its entry. Return pops the identifier through its finite binary
dispatch tree and copies the result words to the caller. Each routine
has fewer than 256 call sites. The call graph is acyclic: word
transfer and ripple arithmetic precede comparison, multiplication and
division; these precede gcd and rational arithmetic; these precede
vector access, framing and the combinatorial routines; normalizers and
mixtures precede the outer evaluator. A loop is an ordinary graph cycle,
not recursion in this call graph. Therefore another invocation cannot
overwrite a still pending return identifier of the same routine.

**Definition 10.2 (word and arithmetic entries).** The entries clear,
reverse-transfer, copy, popword, prepend and concat respectively empty
a stack, reverse its word into another stack, copy without changing
the source, extract the first record of (ML.17), prefix such a record,
and concatenate two finite words. Copy first transfers the source into
an empty temporary, then pops that temporary while pushing each bit
onto both the original and destination. Prepend reverses its payload,
pushes its terminating zero onto the destination, then, at each payload
bit in reverse order, pushes that bit followed by one. Popword removes
successive leading one/bit pairs up to the terminating zero, collecting
the payload through a reversing temporary.

The scalar entries add and sub consume copied argument bits from low
to high. Their finite states retain one carry or borrow bit; absent
high bits are zero. When both words end, add appends its final carry,
whereas sub returns its final borrow. Both trim high zero bits through
a reversed temporary. The sub-result is used as a difference only when
the borrow is zero. Comparison uses this borrow; equality additionally
tests the zero difference. Multiplication consumes the second operand's
low bits, conditionally adds the shifted first operand to an accumulator,
and doubles that first operand at each iteration. Division reverses the
dividend and processes it from high to low, replacing the remainder by
$2r+b$, conditionally subtracting the positive divisor and recording the
quotient bit. It normalizes the quotient at return. Gcd repeatedly calls
division and replaces the pair by divisor/remainder. Reduce divides
numerator and positive denominator by their gcd. Rational addition forms
the two cross-products and the denominator product, adds the former and
reduces. All these entries are compositions of the five instructions in
Definition 10.1; the named entries are not host-arithmetic callbacks.

**Theorem 10.3 (word and scalar contracts on all represented words).**
For every finite represented word or vector, the word entries have
Definition 10.2's meanings and terminate. For every pair of represented
naturals, add and mul return their sum and product; sub returns borrow
one exactly when the first is smaller, and otherwise their difference.
The comparisons return their indicated Boolean naturals. On positive
divisors, div returns the unique quotient and remainder, gcd terminates,
and reduce and rational addition return reduced nonnegative fractions
with positive denominator, including $0/1$.

Proof. Induct on the finite source word for each transfer. In copy, the
first transfer reverses the original, and the second reverses it again
into each of the two destinations. The two pushes in prepend restore
the order of every one/bit pair; its initial zero terminates exactly the
payload, independently of the following records. Induct on the number
of pairs for popword. These proofs apply to arbitrary words, not merely
canonical naturals or bounded test cases.

For ripple addition, after $k$ positions, the produced low part plus
$2^k$ times the carry equals the low parts of the operands' sum. For
subtraction, the corresponding identity has the borrow with the opposite
sign. Exhausting both words gives the claimed final carry/borrow and,
on zero borrow, the difference. Trimming high zeros preserves value and
makes the representation canonical. Shift-add multiplication maintains
accumulator plus shifted operand times the remaining multiplier equal
to the original product. The multiplier loses one bit per iteration.
For division, after processing a high prefix, that prefix equals divisor
times quotient plus remainder, with remainder smaller than the positive
divisor. The next bit and optional single subtraction preserve precisely
this invariant. Each iteration consumes one dividend bit. Euclid has a
strictly decreasing positive second member until it becomes zero.
The gcd of zero and a positive denominator is that denominator, so zero
fractions also reduce without division by zero. Cross-products preserve
the ordinary rational sum. The call order of Definition 10.1 and these
strict decreases prove termination of every stated contract. $\square$

**Definition 10.4 (vector access and ML-F entries).** Get extracts and
discards records until its copied nonnegative index is zero, then
extracts that record. Put moves the preceding records into a temporary
vector in reverse record order, removes the old selected record, prefixes
the replacement onto the tail, then restores the temporary records one
at a time. Zeros prefixes a zero record once per counter decrement.
These entries require an in-range index; their callers establish it.

ReadV counts the initial unary length marks in a finite temporary stack,
then transfers exactly that many following bits. ReadU reverses the
resulting canonical MSB-first unsigned payload and normalizes its zero.
Readcache reads all $15N$ mask bits before any selected value, then
rescans them in original order to read one actual selected value for
each one. Its internal vector has $15N$ entries: zero means unknown,
one means observed zero, and two means observed one. EncU reverses
$\nu(n)$, supplies the one-bit payload zero when $n=0$, and applies V.
EncQ reduces, concatenates the two U-words and prefixes zero sign.
The outer output concatenates V of each rational word after U of its
list length, and uses the ML-F positivity bit and conditional list.

**Theorem 10.5 (accepted-frame correspondence).** Let $x$ be any accepted
ML-F arithmetic frame, including an unreduced rational prior and either
endpoint prior. Supply exactly its bits, in their original order, as
register zero of ML-S, all other registers empty. ReadU and Readcache
recover its $N$, numerator, positive denominator and all original-indexed
cache entries; subsequent ReadV/Readcache calls recover precisely the
stated cylinder list. A cylinder with flag one has no mask and denotes
the empty event. A cylinder with flag zero retains its entire mask and
all its selected bits. EncQ and the outer output recover ML-F's reduced
output format. This transformation is defined on every accepted finite
frame and loses none of its numerical or indexed meanings.

Proof. In V, the unary marks fix the exact number of payload bits, so
induction on this length proves ReadV. The canonical unsigned payload
then gives ReadU, including its explicit zero payload. Positivity of the
prior denominator and $0\le a\le b$ are the accepted-frame premises;
no cancellation of $a/b$ is needed to read it. Readcache's first scan
fixes the positions of the second scan. Its loop invariant after index
$k$ is that precisely the selected values before $k$ have been consumed
and the entire first $k$ entries agree with the received frame. This
also retains unknown and repeated original slots. Induction on the
stated list length gives every cylinder, with its independently framed
finite word. The inverse claims for encoding follow by the same
length induction and Theorem 10.3. Acceptedness here is a premise about
the actual received bytes; a service must validate that premise before
loading. This theorem supplies no validation or acceptance claim for
other input words. $\square$

## 11. The combinatorial entries and the full ordinary correspondence

**Definition 11.1 (partition and label entries).** Blocks scans an RGS
and returns one plus its largest entry. Nextpart scans from the right
for the last position whose value is smaller than one plus the maximum
of its strict prefix, increments that value and sets the later suffix
to zero. If none exists it returns the exhausted flag. The first RGS
is the length-$N$ zero vector. The partition iterator tests the original
caps 72 and 243 before using a denominator.

Countlabels first scans every original sample $j$ and each coordinate
on the chosen side. It copies each known value into its proposed
block/coordinate requirement; two different known values there set a
conflict flag. For each alphabet label, an explicit bit scan of those
requirements constructs the permitted-block indicator. A label that
permits no block leaves the subset array unchanged. For other labels,
new is initialized by copying old. At each nonempty subset $S$ its
entry is initialized from old($S$); for each permitted member $b$ the
entry old($S\setminus\{b\}$) is added. Membership and deletion use
quotient/remainder by the iteratively doubled power of two. All reads
in this addition are from old. Only after the full subset scan does
new replace old. The final full-subset entry is returned.

**Theorem 11.2 (partition and label correspondence).** Nextpart enumerates
every partition in ML-A's order, once. Countlabels returns precisely
$L_p(D)$ or $R_q(D)$ of UJB16.1, including empty and conflicting
restrictions, on the full original index set.

Proof. Increasing the rightmost position that can increase, followed
by the least possible suffix, is exactly the next lexicographic RGS.
Every RGS begins with zero; the first all-zero word and exhaustion
therefore bracket the entire finite RGS set. Each member of an equality
block visits the same requirement cell, so that cell is exactly the
intersection of all its indexed coordinate restrictions. A conflicting
cell allows no label. Otherwise a tested label passes exactly when it
satisfies every required coordinate. UJB16.1's recurrence now applies:
copying old accounts for not using the next label, and each added term
assigns it to one permitted block of $S$. Distinct blocks cannot use it
twice because all predecessor reads use old. The disjoint alternatives
are complete. A label permitting no block has no added terms, justifying
its skip. Induction over the alphabet gives the final full-subset count.
No index is removed by a requirement intersection. $\square$

**Proposition 11.3 (two zero-preserving evaluation shortcuts).** When
all labels on one endpoint side are fully observed, injectivity of the
once-shared label map forces the sole possible sample partition to be
equality of those full observed words. Its compatible label count is
one; every other partition has label count zero. Also, an injective
embedding of $H_{p,q}$ into either literal source is impossible when a
distinguished left vertex has more than 27 different required right
neighbors, or a right vertex has more than eight different required
left neighbors. Thus these tests may bypass only zero summands of
(ML.7), for every $N$, without replacing its index set or denominator.

Proof. Two sampled endpoints with equal full labels are the same
endpoint by injectivity; unequal full labels cannot be the same endpoint.
The equality partition is therefore forced in both directions. Its
block label is already fixed, so its labeling assignment has exactly
one choice. In $G_0$ each literal left endpoint meets three point types
of capacity nine, and a literal right endpoint meets four line types
of capacity two. In $G_1$ the corresponding degrees are 27 and eight.
An embedding sends distinct required neighbors to distinct literal
neighbors. Either excessive degree is impossible. Repeated original
incidences are counted once for this necessary degree test, but still
occur at every original $j$ in the incidence scan and $1944^N$.
This establishes the zero tests, not a replacement law. $\square$

**Definition 11.4 (literal-capacity entry).** Inject first performs
Proposition 11.3's degree test. Otherwise it enumerates mixed-radix
words of length $r+s$: radices $(36,27)$ for the first $r$ and last $s$
positions in source zero, and $(9,9)$ in source one. A rightmost-digit
odometer resets exhausted digits to zero. Each word starts with empty
left/right occupancy vectors and weight one. At each distinguished
vertex it multiplies by capacity minus previous occupancy, using zero
if exhausted, then increments occupancy. The capacities are $(2,9)$
and $(8,27)$. It scans every original $j$, selects the types at $p(j)$
and $q(j)$, and sets weight to zero on failed incidence. It adds each
word's final weight to J.

The source-zero incidence code is the finite Boolean decision tree for
membership of a point in a line of UJB15.2: first its six low line-index
bits, then its five low point-index bits, with absent high bits zero.
Lines use the four displayed directions in UJB15.2 followed by their
lexicographically least point, and points use lexicographic ternary
order. All 36 by 27 entries are public constants. A leaf is one exactly
on membership, and otherwise zero. For source one the test is equality
of the two field-value indices in their common lexicographic order.
The decision tree supplies no source-dependent answers or runtime code.

**Theorem 11.5 (capacity and normalizer entries).** Inject returns
$J_i(H_{p,q})$ of UJB15.3. Normalizer, using Nextpart, Countlabels and
Inject, returns exactly $Z_0^*(D),Z_1^*(D)$ of UJB16.2 for every indexed
cache, including null caches. Its only skipped summands are those proved
zero in Theorem 11.2 or Proposition 11.3, or by the original block caps.

Proof. The odometer enumerates each pair of type maps exactly once.
Within one type, multiplying each successive remaining capacity gives
its falling factorial. A failed capacity makes the same product zero.
The decision tree is the point-on-line relation on the stated finite
sets; source one's common field ordering makes its test equality.
Each original incidence therefore contributes precisely its UJB15.3
indicator. Summing the weights is that existing theorem's $J_i$.
The normalizer multiplies J by the two label counts and divides by
$1944^N(128)_r(256)_s$. These denominators are positive after the block
cap checks. It sums the two source accumulators by reduced rational
addition. Theorem 11.2 and the two zero tests cover exactly the omitted
terms. UJB16.2 identifies the resulting sum with the entire indexed
cache evidence under the same two full maps, including their unobserved
extension factors. No independent map is introduced per coordinate,
block or sample. $\square$

**Theorem 11.6 (all-input ordinary evaluator correspondence).** For
all accepted arithmetic frames of Theorem 10.5, ML-S terminates and
its register-zero output is exactly (ML.5) with ML-F framing, and with
NullEvidence exactly when $Z^*(D)=0$. The other output case contains
all and only the conditional ratios at a positive normalizer. The
statement includes every source-permitted finite $N\ge4$, every
represented rational prior including endpoints and unreduced values,
every original-indexed mask and value, and every finite cylinder list.

Proof. The parser establishes the indexed data of Theorem 10.5. For each
cylinder, Conjoin scans all $15N$ positions. Unknown entries retain the
other restriction; agreeing known entries are retained once; different
known entries set a conflict flag. The flag-one cylinder also sets it.
A flagged normalizer returns two zero fractions. Otherwise Theorem 11.5
applies. Mixture forms $(b-a)Z_0/b+aZ_1/b$ by integer products and
rational addition. It does not alter the represented prior or redraw a
source. The output accumulator receives the three base fractions and
the three fractions for each conjunction in their original list order.
It tests the exact base numerator. Only on a nonzero numerator does it
form the conjunction mixture times base denominator divided by base
numerator times conjunction denominator. All these divisors are then
positive. Theorem 10.5 gives the final framing; UJB17.1 supplies the
conditional-law interpretation.

For termination, every parser and vector scan consumes a finite number
of actual bits or records. Theorem 10.3 covers scalar loops. An RGS
iterator exhausts a finite ordered set; a type-map odometer exhausts its
finite radix product. Each subset loop has exactly $2^r$ finite entries,
and an alphabet loop has 128 or 256 iterations. Degree, occupancy,
incidence and conjunction scans have finite supplied vector lengths.
All vector indices are within the lengths just constructed: sample
indices below $N$, coordinate indices below 15, block indices below
$r,s$, occupancy indices below their type counts, and subset indices
below $2^r$. Bit deletion uses a present subset member. No mathematical
loop requires a host iteration or a numerical oracle. The acyclic
routine calls and their finite return dispatch preserve these contracts,
so their finite compositions terminate. This is an ordinary proof about
the explicitly composed instruction network, not a new Lean client or a
claim about its LAB resource acceptance. $\square$

## 12. The supplied stack compiler and an aligned binary adapter

**Definition 12.1 (serialized register boundary).** For a finite register
family $(w_0,\ldots,w_{k-1})$, use the four-symbol tape

$$
\mathsf s\,\operatorname{bit}(w_0)\,
\mathsf s\,\operatorname{bit}(w_1)\cdots
\mathsf s\,\operatorname{bit}(w_{k-1})\,\mathsf s,
\tag{ML.18}
$$

blank elsewhere, with head at its first separator. This is exactly
StackEncoding.homeTape, with a harmless explicit blank at its left.
Use the supplied StackSimulation.controller: main dispatch, separator
seek, inspect, push/insert/rewind, delete/rewind, and finish. Control
labels are enumerated injectively from the start under all four symbol
successors. Discarding unused label representations changes no reachable
local rule. This uses the licensed StackProgram.compile_run and
StackSimulation.controller_simulates supply under their actual finite
label and represented-register hypotheses. It does not apply a generic
compiler theorem without first supplying ML-S's run of Theorem 11.6.

**Theorem 12.2 (structural simulation for arbitrary finite stack words).**
Starting at (ML.18), every ML-S instruction has the supplied finite
four-symbol macro and decodes the exact successor register family and
control. Every internal prefix has its source instruction, pending
symbol/shift, saved continuation and current scan phase. At a successful
ML-S halt, the four-symbol head is at the first symbol of register zero;
its contiguous bit output is exactly that register, terminated by the
next separator even when the output is empty.

Proof. A separator seek decrements its finite separator counter exactly
at separators, passing every intervening bit without changing it.
Thus its current head is the intended register's first symbol; an empty
register presents the following separator. Peek chooses its exact
empty/zero/one branch and rewinds to the unique left boundary blank.
Pop does the same on empty. On a bit it shifts the entire finite
nonblank suffix one position left, writes the final blank and rewinds.
No earlier register is altered. Push seeks the same position, retains
a carried symbol in finite control, and shifts every following nonblank
one place right until the first blank is filled; it then rewinds.
This inserts exactly the desired bit. These are the supplied insertion,
delete, seek and rewind contracts on arbitrary finite nonblank suffixes;
explicit trailing blanks are equivalent tapes. Goto preserves the tape.
The source halt advances once from the first separator and enters
finish. These cases prove the boundary assertion by induction over any
finite ML-S prefix. Each phase retains the information about an
incomplete shift or seek, so it is not interpreted as another committed
source instruction. The output assertion follows from (ML.18), including
an immediately following separator for an empty word. $\square$

**Definition 12.3 (two-bit tape and eleven-state adapter).** Encode
blank, zero bit, one bit and separator by $00,01,10,11$, respectively.
Encode a four-symbol head at integer $h$ by binary position $2h$.
For each four-symbol state $q$ allocate eleven binary states: aligned
entry 0, first-read alternatives 1–2, first-write alternatives 3–6 and
movement alternatives 7–10. At entry, preserve the first bit and move
right into its retained alternative. Reading the second bit identifies
the symbol. On a source step $(w,d,q')$, write the second bit of $w$
and move left into its first-write alternative; write its first bit and
move left for $d=L$, right otherwise. The movement alternative preserves
its bit and moves left for $d=L$ or stay, right for $d=R$, arriving at
aligned entry $q'$. On a source halt, preserve the second bit and move
left to the sole binary halt. Unreachable alternatives attached to a
terminal read have defined preserving rules to halt. All rows have both
binary read cases, and all destinations are allocated states or halt.

**Theorem 12.4 (all-input compiled-state and output correspondence).**
Each four-symbol step on any finite represented tape has exactly four
binary transitions between aligned entries and preserves the pointwise
two-bit encoding. A four-symbol halt has two preserving binary transitions
and restores the aligned head. Therefore the fixed binary table for ML-S
halts on every encoded accepted arithmetic frame, at the encoded first
output symbol, with exactly Theorem 11.6's framed output under the
reverse symbol decoding. Blanks outside the finite represented tape
remain true $00$ blocks; both bilateral directions and stay are covered.

Proof. After the two reads the old pair is known in control; the second
bit has its intended new value and the first is pending. The next write
finishes exactly that pair. For left movement the two final moves visit
the preceding pair's second then first positions. For right they visit
the current pair's second then the next first position. For stay they
visit the current second then return to its first position. No other
pair is changed. The two halt reads preserve both bits and return to
the original first bit. Induction over four-symbol macro transitions,
including this explicit pending interpretation, gives the claim. Apply
Theorems 11.6 and 12.2. Actual output decoding reads pairs $01,10$ as
output bits until the real $11$ separator; it never infers omitted output
zeros from unrepresented tape. This is structural simulation over all
represented words, not extrapolation from finite tests. $\square$

## 13. A complete closed block representation of the Wang word

**Definition 13.1 (literal templates and resolved destinations).** For
each of the sixteen possibilities for the two source binary rules'
write bits and movement directions, take the entire source-state block
of the fixed ML-N copier. Its only external continuations are the
source zero-read and one-read destination entries. This is a finite
literal template $T_e$ with two explicit destination slots. If the
materialized source binary table has rows $q<m$, put

$$
b_0=0,\qquad b_{q+1}=b_q+|T_{e(q)}|.
\tag{ML.19}
$$

Store all $b_0,\ldots,b_m$ and, for every $q$, its template identifier
and the resolved addresses $b_{\delta(q,0)},b_{\delta(q,1)}$, with
$b_m$ the sole non-erasing halt. At local template state $u$, replace
an internal destination $v$ by $b_q+v$ and an external slot by its
stored resolved address. This gives every row, at both reads, of a
complete non-erasing binary table with $b_m$ states. It is a finite
block representation with no missing evaluator entry. Its inputs are
public table bytes alone.

The associated word $W_U$ has $13b_m+1$ B instructions. Its block at
$13c$ is the NWMG thirteen-instruction block for non-erasing state $c$,
with each transition destination $c'$ replaced by jump target $13c'$;
its final instruction at $13b_m$ is M. The halted program counter is
$13b_m+1$. The block representation stores literal templates, their
finite sizes, every base and every resolved external continuation;
fetch at any PC is thus fully determined. A flat expanded instruction
array and this closed encoding represent the same finite word. The
encoding does not assert that the expanded array has been installed.

**Theorem 13.2 (block-image correspondence and ownership).** The table
of Definition 13.1 is the ML-N copier on the materialized binary
ML-S table, up to the explicit finite relabeling by (ML.19). Its Wang
word therefore has the existing ML-N/NWMG correspondence on every
finite input and every finite run prefix. In particular, on the accepted
inputs of Theorem 12.4 it has the same finite framed result, subject to
the actual input conversion and output decoding. This does not identify
abstract B steps with paid LAB primitives or assert any installed code,
controller, decoder or resource account.

Proof. In the copier, all states internal to one source-state block
use only the two selected write bits and directions, the internal
phase and one of the two destination entries. They consult no other
source-state row. Replacing that row's name by $q$, its local labels by
$b_q+u$, and its two continuations by the stored bases therefore maps
each local rule to exactly the corresponding generic copier rule.
The intervals $[b_q,b_{q+1})$ are disjoint and exhaust all nonhalting
states, so this is a complete graph isomorphism. Internal targets remain
in their interval; the two external targets are allocated entries or
the sole halt. The NWMG block construction then applies at every state
and both reads; its final M implements the same halt convention.
The ML-N copied-record invariant and Theorems 3.3–3.4 give the existing
conditional lower-layer correspondence. The actual conversion starts
from (ML.18)'s paired bits, wraps them by ML-N's initial record, then
uses the NWMG $10/11$ encoding before ML-L. The inverse at halt first
finds the active record and original coordinate offset, then decodes
pairs and the real output separator. These are required concrete data
conversions, not hidden numerical inputs. $\square$

**Definition 13.3 (sealed consumer boundary).** The public immutable
objects are ML-S, the four-symbol and binary tables, the literal copier
templates and resolved block image. The variable numerical input is
only the actually accepted ML-F word. The original port and its physical
binding are separate retained session objects and are never arguments
of a public numerical compiler. The output observation is the finite
ML-F word read from the actual returned head and separator. A consumer
must back table/image fetch, current PC and scan phase; actual work and
source references; conversion, loader and decoder cursors and buffers;
received bits, return phases, grants and cleanup. Selecting a compressed
code representation additionally requires backing its address search
and local-template selection. Supplying a flat expansion instead
requires charging that expansion's actual installation. Neither choice
permits a host evaluator or uncharged operational integers.

Theorem 13.2 gives sufficiency of the stated representation for the
specified mathematical computation. Actual same-port continuation,
complete controller backing, a full evaluator LAB run and the
simultaneous account of §6 remain separate premises/obligations of that
execution; no short reference run or closed code image discharges them.
The spatial and minimum-information limits of §7 are unaltered.

## 追加锚（本行以下为增补区）

## 14. Finite address decoding of the closed Wang image

**Definition 14.1 (paged image object).** Consider the block image of
Definition 13.1 with $m\ge1$, strictly increasing bases
$0=b_0<\cdots<b_m$, sixteen nonempty templates, and valid resolved
destinations. Its byte layout consists, in order, of a twenty-byte
header; sixteen template records, each with a four-byte size and two
ten-byte rules per template state; $m+1$ eight-byte bases; and $m$
seventeen-byte bindings. An internal rule destination is a nonnegative
local state. The two negative eight-byte two's-complement words encode
the two resolved external destination slots. All multibyte integers
have least significant byte first.

Let its length be $L$, let $P=4096$, and put
$C=\lceil L/P\rceil$, $p=2^{\lceil\log_2 C\rceil}$ and
$z=\mathbf1_{C<p}$. Initialize $C$ pages with the actual image bits,
padding only the last page with binary zeros. When $z=1$, initialize
one further all-zero page. A perfect binary directory with $p$ leaves
points to the $C$ image pages in order; each remaining leaf points to
that same additional zero page. Each internal directory object has
two actual reference fields. Each page has $8P$ binary fields.
No page bit has a third value. Sharing the additional zero page does
not identify two image addresses or change the interpretation of a
valid address.

The installation here receives the uncompressed finite image. An
inflation performed while forming this immutable installation is not
an operation of its address decoder. If inflation occurs inside a
claimed runtime, its own input, output, control, scratch and overlap
must also be represented and charged. The paged image definition
alone supplies no such inflation account.

**Definition 14.2 (register decoder).** Fix a valid image for which
all image addresses, bases, $13b_m+1$, and the nonnegative intermediate
sums below fit in sixty-four bits. The decoder's scalar registers are
binary sixty-four-bit fields. Its program is a finite graph whose
nodes have an eight-bit operation, a sixty-four-bit immediate word,
three register-reference fields and two successor-reference fields.
Its operations are constant assignment, copy, addition, subtraction,
fixed shift, equality, comparison, byte/word reading, conditional and
unconditional successor selection, and reply phases.

These operations specify a finite register transition system. A register
microstep may contain a bounded field-selection or fixed-width clearing
circuit. Intermediate states below are cuts of that transition system.
Expansion of these circuits and initialization into a literal installed
ML-I primitive graph is a separate refinement obligation; the mathematical
transition function is not itself that installed graph.

Addition and subtraction scan from the low bit with one carry or
borrow; equality scans all bits; comparison scans from the high bit,
retaining whether the first unequal pair has been found. A word read
first copies its byte address into a separate address register. For
each bit, it follows the directory according to the page-number bits,
then selects the physical page field using the twelve within-page
address bits and the three within-byte bits. The address and unfinished
result remain represented while the next byte address is formed by
a carry scan. The decoder therefore does not use an integer-to-object
map to obtain a page.

Initialization reads the actual header and scans the sixteen actual
template sizes. It obtains the start of the bases and then the start
of the bindings by addition and fixed multiplication. Multiplication
by a fixed nonnegative integer is the finite sequence of shifts and
additions selected by its literal binary digits. These are public
code operations, independent of the numerical ML-F input.

For a requested PC $c$, first handle $c=13b_m$ as M and
$c=13b_m+1$ as stopped. Reject larger PCs. Otherwise compute
$(q,j)$ with $c=13q+j$ and $0\le j<13$ by sixty-four restoring
division stages: shift the partial remainder, append the next actual
PC bit, compare to thirteen, and, when necessary, subtract thirteen
and set the corresponding quotient bit. The cases $j=0,1$ give R
and $J(13q+8)$ directly. In the other cases, search the base array
with a represented interval $[l,h]$, initially $[0,m]$, until
$h-l=1$. Read the binding at $l$, scan template headers to its
template identifier, and read the rule at local offset $q-b_l$,
with read bit zero for $j<8$ and one otherwise. Resolve the two
negative destination words through the actual binding. Resolve a
local destination $v$ as $b_l+v$. The finite NWMG block selector
then emits its actual $j$th instruction.

A reply consists of a three-bit instruction kind and a sixty-four-bit
jump destination, zero for nonjumps. Each bit passes through an
occupied binary latch to the output. End follows the last bit.
Acknowledgement precedes Return. A new request is disabled until
Return; an incomplete reply retains its position and latch occupancy.

**Theorem 14.3 (all-address component correspondence).** For every
valid image and every PC in Definition 14.2's range, the register
decoder terminates with exactly the instruction of Definition 13.1,
including its final M and stopped PC. Every intermediate register
state has an interpretation as an unfinished stated scan, address
search, rule resolution or output suffix. This is a correspondence
of this finite decoder component, not of an entire LAB/session
controller.

Proof. A page address has a unique high-bit path in the perfect
directory. The path selects precisely its page, and its remaining
fifteen bits select precisely the desired physical bit field.
Induction on the result-bit position proves the little-endian word
read, including all byte-boundary carries. During address copying,
the preserved source address and the copied prefix give the stated
unfinished interpretation.

The elementary carry and borrow invariants prove scalar addition
and subtraction. In restoring division, after each scanned PC prefix
$u$ the stored quotient and remainder satisfy
$u=13Q+r$ with $0\le r<13$. Appending one bit makes the temporary
remainder less than twenty-six, so one comparison and at most one
subtraction suffice. After all sixty-four stages this gives the
unique $q,j$.

For a nonterminal $q$, strict base monotonicity gives the invariant
$b_l\le q<b_h$. Reading the midpoint base preserves that invariant
on the selected half. The positive interval length strictly
decreases until it is one; hence $l$ is exactly the unique source
row whose template interval contains $q$. Header scanning terminates
at its finite identifier. The binding supplies its actual template
and both actual external destinations. The rule read therefore
resolves to exactly the corresponding complete non-erasing table
row of Theorem 13.2. The finite thirteen-position case distinction is
the same NWMG block construction, so its selected instruction is
correct.

Each bit scan has bounded position, each directory path has finite
height, each search interval decreases, and each header scan has
at most sixteen entries. Thus all phases terminate. Partial results,
carry, comparison flag, interval endpoints, current directory
reference and output position determine the next specified transition.
No current result is replaced by an audit transcript. End,
acknowledgement and Return give precisely the stated reply order.
The argument quantifies all addresses of this fixed code image;
it does not obtain that conclusion by sampling requests. $\square$

**Definition 14.4 (component storage and tariff boundary).** Let the
register graph have $a$ nodes and $r$ named scalar registers, in
addition to its copied-address register. Its image header retains
length, height and root. Its controller header retains PC, saved PC,
directory cursor, a scratch reference, decoder entry and the input,
output-kind, output-destination and address-register bindings.
Use a fifty-seven-bit binary continuation bank for the phase, scan
positions, carry, comparison flags and occupied/ended/acknowledged
flags. Let $w$ be the chosen reference width. The represented component
has

$$
\begin{aligned}
O&=C+z+(p-1)+a+(r+1)+2,\\
R&=2(p-1)+5a+10,\\
B&=8P(C+z)+72a+64(r+1)+71+57,\\
S&=B+wR+O.
\end{aligned}
\tag{ML.20}
$$

Here $O$ includes the actual pages, directory, program nodes,
scalar-register objects and two headers; the last $O$ bits are the
retained grants. The seventy-one image-header bits store length and
height. Binary zero padding is allocated material. All null
references occupy reference fields. No independent output transcript,
reference-reader result or audit counter is a register or continuation
input.

Reading or writing a scalar bit has its field tariff and the finite
register-selection tariff. A directory edge read has width $w$ and
one navigation step. Page selection has fifteen binary tests and
one physical bit read. Program operation/immediate reads and actual
successor-reference assignments have their corresponding bit and
reference tariffs. Carry, scan-position, phase and latch changes
are bit-field operations. Reply transmission, End, acknowledgement
and Return have distinct events. Initializing every stated field and
grant is part of installation. These coordinates concern this
specified data and register-graph layout; they assert no optimality.
A separate primitive engine adds its actual code, selector state and
scratch to (ML.20). Its installer also adds its chronological pending
material and overlap. The formula does not determine those extra
quantities and cannot replace their realization.

**Proposition 14.5 (retention, audit erasure and composition limit).**
After its installation, any finite sequence of completed decoder
requests retains exactly the component storage (ML.20).
Erasing independent transcripts, inspection counters and comparison
oracles leaves its represented next transition and emitted bits
unchanged. An exact account for this component cannot by itself
supply an exact account for a surrounding computation.

Proof. The request graph allocates no new page, directory, register
or code object. Each transition changes only initialized scalar,
reference, continuation or latch fields. Output is transferred from
the represented result registers, followed by End and acknowledgement;
past output observations are never read by the controller. Induction
on requests proves constant retained component storage and the
audit-erasure assertion.

For the last statement, the surrounding state can vary in head,
program continuation, original-port binding, acquired cache, pending
receipt or a live allocation while this component has the same
represented state. Definition 3.1 or Definition 5.1 can then prescribe
different next actions. Theorem 14.3 supplies neither their represented
fields nor their updates. Similarly a simultaneous peak requires
storage at one common cut, including partially initialized installation
material, all live roots, reference-width overlap and unfinished
source/observer transfers. Adding this component's retained amount
to unrelated individual peaks does not establish that common cut.
The exact-fiber condition of PG19.2 still applies to the entire
claimed state and operation domain. $\square$

## 追加锚（本行以下为增补区）


## 15. Direct field control with an arbitrary finite reserve

**Definition 15.1 (reserved field configuration).** Fix a finite reserve
of $K$ distinct, actually granted objects. Each object has four reference
fields and eight binary fields. Reference zero is a parent in a work
vertex; references one and two are its left and right links; reference
three is its routing-header link. In a list header, references one and
two are head and tail. In a bit cell, reference one is next and bit zero
is payload. Bit seven records extraction from the reserve. The initial
reserve chain uses reference zero; extraction takes its actual head,
advances to that head's actual successor, clears the returned object's
reference zero, and sets its bit seven. No numerical value is converted
into a reference. The reserve may be exhausted. Exhaustion has no
successful allocation successor and cannot complete an unfinished macro.

A direct field graph is a finite pointed graph with operations: set or
test a binary register; copy, test null or compare reference registers;
read or write one specified reference or bit field; bind an actual graph
continuation; follow a saved continuation; and transfer a bit, End or
acknowledgement at its supplied connection. Its registers contain only
bits or actual references. An operation's field selector is a fixed
literal of its graph vertex. The current graph vertex and saved return
references are control locations. Dynamic tape positions, input lengths,
and reserve size are not graph labels.

In an explicit interpreted representation a graph vertex instead has a
five-bit operation, sixteen-bit selector, two operand references and two
successor references. Operand references bind actual register locations;
a continuation-binding vertex may bind an actual code vertex. The
interpreter first reads the operation's five fields, then the selector's
sixteen fields, then the four references, preserving every read prefix.
It dispatches on its represented operation, captures source operands,
performs the selected access, stores its result and finally installs the
selected continuation. It has separate bit and reference latches. Its
bounded scan index, operation, selector, finite phase, occupied output
bit and wait/End/acknowledgement flags are part of its state. This defines
a transition system with finite control and actual field accesses;
a compound finite-control transition is not thereby a single ML-I bit
primitive.

**Definition 15.2 (program cells and literal bilateral driver).** For an
arbitrary finite B program, reserve one object per instruction. Three
binary fields encode L, R, M or J. Reference one is the next instruction,
or null at the end; reference two is a jump's actual destination object.
The initial instruction reference is null for the empty program. The
instruction number used to describe this finite list is a decoding
coordinate, not a runtime counter.

The driver retains root, old and intended head, old and intended
instruction reference, an arm bit and its intended value. Fetch reads the
instruction object's three bits and next reference. M inspects the
current right leaf's actual left link and calls promotion only when that
link is null. J inspects the same link and selects the saved next or
actual jump destination. The two movements use precisely (ML.3), with
actual parent/root equality at a crossing. A destination with null right
link is split before use; an existing branch is used unchanged.

Promotion and splitting are subgraphs, with an actual saved continuation.
Promotion reserves its marker before attachment. Splitting retains the
old marker and reserves its new marker, right vertex and routing header
before its three attachments. Proper-ancestor maintenance retains child,
parent, side, header, new cell and old tail until linking and tail update
are complete. Return follows the saved continuation. Commit copies the
intended head, arm and instruction reference. No subsequent instruction
fetch is on any path between the initial fetch and this commit. Loading
reads an actual input-cell chain and executes Definition 2.2; a null
initial input chain still creates one zero cell.

**Theorem 15.3 (reserve-parametric driver correspondence).** For every
finite B program, every finite input and every finite prefix of its B
run, the direct field driver has exactly that sequence of committed
configurations whenever its finite reserve suffices. Every internal
prefix has an old configuration, intended successor, and a uniquely
specified unfinished field/growth/maintenance operation. At complete
boundaries the comb, head, arm and instruction-reference interpretation
is that of Definitions 1.3 and 2.1. Conversely each completed driver
macro is the next B instruction. This applies to finite prefixes of
nonhalting runs, without a termination assumption.

More precisely, let $q$ be the program length and $m$ the supplied input
length. At a complete boundary let $V,H,D$ be the actual work-vertex,
routing-header and routing-cell counts. With no intervening job, the
number of extracted reserve objects is

$$
q+m+V+H+D.
\tag{ML.21}
$$

Any $K$ at least the largest such count along the required completed
prefix supplies every intervening extraction as well. There is no bound
on $q,m$ or the prefix length independent of $K$ in this assertion.

Proof. The installed instruction list is injectively addressed by its
actual objects. Thus null is the sole halt, a next link is the ordinary
successor, and a jump link is precisely its installed destination. Fetch
and bit inspection select the same cases as Definition 3.1. For the
loader, following its actual input cursor either consumes the next
received bit or reaches null; induction gives Definition 2.2, including
the empty-input case.

The geometric part is Theorem 3.3's case argument, now with each of its
saved references realized explicitly. An outward move takes the current
left link. An inward move takes its parent unless that parent is the
root, in which case it crosses to the other root arm and changes the arm
bit. These are all cases of (ML.3). Mark and jump inspect the actual bit
leaf, so a repeated mark makes no edit and a jump chooses the correct
installed reference.

The promotion guard reads both child links before any edit. The split
guard reads the existing left link and null right link. Its old marker
and fresh objects survive all partial attachments. During maintenance,
parent-left equality selects side zero; otherwise parent-right equality
must select side one. The append initializes its bit and next link before
altering a header or old tail, and advances the tail only after linking.
The child reference then becomes the parent. This ascends a finite
ancestor chain and returns to its saved continuation. Every intermediate
attachment or append retains exactly its remaining obligation. The
saved old configuration remains interpretable during partial commit;
only the completed commit is another B boundary. Induction on completed
macros proves forward simulation and the same case analysis proves the
converse.

The program and original input occupy exactly $q+m$ extracted objects.
Every subsequent extraction is either a work vertex, a routing header or
a routing cell. Promotion extracts one new vertex; splitting extracts two
new vertices and one header; each ancestor append extracts one routing
cell. No other subgraph in this driver extracts an object. This proves
(ML.21). Extracted counts increase, and a partially initialized event's
objects are a subset of those retained at its next complete boundary.
The stated bound therefore covers every intermediate extraction. Taking
larger finite $K$ covers any requested finite run prefix; it does not
identify the pool bound with a program, input or mathematical-domain
bound. $\square$

**Definition 15.4 (bit lowering of the image register graph).** Give each
sixty-four-bit scalar a bank of sixty-four binary locations, and give
source snapshots disjoint scratch banks. Constant assignment writes all
sixty-four fields. Copy branches on each source bit and writes the
corresponding target field. Shift copies its source snapshot at the
fixed displaced index, or writes zero outside the source range. For
addition and subtraction, a finite Boolean decision tree on the two
source bits and carry or borrow writes the result bit and next carry or
borrow. Comparison scans the high positions first and retains whether
the first unequal pair has been found. Equality scans every position.
Both comparisons write their predicate to the low target bit and clear
the remaining sixty-three fields.

For a word read, preserve a separate address snapshot. For each result
bit, follow actual directory links selected by the page-number bits.
Form the fifteen-bit within-page selector from the twelve low byte
address bits and the fixed three-bit position within that byte. A full
binary decision tree on these fifteen bits ends at the corresponding
literal physical page-field access. Its continuation is an actual saved
reference. After each eight result bits, increase the copied byte
address by the same carry subgraph. Clear unused high result fields.
The page-selection tree is shared by calls through saved continuations;
it is not a host-indexed table of fetched instructions.

**Theorem 15.5 (field lowering and its exact domain).** For every valid
image of Definition 14.2, the bit lowering has the same register-graph
boundaries and fetched instructions as Theorem 14.3. Every intervening
field-graph prefix preserves a source snapshot, an unfinished bit scan,
a directory path, or a page-field selection and its continuation.
Connecting its output registers directly to Definition 15.2's instruction
case analysis supplies the same finite B prefixes for the encoded image.
The sixty-four-bit code-address premise does not bound the input word,
tape extent, reserve parameter or an unrelated finite B program.

Proof. Snapshot copying precedes any target overwrite, so source/target
aliasing preserves the source word. Inductively, after $i$ low bits of
addition or subtraction, the written prefix and retained carry or borrow
are those of binary arithmetic on the two preserved source prefixes.
The finite truth tables are exactly exclusive-or and majority, or the
borrow table, respectively. The valid-image premise excludes an
arithmetic result outside the specified nonnegative word range. The
first unequal high pair determines strict comparison; if none occurs,
comparison is false and equality true. Clearing all other predicate
fields preserves the register-graph representation.

Directory traversal selects the actual high-bit path of the copied
address. The fifteen-level decision tree then chooses its unique
physical field. Its leaves contain literal selectors, while the choices
on its path read the represented offset. Bit-position induction proves
the requested little-endian word, including the eight-bit boundaries.
These are exactly the component operations of Definition 14.2.
Induction over register-graph steps and Theorem 14.3 give the fetched
instruction. A saved field-graph return carries the computation directly
to its consuming driver; no external transcript or reference-reader
answer is a runtime operand.

The code address concerns the fixed immutable image. Input and comb
navigation instead follow actual list/tree references, with a separately
chosen finite reserve. The arbitrary instruction-list realization of
Theorem 15.3 uses actual next and jump references. Neither construction
uses the image-address range as a bound on those other domains.
$\square$

## 16. Streaming the actual input and locating the returned output

**Definition 16.1 (fused input converter).** Let $x$ be an actual finite
bit-cell chain and let $r\ge1$ be the fixed stack-register count. A finite
converter writes the following stream to a new bit-cell chain. It first
writes the copier header, with every copier bit passed through NWMG's
$0\mapsto10$, $1\mapsto11$. It then supplies source-binary bits in the
order: $11$ for the initial separator; $01$ for each actual zero input
bit and $10$ for each actual one; and $r$ further $11$ pairs. The input
cursor advances only after its bit is read.

For each supplied source-binary bit $b$, append the copier data block
whose eight fields are

$$
(0,1,0,f,1-b,b,0,0),
\tag{ML.22}
$$

again through the NWMG bit encoding. The first-block flag $f$ is initially
one and is cleared after this block. Finally append the encoded copier
end block. The fixed count $r$ is finite converter control; no dynamic
input length or value is hidden in its control labels. Every append
uses an actual output header, old tail and fresh bit cell. The original
input and unfinished output remain retained while conversion proceeds.

**Theorem 16.2 (all-word acquired-data conversion).** For every finite
$x$, the completed stream of Definition 16.1 is exactly the B input of
Theorems 12.4 and 13.2 for stack zero $x$ and $r-1$ empty stacks. Its
length is $32(|x|+r+2)$. Its extracted objects, apart from previously
installed material, are one output header and exactly that many output
bit cells. Together with the retained original input the count is
$|x|+1+32(|x|+r+2)$. This conversion imposes no new bound on $N$, prior
components, masks or cylinder lists in an accepted arithmetic frame.

Proof. The four-symbol serialization is one separator, $|x|$ actual bit
symbols and $r$ closing separators. Definition 12.3 encodes these symbols
by exactly the pairs streamed above. Their number is $|x|+r+1$, so the
source-binary stream has length $2(|x|+r+1)$ and is nonempty even for
empty $x$. Formula (ML.22) is exactly Definition 4.6's data block: one
head flag in the first data block, one of the two value fields, and zero
unconsumed/handoff fields. The header and end block complete that same
copier input. NWMG encodes each of its bits by two bits, hence the final
length is $16(2(|x|+r+1)+2)=32(|x|+r+2)$.

The append invariant says that its head-to-tail chain is exactly the
already emitted prefix. Its fresh cell is initialized before linking;
its old tail is retained until the header advances. Thus every internal
prefix is an unfinished actual stream append, and the output count is
one header plus one cell per bit. No input bit is guessed from an absent
suffix. Arithmetic acceptedness and the arbitrary finite bit lengths
remain precisely A's premises in Theorems 10.5 and 11.6. $\square$

**Definition 16.3 (returned-header decoder without coordinate recovery).**
Suppose the actual B head is at the first NWMG bit of the returned active
copier header. Retain this reference and scan its actual eight-bit
block. Reading one copier bit checks the first NWMG bit is marked,
advances one actual comb link, reads the second bit by its leaf arity,
and advances to the next pair. Thus a block read uses sixteen actual
comb links and eight retained binary results.

Check the active-header fields, then scan its data blocks. Each has type
$(0,1,0)$, exactly one value field, and zero consumed/handoff fields.
Stop this search at its actual source-binary head flag. Read the value
there and at the next data block as a pair. Pair $01$ appends output zero,
$10$ appends output one, and $11$ terminates at the actual separator.
Pair $00$ is not output. After appending a bit, continue with the next
pair of data blocks. The decoded output has a retained linked header;
printing follows its actual next links, transfers each read bit through
an occupied latch, then transfers End, acknowledgement and Return.
The output sink is not read to choose any later bit or continuation.

This decoder retains no integer coordinate and does not count retired
records. Its task is the evaluator's returned output, not reconstruction
of the source tape at every original integer position.

**Theorem 16.4 (actual-head output correspondence).** On any well-formed
returned active copier record whose unique binary head is at an aligned
four-symbol output word followed by a separator, Definition 16.3
terminates with exactly that word. It preserves the actual returned-head
binding and reaches the actual separator. Every prefix retains its
unfinished record scan, first pair bit, output append or printing phase.
Together with Theorems 12.2, 12.4 and 13.2 this supplies an output
conversion on every accepted evaluator input, conditional on its actual
completed LAB execution and the stated field-operation completions.

Proof. The first part of the scan begins at the supplied active header,
not at a header selected by an answer or coordinate oracle. The active
record consists of finitely many well-formed data blocks with exactly one
source-binary head. Its flag search therefore terminates at that very
head. The NWMG first-bit check and actual second-bit arity read return
each stored copier bit; the data fields then return each source-binary
value. Aligned two-bit decoding is exactly Theorem 12.4's inverse:
$01$ and $10$ are the two bit symbols and $11$ is the separator. The
finite output word has such a separator by Theorem 12.2. Therefore the
pair loop terminates there, including immediate termination for an empty
word. It never infers an output zero from unrepresented space.

All cursors are actual references and all alternatives use already read
binary fields. Appending preserves the emitted-prefix invariant of
Theorem 16.2. Printing reads that chain in order and cannot reach End
until its cursor is null; the supplied acknowledgement precedes Return.
Its latch and current cursor retain an unfinished transfer. Theorem 13.2
binds the completed B head to the returned active copier header, so this
same decoder composes with the unchanged evaluator suppliers under the
stated completion hypotheses. It gives no claim about a whole machine
history or recovery of an unobserved physical source. $\square$

## 17. Finite-control cuts, storage and the primitive boundary

**Definition 17.1 (reserved field-machine storage).** Let $a$ be the
number of installed interpreted field-graph vertices, $r$ the number of
reference-register locations and $b$ the number of binary-register
locations. A vertex has twenty-one bits and four references, including
its two operands. A register location is a separate granted object. The
interpreter has eight reference fields and thirty-eight bits: a
sixteen-bit selector, five-bit operation, five-bit index, seven binary
latches/flags and five-bit phase. Choose one reference width $w$ sufficient
for all these objects, their null references and the $K$ granted reserve
objects. Its retained storage is

$$
\begin{aligned}
O&=K+a+r+b+1,\\
R&=4K+4a+r+8,\\
B&=8K+21a+b+38,\\
S&=B+wR+O.
\end{aligned}
\tag{ML.23}
$$

These terms count represented interpreter state and interpreted graph. A
native realization of its finite dispatcher, selectors and phase transitions
adds its own installed graph and grants; that expansion is not included in
(ML.23). The final $O$ bits are retained grants. If a paged immutable image is
also retained, add its actual objects, fields and grants from Definition
14.1 before choosing $w$. Unextracted reserve objects count in $K$;
extracted objects do not add a second copy of themselves. References and
grants do not acquire a free third binary value.

**Theorem 17.2 (same-reserve cuts and the limits of their tariff).**
Throughout any execution using this same fixed reserve and installed
field graph, (ML.23) is the retained field-machine storage at every cut,
including an unfinished edit, unlinked append, copied address, partial
code read or occupied output latch. Extraction changes occupancy and
links but not that storage total. There is no reference-width overlap
in this fixed-width construction. Its whole actual reserve is paid from
the first retained cut.

Each completed interpreted graph action has exactly twenty-one actual
code-bit reads and four code-reference reads before dispatch, and a
finite sequence of captured operand accesses, result writes and
continuation assignments. These counts alone do not prove a complete
single-bit ML-I tariff, a chronological installation, an online
unbounded allocator or a simultaneous original-source/service account.

Proof. No execution transition allocates an object outside the already
supplied reserve. Its four reference and eight binary fields persist
when it moves from reserve chain to pending material or completed work.
All code, register and interpreter locations also persist. Changes to
references, bit values and occupancy therefore leave each term of
(ML.23) invariant. The choice of $w$ remains sufficient and there is no
second width whose fields could overlap. A different construction that
widens this arena must count both its old and new fields at its real
copying cuts; (ML.23) is not such a construction.

The code-reader phases have lengths five and sixteen and then read the
two operands and two successors. Each captured source survives until its
consuming access. The result survives until its writeback and the saved
successors survive until continuation assignment. Thus the stated counts
and finite-control prefix interpretations hold.

A finite-control update can still write more than one index or phase bit;
a selector can still require its own primitive field-selection subgraph.
Their intermediate single-bit cuts are not identified by the preceding
counts. Similarly the retained configuration does not specify how its
initial code, reserve, grants and headers were installed. Finally its
original source connection, service cache, receipt chain, retained-job
directory and joint source/observer cuts are not arguments of (ML.23).
Holding this configuration fixed while varying such data can change the
next legal Read, output or allocation. The fiber criterion of PG19.2
therefore forbids treating this partial storage account as the complete
service account of §6. $\square$

## 追加锚（本行以下为增补区）


## 18. Literal primitive locations for the field interpreter

**Definition 18.1 (native control boundary ML-P).** Keep precisely ML-I's
individual binary and reference-field accesses, reference assignment,
null/equality/arity tests, supplied finite transition graph, finite bit
connections and current granted rights. A vertex of this native finite
transition graph carries one such primitive action and its fixed literal
field selector. Following its wired zero/one successor is the supplied
finite-control transition; its selection, successor-reference access and
control-reference assignment are charged. A field read returns into its
retained bit or reference read latch. A field write and the following
primitive occur at different cuts. Tests and writes are different vertices.
A read's return latch is part of that primitive's result, not a promise of
a later unrepresented read result.

This boundary is the finite transition graph already supplied by ML-I,
not a new evaluator instruction. Its primitive labels do not include
an encoded-opcode dispatcher, a variable selector, word arithmetic,
validation of a compound frame, or a field-interpreter step. Describing
the mathematical primitive graph in Python or C does not require a second
simulation of that host language. Conversely the interpreted field graph
of Definition 15.1 is data: its operation, selector and continuations are
actually read by the native graph below. Treating that entire interpreted
operation as a native vertex would not meet this definition.

A native graph's fixed field selector is wiring attached to that vertex.
For example, the vertices reading fields zero and one are distinct native
locations; a variable two-valued selector must first traverse its actual
bit-test tree. A tuple naming a finite native location is a mathematical
encoding of that location, not an uncharged variable arithmetic register.
All such locations and their wiring belong to the installed material.

**Definition 18.2 (interpreter state).** An interpreted vertex retains
its five operation bits, sixteen selector bits, two operand references
and two successor references, as in Definition 15.1. A reference-register
object has one reference and no binary field. A binary-register object
has one binary field and no reference. The remaining payload layouts are
four references/eight bits for reserve cells, two references/no bits for
directory forks, and no references/32768 bits for pages. Layout tests are
local ML-I arity tests; a whole grammar or arithmetic validity check is
not hidden in one of them.

The native interpreter has nine separately backed reference registers
PC, old PC, a, b, zero, one, rx, ry and destination. Its binary registers are
five operation fields, sixteen selector fields, predicate, bx, occupied,
waiting, ended and acknowledged. It additionally retains the current
native location, reference read result, saved reference, address latch
and binary read result. These locations and latches persist during every
operation. Bounded scan positions and instruction phases are expanded
into distinct native vertices. They have no multibit update instruction.
In particular a clear of sixteen fields consists of sixteen writes,
and a bit-copy read and its destination write have an intervening cut.

At fetch, read the actual five code fields into their five separate
register locations, one at a time. Do the same for all sixteen selector
fields, then capture the four actual code references. Dispatch through
a high-to-low five-bit test tree. Reset predicate and destination through
separate literal assignments. Each operation requiring a selector tests
all sixteen selector fields through a finite tree. Its admissible leaves
are respectively 0–3, 0–7, 0–32767, 0–1 or 0–1 for reference cells,
binary cells, pages, Boolean constants or directory edges. All other
leaves refuse. No runtime integer-to-field conversion supplies a leaf.

The operation paths are the following primitive compositions. A source
reference is first captured; a dereference uses the retained actual
address latch. Copies to destinations happen only after source capture.

| Interpreted operation | Native path after fetch and local layout checks |
| --- | --- |
| put / test | Select literal zero/one and write the actual bit register; or read its field and test the captured bit. |
| copy / bind | Read the actual source register, or the already captured literal code binding, then write the actual destination register. |
| null / equal | Capture the one/two reference values, retain both for equality, perform the declared test and write predicate through its selected literal path. |
| get / set | Select one of four literal reference-field accesses, capture the read or source value, then write its actual destination. |
| read / write | Select one of eight literal binary-field accesses; preserve the captured bit until its separate write. |
| edge / page | Select one of two literal directory links or one of 32768 literal page fields. Page selection has fifteen low selector tests and rejects a set high selector bit. |
| indirect | Read the actual saved continuation register, test its code layout, and assign destination. |
| emit | Read the actual input bit, retain bx and occupied, transfer that bit at the supplied output, then clear occupied. |
| End / Ack / Return | Execute the supplied connection operation, retaining its phase flags. Ack requires ended; Return requires acknowledged. |
| wait / goto / fault | Set waiting and finish the current operation; continue; or refuse without another completed operation. |

Commit tests destination for null. A nonnull destination becomes PC;
otherwise the captured predicate selects the captured one/zero reference.
The old PC remains in its separate reference register through completion;
the next-PC assignment precedes the next fetch. The next native
instruction is determined by the installed native graph and its captured
values, never by an observer's decoding of a B state or an output list.
The arbitrary generic B program continues to use actual next/jump
references, independently of the immutable image's 64-bit address bank.

**Definition 18.3 (primitive-prefix interpretation).** At a native cut
retain the current interpreted fields, the actual old PC, current interpreted vertex,
the prefix of captured operation/selector/reference fields, operand
snapshots, current native location, read/address latches, any performed
field write and the uncompleted continuation assignment. Before an
interpreted write, its effect is pending. After it, that exact write is
present, while the operation remains busy until continuation completion.
During emission the occupied bit and bx specify the actual unsent bit.
No partly written operand bank is mistaken for a completed new opcode.
Before its effect the state relates to the source operation with that effect
pending; after the effect it relates to its intended successor with control
commit pending. Recovering an overwritten old auxiliary field is not asserted.
The driver separately retains the old logical head/control and its pending
growth interpretation as required by Definition 15.2. A busy native state is
not another completed field or B operation.

**Theorem 18.4 (all-component forward and completed-operation converse).**
For every finite well-typed field graph of Definition 15.1, every valid
owned binding of its registers, directory/pages and sufficient finite
reserve, ML-P realizes every completed field transition by a finite
native primitive path with Definition 18.3's interpretation at every
intermediate cut. Conversely every completed operation on this installed
native path is exactly the next interpreted field operation on those
same actual objects, up to one consistent reference renaming at
installation. This assertion covers every component state in that valid
family, all allowed field selectors, all finite histories and waiting
prefixes. It is not inferred from a number of sampled programs.

Proof. Five one-bit reads determine the actual encoded operation;
sixteen further reads determine its actual selector. The separate latch
writes leave their prefix available at all intervening cuts. The four
reference captures preserve the actual operand bindings and both
successors. No write to an interpreted operand occurs in this prefix.
Induction on the depth of a binary selector tree shows that its current
location represents exactly the already read selector prefix, and that
its eventual valid leaf is the literal selector with those bits. An
invalid prefix has only the refusal continuation. The same argument
applies to operation dispatch.

For a reference copy, the source is captured before the destination
write, so aliases have their original source meaning. A get captures
the actual cell reference and reads the selected one of its four
fields. A set captures both actual cell and value before the selected
write. These are precisely the old field transition, including all
source/destination coincidences. Bit reads/writes use the same argument
with a separate binary latch. Directory and page paths have, respectively,
two and 32768 possible literal leaves; uniqueness of their selector
prefixes proves their exact physical field access. Null, equality and
bit tests use the captured operands and have exactly their declared
truth values. Local layout checks are true on the valid family and
prevent field access on a wrong local layout. The trusted code/binding
invariant prevents an interpreted program from acquiring native control
vertices as an indirect field-program continuation.

The finite continuation-binding path stores the actual captured code
reference. An indirect path reads that saved reference and retains it
as destination. For conditional paths predicate has the value of the
specified test; all other paths retain its reset zero. Therefore commit
assigns exactly the interpreted successor, once. Neither a scratch
write nor a test enables another commit. The emission path transfers
only its backed bx, and cannot clear occupied before that transfer.
The three response-phase paths enforce the stated End/Ack/Return order.
After commit, a native gate reads the actual waiting bit and tests its
captured value. One loops back to that read; zero proceeds to fetch.
An actual resume signal writes zero through the supplied input binding.
Even individual primitive stepping in the paused gate performs no new
code fetch or field commit. After resume the next gate read passes;
a previously captured one can add one finite loop. The outer author
scheduler only groups or pauses these already guarded transitions.
Delaying a granted primitive or supplied connection completion retains
its waiting cut and supplies no invented completion.

Every path just described is a path of the finite native graph. Its
enabled-operation length is finite: after the required resume, the
gate passes on its next read, selector depth is bounded by sixteen and
operand access templates are finite lists. Paused gate prefixes commit
nothing. Thus forward realization holds for
each operation. The cases exhaust the operation algebra and contain
only their stated effects. Induction on completed operations proves the
converse and composition for any finite history. The induction also
preserves the prefix invariant, since the next primitive either extends
a capture, performs its named write/test, or completes its named
continuation. No eventual halt is used. $\square$

**Corollary 18.5 (actual consumers and unrestricted finite domains).**
After the chronological relocation in §19, the native path supplies
Theorems 15.3, 15.5, 16.2 and 16.4 with actual field transitions, for
every finite generic B program/input/prefix, every valid fixed image
and every finite input/returned-word conversion on their original
assumptions. Both forward and completed-macro converse statements of
the generic B driver follow, including busy growth, proper-ancestor
appends, both crossings, repeated marks and nonhalting prefixes.

Proof. Apply Theorem 18.4 to each transition of the existing finite
component graphs, using the old/intended state and saved continuations
already retained in §§15–16. Their field transitions are unchanged;
therefore their earlier inductions compose with the primitive-prefix
interpretation. A chosen reserve bounds the owned material supplied
for one finite prefix; choosing a larger finite reserve covers any
larger finite demand. It imposes no common bound on a program, an input,
$N$, rational components, indices, cylinders or the length of a run.
The 64-bit premise belongs only to that fixed image's addresses and
its proved address arithmetic. $\square$

## 19. Chronological installation with retained literal source material

**Definition 19.1 (literal source and the initial ML-I boundary).** The
public installation input is the complete uncompressed image of
Definition 14.1, the encoded finite field graph, the complete native
interpreter graph, register bindings, received component input and all
chosen reserve cells. It contains no hidden source-dependent answers.
Its byte provenance is the unchanged A interface and code image; the
field graph is the composition of the existing public decoder, driver,
converter, output scanner and routing templates. All source objects
are actually retained, including unused reserve and padding pages.

For each source payload object introduce one descriptor with three
actual references: payload, next descriptor and initially null forward.
The descriptors form a finite chain. Payload reference fields point to
the corresponding descriptors, so relocation does not decode a numerical
object identifier. Each payload additionally has one retained directory
link. Layouts are the six fixed payload layouts in Definition 18.2.
Every source/descriptor object has its supplied current grant. This
literal public input is a separately supplied initial ML-I object;
forming it is not called an installer transition or erased from its
retained census. No claim is made that a gzip inflater executed on ML-I.
The selected installer receives the full uncompressed input and keeps
it. Its real target is constructed below, even when keeping both copies
is more expensive than an alternative representation.

As in Assumption 1.2, execution begins with a supplied native finite
transition graph and its authorized actual bindings. Here that fixed
initial graph is the literal installer and per-bit initializer graph;
its entire material and grants are counted from the first cut. This
uses the original ML-I primitive-control premise. It is not a new
operation that allocates, links or fills the eventual driver in bulk.
The code, decoder and executing interpreter beyond this initial base
are all targets of the chronological copy. This conditional initial
control premise is not a physical bootstrapping or bare P/S theorem.

**Definition 19.2 (initializer control and grants).** The initializer
retains descriptor head/current cursor, pending target, target-directory
head/tail, source-next latch, read-reference latch, source-payload latch,
target latch, a separately bound actual entry descriptor and its current
native location. Native execution's read,
saved-reference, address and current-location latches remain reserved
at the same cuts. The bit initializer retains actual source/target
binary-bank bindings, current native bit vertex, read bit and completion
flag. This bit header belongs to the instance; its initial source,
target and native-location bindings are null. Immutable primitive wiring
may be reused with separately supplied state headers, each counted from
its first cut. Shared-job union accounting remains the separate original
obligation in Definition 20.4. Allocation returns an actual fresh object
with its known layout;
a separate grant delivery is required before linking it into the target
directory. While that delivery is pending, the new object, its grant
slot, whole payload and directory link are already counted.

The initializer's outer control is a literal finite graph. A sequence
of six local arity tests selects one known allocation layout. For each
layout, each reference-field position has its own literal clear vertex;
there is no changing multibit offset. The allocated target's directory
link is cleared, its actual object is linked at the old target tail,
the tail is advanced, and the descriptor's forward field receives that
actual target. These are separate writes, with their intermediate cuts.
Only then are payload references individually cleared and payload bits
copied by Definition 19.3. Read the current descriptor's actual next
reference, assign the current cursor and test for end. At chain end,
restore the actual head and begin the relocation pass.

For every literal payload-reference position, relocation reads the
source field. Null remains null. For a nonnull descriptor reference,
read its actual forward field and reject a missing target. Write that
actual target reference into the current target's literal field.
Advance to the next source descriptor through the same read/assign/test
sequence. After the last relocation, read the bound entry descriptor's
actual forward field, refuse a null result, then write that captured
target into the execution-location slot in a separate primitive. Native
execution reuses this very slot; an observer's source-to-target map does
not install or replace its entry. A target address is never reconstructed
from a source index.
The finite field positions are fixed native vertices; the arbitrarily
long source chain is traversed by its actual next references.

**Definition 19.3 (binary initializer graph).** For each supported
positive bit width $h\in\{1,3,8,21,32768\}$ retain an actual chain
of $3h$ native vertices. At field $i$ its three successive vertices
write binary zero to the target's literal field $i$, read source field
$i$ into the retained bit latch, then write that latch to target field
$i$. The last write's next link is the first clear for field $i+1$,
or a shared completion vertex. That separate vertex sets the completion
flag and returns. Reuse clears that flag in its own native write before
binding source, target and entry; no header is reset in bulk. All selectors here are literal wiring of
these vertices. There is no runtime increment of a field index and no
word-copy instruction. A scheduler may execute many vertices before
returning to its host, but the same primitive state is available after
any one of them.

The private C implementation stores these actual linked vertices and
executes one switch case per primitive vertex. Its source and target
byte buffers are the same backing subsequently read by the native
interpreter; a second host constructor does not replace the copied
fields. The scheduler's step limit and counters are independent
inspection, not machine operands. C compilation is an implementation
of this stated mathematical primitive model, without a claim about
physical transistors or an erasing machine beneath the model.

**Theorem 19.4 (chronological all-source installation correspondence).**
For every finite valid literal source graph of Definition 19.1, with
its initial granted native installer and a sufficient fresh grant for
each requested target, Definitions 19.2–19.3 terminate. They construct
an injective target copy preserving every payload bit, every null and
all reference equalities and links. Each initialized code field, page,
operand binding, reserve successor and entry continuation is the one
actually consumed by ML-P. At every incomplete cut there is a unique
allocated-target prefix, a current pending grant/clear/copy/relocation,
its actual cursor/latches and a specified uncompleted suffix. Conversely
an installation reaching completion through these phases has precisely
that copy, with no skipped descriptor, field or grant.

Proof. Induct on the source descriptor chain in pass one. Fresh
allocation and grant delivery give a distinct authorized target for
that descriptor. Before linking, pending retains it; after linking,
the actual directory head/tail retain it. No future grant overwrites
an earlier target. The forward write records that same reference.
Induction on the literal reference-clear vertices gives binary-null
reference fields, each with its explicit initialization occurrence.

For a bit bank of width $h$, after $i$ triples the first $i$ fields
are exactly the source prefix. At the next clear the new field is zero;
after the source read its actual value is in the latch; after the write
it agrees with the source. All other target fields still have their
actual prior values. The next link leads to exactly the next triple.
This proves the invariant at every one of the $3h$ cuts and its final
bit equality. It proves the same sequence whether the host scheduler
runs one vertex or a batch. No tariff multiplication establishes any
part of this induction: the target writes occur in that actual order.

Source-next traversal advances exactly one actual chain link, so the
first pass visits every descriptor once and ends. All its forwards
are now defined and distinct. In pass two, a null source field yields
null; a descriptor field yields exactly that descriptor's recorded
target. Thus after its first $i$ reference writes the target's first
$i$ references are the transported source references. All old source
links are still present, so later relocation cannot change this lookup.
Induct on positions and then descriptors to obtain the entire graph
isomorphism. Initial PC and all saved code/data bindings are transported
by this same map, including sharing and cycles in payload links.
Only the descriptor enumeration chain is required acyclic.
The final entry read obtains the entry descriptor's same transported
target, and the separate control write delivers it without a numerical
address or observer lookup. The read/null-test/write cuts retain both
actual entry references and are part of installation.

Each source object has one of six finite layouts. Both outer traversals
and each finite field list terminate. The finite source determines a
finite number of allocations and grants. Delaying a supplied grant
preserves its pending state and is not a completion. There is only one
path to installation completion after the final relocation; hence its
completed converse follows from the same prefix invariants. Subsequent
execution uses the written target fields by construction, and Theorem
18.4 applies there. $\square$

## 20. Common installation cuts, exact charges and the remaining service

**Definition 20.1 (one retained census).** Let the source descriptor
count be $n$, the sum of payload reference arities be $r$ and the sum
of payload binary widths be $b$. Source payloads and descriptors occupy
$2n$ granted objects, $r+4n$ reference slots and $b$ payload bits. The
four extra reference slots per source object are its payload directory
link and its descriptor's payload/next/forward fields. Target objects
have their own directory link and grant. Let $j=98404$ be the retained
bit-initializer vertex count, and let $\ell$ be the actual outer
initializer graph's vertex count. A bit vertex has twenty-two literal
binary fields and one next reference; an outer initializer vertex has
twenty-one literal fields and its actual successor/binding references.
The complete native interpreter is already among the $n$ payloads;
it is not free initial-control material.

At an installation cut let $A$ be exactly the allocated target set,
including a not-yet-linked pending object. Write $r_A,b_A$ for its
payload arity sums. The live counts are the counts of that source,
the whole initial native graph and its latches, and

$$
|A|\text{ objects},\qquad r_A+|A|\text{ references},\qquad
b_A\text{ payload bits}.
\tag{ML.24}
$$

Each live object has its one actual grant slot, even when delivery is
pending. Initial bit-control vertices, outer-control vertices and both
initializer state headers retain explicit grant fields supplied as one;
source payloads/descriptors and target objects retain their own fields.
Multiply all reference slots by the one chosen width $w$,
then add payload/literal bits and these grant slots. The chosen $w$
fits every source, target, descriptor, native vertex and null binding.
It depends on this finite material, not on the 64-bit image-address
premise. Neither a receipt nor a retained root outside this component
is silently identified with an initializer object.

**Theorem 20.2 (census, incremental charges and peak agree).** At every
initializer cut, independent traversal of its actual target directory,
plus the still-unlinked pending target if distinct, has precisely the
allocated set $A$ of (ML.24). Incremental object/field charges equal
that census. The source and all partial target material coexist at
these cuts. Completed relocation keeps the entire source, target,
initial native graph and grants. Their retained storage is therefore
the peak of this installation; no early source deletion or incompatible
single-component peaks reduce it.

The bit initializer executes exactly $b$ target-bit initializations,
$b$ source-bit reads and $b$ target-bit writes. Reference initialization
executes exactly $r$ writes. Pass two executes exactly $r$ source-field
reads and $r$ target-field writes, together with its actual null tests
and forward reads. Each source/header reference read separately counts
its returned initializer-latch write; each source-bit read counts its
binary-latch write. Binding the actual bit-graph entry counts both its
literal-reference read and its cursor assignment. Allocation counts
its returned-reference latch. These effect coordinates accompany the
same primitive occurrences and do not invent extra primitive steps.
Every advancing native occurrence has its selection, successor-reference
read and control-reference assignment. A terminal refusal counts its
selection and refusal, with no unperformed successor read or assignment. Allocation,
directory linking, forward writes, grants and cursor operations have
their separate actual event coordinates and reference-width traffic.
These counts are component counts on this one timeline, not ML.16 for
a complete evaluator/session.

Proof. An allocation adds exactly its known payload fields, one
directory link and one grant slot. Before directory attachment it is
reachable from pending. Attaching it introduces no new object; advancing
tail or forward preserves the same set. When a later pending object
replaces it, the old one is already retained by the directory. The
pending/directoried union therefore grows by exactly one object per
allocation. Inductively its arity sums agree with incremental charges.
All null fields, cleared bits and unused reserve remain material;
initialization and extraction do not remove their slots.

The source descriptor chain, source payloads and fixed initial control
are unchanged. Partial targets add the nonnegative coordinates of
(ML.24); no transition removes a source or target. Thus completed
allocation attains the maximum retained coordinates, including during
relocation. Theorem 19.4 gives one triple per payload bit and one clear
and relocation per payload reference, proving the displayed operation
counts. Following each actual native vertex contributes its stated
control events. The outer graph's grants and list operations have
exactly their own occurrences. This establishes agreement on these
same chronological cuts rather than by adding unrelated maxima.
$\square$

**Proposition 20.3 (omission discriminators).** Removing one counted
source-bit read while retaining all installed target bits falsifies
the exact initializer event census. Removing a real native field read
while retaining its executing vertex falsifies the primitive event
census. Replacing the first encoded put-one in an emission graph by
encoded goto changes its emitted bit from one to its initialized zero.
Premature Ack, Return without Ack, a selector four on a four-reference
cell, and exhausted reserve have no completed lawful successor.

Proof. Theorem 19.4 requires each actual source bit to pass its read
vertex, so the first omission gives $b-1$ instead of $b$. Each native
read vertex contributes exactly one read occurrence; omitting it from
charges disagrees with that occurrence enumeration. In the mutation
example the skipped put is the only pre-emission write of one, so the
bit remains zero. The other cases fail their explicit guard/tree
before their prohibited effect can commit. $\square$

**Definition 20.4 (remaining original integration objects).** The
native field engine and chronological public-material installation
are component dependencies of the original service, under ML-I's
initial primitive-control and actual-source-input premises. They do
not supply a completed received-command/frame/parser/loader or its
semantic validation, a backed Evaluate/Read/Predict/Close controller,
the unchanged physical original-root Read handoff, the original-source
receipt/index cache, shared-job directory, cleanup, width migration or
an entire source/observer common timeline. Existing `session.records[-1]`
and `framing.Print.emitted` retain their operational roles and their
uncompleted backing obligations. A law evaluator still cannot provide
an actual Read reply. All earlier work roots and original source
provenance remain required for later composition.

The original strict findings `ML-N-evaluator-execution` and
`ML-Cost-full-evaluator-session` remain. Completing these two component
dependencies does not declare B complete or release C. D and fresh
independent acceptance remain subsequent obligations. Ordinary
correspondence is a conditional mathematical proof, not a new Lean
verification, physical realization, encoding minimum, full serial-history
recovery or quantum frontend. The initial-control premise is explicit;
removing ML-I allocation/field/control rights would require a different
theorem. The native field and installation graphs introduce no such
rights for the original observation source.

**Definition 20.5 (source correspondence and evidence use).** The
executable definitions are `native_engine.Core.build` and
`NativeEngine.microtick` for §§18–18.5, `native_install.Installer` and
`native_bits.initialize` for §19, and their actual directory traversal
and event counters for §20. The connected caller composes the unchanged
`field_decoder.lower`, `field_graph.loader/driver/growth` and
`field_io.conversions/output_decoder/print_buffer`. Its production mode
is the original conversion/driver/output path. Its additional probe
mode is a real installed caller of the same decoder, transferring its
actual result fields with End/Ack/Return; it does not inject an
instruction into the production driver. Native conversion and output
checks consume these installed primitive paths.

All-image byte provenance and the A interface are unchanged. The source
and license scope in §9 and §§10–14 remains: NWMG and the licensed stack
compiler supply their existing structural simulations; §§18–20 are an
ordinary repository-derived implementation/refinement and accounting
argument. The later C119/C123 conditional comparison/filter results do
not supply an original-port service, a LAB-native quantum map or any
missing literal controller. No new literature novelty is claimed.
Exact finite author results corroborate their stated component cases;
the all-family conclusions use Theorems 18.4 and 19.4, with all their
premises. Result data and reproducible experiment sources are private;
process logs and model reasoning are not theory evidence.

## 追加锚（本行以下为增补区）


## 21. Exact storage of the selected native installation

**Definition 21.1 (literal layout counts).** In Definition 20.1's
notation, the selected outer initializer graph has $\ell=167$ actual
vertices, with three reference slots each: zero successor, one successor
and a literal binding, null when unused. Its twenty-one binary fields
encode a five-bit primitive label and sixteen-bit literal. The literal
binding at a bit-bank entry is the actual first bit-initializer vertex,
not a dictionary lookup or a numerical graph-address conversion.

The bit-initializer graphs, including their one shared completion vertex,
have exactly

$$
j=3(1+3+8+21+32768)+1=98404
\tag{ML.25}
$$

vertices. Each carries a fixed twelve-bit byte position, eight-bit
one-hot field mask, two-bit primitive label and one actual next link.
These are literal native location labels/wiring. The C runner's limit
and occurrence counters are independent scheduler/inspection data.
There are no running multibit byte or field counters in the graph.
The C occurrence counters are external instrumentation modulo
$2^{64}$. Each bounded scheduler batch is shorter than that modulus;
its modular counter differences are added to unbounded external integer
coordinates. Counter rollover changes no primitive, reference, result
or original program/input domain.
The bit initializer's retained state has three reference bindings
(source bank, target bank, native location) and two binary flags.
The remaining header reserves fifteen actual reference locations and
two flags: the ten outer descriptor/target/latch references and its
native location, plus the four native execution locations/latches;
its binary flags are outer completion and the execution read-bit latch.
The execution's old-PC register is a separate payload object among the
$n$ copied source objects, in addition to its current PC.

**Theorem 21.2 (completed census and reference traffic).** The selected
completed source-plus-target installation has exactly

$$
\begin{aligned}
O&=3n+98573,\\
R&=2r+5n+98923,\\
B&=2b+2168399,\\
S&=B+wR+O.
\end{aligned}
\tag{ML.26}
$$

Here $B$ counts payload and literal binary fields, and the final $O$
counts the one grant slot per object. At an earlier cut replace the
target's $n,r,b$ contribution by $|A|,r_A,b_A$ as in (ML.24).
Null and pending fields retain their full width. After installation,
reserve extraction changes no term of this census.

For primitive traffic, a reference-field/register read or write, a
reference-latch assignment, and a native successor/current-location
read or assignment each transport their actual $w$ reference bits.
Code-reference reads are a classified subset of reference-field reads;
code-bit reads are a classified subset of binary-field reads. These
subset counters are not added a second time to the corresponding
total-field coordinate. A field read's returned latch remains charged
in the distinct latch-write coordinate. Tests, bit assignments,
connection transfers, grants and directory operations retain their
separate coordinates. A completed interpreted operation has exactly
21 code-bit reads and four code-reference reads, followed by its
actual operand/selection/write/commit path.

Proof. Source payloads and descriptors contribute $2n$ objects,
$r+4n$ references and $b$ payload bits. Targets contribute $n$ objects,
$r+n$ references and $b$ payload bits. The outer header contributes
one object, fifteen references and two bits. The initial bit graph
and its state contribute $j+1$ objects, $j+3$ references and $22j+2$
bits. The outer graph adds 167 objects, 501 references and 3507 bits.
Adding gives (ML.26). The two flags and three bit-initializer bindings
are not duplicated in the outer header. All grants are counted once
by the final $O$. Theorem 20.2 gives the earlier cuts and peak.

Each primitive reference occurrence has the declared width $w$, so
its bit traffic is that width times its actual occurrence count. Its
read-result latch is a different stored location and has its own
write coordinate. Classified subset counters refer to those same
occurrences. The initial fetch's five, sixteen and four literal-read
paths give the last assertion; all subsequent decisions use the
captured fields. Theorem 18.4 determines their actual path, rather
than assigning the same price to every interpreted operation.
$\square$

## 追加锚（本行以下为增补区）


## 22. Received ML-F words with represented validation

**Definition 22.1 (the service field configuration).** The particular
service graph has persistent actual references to the initialized public
word, the original port connection, the receipt-chain header and an
original-indexed cache. All other variable data are linked objects,
reference registers or binary registers. Every such object is a
four-reference/eight-bit reserve cell of Definition 15.1, including
headers and temporary counters. This deliberately overprovisions small
records; all unused fields and grant slots remain charged. Reference
one is the next-bit link, and header references one and two are head
and tail. A receipt uses reference three for its next-receipt link.
The cache uses one such cell per original coordinate, with mask in
bit zero and value in bit one. Thus its logical mask/value word is
still exactly Definition 5.1's indexed restriction, although this
physical layout differs from that definition's two separate bit chains.
No equality of observed values merges two cache cells.

The received connection has three separately backed binary fields:
bit, End and occupied. A producer supplies an actual binary bit or
End only at an empty input latch. The receive graph copies an actual
bit into its retained bit register, clears occupancy, appends that
bit to the request chain and returns to the receive test. Its append
retains fresh cell, old tail and continuation through the same
initialize/link/tail phases as Definition 15.1. Missing input loops at
an installed waiting gate; resumption does not replace the graph PC.
At End the parser begins at the actual request head. There is no
host-supplied length, offset, parsed command or acceptedness flag.

A syntactically proper incomplete prefix retains its request and waits
for further received bits. On the next End, parsing restarts from that
same chain's head, now with its actual appended suffix. Old parser
backing remains allocated and counted; restarting is not a rollback
of acquisition or work. A nested V payload is already a complete word,
so a missing field inside that word is BadFrame rather than a request
for bits beyond its boundary. A represented strictness bit distinguishes
these cases. A malformed completed command or semantic payload produces
Definition 4.1's actual BadFrame. Input scratch is not a source reply.

**Definition 22.2 (lengths, naturals and semantic scans).** The entry
ReadV retains a stack containing one actual token for each leading
unary mark. After its delimiter it reads one payload bit per popped
token and appends it to a fresh word header. Both its token stack and
unfinished output remain real material at every cut. ReadU additionally
rejects an empty payload and a leading zero except for the single-bit
word zero. These are the original U representations, not machine-word
integers.

When a numerical loop count is needed, convert its actual MSB-first
canonical payload to a unary list. For each received digit, traverse a
snapshot ending at the old tail and append one token per old token;
then append one token if that digit is one. Snapshot, current token,
old tail, next token, digit and unfinished append are retained. This
is repeated doubling on a linked word, with no fixed numerical bank.
It is intentionally sufficient rather than a claim of economical
arithmetic.

The N validator requires three or more canonical payload bits, which
is exactly N at least four. Its unary value drives an outer scan;
fifteen literal append blocks per token construct exactly 15N paired
cache-shape cells. A prior reads sign zero and two canonical unsigned
payloads. The denominator must start with one. To compare numerator
with denominator, scan their actual chains in parallel, retain the
first unequal pair, and first decide by total length, using the retained
pair only when the lengths agree. Reject numerator greater than
denominator. Neither payload is reduced or recoded.

Mask validation reads one actual mask bit per shape cell, then rescans
that new mask and reads a value bit exactly at selected positions.
Cylinder validation reads its conflict flag. One requires an immediate
end of that V payload. Zero requires a whole mask/value word with no
trailing bit. A cylinder list reads its canonical unsigned count,
converts that count to a unary list and consumes one actual V word
per token. Its outer cursor, inner cursor, remaining count, shape and
strictness are distinct retained locations. Arithmetic validation
composes precisely these operations: N, prior, cache, cylinder list,
then end. The original arithmetic payload itself is retained unchanged
for the later loader.

**Theorem 22.3 (complete ML-F acceptance and prefix interpretation).**
Under ML-I's actual binary input and sufficient finite reserve, these
scans accept exactly the original well-formed initialization,
Evaluate, Read, Predict and Close inputs of Definitions 4.1, 4.3 and
5.2. They preserve every accepted finite N, prior representation,
mask/value assignment, cylinder count, cylinder and original operand.
There is no common bound on their lengths or numerical values. Proper
incomplete prefixes cannot reach a source call or evaluator loading;
malformed completed semantic payloads cannot be loaded. Each completed
parse has the same decoded command as ML-F on the same received bits.
Every intermediate scan has a retained unread suffix, token count,
partial result and actual continuation.

Proof. After k unary marks, ReadV has exactly k tokens. After i payload
bits, its result is exactly their actual prefix and its remaining stack
has k-i tokens. This induction proves the V contract including the empty
word. The additional two ReadU tests are exactly canonical unsigned
syntax. In unary conversion, if the already consumed digit prefix has
value c, its list has c tokens. Snapshot traversal appends precisely c
more without visiting the newly appended suffix. The optional final
append gives 2c+d. Induction on digits proves arbitrary finite counts;
all scans are finite even when that representation is large.

Canonical positive words have leading one. A canonical word with at
least three digits is exactly a natural at least four. The fifteen-fold
literal loop therefore constructs the exact shape, without reducing N
modulo a register width. Parallel length comparison decides natural
order when lengths differ; the first unequal digit decides it when
lengths agree. The denominator test and sign test are precisely the
prior's stated domain. In particular zero over any positive represented
denominator, equal unreduced numerator/denominator, and all intermediate
unreduced representations survive unchanged.

Induct on shape positions for masks: the first pass fixes all selected
positions, and the second consumes precisely their values in original
order. Induct on the unary cylinder count for lists. The strict inner
boundary prevents a cylinder from borrowing a later cylinder's bits.
Its conflict case consumes no mask, exactly as ML-F requires. The four
command tags and Predict's variant bit give disjoint exhaustive cases;
Read has an arbitrary V operand, and Close has no payload. End tests
exclude all trailing bits. Conversely every successful scan has passed
these same tests and consumed exactly those words. Thus successful
parse and original acceptance coincide.

Each loop consumes a finite old list or digit word. The only unbounded
wait is a missing supplied input completion; it has no parse commit.
At any partial append the fresh object and old tail are retained, and
at any partial read the current cursor and read bit are retained.
A repeated parse uses exactly the accumulated received chain. These
facts prove the internal-prefix assertion and completed-parse converse.
They do not assert a full evaluator execution. $\square$

## 23. Literal Read, receipt and Predict consumers

**Definition 23.1 (two literal output connections).** The service's
encoded field graph retains the existing five-bit operation and
sixteen-bit literal selector. Its emit, End and Ack operations use
literal selector zero for the ordinary output connection and one for
the original-call connection. The specialized native interpreter tests
all sixteen actual selector bits, rejects every other value, and ends
at one of two separately wired primitive paths. Emit retains its payload
in bx and reloads bx after this connection selection, before its actual
bit transfer. Connection-selection tests therefore cannot replace the
payload bit. Old field graphs keep the unchanged selector-zero path.
All other operations retain Theorem 18.4's paths and guards.

The second connection is physically bound to the same supplied original
port, root and current Read authority. Each operand bit is sent there
from the actual received operand cursor. A physical transfer sets one actual bit/occupied peer latch. The
installed graph then tests its occupancy, reads that bit, appends it to
a real transmitted-word header, and clears occupancy in a separate
field write before advancing the operand cursor. The header, latch,
old tail, pending cell and next cursor survive all these intervening
cuts. A call is disabled until the last peer append/release completes.
The received chain, rather than a host-collected output string, is the
backing of the actual transmitted word. Its invocation is exactly the supplied
original-root call of Assumption 1.2, using that word and the unchanged
provider `OriginalPort.call`; it is not a law evaluation, a new probe
menu or a numerical source reference. The private provider keeps its
own field traversal and tariff of Definition 6.5. The call returns its
actual occupied two-bit latch. The service captures its two separate
fields before acknowledging that latch. The connection, its pending
request, returned latch and provider material remain part of the same
configuration. Source-call completion is an ML-I premise, not an
assertion that the observer has compiled the provider or its hardware.

The private connection adapter's word projection denotes its actual
backed transmitted word at this supplied call boundary. It supplies no
service cursor, classification, command, cache update, evaluator result
or next continuation. The original provider's own buffer traversals and received/reply
backing retain their original charges. The new connection acknowledge
only releases its actual occupied reply latch; it performs no bulk
buffer clearing. Both native transmission backing and provider-return
objects remain retained and paid. Their existing host
implementation is not claimed to be another native service program;
a fully primitive joint provider/allocator timeline remains an original
integration obligation. No composite parser, arithmetic operation or
controller step is promoted to an ML-I primitive.

**Definition 23.2 (classification on original cache positions).**
Classification starts with the actual operand cursor and the cache's
first coordinate reference. At an R it advances both cursors. If the
operand ends before the coordinate chain ends it is a constant branch
reply. At the first L it retains that current coordinate and traverses
a fixed depth-two suffix trie. Its two possible replies are precisely
Definition 5.2's complete slot table. A longer suffix is constant absent.
When the coordinate chain is exhausted it instead uses the depth-three
fixed-marker trie; longer suffixes are absent. A pair with equal replies
clears the designated coordinate reference. A differing pair retains
that exact cell and its two reply codes. Thus neither an operand length
nor an original index becomes a numerical control label.

On actual return, create a fresh receipt header and its payload
V(operand) followed by the two captured reply bits. Retain the old chain
tail, link the new receipt through its next-receipt field or the chain
head, and only then advance the chain tail. These separate writes are
actual field operations. The payload has exactly 2|w|+3 cells even for
a repeated or constant operand. No historical record is consulted to
supply the current reply.

For an informative position compare the actual code with both retained
public-table alternatives. The chosen alternative determines its zero
or one. If the mask is already set, compare the existing value before
writing; a disagreement refuses. Then write the mask and actual value
in separate operations. A constant verifies its actual code and changes
no coordinate. Build the Read service frame from the captured reply
bits, traverse it to actual output, then End, Ack and Return. Input is
disabled throughout this busy path.

**Theorem 23.3 (original-port and indexed-receipt correspondence).**
For every finite N at least four, every promised array z, every finite
operand sequence and every legal internal prefix, the installed Read
path has the same literal source returns, ordered occurrence receipts
and original-indexed restriction as Definition 5.2, whenever its supplied
calls and finite reserve complete. This includes all constant/absence
classes, long extensions, partial slots, old-slot requests, repeats and
distinct original indices having equal observations. The assertion
requires no positive prior mass. It preserves both original once-shared
full injections when that probabilistic model is used, without reading
or redrawing them. Completed-operation converse holds for each handler.

Proof. Prefix-tree induction on all sixteen selector bits gives exactly
the declared zero/one connection leaf, with a refusal otherwise. Reloading
bx after that tree preserves the actual payload rather than its last
selector bit. The remaining field operations use Theorem 18.4 unchanged.
For peer reception, after k completed append/release cycles the actual
transmitted header is exactly the first k emitted operand bits and the
latch is empty. At a transfer it contains precisely the next real bit;
its append and separate release restore this invariant. Thus the supplied
finite-word original-call boundary receives exactly the whole emitted
word, with no new host selector or collected-output consumer.

Each R advances one original coordinate; it can neither skip a
coordinate nor merge equal values. Before exhaustion its first L and
finite suffix select exactly the slot table of UJB5.3. At exhaustion,
the marker trie is precisely that theorem's fixed final marker. Every
longer extension is a strict leaf extension and hence absent. These
cases exhaust every finite operand, including one ending on the spine.

The emitted operand is its received chain read in order. The actual
bound original call supplies exactly that source's value. Capturing
both returned fields before Ack preserves that actual value throughout
receipt, cache and answer construction. Appending a receipt first makes
it reachable and only then advertises its tail; saved old/new references
interpret the intervening cuts. Inducting on calls proves that the
chain has precisely the ordered occurrences, not just distinct operands.

At a differing pair the two alternatives are injective in the one
retained original coordinate. Its comparison therefore recovers that
actual bit, even when an alternative is absent. A repeat verifies the
old bit and retains another occurrence. Equal pairs yield no restriction.
This is exactly Theorem 5.3's restriction operation. No graph vertex
grows, copies, resets or rebinds the source. Its actual array and any
full maps underlying it stay fixed. In particular an array outside both
prior supports is still a valid literal source for this theorem.
Every control alternative is fixed by the same captured operands and
actual code. The only route to Return passes the specified append,
update and output operations once, giving the completed-handler converse.
All their intermediate references and bit latches remain represented.
$\square$

**Definition 23.4 (the particular evaluator and Predict controller).**
Evaluate retains the actual validated arithmetic payload and passes its
head to the unchanged converter of Definition 16.1. The production
service graph contains the complete fixed A image decoder, the original
361-register conversion, loader, generic growth/maintenance and B driver,
and actual returned-header decoder of §§12–19. Its B boundary goes
directly to the next installed step, and its halt boundary goes directly
to the actual output decoder. There is no host decision to choose another
B instruction. No smaller evaluator or answer table replaces this path.
The decoder's output is wrapped as an Arithmetic service payload and
printed from its actual bit chain. Re-entering Evaluate uses fresh paid
work material and retains every older root and its routing cells.

Predict uses the initialization's original N/prior bits and its current
attained indexed cache. It serializes all mask bits, then only the selected
value bits in original order. Variant one validates and copies the actual
cylinder list. Variant zero classifies its actual operand as above and
constructs four cylinders in reply-code order. An impossible code gets
only the conflict flag; a possible constant gets the empty mask; an
informative alternative gets exactly one mask bit at that retained
coordinate and the corresponding value. The resulting actual ML-A frame
enters precisely the same complete evaluator path. Predict contains no
original-call operation. Close emits its framed closed response and
ends at a permanent input-disabled waiting gate.

The frontend-only author component replaces the evaluator suffix by an
explicit backed busy/ready latch and waiting gate. It supplies no output,
normalizer, ratio or returned head and is never a production evaluator.
A check at that gate establishes only the acquired evaluator input.

**Theorem 23.5 (conditional particular-service composition).** For every
valid original initialization and finite legal command history, the
production graph has the received-input, Read, Evaluate, Predict and
Close meanings of §§4–5, subject to ML-I, the actual complete image,
sufficient finite material and the stated primitive completions. Every
intermediate operation has its represented source interpretation and
every completed handler has the specified converse. Predict uses the
same attained restriction and no new source response. Its arithmetic
payload retains null evidence, and ratios exist only when the actual
base normalizer is positive.

Proof. Theorem 22.3 supplies acceptedness without a host parser and
preserves the original arithmetic word. Theorems 16.2 and 18.4 transport
that very word into the original serialization/copier/NWMG encoding.
Theorem 19.4 transports the entire supplied code and bindings into the
executing target. Theorems 11.6, 12.2, 12.4 and 13.2 identify its fixed
computation on every accepted input; Theorems 15.3 and 18.4 identify
each actual B macro and every primitive prefix. The autonomous boundary
has exactly the old step successor; it changes neither a B instruction
nor a growth phase. At halt, Theorem 16.4 reads the output from the
actual returned head. Framing wraps those actual decoded bits. Thus a
completed Evaluate returns exactly ML.5, conditional on that actual
execution, rather than on an external answer.

For Predict, its first serialization pass is exactly the current mask,
and its second is exactly its selected values. The public parameter
word is unchanged. For each response code the classification proof
identifies exactly its constant event, one-coordinate event or empty
event. Wrapping these in the original order therefore constructs the
four required cylinders. The explicit list variant is the received
list itself. These are accepted ML-A frames, so the same evaluator
argument applies. UJB17.1 supplies their conditional interpretation at
positive evidence; Theorem 11.6 supplies NullEvidence otherwise. None
of these operations invokes the original source or selects its reply.

Theorem 23.3 handles each actual Read. Close and BadFrame use finite
literal payloads and the same physical Print/End/Ack/Return path. Their
phase guards prevent an output or new command in an unfinished handler.
Induct on completed commands, and within a command on completed field
operations, using Theorem 18.3's pending interpretation. The graph cases
are exhaustive and deterministic on the same actual configuration.
This gives both the forward assertion and completed-operation converse;
a delayed supplied call, bit or acknowledgement remains a pending cut.
No executed full evaluator witness is inferred from this ordinary proof.
$\square$

## 24. Service material, source correspondence and integration boundary

**Definition 24.1 (actual service material and traffic).** Let n,r,b be
the actual literal installation source's descriptor count, reference
arity sum and bit-width sum for this service graph, its native graph,
all registers, chosen reserve, image pages/directory and initial bindings.
The new native operation labels still fit five bits and every native
vertex still has the same four-reference/twenty-one-bit payload. Thus
the native installation account (ML.26) applies to this actual n,r,b,
with exactly its chronological partial-target and grant cuts. Service
connection-selection code is among n; it is not a free dispatch action.
The chosen reference width must cover this whole installed family and
all its nulls, independently of the image's fixed 64-bit address premise.

Every header, V length token, unary numerical token, input/output cell,
paired cache cell, receipt header/payload, saved continuation, scan and
partial append is either a counted register or an extracted object in
that paid reserve. At a service boundary k=15N cache positions occupy
k+1 reserve cells, hence 4(k+1) reference and 8(k+1) binary fields,
including padding; their grants remain counted. At a completed receipt
prefix with a calls and total payload length L, its chain/header and
payload occupy 1+a+L reserve cells, with 4(1+a+L) reference and
8(1+a+L) binary fields. These are classified subsets of the reserve,
not extra additions to (ML.26). Its exact logical payload length is
still the sum of 2|w|+3 over every invocation.

Charge every actual native code/operand/selector/read/write/commit
occurrence as in §21. A connection selection has its actual sixteen-bit
test tree and payload reload. Input deliveries have their actual latch
writes; all transmitted operand bits, original invocations, returned
bits, occupied latches, acknowledgements and provider/connection scans
have their own tariff. An original invocation is charged even when its
address or value has already occurred, or its law has zero mass. Neither
distinct-address counting nor a calculated distribution pays for it.

At each reported service cut retain the actual installed material,
connection material and same original source/rights. Their component
censuses describe that common cut. They do not supply a common physical
reference naming/widening construction or permit addition of unrelated
component peaks. Connection and provider arenas retain their real buffers,
grants, clearing and free-list backing. They are not silently assigned
the field-machine's fixed width. A full unified width/overlap/allocator
and source-observer account remains required before ML.16 can be claimed
for the original complete evaluator/session.

**Proposition 24.2 (reserve-parametric accounting and its limit).** Every
finite service-prefix demand in this construction has a sufficient finite
reserve, and its actual installed component storage and native operations
are charged by Definition 24.1. This gives no bound on N, rational payloads,
original indices or input/run lengths. It does not discharge shared-job,
free-pool, width migration, acknowledgement cleanup or full common-timeline
obligations merely by retaining an unused reserve.

Proof. A finite received prefix creates finitely many append and parser
objects. Each completed validation traverses finite words; every unary
value constructed from a finite binary payload is finite. Each completed
Read constructs one finite receipt and answer, and a terminating evaluator
has a finite work prefix under the existing correspondence. For a finite
history their extraction counts have a finite maximum. A reserve at least
that maximum suffices, with all unextracted cells charged from installation.
No numerical domain bound enters this existence argument. The source is
unchanged throughout, with its own inherited material and provider traffic.

Every extracted cell already has exactly the fields charged in (ML.26).
Every service register and native path is part of its installed graph.
Pending allocations, reply capture, unlinked receipt and output latch are
retained at their simultaneous cuts, so no operation or pending object
is erased by a phase change. But this construction retains spent scratch
and older work material; it does not yet implement a shared reusable-job
allocator or reclaim all retired backing. Fixed-width component fixtures
also provide no widening/overlap proof. Those missing constructions cannot
be inferred by summing these partial censuses. $\square$

**Definition 24.3 (exact executable correspondence and evidence scope).**
`field_service.Service.receive/routines` implements §22;
`Service.classifier/commands` implements §23's actual operands, linked
receipts, paired cache, Predict serialization and framed responses.
`service_graph(height,361)` is the production composition with the
unchanged complete A image and its actual decoder/converter/driver/output
consumers. `service_native.ServiceCore` expands the two literal connection
choices, and `ServiceEngine` uses the chronological native installer.
`OriginalConnection` binds exactly the original provider, not a sampler.
Its source-independent transport is distinct from the service controller.

The new production graph reads neither `session.records[-1]` nor
`framing.Print.emitted`. It supplies concrete replacement receipt/cache
and output consumers on its own path. The older reference/session path
still reads those values and retains its previous operational/backing
obligations whenever that path is used; they are not relabelled audit-only.
An original full-execution acceptance must actually use the replacement
path through arithmetic return, framing and the next original Read.

The author checks distinguish independent field-transition grammar
comparisons, installed native frontend/Read/Predict checks, the actual
complete-image conversion/initial-loader prefix, and the separate existing
component/reference suites. A missing original arithmetic LAB execution is
not replaced by a frontend ready latch, fixture output or stack-reference
run. Operation omissions must change actual received-source operands,
receipts, cache or output, in addition to any count discrepancy. A source
mutation, replay substitution or host-calculated answer is no success case.
The exact private results bind source bytes and measured component cuts.
They are finite corroboration of the ordinary all-family inductions, not
new Lean verification or independent acceptance.

**Definition 24.4 (remaining original objects).** The conditional service
correspondence and its selected native consumers do not close the original
integrated LAB-driver delivery, shared jobs/free-pool/width overlap and
cleanup, full source-observer common timeline, or whole-family integrated
author checks. The original strict objects `ML-N-evaluator-execution` and
`ML-Cost-full-evaluator-session` remain not-executed until the original full
positive and null evaluator runs, actual Arithmetic output/framing, original
Read continuation and complete same-run census execute. B completion, C
release, D completion, fresh independent acceptance and completion of the
long research goal remain separate later obligations.

The source supply remains NWMG, the licensed stack compiler and the exact
UJB/AA/PG scopes in §§9–21. This appendix is ordinary repository-derived
parser/controller/refinement mathematics, with no new universality,
minimality, physical realization, actual serial-history recovery, FIB or
quantum frontend claim. The source port and initial primitive-control,
valid-literal-input and current-rights premises are retained. Input is
repo-prior-exposed; no context sterility or model diversity is asserted.

## 追加锚（本行以下为增补区）
