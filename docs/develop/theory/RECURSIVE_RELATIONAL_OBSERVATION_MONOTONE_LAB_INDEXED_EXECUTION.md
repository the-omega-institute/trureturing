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
NWMG's successive-configuration copying and its 10/11 compiler
effectively give a finite B program, a finite computable input encoding
and a decoder of each simulated configuration. The last complete copy
is selected by the copying simulation's active configuration and head
convention. In the copier choose finite boundary/length delimiters as
part of its encoded configuration records; these are written on the
fresh copy, not supplied by an extra readout primitive. The copy loop
already scans the entire finite old configuration; it copies this
metadata, writes the new length and places its head at the selected
new block. This finite bookkeeping preserves the usual copying
simulation and makes that block's bounds readable. Decode the B
10/11 pairs to that non-erasing configuration and scan its selected
block's triples and ML-T's output delimiters. This recovers precisely
the framed output. These are finite scans of the
actual halted tape, using owned buffers, not a return-value oracle.
The input conversion and these scans are themselves charged bit
algorithms. Theorems 2.3 and 3.3–3.4 realize the resulting B run and
its actual finite tape. ML-F then gives Print, acknowledgement and
Return. At zero evidence the only conditional answer is the explicit
NullEvidence tag. $\square$

**Definition 4.6 (selected lowering ML-N).** Let $W_U$ denote the
finite B program obtained from ML-T with the NWMG copying construction
of §2 and the thirteen-instruction state blocks of §3.1, using its
10/11 non-erasing-symbol encoding and terminal M. The finite copier
metadata convention is the one in the preceding proof. Use the
enumeration order of ML-A, low-bit-first integers and finite record
scans of ML-T; within the copying/transition construction use the
state order of that finite machine description. This fixes an
effective finite-code construction, whose choices of state names
have no mathematical effect. Its initial B word is the compiler's
finite encoding of the actually received ML-A word, with its head
at the compiler's first encoded symbol. The instruction realization
ML-B starts at cell 0 of that encoded input. $W_U$ is installed
from public algorithms alone and works for all represented $N$ and
data; it is not reselected after observing a hidden source. Its
finite construction, input conversion and encoded-output decoding
are distinct paid phases. No arbitrary adaptive/oracle-controller
compiler is included in ML-N or needed by the session handlers.

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
retained distinct roots, retaining all their routing storage. Add the
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
| NWMG, primary pp. 4–9 | Effective finite TM-to-non-erasing-to-B simulation, repeat M, bilateral motion, fixed instruction jumps and decodable configurations. Its abstract tape-time bound is not a LAB resource vector or an original-source port implementation. |
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
